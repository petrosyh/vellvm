(** * TopLevelObs: observation-instrumented pipeline entry points (NI testing)

    Everything the NI testing pipelines add on top of the stock Vellvm
    toplevel lives here, so the original files (Denotation.v,
    InterpretationStack.v, TopLevel.v, Theory/...) stay identical to the
    upstream base (9557f168). Contents:

      - [event_obs] / [observe_L2] — the L2 observation tap: walks the
        L2 itree, records observable events ([Load]/[Store] addresses,
        [DebugBranch] directions, [DebugCall] targets) into a [list Z],
        and re-emits every event unchanged (pure instrumentation).
      - [interp_mcfg4_exec_obs] — the executable interpretation chain
        with the tap inserted between L2 and the memory interpreter.
      - [DObs] — the observation-instrumented denotation instance
        (DenotationObs.v) over the same parameters as the stock
        [IS.LLVM.D].
      - [address_one_function_obs] / [denote_vellvm_obs] /
        [interpreter_gen_obs] — obs variants of the toplevel entry
        points: function bodies are registered with
        [DObs.denote_function] so internal calls also emit the
        branch/call observations.

    Companion files: DenotationObs.v (the emitting denotation),
    LangObs.v (its Lang assembly, used by the taint tracker).

    Observation encoding (decoded by NITests.v's [z_to_obs]):
      Load  at address a  ->  a
      Store at address a  ->  -a
      DebugBranch true    ->  1000000
      DebugBranch false   ->  1000001
      DebugCall z         ->  2000000 + z
*)

(* begin hide *)
From Stdlib Require Import
     List String ZArith.

From ITree Require Import
     ITree
     Events.State.

From ExtLib Require Import
     Structures.Functor
     Structures.Monads
     Data.Map.FMapAList.

From Vellvm Require Import
  Utilities
  Utils.IntMaps
  Syntax
  Syntax.LLVMAst
  Syntax.AstLib
  Semantics.LLVMEvents
  Semantics.DenotationObs
  Semantics.InterpretationStack
  Semantics.TopLevel
  Semantics.VellvmIntegers
  Semantics.StoreId.
Import MonadNotation.
Import ListNotations.
Import Monads.
Open Scope string_scope.
(* end hide *)

Module TopLevelObs (IS : InterpreterStack) (TL : LLVMTopLevel IS).
  Export TL.

  Import IS.LP.Events.
  Import IS.LP.PROV.
  Import IS.LLVM.Intrinsics.
  Import IS.MEM.MEM_MODEL.
  Import IS.MEM.MMEP.MMSP.
  Import IS.MEM.MMEP.MemExecM.
  Import IS.MEM.MEM_EXEC_INTERP.
  Import IS.MEM.MEM_SPEC_INTERP.
  Import IS.MEM.GEP.
  Import IS.LLVM.Pick.
  Import IS.LLVM.Global.
  Import IS.LLVM.Local.
  Import IS.LLVM.Stack.

  (* The observation-instrumented denotation over the same parameters as
     the stock [IS.LLVM.D] (cf. Lang.v's [Module D := Denotation ...]). *)
  Module DObs := DenotationObs IS.LP IS.LLVM.MEM.MP IS.LLVM.MEM.ByteM IS.LLVM.MEM.CP.

  (* ================================================================ *)
  (** ** L2 observation tap                                            *)
  (* ================================================================ *)

  (** Encode an observable L2 event as a [Z] (see header). Returns
      [None] for events that are not observable in this sense. *)
  Definition event_obs {X} (e : L2 X) : option Z :=
    match e with
    | inr1 (inr1 (inl1 (Load _ (DVALUE_Addr a)))) =>
        Some (IS.LP.PTOI.ptr_to_int a)
    | inr1 (inr1 (inl1 (Store _ (DVALUE_Addr a) _))) =>
        Some (Z.opp (IS.LP.PTOI.ptr_to_int a))
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 (DebugBranch true))))))) =>
        Some 1000000%Z
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 (DebugBranch false))))))) =>
        Some 1000001%Z
    (* Call target (control-flow leakage observation): encoded as
       2000000 + target address. Target addresses are non-negative, so
       this band is disjoint from Load (+addr), Store (-addr), and the
       branch sentinels. *)
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 (DebugCall z))))))) =>
        Some (2000000 + z)%Z
    | _ => None
    end.

  (** Walk an itree at L2 and record observation events into a list of
      [Z]. Re-emits every event unchanged — purely instrumentation. *)
  Unset Guard Checking.
  CoFixpoint observe_L2 {R} (obs : list Z) (t : itree L2 R)
    : itree L2 (list Z * R) :=
    match ITreeDefinition.observe t with
    | ITreeDefinition.RetF r => Ret (List.rev obs, r)
    | ITreeDefinition.TauF t' => Tau (observe_L2 obs t')
    | @ITreeDefinition.VisF _ _ _ X e k =>
        let obs' := match event_obs e with
                    | Some z => cons z obs
                    | None => obs
                    end in
        Vis e (fun x : X => observe_L2 obs' (k x))
    end.
  Set Guard Checking.

  Section InterpreterMCFGObs.
    Context {MemM : Type -> Type}.
    Context `{MemMonad MemM}.

    (** Like [IS.interp_mcfg4_exec] but inserts [observe_L2] at L2 to
        collect Load/Store addresses, branch directions, and call
        targets into the result. *)
    Definition interp_mcfg4_exec_obs {R} (t: itree L0 R) g l sid m :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L2_obs         := observe_L2 nil L2_trace in
      let L3_trace       := interp_memory L2_obs sid m in
      let L4_trace       := exec_undef L3_trace in
      L4_trace.
  End InterpreterMCFGObs.

  (* ================================================================ *)
  (** ** Obs variants of the toplevel entry points                     *)
  (* ================================================================ *)

  (** Register a function with [DObs.denote_function] so that internal
      calls run the branch/call-debug-emitting body. [function_denotation]
      is a transparent alias over shared [LLVMEvents] types, so [DObs]'s
      and the stock [D]'s denotations interoperate (the builtins below
      stay the stock ones — they contain no branches/calls). *)
  Definition address_one_function_obs (df : definition dtyp (CFG.cfg dtyp))
    : itree L0 (Z * DObs.function_denotation) :=
    let fid := (dc_name (df_prototype df)) in
    fv <- trigger (GlobalRead fid) ;;
    match fv with
    | DVALUE_Addr addr =>
        ret (IS.LP.PTOI.ptr_to_int addr, DObs.denote_function df)
    | _ => raise "address_one_function_obs: invalid address, should not happen."
    end.

  (** Observation-instrumented [denote_vellvm]: same global
      initialization, but functions and the mcfg are denoted with
      [DObs]. *)
  Definition denote_vellvm_obs
             (ret_typ : dtyp)
             (entry : string)
             (args : list uvalue)
             (mcfg : CFG.mcfg dtyp) : itree L0 dvalue :=
    build_global_environment mcfg ;;
    'defns <- map_monad address_one_function_obs (m_definitions mcfg) ;;
    'builtins <- map_monad address_one_builtin_function (built_in_functions (m_declarations mcfg));;
    'addr <- trigger (GlobalRead (Name entry)) ;;
    'rv <- DObs.denote_mcfg (IP.of_list (defns ++ builtins)) ret_typ (dvalue_to_uvalue addr) args;;
    dv_pred <- trigger (pickNonPoison rv);;
    ret (proj1_sig dv_pred).

  (** Like [TL.interpreter_gen] but uses the observation-collecting
      pipeline. Result wraps an extra [list Z] of observations. *)
  Definition interpreter_gen_obs
    (ret_typ : dtyp)
    (entry : string)
    (arg_gen : itree L0 (list uvalue))
    (prog: ll_toplevel_entities)
    :=
    let t :=
      args <- arg_gen;;
      denote_vellvm_obs ret_typ entry args
        (convert_types (mcfg_of_tle (link PREDEFINED_FUNCTIONS prog)))
    in interp_mcfg4_exec_obs t [] ([],[]) 0 initial_memory_state.

End TopLevelObs.

Module TopLevelBigIntptrObs := TopLevelObs InterpreterStackBigIntptr TopLevelBigIntptr.
