(** * Vellvm NI Taint Tracker (partition design)

    Every SSA variable and every memory location is its own taint source.
    The output [ts_tobs] is the set of source identities that influenced
    an observation event (Load/Store address or branch direction) during
    the execution.

    That set IS the public partition: any source identity NOT in
    [ts_tobs] is guaranteed not to affect the observation trace, so
    varying it across runs is safe.

    Taint alphabet:
      [taint_src := raw_id + Z]
        - [inl id]   — an SSA register named [id]
        - [inr addr] — a memory cell at concrete address [addr]

    Implementation notes:
      - Self-tagging is centralised in [treg_lookup] and [tmem_lookup]:
        any lookup of a variable or memory cell joins in its own identity.
        That eliminates the need to seed identities at definition or
        allocation time.
      - Load/Store cases in [denote_instr_taint] duplicate the event
        sequence from [denote_instr] in order to access the concrete
        memory address ([da] from [concretize_or_pick_unique]).
        Every other instruction kind falls through to [denote_instr]
        and applies a pure AST-only taint update.
      - The tracker is built as a Module functor over [LLVMParams] and
        [Memory LP]; the OCaml driver picks [TaintTrackerBigIntptr] for
        the dynamic address model.

    See also:
      - [src/NI_ARCHITECTURE.md]
      - [src/NI_TESTING.md]
*)

From Stdlib Require Import List String ZArith Bool.
Import ListNotations.

From ITree Require Import ITree ITreeFacts.

From ExtLib Require Import
     Structures.Functor
     Structures.Monads.

From Vellvm Require Import
     Utilities
     Syntax.LLVMAst
     Syntax.AstLib
     Syntax.DynamicTypes
     Syntax.CFG
     Semantics.LLVMEvents
     Semantics.LLVMParams
     Semantics.Lang
     Semantics.MemoryAddress
     Semantics.MemoryParams
     Handlers.MemoryModel
     Handlers.MemoryModelImplementation.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** Source identities and taint sets                               *)
(* ================================================================= *)

Definition taint_src : Type := (raw_id + Z)%type.
Definition taint : Type := list taint_src.

Definition raw_id_eqb (x y : raw_id) : bool :=
  if RawIDOrd.eq_dec x y then true else false.

Definition taint_src_eqb (s1 s2 : taint_src) : bool :=
  match s1, s2 with
  | inl x1, inl x2 => raw_id_eqb x1 x2
  | inr a1, inr a2 => Z.eqb a1 a2
  | _,      _      => false
  end.

(** Remove duplicates using a boolean equality. *)
Fixpoint remove_dupes {A} (eqb : A -> A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: rest =>
      if existsb (eqb x) rest
      then remove_dupes eqb rest
      else x :: remove_dupes eqb rest
  end.

Definition join_taints (t1 t2 : taint) : taint :=
  remove_dupes taint_src_eqb (t1 ++ t2).

(* ================================================================= *)
(** ** Register and memory taint maps with self-tagging defaults      *)
(* ================================================================= *)

Definition treg_map : Type := list (raw_id * taint).
Definition tmem_map : Type := list (Z * taint).

(** Raw lookup returns [[]] when not found (no self-tag).  *)
Fixpoint treg_lookup_raw (tr : treg_map) (id : raw_id) : taint :=
  match tr with
  | []            => []
  | (a, t) :: rest => if raw_id_eqb a id then t else treg_lookup_raw rest id
  end.

(** Public lookup: always joins in the variable's own identity.
    This is the key trick that lets every SSA name behave as if
    self-tagged at definition without modifying every assignment. *)
Definition treg_lookup (tr : treg_map) (id : raw_id) : taint :=
  join_taints [inl id] (treg_lookup_raw tr id).

Definition treg_update (tr : treg_map) (id : raw_id) (t : taint) : treg_map :=
  (id, t) :: List.filter (fun '(a, _) => negb (raw_id_eqb a id)) tr.

Fixpoint tmem_lookup_raw (tm : tmem_map) (addr : Z) : taint :=
  match tm with
  | []             => []
  | (a, t) :: rest => if Z.eqb a addr then t else tmem_lookup_raw rest addr
  end.

(** Memory cells also self-tag automatically. *)
Definition tmem_lookup (tm : tmem_map) (addr : Z) : taint :=
  join_taints [inr addr] (tmem_lookup_raw tm addr).

Definition tmem_update (tm : tmem_map) (addr : Z) (t : taint) : tmem_map :=
  (addr, t) :: List.filter (fun '(a, _) => negb (Z.eqb a addr)) tm.

(* ================================================================= *)
(** ** Taint state                                                    *)
(* ================================================================= *)

Record tstate := mk_tstate {
  ts_tpc   : taint;     (** PC taint (joined in by branches) *)
  ts_tregs : treg_map;  (** register taint map *)
  ts_tobs  : taint;     (** accumulated public partition: identities seen in observation events *)
  ts_tmem  : tmem_map   (** memory taint map *)
}.

Definition init_tstate : tstate :=
  mk_tstate [] [] [] [].

(** Split [tobs] into the public partition: register names + memory addresses. *)
Fixpoint split_taint (t : taint) : (list raw_id * list Z) :=
  match t with
  | []           => ([], [])
  | inl id :: r =>
      let '(ids, addrs) := split_taint r in (id :: ids, addrs)
  | inr a  :: r =>
      let '(ids, addrs) := split_taint r in (ids, a :: addrs)
  end.

(* ================================================================= *)
(** ** Expression taint (polymorphic in [T])                          *)
(* ================================================================= *)

Section ExpTaint.
  Variable T : Set.

  Fixpoint calc_taint_exp (e : @exp T) (tr : treg_map) : taint :=
    match e with
    | EXP_Ident (ID_Local id)  => treg_lookup tr id
    | EXP_Ident (ID_Global _)  => []
    | EXP_Integer _ | EXP_Float _ | EXP_Double _ | EXP_Hex _
    | EXP_Bool _   | EXP_Null    | EXP_Zero_initializer
    | EXP_Undef    | EXP_Poison  => []
    (* Aggregates: collect taint of every component. *)
    | EXP_Cstring fields
    | EXP_Struct fields
    | EXP_Packed_struct fields =>
        List.fold_left
          (fun acc '(_, e) => join_taints acc (calc_taint_exp e tr))
          fields []
    | EXP_Array _ fields
    | EXP_Vector _ fields =>
        List.fold_left
          (fun acc '(_, e) => join_taints acc (calc_taint_exp e tr))
          fields []
    | OP_IBinop _ _ v1 v2
    | OP_FBinop _ _ _ v1 v2 =>
        join_taints (calc_taint_exp v1 tr) (calc_taint_exp v2 tr)
    | OP_ICmp _ _ v1 v2
    | OP_FCmp _ _ v1 v2 =>
        join_taints (calc_taint_exp v1 tr) (calc_taint_exp v2 tr)
    | OP_Conversion _ _ v _ => calc_taint_exp v tr
    | OP_GetElementPtr _ (_, pv) idxs =>
        List.fold_left
          (fun acc '(_, idx) => join_taints acc (calc_taint_exp idx tr))
          idxs (calc_taint_exp pv tr)
    | OP_Select (_, cnd) (_, v1) (_, v2) =>
        join_taints (calc_taint_exp cnd tr)
          (join_taints (calc_taint_exp v1 tr) (calc_taint_exp v2 tr))
    | OP_ExtractElement (_, vec) (_, idx) =>
        join_taints (calc_taint_exp vec tr) (calc_taint_exp idx tr)
    | OP_InsertElement (_, vec) (_, elt) (_, idx) =>
        join_taints (calc_taint_exp vec tr)
          (join_taints (calc_taint_exp elt tr) (calc_taint_exp idx tr))
    | OP_ShuffleVector (_, v1) (_, v2) (_, mask) =>
        join_taints (calc_taint_exp v1 tr)
          (join_taints (calc_taint_exp v2 tr) (calc_taint_exp mask tr))
    | OP_ExtractValue (_, vec) _ => calc_taint_exp vec tr
    | OP_InsertValue (_, vec) (_, elt) _ =>
        join_taints (calc_taint_exp vec tr) (calc_taint_exp elt tr)
    | OP_Freeze (_, v) => calc_taint_exp v tr
    end.

  Definition calc_taint_texp (te : T * @exp T) (tr : treg_map) : taint :=
    calc_taint_exp (snd te) tr.

End ExpTaint.

Arguments calc_taint_exp  {T} _ _.
Arguments calc_taint_texp {T} _ _.

(* ================================================================= *)
(** ** Pure AST-only updates (Phi, Terminator, generic instructions)  *)
(* ================================================================= *)

Section PureUpdates.
  Variable T : Set.

  (** Optional [raw_id] of an instruction's result (None for void). *)
  Definition instr_id_to_raw_id (iid : instr_id) : option raw_id :=
    match iid with
    | IId id => Some id
    | IVoid _ => None
    end.

  (** Update the result register's taint (no-op for void instructions). *)
  Definition maybe_update_tregs (iid : instr_id) (t : taint) (tr : treg_map) : treg_map :=
    match instr_id_to_raw_id iid with
    | Some id => treg_update tr id t
    | None    => tr
    end.

  (** Taint update for one instruction, AST-only (no concrete addresses).
      Load and Store cases here are conservative: they treat memory as
      opaque. The semantic version in [Make.denote_instr_taint] below
      overrides Load/Store with concrete-address handling. *)
  Definition taint_instr_pure (iid : instr_id) (i : @instr T) (ts : tstate) : tstate :=
    let tr := ts_tregs ts in
    let pc := ts_tpc ts in
    let ob := ts_tobs ts in
    let tm := ts_tmem ts in
    match i with
    | INSTR_Op op =>
        let te := calc_taint_exp op tr in
        let new_taint := join_taints te pc in
        mk_tstate pc (maybe_update_tregs iid new_taint tr) ob tm
    | INSTR_Alloca _ _ =>
        (* fresh pointer: taint is just the SSA name's own identity
           (added automatically by [treg_lookup]) plus pc. *)
        mk_tstate pc (maybe_update_tregs iid pc tr) ob tm
    | INSTR_Call (_, _) args _ =>
        let arg_taints :=
          List.fold_left
            (fun acc '((_, e), _) => join_taints acc (calc_taint_exp e tr))
            args []
        in
        mk_tstate pc (maybe_update_tregs iid (join_taints arg_taints pc) tr) ob tm
    (* Load and Store are overridden in the semantic module. The
       fallthrough here is just defensive and AST-only. *)
    | INSTR_Load _ (_, ptr) _ =>
        let ptr_taint := calc_taint_exp ptr tr in
        let obs_taint := join_taints (join_taints ptr_taint pc) ob in
        mk_tstate pc (maybe_update_tregs iid (join_taints ptr_taint pc) tr) obs_taint tm
    | INSTR_Store (_, val) (_, ptr) _ =>
        let ptr_taint := calc_taint_exp ptr tr in
        let obs_taint := join_taints (join_taints ptr_taint pc) ob in
        mk_tstate pc tr obs_taint tm
    | _ => ts
    end.

  (** Phi pickup: argument taint comes from the incoming block. *)
  Definition taint_phi_gen (id : local_id) (p : @phi T) (from_blk : block_id)
    (ts : tstate) : tstate :=
    let '(Phi _ args) := p in
    let te := match List.find (fun '(bid, _) => raw_id_eqb bid from_blk) args with
              | Some (_, e) => calc_taint_exp e (ts_tregs ts)
              | None        => []
              end in
    let rt := join_taints te (ts_tpc ts) in
    mk_tstate (ts_tpc ts) (treg_update (ts_tregs ts) id rt)
              (ts_tobs ts) (ts_tmem ts).

  (** Terminator pickup: branch / switch conditions join PC and observation. *)
  Definition taint_term_gen (t : @terminator T) (ts : tstate) : tstate :=
    let tr := ts_tregs ts in
    let pc := ts_tpc ts in
    let ob := ts_tobs ts in
    let tm := ts_tmem ts in
    match t with
    | TERM_Br v _ _
    | TERM_Switch v _ _ =>
        let te  := calc_taint_texp v tr in
        let pc' := join_taints te pc in
        let ob' := join_taints pc' ob in
        mk_tstate pc' tr ob' tm
    | _ => ts
    end.

End PureUpdates.

Arguments taint_instr_pure {T} _ _ _.
Arguments taint_phi_gen    {T} _ _ _ _.
Arguments taint_term_gen   {T} _ _.

(* ================================================================= *)
(** ** Semantic module: Load/Store with concrete addresses             *)
(* ================================================================= *)

Module Make (LP : LLVMParams) (MEM : Memory LP).
  Module LLVM := Lang.Make LP MEM.
  Import LP.
  Import LP.Events.
  Import LLVM.D.

  (** Extract a concrete [Z] address from a [DVALUE_Addr]. *)
  Definition dvalue_to_addr_z (dv : dvalue) : option Z :=
    match dv with
    | DVALUE_Addr a => Some (LP.PTOI.ptr_to_int a)
    | _ => None
    end.

  (** Denote one instruction AND thread the taint state. Load and Store
      are duplicated so we can grab the concrete address [da] for
      memory-taint lookup / update; every other case delegates to
      [denote_instr] and applies the pure AST-only update. *)
  Definition denote_instr_taint
    (i : instr_id * instr dtyp) (varargs : option ADDR.addr)
    (ts : tstate) : itree instr_E tstate :=
    let '(iid, instr_body) := i in
    let tr := ts_tregs ts in
    let pc := ts_tpc ts in
    let ob := ts_tobs ts in
    let tm := ts_tmem ts in
    match iid, instr_body with

    (* ---- LOAD: duplicate event sequence, capture concrete address ---- *)
    | IId id, INSTR_Load dt (du, ptr) _ =>
        ua <- translate exp_to_instr (denote_exp (Some du) ptr) ;;
        da <- concretize_or_pick_unique ua ;;
        uv <- trigger (Load dt da) ;;
        trigger (LocalWrite id uv) ;;
        let addr_z    := dvalue_to_addr_z da in
        let addr_self := match addr_z with Some z => [inr z] | None => [] end in
        let ptr_taint := calc_taint_exp ptr tr in
        let mem_taint := match addr_z with
                         | Some z => tmem_lookup tm z
                         | None   => []
                         end in
        let result_taint :=
          join_taints (join_taints ptr_taint mem_taint) pc in
        (* The address itself is observable (the Load reveals that this
           specific cell was read). Join it into [tobs] so it appears in
           the public partition. *)
        let obs_taint :=
          join_taints (join_taints (join_taints addr_self ptr_taint) pc) ob in
        ret (mk_tstate pc (maybe_update_tregs iid result_taint tr) obs_taint tm)

    (* ---- STORE: duplicate event sequence, update memory taint ---- *)
    | IVoid _, INSTR_Store (dt, val) (du, ptr) _ =>
        uv <- translate exp_to_instr (denote_exp (Some dt) val) ;;
        ua <- translate exp_to_instr (denote_exp (Some du) ptr) ;;
        da <- concretize_or_pick_unique ua ;;
        match da with
        | DVALUE_Poison _ => raiseUB "Store to poisoned address."
        | _ => trigger (Store dt da uv)
        end ;;
        let addr_z    := dvalue_to_addr_z da in
        let addr_self := match addr_z with Some z => [inr z] | None => [] end in
        let ptr_taint := calc_taint_exp ptr tr in
        let val_taint := calc_taint_exp val tr in
        (* The store address is observable. *)
        let obs_taint :=
          join_taints (join_taints (join_taints addr_self ptr_taint) pc) ob in
        let new_tmem  := match addr_z with
                         | Some z => tmem_update tm z (join_taints val_taint pc)
                         | None   => tm
                         end in
        ret (mk_tstate pc tr obs_taint new_tmem)

    (* ---- Other instructions: delegate to denote_instr, AST-only update ---- *)
    | _, _ =>
        denote_instr (iid, instr_body) varargs ;;
        ret (taint_instr_pure iid instr_body ts)
    end.

  (** Thread tstate through a list of instructions. *)
  Fixpoint denote_code_taint (c : code dtyp) (varargs : option ADDR.addr)
    (ts : tstate) : itree instr_E tstate :=
    match c with
    | [] => ret ts
    | i :: rest =>
        ts' <- denote_instr_taint i varargs ts ;;
        denote_code_taint rest varargs ts'
    end.

  (** Denote a block (phis, code, terminator) and thread tstate. *)
  Definition denote_block_taint (b : block dtyp) (bid_from : block_id)
    (varargs : option ADDR.addr) (ts : tstate)
    : itree instr_E (tstate * (block_id + uvalue)) :=
    denote_phis bid_from (blk_phis b) ;;
    let ts1 := List.fold_left
                 (fun ts' '(id, p) => taint_phi_gen id p bid_from ts')
                 (blk_phis b) ts in
    ts2 <- denote_code_taint (blk_code b) varargs ts1 ;;
    let ts3 := taint_term_gen (blk_term b) ts2 in
    r <- translate exp_to_instr (denote_terminator (blk_term b)) ;;
    ret (ts3, r).

  Definition denote_ocfg_taint (bks : ocfg dtyp) (varargs : option ADDR.addr)
    : (tstate * (block_id * block_id))
      -> itree instr_E
               ((tstate * (block_id * block_id)) + (tstate * uvalue)) :=
    iter (C := ktree _) (bif := sum)
      (fun '(ts, (bid_from, bid_src)) =>
        match find_block bks bid_src with
        | None => ret (inr (inl (ts, (bid_from, bid_src))))
        | Some block_src =>
            '(ts', bd) <- denote_block_taint block_src bid_from varargs ts ;;
            match bd with
            | inr dv => ret (inr (inr (ts', dv)))
            | inl bid_target => ret (inl (ts', (bid_src, bid_target)))
            end
        end).

  Definition denote_cfg_taint (f : cfg dtyp) (varargs : option ADDR.addr)
    (ts : tstate)
    : itree instr_E (tstate * uvalue) :=
    r <- denote_ocfg_taint (blks f) varargs (ts, (init f, init f)) ;;
    match r with
    | inl (_ts', _bid) =>
        raise "Block not found in denote_cfg_taint"
    | inr (ts', uv) => ret (ts', uv)
    end.

  (** Denote a function with taint tracking. Inlines the call-frame
      setup ([MemPush] / [StackPush] / [Alloca] for varargs / [Store]),
      same shape as upstream [denote_function]. Old base has no
      [push_call_frame] / [pop_call_frame] helpers. *)
  Definition denote_function_taint
    (df : definition dtyp (cfg dtyp)) (args : list uvalue)
    : itree L0' (tstate * uvalue) :=
    '(bs, vs) <- lift_err ret (combine_lists_varargs (df_args df) args) ;;
    dts <- lift_err ret (map_monad dtyp_of_uvalue_fun vs) ;;
    let dt := DTYPE_Packed_struct dts in
    trigger MemPush ;;
    trigger (StackPush bs) ;;
    varargs_dv <- trigger (Alloca dt 1 None) ;;
    trigger (Store dt varargs_dv (UVALUE_Packed_struct vs)) ;;
    match varargs_dv with
    | DVALUE_Addr varg =>
        '(ts_final, rv) <- translate instr_to_L0'
                                  (denote_cfg_taint (df_instrs df) (Some varg) init_tstate) ;;
        trigger StackPop ;;
        trigger MemPop ;;
        ret (ts_final, rv)
    | _ => raise "Non-address returned from alloca in denote_function_taint"
    end.

End Make.

(* ================================================================= *)
(** ** Concrete instantiations                                        *)
(* ================================================================= *)

Module TaintTracker64 :=
  Make MemoryModelImplementation.LLVMParams64BitIntptr Memory64BitIntptr.

Module TaintTrackerBigIntptr :=
  Make MemoryModelImplementation.LLVMParamsBigIntptr MemoryBigIntptr.

(** NOTE: The end-to-end taint pipeline is composed in OCaml
    ([src/ml/interpreter.ml]) rather than in Rocq, because Coq's
    extraction generates incompatible (though semantically isomorphic)
    [itree] types for different module instantiations. The OCaml glue
    uses [Obj.magic] to bridge:

      1. [TopLevelBigIntptr.build_global_environment]
      2. [TaintTrackerBigIntptr.denote_function_taint]
      3. [Recursion.interp_mrec]   (L0' → L0; trivial since no CallE)
      4. [InterpreterStackBigIntptr.interp_mcfg4_exec_obs]

    See [src/NI_ARCHITECTURE.md]. *)
