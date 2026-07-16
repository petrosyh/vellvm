(** This file contains QuickChick generators for LLVM programs.

    There are many different ways of generating values of different
    types which have different constraints (e.g., positive values,
    sized types, etc). This is necessary to satisfy the invariants of
    LLVM programs.

    Currently programs are rather simple, only generating integer
    types and simple loops, but we hope to expand this soon.

    See vellvm-quickchick-overview.org in the root of the project for
    more details. *)
Require Import Ceres.Ceres.

From Vellvm.Syntax Require Import
  CFG
  TypeUtil
  TypToDtyp.

From Vellvm.Handlers Require Import
  Handlers.

From Vellvm.Semantics Require Import
  TopLevel.

From Vellvm Require Import
  LLVMAst
  Utilities
  AstLib
  DynamicTypes
  DList
  IntMaps
  Utils.Default.

From Vellvm.QC Require Import
  Utils
  Generators
  ECS
  Lens
  GenMetadata.

Require Import Integers.


From ExtLib.Structures Require Export
     Functor Applicative Monads Monoid.

Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Structures.Foldable.
Require Import ExtLib.Structures.Monads.

From Stdlib Require Import List.

Import ListNotations.

Import ListNotations.
Import MonadNotation.
Import FunctorNotation.
Import LensNotations.
Import ApplicativeNotation.

From Stdlib Require Import
     ZArith Lia Bool.Bool.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

From ExtLib.Structures Require Export
     Functor.
Open Scope Z_scope.
Open Scope lens.
Open Scope string.

(* Disable guard checking. This file is only used for generating test
    cases. Some of our generation functions terminate in non-trivial
    ways, but since they're only used to generate test cases (and are
    not used in proofs) it's not terribly important to prove that they
    actually terminate.  *)
Unset Guard Checking.

(* Controls whether or not we generate floats... The float generators
often break with updates, so this may be convenient *)
Definition enable_float_generation : bool := true.

Section Helpers.
  Definition l_is_empty {A : Type} (l : list A) : bool :=
    match l with
    | [] => true
    | _ => false
    end.


  Fixpoint is_sized_type_h (t : typ) : bool
    := match t with
       | TYPE_I sz => true
       | TYPE_IPTR => true
       | TYPE_Pointer (Some t) => is_sized_type_h t
       | TYPE_Pointer None => true
       | TYPE_Void => false
       | TYPE_Half => true
       | TYPE_Float => true
       | TYPE_Double => true
       | TYPE_X86_fp80 => true
       | TYPE_Fp128 => true
       | TYPE_Ppc_fp128 => true
       | TYPE_Metadata => true (* Not sure if this is right *)
       | TYPE_X86_mmx => true
       | TYPE_Array sz t => is_sized_type_h t
       | TYPE_Function ret args vararg => false
       | TYPE_Struct fields
       | TYPE_Packed_struct fields =>
           forallb is_sized_type_h fields
       | TYPE_Opaque => false
       | TYPE_Vector sz t => is_sized_type_h t
       | TYPE_Identified id => false
       end.

  Definition is_int_type_h (t : typ) : bool
    := match t with
       | TYPE_I sz => true
       | _ => false
       end.

  (* Only works correctly if the type is well formed *)
  Definition is_int_type (typ_ctx : list (ident * typ)) (t : typ) : bool
    := is_int_type_h (normalize_type typ_ctx t).

  Definition is_function_type_h (t : typ) : bool
    := match t with
       | TYPE_Function _ _ _ => true
       | _ => false
       end.

  Definition is_function_type (typ_ctx : list (ident * typ)) (t : typ) : bool
    := is_function_type_h (normalize_type typ_ctx t).

  Definition is_function_pointer_h (t : typ) : bool
    := match t with
       | TYPE_Pointer (Some (TYPE_Function _ _ _)) => true
       (* TODO: What about opaque pointers?  *)
       | _ => false
       end.

  (* TODO: incomplete. Should typecheck *)
  Definition well_formed_op (typ_ctx : list (ident * typ)) (op : exp typ) : bool :=
    match op with
    | OP_IBinop iop t v1 v2              => true
    | OP_ICmp cmp t v1 v2                => true
    | OP_FBinop fop fm t v1 v2           => true
    | OP_FCmp cmp t v1 v2                => true
    | OP_Conversion conv t_from v t_to   => true
    | OP_GetElementPtr t ptrval idxs     => true
    | OP_ExtractElement vec idx          => true
    | OP_InsertElement vec elt idx       => true
    | OP_ShuffleVector vec1 vec2 idxmask => true
    | OP_ExtractValue vec idxs           => true
    | OP_InsertValue vec elt idxs        => true
    | OP_Select cnd v1 v2                => true
    | OP_Freeze v                        => true
    | _                                  => false
    end.

  (*
  Fixpoint well_formed_instr (ctx : list (ident * typ)) (i : instr typ) : bool :=
    match i with
    | INSTR_Comment msg => true
    | INSTR_Op op => well_formed_op ctx op
    | INSTR_Call fn args => _
    | INSTR_Alloca t nb align => is_sized_typ ctx t (* The alignment may not be greater than 1 << 29. *)
    | INSTR_Load volatile t ptr align => _
    | INSTR_Store volatile val ptr align => _
    | INSTR_Fence => _
    | INSTR_AtomicCmpXchg => _
    | INSTR_AtomicRMW => _
    | INSTR_Unreachable => _
    | INSTR_VAArg => _
    | INSTR_LandingPad => _
    end.
   *)

  Definition genPosZ : G Z
    :=
      n <- (arbitrary : G nat);;
      ret (Z.of_nat (S n)).
  (* ret (Z.of_nat n). *)
  (* TODO: ^This is the original code. Is this correct??? *)

  Definition genN : G N
    :=
      n <- (arbitrary : G nat);;
      ret (N.of_nat n).

  Definition genPosN : G N
    :=
      n <- (arbitrary : G nat);;
      ret (N.of_nat (S n)).
End Helpers.

Section GenerationState.

  Definition VariableMetadata := Metadata FieldOf.
  Definition VariableMetadataMap := IM.Raw.t VariableMetadata.
  Definition type_context := VariableMetadataMap.
  Definition var_context := VariableMetadataMap.
  Definition ptr_to_int_context := VariableMetadataMap.
  Definition all_local_var_contexts := (var_context * ptr_to_int_context)%type.
  Definition all_var_contexts := (var_context * var_context * ptr_to_int_context)%type.
  Definition ContextMetadata s := Metadata s.

  (* [obs-freeze] per-function freeze state (PLAN_obs-freeze.en.md §3 D1/D2).
     fz_bits  : frozen_bits — bit i is FROZEN once it has reached an observation
                (D1: conditional-branch condition) or entered a call as an argument
                (D2: chain-entry). Reset at every gen_definition entry (per-function
                scoping — helper-local bits must not leak into main and vice versa).
     fz_heads : bit index (as Z key) -> HEAD entity id. The head is the ONE carrier
                of a frozen bit exempt from the D1 filter (the chain baton, D2);
                transfers per the D2 head-transfer table.
     fz_moved : transient side-channel (same idea as cur_mask): bits whose head was
                consumed as an operand since the last result binding. Applied at
                add_to_local_ctx (SSA consumption -> result becomes head) or at a
                store (-> cell becomes head); discarded at instruction boundaries
                (consumption with no result -> headship lapses). *)
  Record FreezeState :=
    mkFreezeState
      { fz_bits  : N
      ; fz_heads : IM.Raw.t Z
      ; fz_moved : N
      (* [param-obs-ban] per-function param provenance + transient
         observation-context flag. fz_param = OR of the seed bits of the
         CURRENT (non-main) function's formals (0 in main / at reset). fz_pob_on
         = a transient flag set ONLY around the observation-feeding pick sites
         (S1 the cond-br condition, S2 loop_init's operands): while true, the
         ban's hard filter in gen_var_ent drops candidates carrying any bit of
         fz_param. Both live here (rather than in a new GenState field) so they
         ride the existing freeze_st' lens — no extra lens plumbing. They are
         INDEPENDENT of the freeze knobs: written only under route_a_param_obs_ban
         <> 0, read only under the same gate, so both-off is byte-identical. *)
      ; fz_param  : N
      ; fz_pob_on : bool
      }.

  Definition freeze_empty : FreezeState :=
    {| fz_bits := 0%N; fz_heads := IM.Raw.empty _; fz_moved := 0%N
     ; fz_param := 0%N; fz_pob_on := false |}.

  Record GenState s :=
    mkGenState
    { num_void : N
    ; num_raw  : N
    ; num_global : N
    ; num_blocks : N
    ; context : ContextMetadata s
    ; global_memo : list (global typ)
    ; debug_stack : list string
    (* [route-A storage] arg-provenance maps for densifying killer programs.
       Detailed explanation (KO): private_notes/ROUTE_A_IMPL.private.md  §1-storage.
       arg_set : entity-id (Z) -> bitmask N. Bit i set <-> this value MAY depend on main
         arg #i (args {0..7}). N.lor = propagation (result = OR of operand masks);
         (N <> 0) <-> tainted; (N.land a b = a) <-> a subset-of b  (operand-diversity check).
         Covers SSA variables AND memory cells (a cell's arg_set = its content provenance),
         so no separate cell_content map.
       points_to : pointer-holder entity -> the cell entity it addresses (shadow memory).
         Now populated variable->cell; later cell->cell (pointer-in-memory, pointer cluster). *)
    ; arg_set : IM.Raw.t N
    ; points_to : IM.Raw.t Z
    (* [route-A propagation] transient side-channel accumulator: OR of the masks of the
       values picked as operands since the last result-binding. Assigned to the new result
       at add_to_local_ctx, then reset to 0. See ROUTE_A_IMPL.private.md §2-propagation. *)
    ; cur_mask : N
    (* [route-A chain-vector] vector-lane provenance for insert->extract chaining.
       vec_lanes : vector entity -> [(lane, mask)]: lanes whose CURRENT content is likely
         arg-derived. Recorded at insertelement (the result inherits the source vector's
         recorded lanes; the written lane is overwritten by the inserted element's mask).
         Consumed by gen_extractelement to soft-bias the lane pick toward a tainted lane
         of the SAME vector — a kill needs the REAL dataflow (insert lane = extract lane),
         not just a tainted-labelled vector; uniform lane matching is ~1/sz.
       cur_ent : transient side-channel: entity of the LAST gen_var_ent pick. Lets a
         generator learn WHICH entity an operand expression resolved to (the exp itself
         only carries the NAME; there is no name->entity reverse index — same obstacle
         as §2-propagation, same interception answer). Cleared at instruction boundaries;
         read-and-cleared by cur_ent_take. Misattribution is possible (e.g. a literal
         vector whose nested element pick was the last gen_var_ent call) — harmless:
         wrong entries never type-match a later lookup, costing only sampling efficiency.
       See ROUTE_A_IMPL.private.md §4-chain-vector. *)
    ; vec_lanes : IM.Raw.t (list (Z * N))
    ; cur_ent : option Z
    (* [route-A ret-bridge] per-function state for the "bridge to the return type"
       instruction arm in gen_instr (targets call-drop-ret / ret-drop-val).
       cur_ret_t : the return type of the HELPER currently being generated (None in
         main / outside function bodies) — gen_instr needs it but only gen_definition_h
         knows it, so it travels by state (same side-channel idea as cur_mask/cur_ent).
       ret_bridge_budget : remaining insertions for this function (the knob
         route_a_ret_bridge is the per-function cap; 1-2 bridge instructions per
         function are plausible real code — "building the return value").
       See ROUTE_A_IMPL §6b-ret-bridge. *)
    ; cur_ret_t : option typ
    ; ret_bridge_budget : nat
    (* [route-A callee-bias 2b] the TYPES (as registered in the global ctx:
       TYPE_Pointer (Some (TYPE_Function ...))) of helper functions whose body LOADS
       through one of their pointer params — recorded at gen_definition time by a pure
       AST scan of the just-built body (approximation documented in
       private_notes/exp_step2bc/NOTES.md). Read ONLY by the knob-gated 2b bias in
       gen_function_pointer_type (route_a_callee_ptr_w). The RECORDING is always-on
       (like vec_lanes): a pure state append, invisible to all generation-time reads
       when the knob is 0, so it does not perturb the knob=0 stream (MD5-verified). *)
    ; loading_fn_types : list typ
    (* [obs-freeze] per-function freeze state — see the FreezeState comment above. *)
    ; freeze_st : FreezeState
    }.

  Instance Default_GenState {s} : Default (GenState s)
    :=
    { def := {| num_void   := 0
             ; num_raw    := 0
             ; num_global := 0
             ; num_blocks := 0
             ; context := def
             ; global_memo := []
             ; debug_stack := []
             ; arg_set := IM.Raw.empty _   (* [route-A storage] empty provenance; see ROUTE_A_IMPL §1-storage *)
             ; points_to := IM.Raw.empty _
             ; cur_mask := 0               (* [route-A propagation] *)
             ; vec_lanes := IM.Raw.empty _ (* [route-A chain-vector] *)
             ; cur_ent := None             (* [route-A chain-vector] *)
             ; cur_ret_t := None           (* [route-A ret-bridge] *)
             ; ret_bridge_budget := 0      (* [route-A ret-bridge] *)
             ; loading_fn_types := []      (* [route-A callee-bias 2b] *)
             ; freeze_st := freeze_empty   (* [obs-freeze] *)
             |}
    }.

  Definition num_void' {s} : Lens' (GenState s) N.
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply x
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        | apply (arg_set s)
        | apply (points_to s)
        | apply (cur_mask s)
        | apply (vec_lanes s)
        | apply (cur_ent s)
        | apply (cur_ret_t s)
        | apply (ret_bridge_budget s)
        | apply (loading_fn_types s)
        | apply (freeze_st s)
        ]; apply gs.
    - apply num_void.
  Defined.

  Definition num_raw' {s} : Lens' (GenState s) N.
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply x
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        | apply (arg_set s)
        | apply (points_to s)
        | apply (cur_mask s)
        | apply (vec_lanes s)
        | apply (cur_ent s)
        | apply (cur_ret_t s)
        | apply (ret_bridge_budget s)
        | apply (loading_fn_types s)
        | apply (freeze_st s)
        ]; apply gs.
    - apply num_raw.
  Defined.

  Definition num_global' {s} : Lens' (GenState s) N.
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply x
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        | apply (arg_set s)
        | apply (points_to s)
        | apply (cur_mask s)
        | apply (vec_lanes s)
        | apply (cur_ent s)
        | apply (cur_ret_t s)
        | apply (ret_bridge_budget s)
        | apply (loading_fn_types s)
        | apply (freeze_st s)
        ]; apply gs.
    - apply num_global.
  Defined.

  Definition num_blocks' {s} : Lens' (GenState s) N.
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply x
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        | apply (arg_set s)
        | apply (points_to s)
        | apply (cur_mask s)
        | apply (vec_lanes s)
        | apply (cur_ent s)
        | apply (cur_ret_t s)
        | apply (ret_bridge_budget s)
        | apply (loading_fn_types s)
        | apply (freeze_st s)
        ]; apply gs.
    - apply num_blocks.
  Defined.

  Definition context' {s} : Lens' (GenState s) (ContextMetadata s).
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply x
        | apply (global_memo s)
        | apply (debug_stack s)
        | apply (arg_set s)
        | apply (points_to s)
        | apply (cur_mask s)
        | apply (vec_lanes s)
        | apply (cur_ent s)
        | apply (cur_ret_t s)
        | apply (ret_bridge_budget s)
        | apply (loading_fn_types s)
        | apply (freeze_st s)
        ]; apply gs.
    - apply context.
  Defined.

  Definition global_memo' {s} : Lens' (GenState s) (list (global typ)).
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply x
        | apply (debug_stack s)
        | apply (arg_set s)
        | apply (points_to s)
        | apply (cur_mask s)
        | apply (vec_lanes s)
        | apply (cur_ent s)
        | apply (cur_ret_t s)
        | apply (ret_bridge_budget s)
        | apply (loading_fn_types s)
        | apply (freeze_st s)
        ]; apply gs.
    - apply global_memo.
  Defined.

  Definition debug_stack' {s} : Lens' (GenState s) (list string).
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply x
        | apply (arg_set s)
        | apply (points_to s)
        | apply (cur_mask s)
        | apply (vec_lanes s)
        | apply (cur_ent s)
        | apply (cur_ret_t s)
        | apply (ret_bridge_budget s)
        | apply (loading_fn_types s)
        | apply (freeze_st s)
        ]; apply gs.
    - apply debug_stack.
  Defined.

  (* [route-A storage] lenses for the two provenance maps. See ROUTE_A_IMPL §1-storage. *)
  Definition arg_set' {s} : Lens' (GenState s) (IM.Raw.t N).
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        | apply x
        | apply (points_to s)
        | apply (cur_mask s)
        | apply (vec_lanes s)
        | apply (cur_ent s)
        | apply (cur_ret_t s)
        | apply (ret_bridge_budget s)
        | apply (loading_fn_types s)
        | apply (freeze_st s)
        ]; apply gs.
    - apply arg_set.
  Defined.

  Definition points_to' {s} : Lens' (GenState s) (IM.Raw.t Z).
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        | apply (arg_set s)
        | apply x
        | apply (cur_mask s)
        | apply (vec_lanes s)
        | apply (cur_ent s)
        | apply (cur_ret_t s)
        | apply (ret_bridge_budget s)
        | apply (loading_fn_types s)
        | apply (freeze_st s)
        ]; apply gs.
    - apply points_to.
  Defined.

  (* [route-A propagation] lens for the transient accumulator. See ROUTE_A_IMPL §2-propagation. *)
  Definition cur_mask' {s} : Lens' (GenState s) N.
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        | apply (arg_set s)
        | apply (points_to s)
        | apply x
        | apply (vec_lanes s)
        | apply (cur_ent s)
        | apply (cur_ret_t s)
        | apply (ret_bridge_budget s)
        | apply (loading_fn_types s)
        | apply (freeze_st s)
        ]; apply gs.
    - apply cur_mask.
  Defined.

  (* [route-A chain-vector] lenses for the vector-lane records and the last-pick
     side-channel. See ROUTE_A_IMPL §4-chain-vector. *)
  Definition vec_lanes' {s} : Lens' (GenState s) (IM.Raw.t (list (Z * N))).
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        | apply (arg_set s)
        | apply (points_to s)
        | apply (cur_mask s)
        | apply x
        | apply (cur_ent s)
        | apply (cur_ret_t s)
        | apply (ret_bridge_budget s)
        | apply (loading_fn_types s)
        | apply (freeze_st s)
        ]; apply gs.
    - apply vec_lanes.
  Defined.

  Definition cur_ent' {s} : Lens' (GenState s) (option Z).
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        | apply (arg_set s)
        | apply (points_to s)
        | apply (cur_mask s)
        | apply (vec_lanes s)
        | apply x
        | apply (cur_ret_t s)
        | apply (ret_bridge_budget s)
        | apply (loading_fn_types s)
        | apply (freeze_st s)
        ]; apply gs.
    - apply cur_ent.
  Defined.

  (* [route-A ret-bridge] lenses for the per-function bridge state. *)
  Definition cur_ret_t' {s} : Lens' (GenState s) (option typ).
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        | apply (arg_set s)
        | apply (points_to s)
        | apply (cur_mask s)
        | apply (vec_lanes s)
        | apply (cur_ent s)
        | apply x
        | apply (ret_bridge_budget s)
        | apply (loading_fn_types s)
        | apply (freeze_st s)
        ]; apply gs.
    - apply cur_ret_t.
  Defined.

  Definition ret_bridge_budget' {s} : Lens' (GenState s) nat.
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        | apply (arg_set s)
        | apply (points_to s)
        | apply (cur_mask s)
        | apply (vec_lanes s)
        | apply (cur_ent s)
        | apply (cur_ret_t s)
        | apply x
        | apply (loading_fn_types s)
        | apply (freeze_st s)
        ]; apply gs.
    - apply ret_bridge_budget.
  Defined.

  (* [route-A callee-bias 2b] lens for the loading-ptr-param helper-type list. *)
  Definition loading_fn_types' {s} : Lens' (GenState s) (list typ).
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        | apply (arg_set s)
        | apply (points_to s)
        | apply (cur_mask s)
        | apply (vec_lanes s)
        | apply (cur_ent s)
        | apply (cur_ret_t s)
        | apply (ret_bridge_budget s)
        | apply x
        | apply (freeze_st s)
        ]; apply gs.
    - apply loading_fn_types.
  Defined.

  (* [obs-freeze] lens for the per-function freeze state. *)
  Definition freeze_st' {s} : Lens' (GenState s) FreezeState.
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        | apply (arg_set s)
        | apply (points_to s)
        | apply (cur_mask s)
        | apply (vec_lanes s)
        | apply (cur_ent s)
        | apply (cur_ret_t s)
        | apply (ret_bridge_budget s)
        | apply (loading_fn_types s)
        | apply x
        ]; apply gs.
    - apply freeze_st.
  Defined.


  Definition increment_raw {s} (gs : GenState s) : GenState s
    := gs & num_raw' %~ N.succ.

  Definition increment_global {s} (gs : GenState s) : GenState s
    := gs & num_global' %~ N.succ.

  Definition increment_void {s} (gs : GenState s) : GenState s
    := gs & num_void' %~ N.succ.

  Definition increment_blocks {s} (gs : GenState s) : GenState s
    := gs & num_blocks' %~ N.succ.

  Definition replace_local_ctx {s} (ctx : Component s Field unit) (gs : GenState s) : GenState s
    := gs & (context' .@  is_local') .~ ctx.

  Definition replace_global_ctx {s} (ctx : Component s Field unit) (gs : GenState s) : GenState s
    := gs & (context' .@  is_global') .~ ctx.

  Definition replace_typ_ctx {s} (typ_ctx : Component s Field typ) (gs : GenState s) : GenState s
    := gs & (context' .@ type_alias') .~ typ_ctx.

  Definition replace_ptrtoint_ctx {s} (ptrtoint_ctx : Component s Field Ent) (gs: GenState s) : GenState s
    := gs & (context' .@ from_pointer') .~ ptrtoint_ctx.

  Definition replace_global_memo {s} (global_memo : list (global typ)) (gs : GenState s) : GenState s
    := gs & global_memo' .~ global_memo.

  Definition GenLLVM := (eitherT string (SystemT GenState G)).

  (* Need this because extlib doesn't declare this instance as global :|. *)
  #[global] Instance monad_stateT {s m} `{Monad m} : Monad (stateT s m).
  Proof.
    apply Monad_stateT;
      typeclasses eauto.
  Defined.

  #[global] Instance MonadState_GenLLVM : MonadState (SystemState GenState G) GenLLVM.
  unfold SystemT.
  try typeclasses eauto.
  Defined.

  Definition gen_context' : Lens' (SystemState GenState G) (ContextMetadata _)
    := (metadata .@ context').

  Definition get_raw {s} (gs : GenState s) : N
    := gs .^ num_raw'.

  Definition get_global {s} (gs : GenState s) : N
    := gs .^ num_global'.

  Definition get_void {s} (gs : GenState s) : N
    := gs .^ num_void'.

  Definition get_blocks {s} (gs : GenState s) : N
    := gs .^ num_blocks'.

  Definition new_id {ID} (id_lens : forall {s : StorageType}, Lens' (GenState s) N) (id_gen : N -> ID) : GenLLVM ID
    := n <- use (metadata .@ num_raw');;
       metadata .@ num_raw' %= N.succ;;
       ret (id_gen n).

  Definition new_local_id : GenLLVM local_id
    := new_id (@num_raw') (fun n => Name ("v" ++ show n)).

  Definition new_global_id : GenLLVM global_id
    := new_id (@num_raw') (fun n => Name ("g" ++ show n)).

  Definition new_void_id : GenLLVM instr_id
    := new_id (@num_void') (fun n => IVoid (Z.of_N n)).

  Definition new_block_id : GenLLVM block_id
    := new_id (@num_blocks') (fun n => Name ("b" ++ show n)).

  (* [route-A propagation] arg-provenance helpers (side-channel accumulator).
     See ROUTE_A_IMPL.private.md §2-propagation.
     arg_set : entity-id (Z) -> mask N (bit i <-> main arg #i). cur_mask : transient accum. *)
  Definition arg_mask_lookup (e : Z) : GenLLVM N
    := m <- use (metadata .@ arg_set');;
       ret (match IM.Raw.find e m with
            | Some v => v
            | None => 0%N
            end).

  Definition arg_mask_set (e : Z) (v : N) : GenLLVM unit
    := m <- use (metadata .@ arg_set');;
       metadata .@ arg_set' .= IM.Raw.add e v m;;
       ret tt.

  (* OR the mask of a picked value (entity e) into the accumulator. *)
  Definition cur_mask_accum (e : Z) : GenLLVM unit
    := v <- arg_mask_lookup e;;
       c <- use (metadata .@ cur_mask');;
       metadata .@ cur_mask' .= N.lor c v;;
       ret tt.

  (* Read the accumulator and reset it to 0 (called when binding a result). *)
  Definition cur_mask_take : GenLLVM N
    := c <- use (metadata .@ cur_mask');;
       metadata .@ cur_mask' .= 0%N;;
       ret c.

  (* [route-A chain-vector] helpers. cur_ent = entity of the LAST gen_var_ent pick
     (the name->entity bridge; same interception idea as cur_mask). vec_lanes =
     per-vector tainted-lane records. See ROUTE_A_IMPL §4-chain-vector. *)
  Definition cur_ent_set (e : Z) : GenLLVM unit
    := _ <- use (metadata .@ cur_ent');;
       metadata .@ cur_ent' .= (Some e : option Z);;
       ret tt.

  (* Read the last-picked entity and clear it. Also used as a pre-pick reset, so a
     stale pick cannot be attributed to the operand about to be generated. *)
  Definition cur_ent_take : GenLLVM (option Z)
    := c <- use (metadata .@ cur_ent');;
       metadata .@ cur_ent' .= (None : option Z);;
       ret c.

  Definition vec_lanes_find (e : Z) : GenLLVM (list (Z * N))
    := m <- use (metadata .@ vec_lanes');;
       ret (match IM.Raw.find e m with
            | Some l => l
            | None => []
            end).

  (* Record the lanes of a NEW vector [e] built by insertelement: inherit the source
     vector's recorded lanes ([osrc], if the source was an ident pick), then overwrite
     lane [idx] with the inserted element's mask [m] (m = 0 erases the lane: tainted
     content was clobbered by an untainted element). No entry is stored when nothing
     is tainted. *)
  Definition vec_lanes_update (e : Z) (osrc : option Z) (idx : Z) (m : N) : GenLLVM unit
    := inherited <- (match osrc with
                     | Some src => vec_lanes_find src
                     | None => ret []
                     end);;
       let cleared := List.filter (fun '(l, _) => negb (Z.eqb l idx)) inherited in
       let entry := if N.eqb m 0%N then cleared else ((idx, m) :: cleared) in
       match entry with
       | [] => ret tt
       | _ :: _ =>
           mm <- use (metadata .@ vec_lanes');;
           metadata .@ vec_lanes' .= IM.Raw.add e entry mm;;
           ret tt
       end.

  (* [route-A chain-memory] shadow-memory helpers. A CELL = one synthetic entity per
     memory object (alloca / global), minted BARE (no context registration, no
     metadata) so cells never appear in candidate folds or queries — writing to them
     is inert for generation. points_to : pointer entity -> its cell.
     arg_set[cell] = provenance of the cell's CURRENT content (store OVERWRITES it:
     object granularity — a multi-slot object is approximated by its last store).
     See ROUTE_A_IMPL §5-chain-memory. *)
  Definition points_to_set (p c : Z) : GenLLVM unit
    := m <- use (metadata .@ points_to');;
       metadata .@ points_to' .= IM.Raw.add p c m;;
       ret tt.

  Definition points_to_find (p : Z) : GenLLVM (option Z)
    := m <- use (metadata .@ points_to');;
       ret (IM.Raw.find p m).

  (* STORE: the cell addressed by [optr] now holds content with mask [m].
     No-op when the pointer's cell is unknown (under-approx; bias-only, principle 3). *)
  Definition cell_mask_record (optr : option Z) (m : N) : GenLLVM unit
    := match optr with
       | None => ret tt
       | Some p =>
           oc <- points_to_find p;;
           match oc with
           | None => ret tt
           | Some c => arg_mask_set c m
           end
       end.

  (* OR a raw mask into the accumulator (LOAD: cell content -> result provenance). *)
  Definition cur_mask_accum_mask (v : N) : GenLLVM unit
    := c <- use (metadata .@ cur_mask');;
       metadata .@ cur_mask' .= N.lor c v;;
       ret tt.

  (* [route-A chain-memory] soft weight for LOAD's pointer pick: with probability
     w/(w+1) read through a pointer whose cell currently holds arg-tainted content
     (completing a store->load same-cell chain). w = 0 => OFF: no candidate scan, no
     extra randomness, AND load-result mask propagation disabled too — that write
     feeds arg_set, which the always-on §3 bias READS, so ungated it would shift the
     stream even at w=0. The cell/points_to RECORDING stays always-on (cells are
     invisible to candidate folds). Knob — tune against the 4 metrics. *)
  Definition route_a_mem_w : nat := 3.

  (* [route-A chain-call] FLAG, not a weight: 0 = seed only main's args (original
     behaviour); <> 0 = ALSO seed every helper function's params with function-local
     bits (bit i = "derives from THIS function's param #i"), so the existing §2/§3
     machinery densifies param->ret flows inside callee bodies (gen_ret's value pick
     already goes through the bias). Targets call-drop-ret / ret-drop-val: their kill
     needs the REAL chain [tainted arg -> callee returns param-derived -> caller
     observes the result]; the caller-side halves already work (§3 biases the args;
     the call result's mask is the OR of the arg masks). Gated because seeding writes
     arg_set, which the always-on §3 bias READS — ungated it would change generation
     at flag=0. See ROUTE_A_IMPL §6-chain-call. *)
  Definition route_a_call_seed : nat := 1.

  (* [route-A ret-bridge] knob = per-function CAP on inserted bridge instructions
     (0 = OFF: the arm never enters gen_instr's menu -> stream-identical). A bridge
     instruction produces a value OF THE CURRENT FUNCTION'S RETURN TYPE from a
     tainted source (opportunistic load from a tainted cell, else a conversion of a
     tainted int local), anywhere in the body — so the later [ret] pick finds a
     tainted candidate of the right type instead of falling back to a constant
     (97% of helper rets did, ROUTE_A_IMPL §6 diagnosis). 1-2 per function is
     realistic ("the code that builds the return value"). See §6b. *)
  Definition route_a_ret_bridge : nat := 2.

  (* [route-A chain-vector] soft weight for extractelement's lane pick: read a
     recorded tainted lane of the picked vector with probability w/(w+1); every lane
     stays reachable via the uniform fallback. w = 0 => ORIGINAL uniform pick (chain
     OFF — consumes identical randomness, so the generated stream is unchanged;
     clean A/B switch). Knob — tune against the 4 metrics. *)
  Definition route_a_chain_w : nat := 3.

  (* [route-A bias] soft preference weight for tainted (arg-derived) operands.
     The tainted-filtered pick is kept with probability w/(w+1); an untainted value
     stays reachable at 1/(w+1). w = 0 => ORIGINAL selection (bias OFF, semantics-
     preserving). Knob — tune against the 4 metrics. See ROUTE_A_IMPL §3-bias. *)
  Definition route_a_bias_w : nat := 3.

  (* [route-A ptr-arg] soft weight for the pointer-argument-to-tainted-cell bias at
     CALL sites (intervention (c), PLAN §4.3(c)). 0 = OFF and STREAM-IDENTICAL:
     gen_call_list then takes EXACTLY the original gen_call path with the original
     randomness (no gen_mem_chain_ptr call at call sites, no extra draws). w > 0
     enables two mechanisms for each pointer-typed call argument:
       M1 (pick swap, no new instructions): try gen_mem_chain_ptr FIRST — reuse an
          in-scope pointer whose cell is already tainted (its cur_mask/cur_ent
          bookkeeping is done inside gen_mem_chain_ptr); on None, fall through to the
          ORIGINAL arg generation (which may retro-mint a clean global — program text
          unchanged; since r7b the mint site exposes the entity via cur_ent so M2/deref
          shadow bookkeeping reaches retro pointers too).
       M2 (pre-call tainted store): if M1 found nothing, with prob w/(w+1) PREPEND one
          [conv; store] pair writing a tainted scalar THROUGH the pointer the ordinary
          path produced (SCALAR pointee only; non-scalar pointees skip M2), so the
          callee can load the tainted content across the call boundary. The store
          mirrors gen_store's shadow bookkeeping (isolate the value's mask, then
          cell_mask_record the pointer's cell). Attacks Step-1's 100%-retro-mint /
          0%-tainted-cell facts. Knob — tune against the metrics. *)
  Definition route_a_ptrarg_w : nat := 3.

  (* [route-A callee-bias 2a] (PLAN §4.3(b), plan-literal) soft weight for the CALLEE
     SELECTION at the ofun_ptr_typ layer (gen_function_pointer_type). With prob
     w/(w+1) restrict the picked function-pointer TYPE to candidates whose signature
     has >=1 SCALAR param (TYPE_I / Float / Double at top level, checked on the
     NORMALIZED signature); on the 1/(w+1) draw or when no such candidate exists, fall
     back to the ordinary uniform pick. 0 = OFF and STREAM-IDENTICAL (no candidate
     scan, no draw — gen_function_pointer_type is EXACTLY the original genMatch).
     Follows the §3-bias subset pattern. See private_notes/exp_step2bc/NOTES.md. *)
  Definition route_a_callee_w : nat := 3.

  (* [route-A callee-bias 2b] (lead-adjudicated extension, SEPARATE knob so 2a stays
     plan-literal and 2b is independently disable-able) soft weight for preferring a
     LOADING-PTR-PARAM helper at callee selection: candidates whose registered type is
     in loading_fn_types (helpers whose body loads through a pointer param — recorded
     per-helper at definition time by a pure AST scan, NOT by a type proxy). Composed
     BEFORE 2a (channel-B priority, per the plan's (c)-then-(b) spirit): 2b soft-prefers
     first, and its 1/(w+1)-fallback / empty-subset case defers to the 2a-biased pick,
     which in turn defers to the ordinary uniform pick. 0 = OFF and STREAM-IDENTICAL.
     See private_notes/exp_step2bc/NOTES.md §bias-composition. *)
  Definition route_a_callee_ptr_w : nat := 3.

  (* [route-A param-cell] (USER AMENDMENT r6, PLAN §4.3b) FLAG, not a weight (0 = OFF).
     Completes the params-as-sources approximation for POINTER params. The param VALUE
     seed (route_a_call_seed, at param registration) marks the pointer's own bit, but a
     passed address is a run-invariant constant — runtime-DEAD. The LIVE half is the
     memory the pointer names. So with the flag on, EVERY function's TYPE_Pointer(Some t)
     param gets a minted synthetic cell (points_to[param]) whose content mask is the
     param's own bit (2^i). The always-on route_a_mem_w machinery then (i) soft-prefers
     loads THROUGH the param inside the body, (ii) propagates bit i into the loaded value,
     and (iii) the ret-bridge load-arm can pick the param — making the K2-callee shape
     ("load the param, return it") a preferred generation pattern; store-through-param /
     gep-of-param cell bookkeeping composes for free (all via points_to/arg_set, no read
     path changes). 0 gates BOTH the cell mint and the mask seed: no entity ids consumed,
     nothing written -> trivially stream-identical. Channel-B package (the callee-side
     receptor of intervention (c)), NOT a third kill intervention: the two-intervention
     litmus budget is unchanged. See private_notes/exp_step2d/NOTES.md. *)
  Definition route_a_param_cell : nat := 1.

  (* [route-A arg-deref] (USER AMENDMENT r7, PLAN §4.3c) FLAG, not a weight (0 = OFF).
     The CALLER-SIDE dual of route_a_param_cell (r6). The pre-r7 call-result approximation
     "result mask = OR of the arg masks" uses only each pointer ARG's VALUE mask; the
     POINTEE cell's content mask is IGNORED. Consequence: in the exact channel-B killer
     chain (main passes a pointer to a tainted cell, the callee loads+returns), the call
     result is shadow-UNTAINTED, so §3 never routes it toward an observation — funnel
     stage s4 stays unbiased (a hidden multiplicative penalty). With the flag on, for each
     pointer argument whose cell is KNOWN, OR arg_set[points_to[p]] (the pointee cell's
     content provenance — ONE indirection level, matching the shadow's object granularity)
     into the arg-mask accumulator that add_to_local_ctx assigns to the call RESULT, so the
     result's SSA mask reflects reachable-memory taint. Covers all THREE settle paths in
     gen_call_arg: M1 pick (pointer entity in cur_ent), ordinary pick (optr captured by
     cur_ent_take), and retro-minted global — which, since r7b, ALSO lands in optr: the
     retro-mint site sets cur_ent (see [route-A arg-deref r7b] in gen_exp_size'), because
     retro-minting is the DOMINANT ptr-arg path (Step-1 m4 ~100%) and with optr = None
     both M2's cell_mask_record and this deref were no-ops exactly where M2 creates the
     taint (lead review finding). optr = None survives only as a defensive dead case.
     When M2 (the pre-call tainted store) fired, the deref runs AFTER cell_mask_record so
     it reads the JUST-STORED cell mask. 0 gates every read/write/draw -> trivially
     stream-identical. NOTE: this flag RIDES the knob-on call-arg path — gen_call_arg is
     only reached when route_a_ptrarg_w <> 0 (gen_call_list gates on it), so the flag can
     act only then. State-only (no randomness). NOT a kill intervention (a consistency
     completion like r6); the two-intervention litmus budget is unchanged. See
     private_notes/exp_step2e/NOTES.md. *)
  Definition route_a_arg_deref : nat := 1.

  (* [obs-freeze D1] (PLAN_obs-freeze.en.md §3 D1) knob for per-bit observation
     exclusivity: 0 = OFF (every new code path dead -> stream-identical to the
     chain-ON HEAD), 1 = SOFT (frozen-hit carriers are demoted out of the
     tainted-preferred tiers only; unbiased fallback picks remain possible),
     2 = HARD (frozen-hit carriers are excluded from the FULL gen_var_ent pool,
     all branches, AND from the P0.c rows 2-6 pools). The head (D2 baton) is
     always exempt. TRIGGERS (per-function frozen_bits |= condition mask):
     the 4458 cond-br condition (bracketed cur_mask take, NB3) and the two
     GENUINE loop branch conditions (loop_cond/next_cond, via arg_set[loop_init]
     per P0.a — the 4514 select condition is NOT an observation, no trigger). *)
  Definition route_a_obs_freeze : nat := 0.

  (* [obs-freeze D2] (PLAN §3 D2) chain-entry freeze knob: 0 = OFF,
     1 = trigger at ALL internal calls, 2 = only at PLAUSIBLE callees
     (signature-level: a type in loading_fn_types, or a scalar-param signature).
     Trigger: when a carrier of bit i is consumed as a call ARGUMENT the bit is
     frozen (calls do not observe arguments — no observation budget is spent);
     pending_ce accumulates during arg generation (= cur_mask at the peek point,
     P0.d) and is APPLIED at call-instruction assembly (result entity minted,
     callee fixed): frozen_bits |= pending_ce; head[b] := call result for each
     bit (void result -> headship lapses). NOTE: rides the knob-on call path —
     gen_call_arg/gen_call_list's arg loop is only reached when
     route_a_ptrarg_w <> 0 (HEAD default 3), like route_a_arg_deref. *)
  Definition route_a_ce_freeze : nat := 0.

  (* Either freeze knob active? (compile-time constant; gates every new state op). *)
  Definition freeze_on : bool :=
    negb (andb (Nat.eqb route_a_obs_freeze 0) (Nat.eqb route_a_ce_freeze 0)).

  (* [param-obs-ban D1] (PLAN_param-obs-ban §3-D1) unconditional ban knob:
     0 = OFF (stream-identical to HEAD), 1 = ON. When on, a helper NEVER
     observes its own parameters: at the two observation-feeding pick contexts
     — S1 the cond-br condition (~gen_terminator_sz) and S2 loop_init's operand
     picks (gen_loop_sz) — every candidate whose arg-provenance mask intersects
     the current function's param bits (fz_param) is HARD-excluded from the pool.
     Ret / store / select-cond / call-arg picks are NOT observations and are
     untouched (the ret channel is the mutant's through-cut, preserved for g4).
     Preconditions (PLAN NB4): route_a_call_seed<>0 (else no param bits are
     seeded -> ban vacuous) and route_a_mem_w<>0 (stored-param->cell->reload
     route keeps mask coverage); both hold at HEAD defaults. INDEPENDENT of the
     freeze knobs — own key (fz_param), own gate, own sites. *)
  Definition route_a_param_obs_ban : nat := 0.

  (* Compile-time gate for every ban state op / pool filter. *)
  Definition param_ban_on : bool :=
    negb (Nat.eqb route_a_param_obs_ban 0).

  (* ================================================================== *)
  (* [obs-freeze] state helpers. All are pure state reads/writes — no    *)
  (* randomness; every call site is knob-gated so the both-knobs-0       *)
  (* stream is byte-identical to HEAD.                                   *)
  (* ================================================================== *)

  (* Set head[b] := e for every bit b of mask m. Fuel N.size m covers the MSB. *)
  Fixpoint heads_set_aux (fuel : nat) (bit : N) (m : N) (e : Z) (h : IM.Raw.t Z)
    {struct fuel} : IM.Raw.t Z :=
    match fuel with
    | O => h
    | S f =>
        let h' := if N.testbit m bit then IM.Raw.add (Z.of_N bit) e h else h in
        heads_set_aux f (N.succ bit) m e h'
    end.

  Definition heads_set_bits (m : N) (e : Z) (h : IM.Raw.t Z) : IM.Raw.t Z :=
    heads_set_aux (N.to_nat (N.size m)) 0%N m e h.

  (* The bits (as a mask) whose head is exactly entity e. *)
  Definition heads_bits_of (h : IM.Raw.t Z) (e : Z) : N :=
    IM.Raw.fold (fun (k : Z) (he : Z) (acc : N) =>
                   if Z.eqb he e then N.lor acc (N.shiftl 1%N (Z.to_N k)) else acc)
                h 0%N.

  (* Remove every bit of mask m from the head map (rebuild-without). *)
  Definition heads_remove_bits (h : IM.Raw.t Z) (m : N) : IM.Raw.t Z :=
    IM.Raw.fold (fun (k : Z) (he : Z) (acc : IM.Raw.t Z) =>
                   if N.testbit m (Z.to_N k) then acc else IM.Raw.add k he acc)
                h (IM.Raw.empty _).

  (* Does [inter] contain a bit whose head is NOT entity e (incl. headless)? *)
  Fixpoint freeze_hit_aux (fuel : nat) (bit : N) (inter : N) (h : IM.Raw.t Z) (e : Z)
    {struct fuel} : bool :=
    match fuel with
    | O => false
    | S f =>
        if N.testbit inter bit
        then match IM.Raw.find (Z.of_N bit) h with
             | Some he => if Z.eqb he e then freeze_hit_aux f (N.succ bit) inter h e
                          else true
             | None => true
             end
        else freeze_hit_aux f (N.succ bit) inter h e
    end.

  (* THE filter predicate: carrier e (mask m) is frozen-hit iff it carries a
     frozen bit for which it is not the head. Head-exempt = head of EVERY frozen
     bit it carries (in hard mode a non-head frozen carrier is unpickable, so a
     multi-frozen-bit carrier is a baton-merge result heading all of them). *)
  Definition freeze_hit_b (frozen : N) (h : IM.Raw.t Z) (e : Z) (m : N) : bool :=
    let inter := N.land m frozen in
    if N.eqb inter 0%N then false
    else freeze_hit_aux (N.to_nat (N.size inter)) 0%N inter h e.

  Definition freeze_get : GenLLVM FreezeState :=
    use (metadata .@ freeze_st').

  (* Per-function reset (gen_definition_h entry; PLAN r2 Codex B1 scoping). *)
  Definition freeze_reset : GenLLVM unit :=
    if freeze_on
    then metadata .@ freeze_st' .= freeze_empty;; ret tt
    else ret tt.

  (* Trigger core: frozen_bits |= m (heads untouched). *)
  Definition freeze_or_bits (m : N) : GenLLVM unit :=
    fz <- freeze_get;;
    metadata .@ freeze_st' .=
      {| fz_bits := N.lor (fz_bits fz) m
       ; fz_heads := fz_heads fz
       ; fz_moved := fz_moved fz
       ; fz_param := fz_param fz ; fz_pob_on := fz_pob_on fz |};;
    ret tt.

  (* D1 trigger (observation emission site). Gated on the D1 knob. *)
  Definition obs_freeze_trigger (m : N) : GenLLVM unit :=
    if Nat.eqb route_a_obs_freeze 0
    then ret tt
    else if N.eqb m 0%N then ret tt else freeze_or_bits m.

  (* D2 head installation at call assembly: head[b] := e for all b in m. *)
  Definition freeze_set_heads (m : N) (e : Z) : GenLLVM unit :=
    fz <- freeze_get;;
    metadata .@ freeze_st' .=
      {| fz_bits := fz_bits fz
       ; fz_heads := heads_set_bits m e (fz_heads fz)
       ; fz_moved := fz_moved fz
       ; fz_param := fz_param fz ; fz_pob_on := fz_pob_on fz |};;
    ret tt.

  (* Head consumption at an operand/candidate pick (D2 transfer table,
     per-operand-pick detection — the chain-vector cur_ent-take precedent moved
     to the pick itself): the FIRST consumption removes the head entry and parks
     the bits in fz_moved; the next result binding whose mask carries them takes
     headship (add_to_local_ctx), a store moves them into the cell
     (freeze_transfer_store), anything else lapses at the boundary. Later
     same-round references of the stale head are ordinary frozen carriers. *)
  Definition freeze_consume_pick (e : Z) : GenLLVM unit :=
    if freeze_on
    then
      fz <- freeze_get;;
      let consumed := N.land (heads_bits_of (fz_heads fz) e) (fz_bits fz) in
      if N.eqb consumed 0%N
      then ret tt
      else
        metadata .@ freeze_st' .=
          {| fz_bits := fz_bits fz
           ; fz_heads := heads_remove_bits (fz_heads fz) consumed
           ; fz_moved := N.lor (fz_moved fz) consumed
           ; fz_param := fz_param fz ; fz_pob_on := fz_pob_on fz |};;
        ret tt
    else ret tt.

  (* Read-and-clear the moved-bits channel. *)
  Definition fz_moved_take : GenLLVM N :=
    fz <- freeze_get;;
    metadata .@ freeze_st' .=
      {| fz_bits := fz_bits fz
       ; fz_heads := fz_heads fz
       ; fz_moved := 0%N
       ; fz_param := fz_param fz ; fz_pob_on := fz_pob_on fz |};;
    ret (fz_moved fz).

  (* Boundary lapse (gen_instr entry / br-condition bracket): consumption that
     reached no result binding ends the bits' chains (dead-probe cost, D2). *)
  Definition fz_moved_discard : GenLLVM unit :=
    if freeze_on then _ <- fz_moved_take;; ret tt else ret tt.

  (* Head transfer at a result binding: bits (fz_moved ∩ result mask) move onto
     the new entity; bits outside the result's mask stay parked (they lapse at
     the next boundary — e.g. a pointer-head consumed by a store's address). *)
  Definition freeze_transfer_result (e : Z) (resmask : N) : GenLLVM unit :=
    if freeze_on
    then
      fz <- freeze_get;;
      let mv := N.land (fz_moved fz) resmask in
      if N.eqb mv 0%N
      then ret tt
      else
        metadata .@ freeze_st' .=
          {| fz_bits := fz_bits fz
           ; fz_heads := heads_set_bits mv e (fz_heads fz)
           ; fz_moved := N.ldiff (fz_moved fz) mv
           ; fz_param := fz_param fz ; fz_pob_on := fz_pob_on fz |};;
        ret tt
    else ret tt.

  (* Store of a head: the baton moves into the target CELL (transfer table).
     valmask = the stored value's mask; unknown cell -> the bits lapse. *)
  Definition freeze_transfer_store (optr : option Z) (valmask : N) : GenLLVM unit :=
    if freeze_on
    then match optr with
         | None => ret tt
         | Some p =>
             oc <- points_to_find p;;
             match oc with
             | None => ret tt
             | Some c => freeze_transfer_result c valmask
             end
         end
    else ret tt.

  (* [obs-freeze D1-hard] drop frozen-hit carriers (head-exempt) from a candidate
     pool map. Pure; call sites gate on the knob (mode 2 only for gen_var_ent's
     full pool; the rows 2-6 tainted tiers filter at any mode <> 0). *)
  Definition freeze_filter_pool {a} (argmap : IM.Raw.t N) (fz : FreezeState)
    (pool : IM.Raw.t a) : IM.Raw.t a :=
    if N.eqb (fz_bits fz) 0%N
    then pool
    else
      IM.Raw.fold
        (fun (k : Z) (v : a) (acc : IM.Raw.t a) =>
           let m := match IM.Raw.find k argmap with
                    | Some mv => mv
                    | None => 0%N
                    end in
           if freeze_hit_b (fz_bits fz) (fz_heads fz) k m
           then acc
           else IM.Raw.add k v acc)
        pool (IM.Raw.empty _).

  (* ================================================================== *)
  (* [param-obs-ban] state helpers. Pure state reads/writes; every call    *)
  (* site is gated on param_ban_on so the knob-0 stream is byte-identical.  *)
  (* Reuse freeze_get (the freeze_st' accessor) — fz_param/fz_pob_on live   *)
  (* in the same record.                                                    *)
  (* ================================================================== *)

  (* Per-function capture (gen_definition_h): set fz_param := m and clear the
     transient context flag. Overwrites unconditionally so nothing leaks across
     function boundaries; preserves the freeze fields (empty in arm B, live in
     arm C where freeze_reset already ran first). *)
  Definition pob_set_param (m : N) : GenLLVM unit :=
    fz <- freeze_get;;
    metadata .@ freeze_st' .=
      {| fz_bits := fz_bits fz
       ; fz_heads := fz_heads fz
       ; fz_moved := fz_moved fz
       ; fz_param := m ; fz_pob_on := false |};;
    ret tt.

  (* Toggle the transient observation-context flag around S1/S2 pick sites. *)
  Definition pob_set_ctx (b : bool) : GenLLVM unit :=
    fz <- freeze_get;;
    metadata .@ freeze_st' .=
      {| fz_bits := fz_bits fz
       ; fz_heads := fz_heads fz
       ; fz_moved := fz_moved fz
       ; fz_param := fz_param fz ; fz_pob_on := b |};;
    ret tt.

  (* [param-obs-ban D1] the hard pool filter: drop every carrier whose mask
     intersects pbits. Pure; the call site gates on param_ban_on AND fz_pob_on
     (so it fires ONLY inside an observation-feeding pick). pbits=0 (main, or a
     seedless helper at call_seed=0) => identity => ban vacuous. Non-value picks
     (types/globals) carry mask 0 => never excluded. *)
  Definition pob_filter_pool {a} (argmap : IM.Raw.t N) (pbits : N)
    (pool : IM.Raw.t a) : IM.Raw.t a :=
    if N.eqb pbits 0%N
    then pool
    else
      IM.Raw.fold
        (fun (k : Z) (v : a) (acc : IM.Raw.t a) =>
           let m := match IM.Raw.find k argmap with
                    | Some mv => mv
                    | None => 0%N
                    end in
           if N.eqb (N.land m pbits) 0%N
           then IM.Raw.add k v acc
           else acc)
        pool (IM.Raw.empty _).

  (* #[global] Instance STGST : Monad (stateT GenState G). *)
  (* apply Monad_stateT. *)
  (* typeclasses eauto. *)
  (* Defined. *)

  #[global] Instance MGEN : Monad GenLLVM.
  unfold GenLLVM.
  apply Monad_eitherT.
  typeclasses eauto.
  Defined.

  (* GC: For following, I will leave pieces defined in another way so I can learn more about how to use monad *)
  (* Definition lift_GenLLVM {A} (g : G A) : GenLLVM A := *)
  (* mkEitherT (mkStateT (fun stack => mkStateT (fun st => a <- g;; ret (inr a, stack, st)))). *)

  Definition lift_GenLLVM {A} (g : G A) : GenLLVM A.
    unfold GenLLVM.
    apply mkEitherT.
    apply mkStateT.
    (* intros. *)
    refine (fun st => _).
    refine (a <- g ;; ret _).
    exact (inr a, st).
  Defined.

  #[global] Instance MGENT: MonadT GenLLVM G.
  unfold GenLLVM.
  constructor.
  exact @lift_GenLLVM.
  Defined.

  Definition lift_system_GenLLVM {A} (system : SystemT GenState G A) : GenLLVM A.
    unfold GenLLVM.
    apply mkEitherT.
    apply (fmap ret system).
  Defined.

  #[global] Instance MGENTSYSTEM: MonadT GenLLVM (SystemT GenState G).
  unfold GenLLVM.
  constructor.
  exact @lift_system_GenLLVM.
  Defined.

  (* SAZ:
     [failGen] was the one piece of the backtracking variant of QuickChick we
     needed.
   *)
  (* Definition failGen {A:Type} (s:string) : GenLLVM A := *)
  (* mkEitherT (mkStateT (fun stack => ret (inl s, stack))). *)

  Definition failGen {A:Type} (s:string) : GenLLVM A.
    apply mkEitherT.
    apply mkStateT.
    refine (fun stack => _).
    exact (ret (inl (s), stack)).
  Defined.

  Definition annotate {A:Type} (s:string) (g : GenLLVM A) : GenLLVM A
    := old_stack <- use (metadata .@ debug_stack');;
       metadata .@ debug_stack' %= (fun stack => s :: stack);;
       a <- g;;
       metadata .@ debug_stack' .= old_stack;;
       ret a.

  Definition annotate_debug (s : string) : GenLLVM unit :=
    annotate s (ret tt).

  Definition dup_string_wrt_nat (s : string) (n : nat) :=
    let fix dup_string_wrt_nat_tail_recur (acc : string) (n : nat):=
      match n with
      | 0%nat => acc
      | S z => dup_string_wrt_nat_tail_recur (s ++ acc)%string z
      end in dup_string_wrt_nat_tail_recur "" n.

  #[global] Instance MetadataStore_GenState : @MetadataStore G Metadata (SystemState GenState G).
  split.
  apply gen_context'.
  Defined.

  Definition contextFromMap {a} (m : IM.Raw.t a) : GenLLVM var_context
    := IM.Raw.fold
         (fun (k : Z) _ (acc : GenLLVM var_context) =>
            e <- lift_system_GenLLVM (getEntity (mkEnt k));;
            ctx <- acc;;
            ret (IM.Raw.add k e ctx)
         ) m (ret (IM.Raw.empty _)).

  Definition get_local_ctx : GenLLVM var_context
    := locals <- use (gen_context' .@ is_local');;
       contextFromMap locals.

  Definition get_global_ctx : GenLLVM var_context
    := globals <- use (gen_context' .@ is_global');;
       contextFromMap globals.

  Definition merge_var_context (c1 : var_context) (c2 : var_context) : var_context
    := IM.Raw.merge c1 c2.

  Definition get_ctx : GenLLVM var_context
    := locals <- use (gen_context' .@ is_local');;
       globals <- use (gen_context' .@ is_global');;
       contextFromMap (IM.Raw.merge globals locals).

  Definition get_typ_ctx : GenLLVM type_context
    := types <- use (gen_context' .@ type_alias');;
       contextFromMap types.

  Definition get_ptrtoint_ctx : GenLLVM ptr_to_int_context
    := ptois <- use (gen_context' .@ from_pointer');;
       contextFromMap ptois.

  (* Get all variable contexts that might need to be saved *)
  Definition get_variable_ctxs : GenLLVM all_var_contexts
    := local_ctx <- get_local_ctx;;
       global_ctx <- get_global_ctx;;
       ptoi_ctx <- get_ptrtoint_ctx;;
       ret (local_ctx, global_ctx, ptoi_ctx).

  Definition get_global_memo : GenLLVM (list (global typ))
    := use (metadata .@ global_memo').

  Definition set_local_ctx (ctx : var_context) : GenLLVM unit
    := lift (setEntities ctx).

  Definition set_global_ctx (ctx : var_context) : GenLLVM unit
    := lift (setEntities ctx).

  Definition set_ptrtoint_ctx (ptoi_ctx : ptr_to_int_context) : GenLLVM unit
    := lift (setEntities ptoi_ctx).

  Definition set_global_memo (memo : list (global typ)) : GenLLVM unit
    := (metadata .@ global_memo') .= memo;;
       ret tt.

  Definition add_to_global_memo (x : (global typ)) : GenLLVM unit
    := (metadata .@ global_memo') %= (fun memo => x :: memo);;
       ret tt.

  Definition restore_variable_ctxs (ctxs : all_var_contexts) : GenLLVM unit
    := match ctxs with
       | (local_ctx, global_ctx, ptoi_ctx) =>
           set_local_ctx local_ctx;;
           set_global_ctx global_ctx;;
           set_ptrtoint_ctx ptoi_ctx
       end.

  Definition restore_local_variable_ctxs (ctxs : all_local_var_contexts) : GenLLVM unit
    := match ctxs with
       | (local_ctx, ptoi_ctx) =>
           set_local_ctx local_ctx;;
           set_ptrtoint_ctx ptoi_ctx
       end.

  Definition append_ctx (vars :var_context) : GenLLVM unit
    := lift (setEntities vars).

  (* This is very aggressive and will reset entities / entity counter *)
  Definition backtrackMetadata {A} (g : GenLLVM A) : GenLLVM A
    := m <- use gen_context';;
       a <- g;;
       gen_context' .= m;;
       ret a.

  Definition reset_local_ctx : GenLLVM unit
    := locals <- use (gen_context' .@ is_local');;
       lift (deleteEntities locals).

  Definition reset_global_ctx : GenLLVM unit
    := globals <- use (gen_context' .@ is_global');;
       lift (deleteEntities globals).

  Definition reset_ctx : GenLLVM unit
    := reset_local_ctx;;
       reset_global_ctx.

  Definition reset_typ_ctx : GenLLVM unit
    := types <- use (gen_context' .@ type_alias');;
       lift (deleteEntities types).

  Definition reset_ptrtoint_ctx : GenLLVM unit
    := ptrs <- use (gen_context' .@ from_pointer');;
       lift (deleteEntities ptrs).

  Definition reset_global_memo : GenLLVM unit
    := metadata .@ global_memo' .= def;;
       ret tt.

  Definition hide_local_ctx {A} (g : GenLLVM A) : GenLLVM A
    := saved_local_ctx <- get_local_ctx;;
       reset_local_ctx;;
       a <- g;;
       set_local_ctx saved_local_ctx;;
       ret a.

  Definition hide_global_ctx {A} (g : GenLLVM A) : GenLLVM A
    := saved_global_ctx <- get_global_ctx;;
       reset_global_ctx;;
       a <- g;;
       set_global_ctx saved_global_ctx;;
       ret a.

  Definition hide_ctx {A} (g: GenLLVM A) : GenLLVM A
    := hide_global_ctx (hide_local_ctx g).

  Definition hide_ptrtoint_ctx {A} (g: GenLLVM A) : GenLLVM A
    := saved_ctx <- get_ptrtoint_ctx;;
       reset_ptrtoint_ctx;;
       a <- g;;
       append_ctx saved_ctx;;
       ret a.

  Definition hide_variable_ctxs {A} (g: GenLLVM A) : GenLLVM A
    := hide_ctx (hide_ptrtoint_ctx g).

  (** Restore context after running a generator. *)
  Definition backtrack_local_ctx {A} (g: GenLLVM A) : GenLLVM A
    := saved_local_ctx <- get_local_ctx;;
       a <- g;;
       reset_local_ctx;;
       set_local_ctx saved_local_ctx;;
       ret a.

  Definition backtrack_global_ctx {A} (g: GenLLVM A) : GenLLVM A
    := saved_global_ctx <- get_global_ctx;;
       a <- g;;
       reset_global_ctx;;
       set_global_ctx saved_global_ctx;;
       ret a.

  Definition backtrack_ctx {A} (g : GenLLVM A) : GenLLVM A
    := backtrack_global_ctx (backtrack_local_ctx g).

  (** Restore ptrtoint context after running a generator. *)
  Definition backtrack_ptrtoint_ctx {A} (g: GenLLVM A) : GenLLVM A
    := saved_ctx <- get_ptrtoint_ctx;;
       a <- g;;
       reset_global_ctx;;
       set_ptrtoint_ctx saved_ctx;;
       ret a.

  (** Restore all variable contexts after running a generator. *)
  Definition backtrack_variable_ctxs {A} (g: GenLLVM A) : GenLLVM A
    := backtrack_ctx (backtrack_ptrtoint_ctx g).

  (* Elems implemented with reservoir sampling *)
  Definition elems_res {A} (def : G A) (l : list A) : G A
    := fst
         (fold_left
            (fun '(gacc, k) a =>
               let gen' :=
                 swap <- fmap (N.eqb 0) (choose (0%N, k));;
                 if swap
                 then (* swap *)
                   ret a
                 else (* No swap *)
                   gacc
               in (gen', (k+1)%N))
            l (def, 0%N)).

  Definition oneOf_LLVM {A} (gs : list (GenLLVM A)) : GenLLVM A
    := fst
         (fold_left
            (fun '(gacc, k) a =>
               let gen' :=
                 swap <- lift (fmap (N.eqb 0) (choose (0%N, k)));;
                 if swap
                 then (* swap *)
                   a
                 else (* No swap *)
                   gacc
               in (gen', (k+1)%N))
            gs (failGen "oneOf_LLVM", 0%N)).

  Definition oneOf_res {A} (def : G A) (gs : list (G A)) : G A
    := fst
         (fold_left
            (fun '(gacc, k) a =>
               let gen' :=
                 swap <- fmap (N.eqb 0) (choose (0%N, k));;
                 if swap
                 then (* swap *)
                   a
                 else (* No swap *)
                   gacc
               in (gen', (k+1)%N))
            gs (def, 0%N)).

  Definition freq_res {A} (def : G A) (gs : list (N * G A)) : G A
    := fst
         (fold_left
            (fun '(gacc, k) '(fk, a) =>
               let k' := (k + fk)%N in
               let gen' :=
                 swap <- fmap (fun x => N.leb x fk) (choose (0%N, k'));;
                 if swap
                 then (* swap *)
                   a
                 else (* No swap *)
                   gacc
               in (gen', k'))
            gs (def, 0%N)).

  Definition freq_LLVM_N {A} (gs : list (N * GenLLVM A)) : GenLLVM A
    := fst
         (fold_left
            (fun '(gacc, k) '(fk, a) =>
               let k' := (k + fk)%N in
               let gen' :=
                 swap <- lift (fmap (fun x => N.leb x fk) (choose (0%N, k')));;
                 if swap
                 then (* swap *)
                   a
                 else (* No swap *)
                   gacc
               in (gen', k'))
            gs (failGen "freq_LLVM_N", 0%N)).

  Definition freq_LLVM {A} (gs : list (nat * GenLLVM A)) : GenLLVM A
    :=
    (* ctx <- get_ctx;; *)
    (* let is_empty := l_is_empty ctx in *)
    fst
         (fold_left
            (fun '(gacc, k) '(fk, a) =>
               let fkn := N.of_nat fk in
               let k' := (k + fkn)%N in
               let gen' :=
                 swap <- lift (fmap (fun x => N.leb x fkn) (choose (0%N, k')));;
                 if swap
                 then (* swap *)
                   a
                 else (* No swap *)
                   gacc
               in (gen', k'))
            gs (failGen ("freq_LLVM" (* ++ newline ++ if (is_empty) then "Current context is empty" else "Current context: " ++ show ctx *)), 0%N)).

  (* SAZ: Where do we need this? *)
  (*
  Definition freq_LLVM' {A} (gs : list (nat * GenLLVM A)) : GenLLVM A
    :=
        mkStateT
          (fun st => freq_ failGen (fmap (fun '(n, g) => (n, runStateT g st)) gs)).
   *)


  Definition thunkGen_LLVM {A} (thunk : unit -> GenLLVM A) : GenLLVM A
    := u <- ret tt;;
       thunk tt.

  Definition oneOf_LLVM_thunked {A} (gs : list (unit -> GenLLVM A)) : GenLLVM A
    := thunkGen_LLVM
         (fst
            (fold_left
               (fun '(gacc, k) a =>
                  let gen' := fun x =>
                    swap <- lift (fmap (N.eqb 0) (choose (0%N, k)));;
                    if swap
                    then (* swap *)
                      a x
                    else (* No swap *)
                      gacc x
                  in (gen', (k+1)%N))
               gs (fun _ => failGen "oneOF_LLVM_thunked", 0%N))).

  Definition oneOf_LLVM_thunked' {A} (gs : list (unit -> GenLLVM A)) : GenLLVM A
    := n <- lift (choose (0, List.length gs - 1)%nat);;
       thunkGen_LLVM (nth n gs (fun _ => failGen "oneOf_LLVM_thunked'")).

  Definition freq_LLVM_thunked_N {A} (gs : list (N * (unit -> GenLLVM A))) : GenLLVM A
    := thunkGen_LLVM
         (fst
            (fold_left
               (fun '(gacc, k) '(fk, a) =>
                  let k' := (k + fk)%N in
                  let gen' := fun x =>
                    swap <- lift (fmap (fun x => N.leb x fk) (choose (0%N, k')));;
                    if swap
                    then (* swap *)
                      a x
                    else (* No swap *)
                      gacc x
                  in (gen', k'))
               gs (fun _ => failGen "freq_LLVM_thunked_N'", 0%N))).

  Definition freq_LLVM_thunked {A} (gs : list (nat * (unit -> GenLLVM A))) : GenLLVM A
    := thunkGen_LLVM
         (fst
            (fold_left
               (fun '(gacc, k) '(fk, a) =>
                  let fkn := N.of_nat fk in
                  let k' := (k + fkn)%N in
                  let gen' := fun x =>
                    swap <- lift (fmap (fun x => N.leb x fkn) (choose (0%N, k')));;
                    if swap
                    then (* swap *)
                      a x
                    else (* No swap *)
                      gacc x
                  in (gen', k'))
               gs (fun _ => failGen "freq_LLVM_thunked", 0%N))).

  (* SAZ: do we need this? *)
  (*
  Definition freq_LLVM_thunked' {A} (gs : list (nat * (unit -> GenLLVM A))) : GenLLVM A
    := mkStateT
         (fun st => freq_ failGen (fmap (fun '(n, g) => (n, runStateT (thunkGen_LLVM g) st)) gs)).
   *)

  Definition elems_LLVM {A : Type} (l: list A) : GenLLVM A
    := fst
         (fold_left
            (fun '(gacc, k) a =>
               let gen' :=
                 swap <- lift (fmap (N.eqb 0) (choose (0%N, k)));;
                 if swap
                 then (* swap *)
                   ret a
                 else (* No swap *)
                   gacc
               in (gen', (k+1)%N))
            l (failGen "elems_LLVM", 0%N)).

  Definition vectorOf_LLVM {A : Type} (k : nat) (g : GenLLVM A)
    : GenLLVM (list A) :=
    fold_left (fun m' m =>
                 x <- m;;
                 xs <- m';;
                 ret (x :: xs)) (repeat g k) (ret []).

  Definition sized_LLVM {A : Type} (gn : nat -> GenLLVM A) : GenLLVM A.
    apply mkEitherT.
    apply mkStateT.
    refine (fun st => sized _).
    refine (fun n => _).
    refine (let opt := unEitherT (gn n) in _).
    refine (let ann := runStateT opt st in ann).
    Defined.

  (* Definition sized_LLVM {A : Type} (gn : nat -> GenLLVM A) : GenLLVM A *)
  (*   := mkEitherT (mkStateT *)
  (*                   (fun st => sized (fun n => runStateT (unEitherT (gn n)) st))). *)

  Definition resize_LLVM {A : Type} (sz : nat) (g : GenLLVM A) : GenLLVM A.
    apply mkEitherT.
    apply mkStateT.
    refine (fun st => _).
    refine (let opt := unEitherT g in _).
    refine (let ans := runStateT opt st in _).
    refine (resize sz ans).
    Defined.

  (* Definition resize_LLVM {A : Type} (sz : nat) (g : GenLLVM A) : GenLLVM A *)
  (*   := mkEitherT (mkStateT *)
  (*                   (fun st => resize sz (runStateT (unEitherT g) st))). *)

  Definition listOf_LLVM {A : Type} (g : GenLLVM A) : GenLLVM (list A) :=
    sized_LLVM (fun n =>
                  k <- lift (choose (0, n)%nat);;
                  vectorOf_LLVM k g).

  Definition nonemptyListOf_LLVM
             {A : Type} (g : GenLLVM A) : GenLLVM (list A)
    := sized_LLVM (fun n =>
                     k <- lift (choose (1, n)%nat);;
                     vectorOf_LLVM k g).

  Definition run_GenLLVM {A} (g: GenLLVM A) : G (string + A) :=
    let ran := runStateT (unEitherT g) def in
    '(err_a,st) <- ran;;
    let stack := st .^ metadata .@ debug_stack' in
    let debug : string := fold_right (fun d1 drest => (d1 ++ newline ++ drest)%string) "" (rev stack) in
    let flushed_err :=
      match err_a with
      | inl err_str => inl (err_str ++ newline ++ "DEBUG SECTION: " ++ newline ++ debug)%string
      | inr _ => err_a
      end in
    ret flushed_err.

End GenerationState.

Section TypGenerators.
  Definition assign_if {m : Type -> Type} {s a b : Type} `{HM : Monad m} `{ST : @MonadState s m}
    (cnd : bool) (l : ASetter s s a b) (v : b) : m unit
    := if cnd then l .= v;; ret tt else ret tt.

  Definition bool_setter (cnd : bool) : Update unit
    := if cnd then SetValue _ tt else Unset _.

  Definition GenQuery' m := QueryT Metadata m.
  Definition runGenQuery {m A E}
    `{TE : ToEnt E}
    `{Monad m}
    `{MS: MetadataStore m Metadata (SystemState GenState m)}
    `{MT: MonadT (SystemT GenState m) m}
    (q : GenQuery' m A) (k : E) : SystemT GenState m (option A):=
    let e := toEnt k in
    meta <- getEntity e;;
    lift (unQueryT q e meta).
  Definition GenQuery := GenQuery' G.

  Definition runGenQueryLLVM {A E} `{TE : ToEnt E}
    (q : GenQuery A) (k : E) : GenLLVM (option A):=
    lift (runGenQuery q k).

  (* Attempt to find a matching entity in the context...
     Note: this is not a random selection, the first thing found is returned.
   *)
  Definition genFind {a es E}
    `{ToEnt E} `{Foldable es E}
    (focus : @EntTarget es E _ _ GenState G)
    (filter : GenQuery a)
    : GenLLVM (option a)
    := lift (efind focus filter).

  (* Normalize a type using the GenState to look up type aliases *)
  Program Fixpoint normalize_type_GenLLVM (t : typ) : GenLLVM typ :=
    match t with
    | TYPE_Array sz t =>
        nt <- normalize_type_GenLLVM t;;
        ret (TYPE_Array sz nt)

    | TYPE_Function ret_t args varargs =>
        nret <- normalize_type_GenLLVM ret_t;;
        nargs <- map_monad normalize_type_GenLLVM args;;
        ret (TYPE_Function nret nargs varargs)

    | TYPE_Struct fields =>
        nfields <- map_monad normalize_type_GenLLVM fields;;
        ret (TYPE_Struct nfields)

    | TYPE_Packed_struct fields =>
        nfields <- map_monad normalize_type_GenLLVM fields;;
        ret (TYPE_Packed_struct nfields)

    | TYPE_Vector sz t =>
        nt <- normalize_type_GenLLVM t;;
        ret (TYPE_Vector sz nt)

    | TYPE_Identified id =>
        ot <- genFind
               (use (gen_context' .@ type_alias'))
               (n <- queryl name';;
                if Ident.eq_dec id n
                then queryl type_alias'
                else mzero);;
        match ot with
        | Some t' =>
            normalize_type_GenLLVM t'
        | None =>
            ret (TYPE_Identified id)
        end
    | TYPE_I sz => ret t
    | TYPE_IPTR => ret t
    | TYPE_Pointer (Some t') =>
        pt <- normalize_type_GenLLVM t';;
        ret (TYPE_Pointer (Some pt))
    | TYPE_Pointer None => ret t
    | TYPE_Void => ret t
    | TYPE_Half => ret t
    | TYPE_Float => ret t
    | TYPE_Double => ret t
    | TYPE_X86_fp80 => ret t
    | TYPE_Fp128 => ret t
    | TYPE_Ppc_fp128 => ret t
    | TYPE_Metadata => ret t
    | TYPE_X86_mmx => ret t
    | TYPE_Opaque => ret t
    end.

  (* Only works correctly if the type is well formed *)
  Definition is_sized_type (t : typ) : GenLLVM bool
    := t' <- normalize_type_GenLLVM t;;
       ret (is_sized_type_h t').

  (* TODO: handle opaque PTR *)
  Definition typ_metadata_setter (τ : typ) : GenLLVM (Metadata SetterOf) :=
    normalized <- normalize_type_GenLLVM τ;;
    let st := is_sized_type_h normalized in
    ret (def
         & (@normalized_type' SetterOf .~ SetValue _ normalized)
         & (@is_sized' SetterOf .~ bool_setter st)
         & (@is_pointer' SetterOf .~ bool_setter (match τ with | TYPE_Pointer _ => true | _ => false end))
         & (@is_sized_pointer' SetterOf .~
              bool_setter
              (match τ with
               | TYPE_Pointer τ' => st
               | _ => false
               end))
         & (@is_aggregate' SetterOf .~
              bool_setter
              (match normalized with
               | TYPE_Array _ _
               | TYPE_Struct _
               | TYPE_Packed_struct _ => true
               | _ => false
               end))
         & (@is_indexable' SetterOf .~
              bool_setter
              (match normalized with
               | TYPE_Array sz _ => N.ltb 0 sz
               | TYPE_Struct l
               | TYPE_Packed_struct l => negb (l_is_empty l)
               | _ => false
               end))
         & (@is_non_void' SetterOf .~
              bool_setter
              (match normalized with
               | TYPE_Void => false
               | _ => true
               end))
         & (@is_vector' SetterOf .~
              bool_setter
              (match normalized with
               | TYPE_Vector _ _ => true
               | _ => false
               end))
         & (@is_ptr_vector' SetterOf .~
              bool_setter
              (match normalized with
               | TYPE_Pointer _ => true
               | TYPE_Vector _ (TYPE_Pointer _) => true
               | _ => false
               end))
         & (@is_sized_ptr_vector' SetterOf .~
              bool_setter
              (match normalized with
               | TYPE_Pointer t => st
               | TYPE_Vector _ (TYPE_Pointer t) => st
               | _ => false
               end))
         & (@is_first_class_type' SetterOf .~
              bool_setter
              (match normalized with
               | TYPE_Struct _
               | TYPE_Packed_struct _ => false
               | TYPE_Array _ _ => false
               | TYPE_Pointer (Some (TYPE_Function _ _ _)) => false
               | _ => true
               end))
         & (@is_function_pointer' SetterOf .~
              bool_setter (is_function_pointer_h normalized))).

  Definition set_typ_metadata (e : Ent) (τ : typ) : GenLLVM unit
    := setter <- typ_metadata_setter τ;;
       lift (setEntity e setter).

  Definition add_to_local_ctx (x : (ident * typ)) : GenLLVM Ent
    := let '(n, t) := x in
       e <- lift newEntity;;
       (gen_context' .@ entl e .@ is_local') .= ret tt;;
       (gen_context' .@ entl e .@ name') .= ret n;;
       (gen_context' .@ entl e .@ variable_type') .= ret t;;
       (* Default to deterministic *)
       (gen_context' .@ entl e .@ deterministic') .= true;;
       set_typ_metadata e t;;
       (* [route-A propagation] assign the accumulated operand-mask to this new result,
          then reset the accumulator for the next instruction. See ROUTE_A_IMPL §2. *)
       m <- cur_mask_take;;
       arg_mask_set (unEnt e) m;;
       (* [obs-freeze D2 transfer] SSA consumption of a head: the result whose mask
          carries the moved bits becomes their new head (gated; no-op at knobs 0). *)
       freeze_transfer_result (unEnt e) m;;
       ret e.

  Definition genLocalEnt (τ : typ) : GenLLVM (ident * Ent)
    :=  n <- ID_Local <$> new_local_id;;
        e <- add_to_local_ctx (n, τ);;
        ret (n, e).

  Definition genLocal (τ : typ) : GenLLVM ident
    :=  fst <$> genLocalEnt τ.

  (* [route-A chain-memory] mint a fresh cell for the memory object named by pointer
     entity [p]. Bare newEntity: consumes only the entity counter — entity IDs of
     everything created later SHIFT vs. a build without minting. Analysed harmless
     (no generation decision reads id VALUES; names come from num_raw) and verified
     empirically by the w=0 seed-fixed MD5 A/B. *)
  Definition cell_mint (p : Z) : GenLLVM unit
    := c <- lift newEntity;;
       points_to_set p (unEnt c).

  Definition add_to_global_ctx (x : (ident * typ)) : GenLLVM Ent
    := let '(n, t) := x in
       e <- lift newEntity;;
       (gen_context' .@ entl e .@ is_global') .= ret tt;;
       (gen_context' .@ entl e .@ name') .= ret n;;
       (gen_context' .@ entl e .@ variable_type') .= ret t;;
       (* Default to deterministic *)
       (gen_context' .@ entl e .@ deterministic') .= true;;
       set_typ_metadata e t;;
       (* [route-A chain-memory] a global names a memory object -> give it a cell.
          Initializers are constants (content mask starts 0); function symbols get a
          dead cell — harmless. Covers the global-pointer share of load/store traffic. *)
       cell_mint (unEnt e);;
       ret e.

  Definition genGlobalEnt (τ : typ) : GenLLVM (ident * Ent)
    :=  n <- ID_Global <$> new_global_id;;
        e <- add_to_global_ctx (n, τ);;
        ret (n, e).

  Definition genGlobal (τ : typ) : GenLLVM ident
    := fst <$> genGlobalEnt τ.

  (* A little uncertain about this. Should void instructions have
  names? Cannot refer to their results anyway, so maybe not? *)
  Definition genVoidEnt : GenLLVM (instr_id * Ent)
    :=  e <- lift newEntity;;
        n <- new_void_id;;
       set_typ_metadata e TYPE_Void;;
       ret (n, e).

  Definition genVoid : GenLLVM instr_id
    :=  fmap fst genVoidEnt.

  (* Generate an id for the instruction given the return type *)
  Definition genInstrIdEnt (τ : typ) : GenLLVM (instr_id * Ent)
    := match τ with
       | TYPE_Void => genVoidEnt
       | _ => (fun '(n, e) => (IId (ident_to_raw_id n), e)) <$> genLocalEnt τ
       end.

  (* Generate an id for the instruction given the return type *)
  Definition genInstrId (τ : typ) : GenLLVM instr_id
    := match τ with
       | TYPE_Void => genVoid
       | _ => (fun (n : ident) => IId (ident_to_raw_id n)) <$> genLocal τ
       end.

  Definition add_to_typ_ctx (x : (ident * typ)) : GenLLVM unit
    := let '(n, t) := x in
       e <- lift newEntity;;
       (gen_context' .@ entl e .@ name') .= ret n;;
       (gen_context' .@ entl e .@ type_alias') .= ret t;;
       set_typ_metadata e t;;
       st <- use (gen_context' .@ entl e .@ is_sized');;
       (gen_context' .@ entl e .@ is_sized_type_alias') .= st;;
       (gen_context' .@ entl e .@ is_sized') .= None;;
       (* Disable type alias usage for now. See https://github.com/vellvm/vellvm/issues/361 *)
       (gen_context' .@ entl e .@ type_alias') .= None;;
       (gen_context' .@ entl e .@ is_sized_type_alias') .= None;;
       ret tt.

  (* Should this be a local? *)
  Definition add_to_ptrtoint_ctx (x : (typ * ident * Ent)) : GenLLVM unit
    := let '(t, name, ptr) := x in
       e <- lift newEntity;;
       (gen_context' .@ entl e .@ name') .= ret name;;
       (gen_context' .@ entl e .@ is_local') .= ret tt;;
       (gen_context' .@ entl e .@ from_pointer') .= ret ptr;;
       (* non-deterministic if the pointer is (could have
          deterministic pointers like null) *)
       d <- use (gen_context' .@ entl ptr .@ deterministic');;
       (gen_context' .@ entl e .@ deterministic') .= d;;
       set_typ_metadata e t;;
       ret tt.


  (* (*filter all the (ident, typ) in ctx such that typ is a ptr*) *)
  (* Definition filter_ptr_typs (typ_ctx : type_context) (ctx : var_context) : var_context := *)
  (*   filter (fun '(_, t) => match normalize_type typ_ctx t with *)
  (*                       | TYPE_Pointer _ => true *)
  (*                       | _ => false *)
  (*                       end) ctx. *)

  (* Definition filter_sized_ptr_typs (typ_ctx : type_context) (ctx : var_context) : var_context := *)
  (*   filter (fun '(_, t) => match normalize_type typ_ctx t with *)
  (*                       | TYPE_Pointer t => is_sized_type typ_ctx t *)
  (*                       | _ => false *)
  (*                       end) ctx. *)

  (* Definition filter_sized_typs (typ_ctx: type_context) (ctx : var_context) : var_context := *)
  (*   filter (fun '(_, t) => is_sized_type typ_ctx t) ctx. *)

  (* Definition filter_non_void_typs (typ_ctx : type_context) (ctx : var_context) : var_context := *)
  (*   filter (fun '(_, t) => match normalize_type typ_ctx t with *)
  (*                       | TYPE_Void => false *)
  (*                       | _ => true *)
  (*                       end) ctx. *)

  (* Definition filter_agg_typs (typ_ctx : type_context) (ctx: var_context) : var_context := *)
  (*   filter (fun '(_, t) => *)
  (*             match normalize_type typ_ctx t with *)
  (*             | TYPE_Array sz _ => N.ltb 0 sz *)
  (*             | TYPE_Struct l *)
  (*             | TYPE_Packed_struct l => negb (l_is_empty l) *)
  (*             | _ => false *)
  (*             end ) ctx. *)

  (* Definition filter_vec_typs (typ_ctx : type_context) (ctx: var_context) : var_context := *)
  (*   filter (fun '(_, t) => *)
  (*             match normalize_type typ_ctx t with *)
  (*             | TYPE_Vector _ _ => true *)
  (*             | _ => false *)
  (*             end) ctx. *)

  (* Definition filter_ptr_vecptr_typs (typ_ctx : type_context) (ctx: var_context) : var_context := *)
  (*   filter (fun '(_, t) => *)
  (*             match normalize_type typ_ctx t with *)
  (*             | TYPE_Pointer _ => true *)
  (*             | TYPE_Vector _ (TYPE_Pointer _) => true *)
  (*             | _ => false *)
  (*             end) ctx. *)

  (* Definition filter_sized_ptr_vecptr_typs (typ_ctx : type_context) (ctx: var_context) : var_context := *)
  (*   filter (fun '(_, t) => *)
  (*             match normalize_type typ_ctx t with *)
  (*             | TYPE_Pointer t => is_sized_type typ_ctx t *)
  (*             | TYPE_Vector _ (TYPE_Pointer t) => is_sized_type typ_ctx t *)
  (*             | _ => false *)
  (*             end) ctx. *)

  Definition gen_IntMapRaw_key_filter {a b} (m : IM.Raw.t a) (filter : GenQuery b) : GenLLVM (option Z)
    := '(g, _) <- (IM.Raw.fold
                    (fun key _ (grest : GenLLVM (option Z * N)) =>
                       cnd <- is_some <$> runGenQueryLLVM filter key;;
                       '(gacc, k) <- grest;;
                       swap <- lift (fmap (N.eqb 0) (choose (0%N, k)));;
                       let k' := if cnd then (k+1)%N else k in
                       if swap && cnd
                       then (* swap *)
                         ret (Some key, k')
                       else (* No swap *)
                         ret (gacc, k'))
                    m (ret (@None Z, 0%N)));;
       ret g.

  Definition gen_IntMapRaw_filter {a b} (m : IM.Raw.t a) (filter : GenQuery b) : GenLLVM (option b)
    := '(g, _) <- (IM.Raw.fold
                    (fun key _ (grest : GenLLVM (option b * N)) =>
                       qres <- runGenQueryLLVM filter key;;
                       let cnd := is_some qres in
                       '(gacc, k) <- grest;;
                       swap <- lift (fmap (N.eqb 0) (choose (0%N, k)));;
                       let k' := if cnd then (k+1)%N else k in
                       if swap && cnd
                       then (* swap *)
                         ret (qres, k')
                       else (* No swap *)
                         ret (gacc, k'))
                    m (ret (@None b, 0%N)));;
       ret g.

  Definition gen_IntMapRaw_key {a} (m : IM.Raw.t a) : GenLLVM (option Z)
    := gen_IntMapRaw_key_filter m (ret tt).

  Definition gen_IntMapRaw_ent {a} (m : IM.Raw.t a) : GenLLVM (option Ent)
    := fmap (fmap mkEnt) (gen_IntMapRaw_key m).

  Definition gen_IntMapRaw_ent_filter {a b} (m : IM.Raw.t a) (filter : GenQuery b) : GenLLVM (option Ent)
    := fmap (fmap mkEnt) (gen_IntMapRaw_key_filter m filter).

  Definition gen_sized_type_alias : GenLLVM (option ident)
    := es <- use (gen_context' .@ is_sized_type_alias');;
       var <- gen_IntMapRaw_ent_filter es (withoutl is_function_pointer');;
       match var with
       | Some var =>
           id <- use (gen_context' .@ entl var .@ name');;
           ret id
       | None => ret None
       end.

  Definition gen_entity_with {a} (focus : Lens' (SystemState GenState G) (IM.Raw.t a)): GenLLVM (option Ent)
    := es <- use focus;;
       gen_IntMapRaw_ent es.

  Definition gen_entity_with_filter {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a))
    (filter : GenQuery b)
    : GenLLVM (option Ent)
    := es <- use focus;;
       gen_IntMapRaw_ent_filter es filter.

  (* Randomly select from all matching entities in the context *)
  Definition gen_foldable_filter_ent {b es E} `{ToEnt E} `{Foldable es E}
    (m : es) (filter : GenQuery b) : GenLLVM (option (Ent * b))
    := '(g, _) <- (fold _
                    (fun key (grest : GenLLVM (option (Ent * b) * N)) =>
                       qres <- runGenQueryLLVM filter key;;
                       let cnd := is_some qres in
                       '(gacc, k) <- grest;;
                       swap <- lift (fmap (N.eqb 0) (choose (0%N, k)));;
                       let k' := if cnd then (k+1)%N else k in
                       if swap && cnd
                       then (* swap *)
                         ret (fmap (fun x => (toEnt key, x)) qres, k')
                       else (* No swap *)
                         ret (gacc, k'))
                    (ret (@None (Ent * b), 0%N))) m;;
       ret g.

  Definition gen_foldable_filter {b es E} `{ToEnt E} `{Foldable es E}
    (m : es) (filter : GenQuery b) : GenLLVM (option b)
    := fmap snd <$> gen_foldable_filter_ent m filter.

  Definition genMatchEnt {a es E}
    `{ToEnt E} `{Foldable es E}
    (focus : @EntTarget es E _ _ GenState G)
    (filter : GenQuery a)
    : GenLLVM (option (Ent * a))
    := es <- lift focus;;
       gen_foldable_filter_ent es filter.

  Definition genMatch {a es E}
    `{ToEnt E} `{Foldable es E}
    (focus : @EntTarget es E _ _ GenState G)
    (filter : GenQuery a)
    : GenLLVM (option a)
    := es <- lift focus;;
       gen_foldable_filter es filter.

  Definition get_type_from_alias (var : Ent) : GenLLVM typ
    := mident <- use (gen_context' .@ entl var .@ type_alias');;
       match mident with
       | Some id => ret id
       | None => failGen "gen_sized_type_alias, couldn't find entity... Shouldn't happen"
       end.

  Definition get_type_of_variable (var : Ent) : GenLLVM typ
    := mident <- use (gen_context' .@ entl var .@ variable_type');;
       match mident with
       | Some id => ret id
       | None => failGen "gen_sized_type_alias, couldn't find entity... Shouldn't happen"
       end.

  (* Generate a type that matches one of the type aliases *)
  Definition gen_sized_type_of_alias {a} (focus : Lens' (SystemState GenState G) (IM.Raw.t a)) : GenLLVM typ
    := var <- gen_entity_with focus;;
       match var with
       | Some var =>
           get_type_from_alias var
       | None => failGen "gen_sized_type_of_alias, couldn't find entity... Shouldn't happen"
       end.

  Definition gen_sized_type_of_alias_filter {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a))
    (filter : GenQuery b)
    : GenLLVM (option typ)
    := var <- gen_entity_with_filter focus filter;;
       match var with
       | Some var => fmap Some (get_type_from_alias var)
       | None => ret None
       end.

  (* Generate a type that matches one of the variables *)
  Definition gen_type_of_variable_filter {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a))
    (filter : GenQuery b)
    : GenLLVM (option typ)
    := var <- gen_entity_with_filter focus filter;;
       match var with
       | Some var => fmap Some (get_type_of_variable var)
       | None => ret None
       end.

  (* Not sized in the QuickChick sense, sized in the LLVM sense. *)
  Definition gen_sized_typ_0 : GenLLVM typ :=
    oid <- gen_sized_type_alias;;
    let ident_gen :=
      match oid with
      | None => []
      | Some id => [ret (TYPE_Identified id)]
      end
    in
    oneOf_LLVM
      (ident_gen ++
         (map ret
            ([ TYPE_I 1
               ; TYPE_I 8
               ; TYPE_I 16
               ; TYPE_I 32
               ; TYPE_I 64
                        (* TODO: Could generate TYPE_Identified if we filter for sized types *)
                        (* ; TYPE_Half *)
                        (* ; TYPE_X86_fp80 *)
                        (* ; TYPE_Fp128 *)
                        (* ; TYPE_Ppc_fp128 *)
                        (* ; TYPE_Metadata *)
                        (* ; TYPE_X86_mmx *)
                        (* ; TYPE_Opaque *)
              ] ++
               (if enable_float_generation
                then
                 [ (* TODO: Generate floats and stuff *)
                   TYPE_Float
                   (* ; TYPE_Double *)
                 ]
               else
                 [])
         ))).

  (* TODO: Move this *)
  Definition lengthN {X} (xs : list X) : N :=
    fold_left (fun acc x => (acc + 1)%N) xs 0%N.

  (* Definition gen_typ_from_ctx (ctx : var_context) : GenLLVM typ *)
  (*   := fmap snd (elems_LLVM ctx). *)

  (* Definition gen_ident_from_ctx (ctx : var_context) : GenLLVM ident *)
  (*   := fmap fst (elems_LLVM ctx). *)

  Definition def_option_GenLLVM {a} (def : GenLLVM a) (gopt : GenLLVM (option a)) : GenLLVM a
    := o <- gopt;;
       match o with
       | Some a => ret a
       | None => def
       end.

  Definition gen_type_matching_alias_focus {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a)) (filter : GenQuery b)
    : GenLLVM (option typ)
    := gen_sized_type_of_alias_filter focus filter.

  Definition gen_type_matching_variable_focus {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a)) (filter : GenQuery b)
    : GenLLVM (option typ)
    := gen_type_of_variable_filter focus filter.

  Definition gen_type_matching_alias {b} (filter : GenQuery b) : GenLLVM (option typ)
    := gen_type_matching_alias_focus (gen_context' .@ is_sized_type_alias') filter.

  Definition gen_type_matching_local {b} (filter : GenQuery b) : GenLLVM (option typ)
    := gen_type_matching_variable_focus (gen_context' .@ is_local') filter.

  Definition gen_type_matching_global {b} (filter : GenQuery b) : GenLLVM (option typ)
    := gen_type_matching_variable_focus (gen_context' .@ is_global') filter.

  Definition gen_type_matching_variable {b} (filter : GenQuery b) : GenLLVM (option typ)
    := gen_type_matching_variable_focus (gen_context' .@ variable_type') filter.

  Definition gen_primitive_typ : GenLLVM typ :=
    oneOf_LLVM
      ([ret (TYPE_I 1)
        ; ret (TYPE_I 8)
        ; ret (TYPE_I 16)
        ; ret (TYPE_I 32)
        ; ret (TYPE_I 64)
        ] ++ if enable_float_generation then [ret (TYPE_Float) (* ; ret TYPE_DOUBLE *)] else []).

  Definition sized_aggregate_typ_gens (subg : nat -> GenLLVM typ) (sz : nat) :  list (unit -> GenLLVM typ)
    := [ (fun _ => gen_sized_typ_0)
       ; (fun _ => ret (fun t => TYPE_Pointer (Some t)) <*> subg sz)
       (* TODO: Might want to restrict the size to something reasonable *)
       ; (fun _ => ret TYPE_Array <*> lift_GenLLVM genN <*> subg sz)
       ; (fun _ => ret TYPE_Vector <*> (n <- lift_GenLLVM genN;; ret (n + 1)%N) <*> gen_primitive_typ)
       ; (fun _ => ret TYPE_Struct <*> nonemptyListOf_LLVM (subg sz))
       ; (fun _ => ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (subg sz))
    ].

  Fixpoint gen_typ_size'
    (baseGen : GenLLVM typ)
    (aggregate_gens : (nat -> GenLLVM typ) -> nat -> list (unit -> GenLLVM typ))
    (from_context : GenLLVM (option typ)) (sz : nat)
    {struct sz} : GenLLVM typ :=
    match sz with
    | O => baseGen
    | (S sz') =>
        ofc <- from_context;;
        let fc : list (N * (unit -> GenLLVM typ)) :=
          match ofc with
          | None => []
          | Some fc =>
              [(10%N, fun _ : unit => ret fc)]
          end
        in
        let aggregates := (sized_aggregate_typ_gens (fun sz => @gen_typ_size' baseGen aggregate_gens from_context sz) sz') in
        freq_LLVM_thunked_N (fc ++ fmap (fun x => (1%N, x)) aggregates)
    end.

  Definition gen_sized_typ_size :=
    gen_typ_size' gen_sized_typ_0 sized_aggregate_typ_gens (gen_type_matching_variable (withl is_sized')).

  Definition max_typ_size : nat := 4.

  Definition gen_sized_typ  : GenLLVM typ
    := sized_LLVM (fun sz => gen_sized_typ_size (min sz max_typ_size)).

(*   (* Want to be able to use gen_sized_typ' to do this... *)
(*      But I did not notice this wants only sized types from the contexts. *)
(*      Need to be able to filter focused entities to only the ones with the sized type tags... Should be doable. *)
(*    *) *)
(*   Definition gen_sized_typ_ptrin_fctx : GenLLVM typ *)
(*     := gen_typ_size' ( *)
(*     ctx <- get_ctx;; *)
(*     aliases <- get_typ_ctx;; *)
(*     let typs_in_ctx := filter_sized_typs aliases ctx in *)
(*     sized_LLVM (fun sz => gen_sized_typ_size_ptrinctx sz typs_in_ctx). *)

(* gen_sized_typ_ptrin_fctx seems to grab a  *)

(*   Definition gen_sized_typ_ptrin_gctx : GenLLVM typ *)
(*     := *)
(*     gctx <- get_global_ctx;; *)
(*     aliases <- get_typ_ctx;; *)
(*     let typs_in_ctx := filter_sized_typs aliases gctx in *)
(*     sized_LLVM (fun sz => gen_sized_typ_size_ptrinctx sz typs_in_ctx). *)

  Definition gen_type_alias_ident : GenLLVM (option ident)
    := es <- use (gen_context' .@ type_alias');;
       var <- gen_IntMapRaw_ent es;;
       match var with
       | Some var =>
           id <- use (gen_context' .@ entl var .@ name');;
           ret id
       | None => ret None
       end.

  (* Generate a type of size 0 *)
  Definition gen_typ_0 : GenLLVM typ :=
    oid <- gen_sized_type_alias;;
    (* let ident_gen := *)
    (*   match oid with *)
    (*   | None => [] *)
    (*   | Some id => [ret (TYPE_Identified id)] *)
    (*   end *)
    (* in *)
    oneOf_LLVM
          ((* identified ++ *)
           (map ret
                ([ TYPE_I 1
                ; TYPE_I 8
                ; TYPE_I 16
                ; TYPE_I 32
                ; TYPE_I 64
                ; TYPE_Void
                (* ; TYPE_Metadata *)
                (* ; TYPE_X86_mmx *)
                (* ; TYPE_Opaque *)
                ] ++
                   (if enable_float_generation
                    then
                      [ (* TODO: Generate floats and stuff *)
                        TYPE_Float
                          (* ; TYPE_Double *)
                          (* ; TYPE_Half *)
                          (* ; TYPE_X86_fp80 *)
                          (* ; TYPE_Fp128 *)
                          (* ; TYPE_Ppc_fp128 *)
                      ]
                    else
                      [])))).


  Definition aggregate_typ_gens (subg : nat -> GenLLVM typ) (sz : nat) :  list (unit -> GenLLVM typ)
    := [ (fun _ => subg 0%nat)
       ; (fun _ => ret (fun t => TYPE_Pointer (Some t)) <*> subg sz)
       (* TODO: Might want to restrict the size to something reasonable *)
       ; (fun _ => ret TYPE_Array <*> lift_GenLLVM genN <*> subg sz)
       ; (fun _ => ret TYPE_Vector <*> (n <- lift_GenLLVM genN;; ret (n + 1)%N) <*> gen_primitive_typ)
       ; (fun _ =>
          let n := Nat.div (S sz) 2 in
          ret TYPE_Function <*> subg n <*> listOf_LLVM (gen_sized_typ_size n) <*> ret false)
       ; (fun _ => ret TYPE_Struct <*> nonemptyListOf_LLVM (subg sz))
       ; (fun _ => ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (subg sz))
    ].

  (* TODO: This should probably be mutually recursive with
     gen_sized_typ since pointers of any type are considered sized *)
  Definition gen_typ_size : nat -> GenLLVM typ :=
    gen_typ_size' gen_typ_0 aggregate_typ_gens (gen_type_matching_variable (ret tt)).

  Definition gen_typ : GenLLVM typ
    := sized_LLVM (fun sz => gen_typ_size (min sz max_typ_size)).

  Definition gen_typ_non_void_0 : GenLLVM typ :=
    oid <- gen_sized_type_alias;;
    let ident_gen :=
      match oid with
      | None => []
      | Some id => [ret (TYPE_Identified id)]
      end
    in
    oneOf_LLVM
      (ident_gen ++
         (map ret
            ([ TYPE_I 1
               ; TYPE_I 8
               ; TYPE_I 16
               ; TYPE_I 32
               ; TYPE_I 64
                        (* ; TYPE_Metadata *)
                        (* ; TYPE_X86_mmx *)
                        (* ; TYPE_Opaque *)
              ] ++ (if enable_float_generation
                    then
                      [ (* TODO: Generate floats and stuff *)
                        TYPE_Float
                          (* ; TYPE_Double *)
                          (* ; TYPE_Half *)
                          (* ; TYPE_X86_fp80 *)
                          (* ; TYPE_Fp128 *)
                          (* ; TYPE_Ppc_fp128 *)
                      ]
                    else
                      [])))).

  Definition gen_typ_non_void_size : nat -> GenLLVM typ :=
    gen_typ_size' gen_typ_non_void_0 aggregate_typ_gens (gen_type_matching_variable (withl is_non_void')).

  Definition gen_typ_non_void : GenLLVM typ :=
    sized_LLVM (fun sz => gen_typ_non_void_size (min sz max_typ_size)).

  (* Non-void, non-function types *)
  Definition gen_typ_non_void_size_wo_fn : nat -> GenLLVM typ :=
    gen_typ_size' gen_typ_non_void_0 sized_aggregate_typ_gens (gen_type_matching_variable (withl is_non_void')).

  Definition gen_typ_non_void_wo_fn : GenLLVM typ :=
    sized_LLVM (fun sz => gen_typ_non_void_size_wo_fn (min sz max_typ_size)).

  (* TODO: look up identifiers *)
  (* Types for operation expressions *)
  Definition gen_op_typ : GenLLVM typ :=
    oneOf_LLVM
      (map ret
         ([ TYPE_I 1
            ; TYPE_I 8
            ; TYPE_I 16
            ; TYPE_I 32
            ; TYPE_I 64
                     (* ; TYPE_Metadata *)
                     (* ; TYPE_X86_mmx *)
                     (* ; TYPE_Opaque *)
           ] ++ (if enable_float_generation
                 then
                   [ (* TODO: Generate floats and stuff *)
                     TYPE_Float
                       (* ; TYPE_Double *)
                       (* ; TYPE_Half *)
                       (* ; TYPE_X86_fp80 *)
                       (* ; TYPE_Fp128 *)
                       (* ; TYPE_Ppc_fp128 *)
                   ]
                 else
                   []))).

  (* TODO: look up identifiers *)
  Definition gen_int_typ : GenLLVM typ :=
    elems_LLVM
      [ TYPE_I 1
        ; TYPE_I 8
        ; TYPE_I 16
        ; TYPE_I 32
        ; TYPE_I 64
      ].

  (* TODO: look up identifiers *)
  Definition gen_float_typ : GenLLVM typ :=
    elems_LLVM
      [ TYPE_Float
        (* ; TYPE_Double *)
      ].

  (* TODO: IPTR not implemented *)
  Definition gen_int_typ_for_ptr_cast : GenLLVM typ :=
    ret (TYPE_I 64).
End TypGenerators.

Section ExpGenerators.

  (* SAZ: Here there were old uses of [failGen] that I replaced (arbitrarily) with the
     last element of the non-empty list. *)

  Definition gen_ibinop : G ibinop :=
     oneOf_ (ret Xor) (* SAZ: This default case is a hack *)
           [ ret LLVMAst.Add <*> ret false <*> ret false
           ; ret Sub <*> ret false <*> ret false
           ; ret Mul <*> ret false <*> ret false
           ; ret Shl <*> ret false <*> ret false
           ; ret UDiv <*> ret false
           ; ret SDiv <*> ret false
           ; ret LShr <*> ret false
           ; ret AShr <*> ret false
           ; ret URem
           ; ret SRem
           ; ret And
           ; ret Or
           ; ret Xor
           ].

  (*Float operations*)
  Definition gen_fbinop : G fbinop :=
    oneOf_ (ret FRem) (* SAZ: This default case is a hack *)
            [ ret LLVMAst.FAdd
            ; ret FSub
            ; ret FMul
            ; ret FDiv
            (* ; ret FRem *) (* Disable FRem because vellvm doesn't support it yet *)
            ].

  Definition gen_icmp : G icmp :=
    oneOf_ (ret Sle) (* SAZ: This default case is a hack *)
           (map ret
                [ Eq; Ne; Ugt; Uge; Ult; Ule; Sgt; Sge; Slt; Sle]).

  Definition gen_fcmp : G fcmp :=
    oneOf_ (ret FTrue) (* SAZ: This default case is a hack *)
            (map ret
                  [FFalse; FOeq; FOgt; FOge; FOlt; FOle; FOne; FOrd;
                   FUno; FUeq; FUgt; FUge; FUlt; FUle; FUne; FTrue]).

  (* Generate an expression of a given type *)
  (* Context should probably not have duplicate ids *)
  (* May want to decrease size more for arrays and vectors *)
  (* TODO: Need a restricted version of the type generator for this? *)
  (* TODO: look up named types from the context *)
  (* TODO: generate conversions? *)

  (* TODO: Move this*)
  Fixpoint dtyp_eq (a : dtyp) (b : dtyp) {struct a} : bool
    := match a, b with
       | DTYPE_I sz, DTYPE_I sz' =>
         if Pos.eq_dec sz sz' then true else false
       | DTYPE_I _, _ => false
       | DTYPE_IPTR, DTYPE_IPTR => true
       | DTYPE_IPTR, _ => false
       | DTYPE_Pointer, DTYPE_Pointer => true
       | DTYPE_Pointer, _ => false
       | DTYPE_Void, DTYPE_Void => true
       | DTYPE_Void, _ => false
       | DTYPE_Half, DTYPE_Half => true
       | DTYPE_Half, _ => false
       | DTYPE_Float, DTYPE_Float => true
       | DTYPE_Float, _ => false
       | DTYPE_Double, DTYPE_Double => true
       | DTYPE_Double, _ => false
       | DTYPE_X86_fp80, DTYPE_X86_fp80 => true
       | DTYPE_X86_fp80, _ => false
       | DTYPE_Fp128, DTYPE_Fp128 => true
       | DTYPE_Fp128, _ => false
       | DTYPE_Ppc_fp128, DTYPE_Ppc_fp128 => true
       | DTYPE_Ppc_fp128, _ => false
       | DTYPE_Metadata, DTYPE_Metadata => true
       | DTYPE_Metadata, _ => false
       | DTYPE_X86_mmx, DTYPE_X86_mmx => true
       | DTYPE_X86_mmx, _ => false
       | DTYPE_Array sz t, DTYPE_Array sz' t' =>
           if N.eq_dec sz sz'
           then dtyp_eq t t'
           else false
       | DTYPE_Array _ _, _ => false
       | DTYPE_Struct fields, DTYPE_Struct fields' =>
         if Nat.eqb (Datatypes.length fields) (Datatypes.length fields')
         then forallb id (map_In (zip fields fields') (fun '(a, b) HIn => dtyp_eq a b))
         else false
       | DTYPE_Struct _, _ => false
       | DTYPE_Packed_struct fields, DTYPE_Packed_struct fields' =>
         if Nat.eqb (Datatypes.length fields) (Datatypes.length fields')
         then forallb id (map_In (zip fields fields') (fun '(a, b) HIn => dtyp_eq a b))
         else false
       | DTYPE_Packed_struct _, _ => false
       | DTYPE_Opaque, DTYPE_Opaque => false (* TODO: Unsure if this should compare equal *)
       | DTYPE_Opaque, _ => false
       | DTYPE_Vector sz t, DTYPE_Vector sz' t' =>
           if N.eq_dec sz sz'
           then dtyp_eq t t'
           else false
       | DTYPE_Vector _ _, _ => false
       end.

  (* TODO: Move this*)
  (* This only returns what you expect on normalized typs *)
  (* TODO: I don't think this does the right thing for pointers to
           identified types... It should be conservative and say that
           the types are *not* equal always, though.
   *)
  Fixpoint normalized_typ_eq (a : typ) (b : typ) {struct a} : bool
    := match a with
       | TYPE_I sz =>
         match b with
         | TYPE_I sz' => if Pos.eq_dec sz sz' then true else false
         | _ => false
         end
       | TYPE_IPTR =>
         match b with
         | TYPE_IPTR => true
         | _ => false
         end
       | TYPE_Pointer t =>
         match b with
         | TYPE_Pointer t' =>
             match (t, t') with
             | (Some t, Some t') => normalized_typ_eq t t'
             | (None, None) => true
             | _ => false
             end
         | _ => false
         end
       | TYPE_Void =>
         match b with
         | TYPE_Void => true
         | _ => false
         end
       | TYPE_Half =>
         match b with
         | TYPE_Half => true
         | _ => false
         end
       | TYPE_Float =>
         match b with
         | TYPE_Float => true
         | _ => false
         end
       | TYPE_Double =>
         match b with
         | TYPE_Double => true
         | _ => false
         end
       | TYPE_X86_fp80 =>
         match b with
         | TYPE_X86_fp80 => true
         | _ => false
         end
       | TYPE_Fp128 =>
         match b with
         | TYPE_Fp128 => true
         | _ => false
         end
       | TYPE_Ppc_fp128 =>
         match b with
         | TYPE_Ppc_fp128 => true
         | _ => false
         end
       | TYPE_Metadata =>
         match b with
         | TYPE_Metadata => true
         | _ => false
         end
       | TYPE_X86_mmx =>
         match b with
         | TYPE_X86_mmx => true
         | _ => false
         end
       | TYPE_Array sz t =>
         match b with
         | TYPE_Array sz' t' =>
           if N.eq_dec sz sz'
           then normalized_typ_eq t t'
           else false
         | _ => false
         end
       | TYPE_Function ret args varargs=>
         match b with
         | TYPE_Function ret' args' varargs' =>
             Nat.eqb (Datatypes.length args) (Datatypes.length args') &&
               normalized_typ_eq ret ret' &&
               forallb id (zipWith (fun a b => normalized_typ_eq a b) args args')
             && Bool.eqb varargs varargs'
         | _ => false
         end
       | TYPE_Struct fields =>
         match b with
         | TYPE_Struct fields' =>
             Nat.eqb (Datatypes.length fields) (Datatypes.length fields') &&
             forallb id (zipWith (fun a b => normalized_typ_eq a b) fields fields')
         | _ => false
         end
       | TYPE_Packed_struct fields =>
         match b with
         | TYPE_Packed_struct fields' =>
             Nat.eqb (Datatypes.length fields) (Datatypes.length fields') &&
             forallb id (zipWith (fun a b => normalized_typ_eq a b) fields fields')
         | _ => false
         end
       | TYPE_Opaque =>
         match b with
         | TYPE_Opaque => false (* TODO: Unsure if this should compare equal *)
         | _ => false
         end
       | TYPE_Vector sz t =>
         match b with
         | TYPE_Vector sz' t' =>
           if N.eq_dec sz sz'
           then normalized_typ_eq t t'
           else false
         | _ => false
         end
       | TYPE_Identified id =>
           match b with
           | TYPE_Identified id' =>
               if Ident.eq_dec id id'
               then true
               else false
           | _ => false
           end
       end.

  (* This needs to use normalized_typ_eq, instead of dtyp_eq because of pointer types...
     dtyps only tell you that a type is a pointer, the other type
     information about the pointers is erased.
   *)
  Definition filter_type (ty : typ) (ctx : list (ident * typ)) : list (ident * typ)
    := filter (fun '(i, t) => normalized_typ_eq (normalize_type ctx ty) (normalize_type ctx t)) ctx.

  Variant contains_flag :=
  | soft
  | hard.

  (* This is a part of the easy fix for Issue 260. It can also potentially help other generators in filtering
     If there exists a subtyp of certain tribute *)
  Fixpoint contains_typ (t_from : typ) (t : typ) (flag : contains_flag): bool :=
    match t_from with
    | TYPE_I _ =>
        match t with
        | TYPE_I _ =>
            match flag with
            | soft => true
            | hard => normalized_typ_eq t_from t
            end
        | _ => false
        end
    | TYPE_IPTR
    | TYPE_Pointer None
    | TYPE_Half
    | TYPE_Float
    | TYPE_Double
    | TYPE_X86_fp80
    | TYPE_Fp128
    | TYPE_Ppc_fp128
    | TYPE_Metadata
    | TYPE_X86_mmx => normalized_typ_eq t_from t
    | TYPE_Pointer (Some subtyp) =>
        match t with
        | TYPE_Pointer (Some subtyp') =>
            match flag with
            | soft => true
            | hard => normalized_typ_eq subtyp subtyp' || contains_typ subtyp t flag
            end
        | _ => contains_typ subtyp t flag
        end
    | TYPE_Array sz subtyp =>
        match t with
        | TYPE_Array sz' subtyp' =>
            match flag with
            | soft => true
            | hard =>  (sz =? sz')%N && ((normalized_typ_eq subtyp subtyp') || (contains_typ subtyp t flag))
            end
        | _ => contains_typ subtyp t flag
        end
    | TYPE_Vector sz subtyp =>
        match t with
        | TYPE_Vector sz' subtyp' =>
            match flag with
            | soft => true
            | hard =>  (sz =? sz')%N && ((normalized_typ_eq subtyp subtyp') || (contains_typ subtyp t flag))
            end
        | _ => contains_typ subtyp t flag
        end
    | TYPE_Struct fields =>
        match t with
        | TYPE_Struct fields' =>
            match flag with
            | soft => true
            | hard => normalized_typ_eq t_from t || fold_left (fun acc x => acc || x) (map (fun y => contains_typ y t flag) fields) false
            end
        | _ => fold_left (fun acc x => acc || contains_typ x t flag) fields false
        end
    | TYPE_Packed_struct fields =>
        match t with
        | TYPE_Packed_struct fields' =>
            match flag with
            | soft => true
            | hard =>  normalized_typ_eq t_from t || fold_left (fun acc x => acc || x) (map (fun y => contains_typ y t flag) fields) false
            end
        | _ => fold_left (fun acc x => acc || contains_typ x t flag) fields false
        end
    | TYPE_Function ret_t args vararg =>
        match t with
        | TYPE_Function ret_t args vararg =>
            match flag with
            | soft => true
            | hard => normalized_typ_eq t_from t
            end
        | _ => false
        end
    | _ => false
    end.

  (* TODO: remove this *)
  (* Definition filter_function_pointers (typ_ctx : type_context) (ctx : var_context) : var_context := *)
  (*   filter (fun '(_, t) => is_function_pointer typ_ctx t) ctx. *)

  (* Can't use choose for these functions because it gets extracted to
     ocaml's Random.State.int function which has small bounds. *)

  Definition gen_bitZ : G Z :=
    b <- (arbitrary : G bool);;
    if b then ret 1 else ret 0.

  Fixpoint gen_unsigned_bitwidth_h (acc : Z) (bitwidth : positive) {struct bitwidth} : G Z :=
    if Pos.eqb bitwidth 1
    then gen_bitZ
    else
      bit <- gen_bitZ;;
      gen_unsigned_bitwidth_h (2 * acc + bit)%Z (bitwidth-1).

  Definition gen_unsigned_bitwidth (bitwidth : positive) : G Z :=
    gen_unsigned_bitwidth_h 0 bitwidth.

  Definition gen_signed_bitwidth (bitwidth : positive) : G Z :=
    let zbitwidth := Zpos bitwidth in
    let zhalf := zbitwidth - 1 in

    z <- (arbitrary : G Z);;
    negative <- (arbitrary : G bool);;
    if negative : bool
    then
      ret (-((Z.modulo z (2^zhalf)) + 1))
    else
      ret (Z.modulo z (2^zhalf)).

  Definition gen_gt_zero (bitwidth : option positive) : G Z
    := match bitwidth with
       | None =>
           (* Unbounded *)
           n <- gen_unsigned_bitwidth 64;;
           ret (1 + Z.modulo n (2^64 - 1))
       | Some bitwidth =>
           n <- gen_unsigned_bitwidth bitwidth;;
           ret (1 + Z.modulo n (2^(Zpos bitwidth) - 1))
       end.

  Definition gen_non_zero (bitwidth : option positive) : G Z
    := match bitwidth with
       | None =>
           (* Unbounded *)
           x <- gen_gt_zero None;;
           elems_ x [x; -x]
       | Some bitwidth =>
           let zbitwidth := Zpos bitwidth in
           let half := (bitwidth - 1)%positive in
           let zhalf := zbitwidth - 1 in
           if Z.eqb zhalf 0
           then ret (-1)
           else
             negative <- (arbitrary : G bool);;
             if (negative : bool)
             then
               n <- gen_unsigned_bitwidth half;;
               ret (-(1 + Z.modulo n (2^zhalf)))
             else
               n <- gen_unsigned_bitwidth half;;
               ret (1 + Z.modulo n (2^zhalf - 1))
       end.

  (* TODO: make this more complex using metadata *)
  Definition gen_non_zero_exp_size (sz : nat) (t : typ) : GenLLVM (exp typ)
    := match t with
       | TYPE_I n => ret EXP_Integer <*> lift (gen_non_zero (Some n))
       | TYPE_IPTR => ret EXP_Integer <*> lift (gen_non_zero None)
       | TYPE_Float => ret EXP_Float <*> lift fing32 (* TODO: is this actually non-zero...? *)
       | TYPE_Double => ret EXP_Double <*> lift fing64 (*TODO : Fix generator for double*)
       | _ => failGen "gen_non_zero_exp_size"
       end.

  Definition gen_gt_zero_exp_size (sz : nat) (t : typ) : GenLLVM (exp typ)
    := match t with
       | TYPE_I n => ret EXP_Integer <*> lift (gen_gt_zero (Some n))
       | TYPE_IPTR => ret EXP_Integer <*> lift (gen_gt_zero None)
       | TYPE_Float => failGen "gen_gt_zero_exp_size TYPE_Float"
       | TYPE_Double => failGen "gen_gt_zero_exp_size TYPE_Double"(*ret EXP_Double <*> lift fing64*) (*TODO : Fix generator for double*)
       | _ => failGen "gen_gt_zero_exp_size"
       end.

  Variant exp_source :=
    | FULL_CTX
    | GLOBAL_CTX.

  (* Generate an entity to a variable *)
  Definition gen_var_ent {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a)) (filter : GenQuery b) : GenLLVM (option Ent)
    := focused_all <- use focus;;
       (* [obs-freeze D1-hard] mode 2: exclude frozen-hit carriers (head-exempt)
          from the FULL candidate pool, ahead of ALL branches below (tainted
          subset, b=0/None fallbacks, bias_w=0 path). mode 0/1: pool untouched
          (soft demotes from the tainted-preferred tier only — below). *)
       focused <- (if Nat.eqb route_a_obs_freeze 2
                   then argmap_f <- use (metadata .@ arg_set');;
                        fz <- freeze_get;;
                        ret (freeze_filter_pool argmap_f fz focused_all)
                   else ret focused_all);;
       (* [param-obs-ban D1] hard-exclude param-tainted carriers WHEN inside an
          observation-feeding pick context (fz_pob_on true — set only around the
          S1 cond-br condition and S2 loop_init operands). Own gate, own key
          (fz_param); at knob 0 this is `ret focused` (no state read, no
          randomness) => stream-identical. *)
       focused <- (if param_ban_on
                   then fz <- freeze_get;;
                        if fz_pob_on fz
                        then argmap_p <- use (metadata .@ arg_set');;
                             ret (pob_filter_pool argmap_p (fz_param fz) focused)
                        else ret focused
                   else ret focused);;
       (* [route-A bias] soft-prefer tainted (arg-derived) candidates. See ROUTE_A_IMPL §3-bias.
          Build the tainted subset (arg_set != 0) of the candidates, pick from it, and keep
          that pick with prob w/(w+1); otherwise fall back to the original unbiased pick (so
          untainted values stay reachable). w = 0 => original selection (bias off). The bias is
          inert where no candidate is tainted (tainted subset empty -> unbiased), so it only
          affects value-operand selection, not type/global lookups. *)
       oe <- (if Nat.eqb route_a_bias_w 0
              then gen_IntMapRaw_ent_filter focused filter
              else
                argmap <- use (metadata .@ arg_set');;
                (* [obs-freeze D1-soft] mode 1: demote frozen-hit carriers out of
                   the tainted-preferred tier only (fallback picks untouched). *)
                ofz <- (if Nat.eqb route_a_obs_freeze 1
                        then fz <- freeze_get;; ret (Some fz)
                        else ret (None : option FreezeState));;
                let tainted :=
                  IM.Raw.fold
                    (fun (k : Z) v acc =>
                       match IM.Raw.find k argmap with
                       | Some m =>
                           if N.eqb m 0%N then acc
                           else match ofz with
                                | Some fz =>
                                    if freeze_hit_b (fz_bits fz) (fz_heads fz) k m
                                    then acc
                                    else IM.Raw.add k v acc
                                | None => IM.Raw.add k v acc
                                end
                       | None => acc
                       end) focused (IM.Raw.empty _) in
                oe_t <- gen_IntMapRaw_ent_filter tainted filter;;
                match oe_t with
                | Some _ =>
                    b <- lift (choose (0%nat, route_a_bias_w));;
                    if Nat.eqb b 0%nat
                    then gen_IntMapRaw_ent_filter focused filter
                    else ret oe_t
                | None => gen_IntMapRaw_ent_filter focused filter
                end);;
       (* [route-A propagation] the picked value becomes an operand -> OR its mask into the
          side-channel accumulator. See ROUTE_A_IMPL §2.
          [route-A chain-vector] also remember WHICH entity was picked (cur_ent), for
          generators that need the operand's identity (vector chaining). Pure state ops,
          no randomness consumed. *)
       (match oe with
        | Some e => cur_mask_accum (unEnt e);;
                    cur_ent_set (unEnt e);;
                    (* [obs-freeze D2 transfer] per-operand-pick head-consumption
                       detection (gated; no-op at knobs 0). *)
                    freeze_consume_pick (unEnt e)
        | None => ret tt
        end);;
       ret oe.

  Definition gen_var_ident {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a)) (filter : GenQuery b) : GenLLVM (option ident)
    := oe <- gen_var_ent focus filter;;
       match oe with
       | None => ret None
       | Some e => use (gen_context' .@ entl e .@ name')
       end.

  (* Generate an entity for a variable of a given typ *)
  (* t should already be normalized *)
  Definition gen_var_of_typ_ent {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a))
    (filter : GenQuery b)
    (t : typ) : GenLLVM (option Ent)
    := gen_var_ent focus
         (vt <- queryl variable_type';;
          if (normalized_typ_eq t vt)
          then filter
          else mzero).

  (* Generate an ident for a variable of a given typ *)
  (* t should already be normalized *)
  Definition gen_var_of_typ_ident {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a))
    (filter : GenQuery b)
    (t : typ) : GenLLVM (option ident)
    := gen_var_ident focus
         (vt <- queryl variable_type';;
          if (normalized_typ_eq t vt)
          then filter
          else mzero).

  Fixpoint gen_exp_size' (gen_global_of_typ : typ -> GenLLVM (option ident)) (gen_ident_of_typ : typ -> GenLLVM (option ident)) (sz : nat) (t : typ) {struct t} : GenLLVM (exp typ) :=
    match sz with
    | 0%nat =>
        (* annotate_debug ("++++++++GenExpOT: " ++ show t);; *)
        i <- gen_ident_of_typ t;;
        let gen_idents : list (nat * GenLLVM (exp typ)) :=
          match i with
          | None => []
          | Some ident => [(320%nat, fmap (fun i => EXP_Ident i) (@ret GenLLVM _ _ ident))]
          end in
        let fix gen_size_0 (t: typ) :=
          match t with
          | TYPE_I n                  =>
              z <- lift (gen_unsigned_bitwidth n);;
              ret (EXP_Integer z)
          (* lift (x <- (arbitrary : G nat);; ret (Z.of_nat x)) *)
          (*  (* TODO: should the integer be forced to be in bounds? *) *)
          | TYPE_IPTR => ret EXP_Integer <*> lift (arbitrary : G Z)
          | TYPE_Pointer _       => failGen "gen_exp_size TYPE_Pointer"
          (* Only pointer type expressions might be conversions? Maybe GEP? *)
          | TYPE_Void                 => failGen "gen_exp_size TYPE_Void" (* There should be no expressions of type void *)
          | TYPE_Function ret args _   => failGen "gen_exp_size TYPE_Function"(* No expressions of function type *)
          | TYPE_Opaque               => failGen "gen_exp_size TYPE_Opaque" (* TODO: not sure what these should be... *)

          (* Generate literals for aggregate structures *)
          | TYPE_Array n t =>
              es <- (vectorOf_LLVM (N.to_nat n) (gen_exp_size' gen_global_of_typ gen_global_of_typ 0%nat t));;
              ret (EXP_Array (TYPE_Array n t) (map (fun e => (t, e)) es))
          | TYPE_Vector n t =>
              es <- (vectorOf_LLVM (N.to_nat n) (gen_exp_size' gen_global_of_typ gen_global_of_typ 0%nat t));;
              ret (EXP_Vector (TYPE_Vector n t) (map (fun e => (t, e)) es))
          | TYPE_Struct fields =>
              (* Should we divide size evenly amongst components of struct? *)
              tes <- map_monad (fun t => e <- (gen_exp_size' gen_global_of_typ gen_global_of_typ 0%nat t);; ret (t, e)) fields;;
              ret (EXP_Struct tes)
          | TYPE_Packed_struct fields =>
              (* Should we divide size evenly amongst components of struct? *)
              tes <- map_monad (fun t => e <- (gen_exp_size' gen_global_of_typ gen_global_of_typ 0%nat t);; ret (t, e)) fields;;
              ret (EXP_Packed_struct tes)

          | TYPE_Identified id        =>
              t <- def_option_GenLLVM (failGen "gen_exp_size TYPE_Identified")
                    (genFind
                       (use (gen_context' .@ type_alias'))
                       (n <- queryl name';;
                        if Ident.eq_dec id n
                        then queryl type_alias'
                        else mzero));;
              gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t
          (* Not generating these types for now *)
          | TYPE_Half                 => failGen "gen_exp_size TYPE_Half"
          | TYPE_Float                => ret EXP_Float <*> lift fing32(* referred to genarators in flocq-quickchick*)
          | TYPE_Double               => ret EXP_Double <*> lift fing64 (* TODO: Fix generator for double*)
          | TYPE_X86_fp80             => failGen "gen_exp_size TYPE_X86_fp80"
          | TYPE_Fp128                => failGen "gen_exp_size TYPE_Fp128"
          | TYPE_Ppc_fp128            => failGen "gen_exp_size TYPE_Ppc_fp128"
          | TYPE_Metadata             => failGen "gen_exp_size TYPE_Metadata"
          | TYPE_X86_mmx              => failGen "gen_exp_size TYPE_X86_mmx"
          end in
        (* Hack to avoid failing way too much *)
        match t with
        | TYPE_Pointer (Some t) =>
            if (seq.nilp gen_idents)
            then
              (* Generate Global Pointer retroactively *)
              (* 0. Flip the global context if we are at the first level *)
              (* 1. Generate a global id, *)
              (* 2. recursively define the receiving types *)
              annotate "retroactive global pointer"
                (in_exp <- gen_exp_size' gen_global_of_typ gen_global_of_typ 0%nat t;;
                 name <- new_global_id;;
                 add_to_global_memo (mk_global name t false (Some in_exp) false []);;
                 e <- add_to_global_ctx (ID_Global name, TYPE_Pointer (Some t));;
                 (gen_context' .@ entl e .@ deterministic') .= false;;
                 (* [route-A arg-deref r7b] (PLAN §4.3c) expose the retro-minted pointer's
                    ENTITY via cur_ent, exactly like an ordinary gen_var_ent pick — so the
                    call-arg capture (optr <- cur_ent_take in gen_call_arg) sees it and BOTH
                    cell_mask_record (M2's store bookkeeping) and arg_deref_reflect act on
                    it. Pre-r7b, optr stayed None on this DOMINANT path (Step-1 m4: ~100%
                    of main's ptr args are retro-minted), nullifying §4.3c exactly where
                    (c)'s M2 creates the reachable-memory taint. GATED on route_a_ptrarg_w
                    (the (c) cluster this serves): the ALWAYS-ON variant measurably shifted
                    the ptrarg=0 stream (exp_step2e proghash_r7b_offpath.txt, cascade from
                    program 6) — gen_store's always-on capture then records tainted cells
                    through store-window retro-mints, and gen_mem_chain_ptr READS cell
                    masks at the COMMITTED default route_a_mem_w=3 — so §2.1 knob
                    discipline demands the gate. At ptrarg<>0 the set fires at EVERY retro
                    mint (call args AND the store/gep/load pick windows): the extra
                    store/gep shadow bookkeeping on retro pointers is a semantically
                    correct improvement, fine for the knob-on stream (no baseline).
                    State-only, no randomness; stale values die at gen_instr's boundary
                    reset or the captures' clear-before-pick takes; non-call-arg capture
                    consumers read value-identical data for a FRESH retro entity
                    (vec_lanes_find = [], arg-mask/cell-mask = 0). *)
                 (if Nat.eqb route_a_ptrarg_w 0
                  then ret tt
                  else cur_ent_set (unEnt e));;
                 ret (EXP_Ident (ID_Global name)))
            else freq_LLVM (gen_idents)
        (* TODO: handle opaque ptrs *)

        (* freq_LLVM ((* (1%nat, ret EXP_Undef) :: *) gen_idents) *)
        (* TODO: Add some retroactive global generation *)
        | _ => freq_LLVM
                ((10%nat, gen_size_0 t) :: (* (1%nat, ret EXP_Zero_initializer) :: *) gen_idents)
        end
    | (S sz') =>
        let gens :=
          match t with
          | TYPE_I isz =>
              if Pos.eqb isz 1
              then
                ([ gen_ibinop_exp gen_global_of_typ gen_ident_of_typ isz
                  ; τ <- gen_int_typ;;
                    gen_icmp_exp_typ gen_global_of_typ gen_ident_of_typ τ
                ] ++
                  if enable_float_generation
                  then
                    [τ <- gen_float_typ;;
                     gen_fcmp_exp_typ gen_global_of_typ gen_ident_of_typ τ
                    ]
                  else [])%list
              else
                [ gen_ibinop_exp gen_global_of_typ gen_ident_of_typ isz ]
          | TYPE_IPTR =>
              [gen_ibinop_exp_typ gen_global_of_typ gen_ident_of_typ TYPE_IPTR]
          | TYPE_Pointer _         => [] (* GEP? *)

          (* TODO: currently only generate literals for aggregate structures with size 0 exps *)
          | TYPE_Array n t => []
          | TYPE_Vector n t => []
          | TYPE_Struct fields => []
          | TYPE_Packed_struct fields => []

          | TYPE_Void              => [failGen "gen_exp_size TYPE_VOID list"] (* No void type expressions *)
          | TYPE_Function ret args _ => [failGen "gen_exp_size TYPE_Function list"] (* These shouldn't exist, I think *)
          | TYPE_Opaque            => [failGen "gen_exp_size TYPE_Opaque list"] (* TODO: not sure what these should be... *)
          | TYPE_Half              => [failGen "gen_exp_size TYPE_Half list" ]
          | TYPE_Float             => [gen_fbinop_exp gen_global_of_typ gen_ident_of_typ TYPE_Float]
          | TYPE_Double            => [gen_fbinop_exp gen_global_of_typ gen_ident_of_typ TYPE_Double]
          | TYPE_X86_fp80          => [failGen "gen_exp_size TYPE_X86_fp80 list"]
          | TYPE_Fp128             => [failGen "gen_exp_size TYPE_Fp128 list"]
          | TYPE_Ppc_fp128         => [failGen "gen_exp_size TYPE_Ppc_fp128 list"]
          | TYPE_Metadata          => [failGen "gen_exp_size TYPE_Metadata list"]
          | TYPE_X86_mmx           => [failGen "gen_exp_size TYPE_X86_mmx list"]
          | TYPE_Identified id     =>
              [ t <- def_option_GenLLVM (failGen "gen_exp_size TYPE_Identified")
                      (genFind
                         (use (gen_context' .@ type_alias'))
                         (n <- queryl name';;
                          if Ident.eq_dec id n
                          then queryl type_alias'
                          else mzero));;
                gen_exp_size' gen_global_of_typ gen_ident_of_typ sz t
              ]
          end
        in
        (* short-circuit to size 0 *)
        oneOf_LLVM (gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t :: gens)
    end
  with
  (* TODO: Make sure we don't divide by 0 *)
  gen_ibinop_exp_typ (gen_global_of_typ : typ -> GenLLVM (option ident)) (gen_ident_of_typ : typ -> GenLLVM (option ident)) (t : typ) {struct t} : GenLLVM (exp typ)
  := ibinop <- lift gen_ibinop;;

    if Handlers.LLVMEvents.DV.iop_is_div ibinop && Handlers.LLVMEvents.DV.iop_is_signed ibinop
    then
      ret (OP_IBinop ibinop) <*> ret t <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t <*> gen_non_zero_exp_size 0%nat t
    else
      if Handlers.LLVMEvents.DV.iop_is_div ibinop
      then
        ret (OP_IBinop ibinop) <*> ret t <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t <*> gen_gt_zero_exp_size 0%nat t
      else
        exp_value <- gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t;;
        if Handlers.LLVMEvents.DV.iop_is_shift ibinop
        then
          let max_shift_size :=
            match t with
            | TYPE_I i => BinIntDef.Z.of_N (Npos i - 1)%N
            | _ => 0%Z
            end in
          x <- lift (choose (0%Z, max_shift_size));;
          let exp_value2 : exp typ := EXP_Integer x in
          ret (OP_IBinop ibinop t exp_value exp_value2)
        else ret (OP_IBinop ibinop t exp_value) <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t
  with
  gen_ibinop_exp (gen_global_of_typ : typ -> GenLLVM (option ident)) (gen_ident_of_typ : typ -> GenLLVM (option ident)) (isz : positive) {struct isz} : GenLLVM (exp typ)
  :=
    let t := TYPE_I isz in
    gen_ibinop_exp_typ gen_global_of_typ gen_ident_of_typ t
  with
  gen_fbinop_exp (gen_global_of_typ : typ -> GenLLVM (option ident)) (gen_ident_of_typ : typ -> GenLLVM (option ident)) (ty: typ) {struct ty} : GenLLVM (exp typ)
  :=
    match ty with
    | TYPE_Float => fbinop <- lift gen_fbinop;;
                   if (Handlers.LLVMEvents.DV.fop_is_div fbinop)
                   then ret (OP_FBinop fbinop nil) <*> ret ty <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat ty <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat ty
                   else ret (OP_FBinop fbinop nil) <*> ret ty <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat ty <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat ty
    | TYPE_Double => fbinop <- lift gen_fbinop;;
                    if (Handlers.LLVMEvents.DV.fop_is_div fbinop)
                    then ret (OP_FBinop fbinop nil) <*> ret ty <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat ty <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat ty
                    else ret (OP_FBinop fbinop nil) <*> ret ty <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat ty <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat ty
    | _ => failGen "gen_fbinop_exp"
    end
  with
  gen_icmp_exp_typ (gen_global_of_typ : typ -> GenLLVM (option ident)) (gen_ident_of_typ : typ -> GenLLVM (option ident)) (t : typ) {struct t} : GenLLVM (exp typ)
  := cmp <- lift gen_icmp;;
     (* [Phase 1a] icmp v2: const(non-zero) -> SSA-allowing gen_exp_size' so v2 can
        carry arg taint (icmp never traps; the non-zero constraint was spurious,
        copied from the div generator). Litmus for the "i32 pool already tainted" claim. *)
     ret (OP_ICmp cmp) <*> ret t <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t
  with
  gen_fcmp_exp_typ (gen_global_of_typ : typ -> GenLLVM (option ident)) (gen_ident_of_typ : typ -> GenLLVM (option ident)) (t : typ) {struct t} : GenLLVM (exp typ)
  := cmp <- lift gen_fcmp;;
     ret (OP_FCmp cmp) <*> ret t <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t <*> gen_non_zero_exp_size 0%nat t.

  Definition gen_icmp_exp (gen_global_of_typ : typ -> GenLLVM (option ident)) (gen_ident_of_typ : typ -> GenLLVM (option ident)) : GenLLVM (exp typ)
    := τ <- gen_int_typ;;
       gen_icmp_exp_typ gen_global_of_typ gen_ident_of_typ τ.

  Definition gen_fcmp_exp (gen_global_of_typ : typ -> GenLLVM (option ident)) (gen_ident_of_typ : typ -> GenLLVM (option ident)) : GenLLVM (exp typ)
    := τ <- gen_float_typ;;
       gen_fcmp_exp_typ gen_global_of_typ gen_ident_of_typ τ.

  Definition gen_deterministic_global_ident :=
    gen_var_of_typ_ident (gen_context' .@ is_global') (withl is_deterministic').

  Definition gen_global_ident :=
    gen_var_of_typ_ident (gen_context' .@ is_global') (ret tt).

  Definition gen_deterministic_ident :=
    gen_var_of_typ_ident (gen_context' .@ variable_type') (withl is_deterministic').

  Definition gen_ident :=
    gen_var_of_typ_ident (gen_context' .@ variable_type') (ret tt).

  Definition gen_exp_size :=
    gen_exp_size' gen_deterministic_global_ident.

  Definition gen_exp_possibly_non_deterministic_size :=
    gen_exp_size' gen_global_ident.

  Definition gen_exp (t : typ) : GenLLVM (exp typ)
    := annotate ("gen_exp: " ++ show t)
         (sized_LLVM (fun sz => gen_exp_size gen_deterministic_ident sz t)).

  Definition gen_exp_possibly_non_deterministic (t : typ) : GenLLVM (exp typ)
    := annotate ("gen_exp_possibly_non_deterministic: " ++ show t)
         (sized_LLVM (fun sz => gen_exp_possibly_non_deterministic_size gen_ident sz t)).

  Definition gen_exp_sz0 (t : typ) : GenLLVM (exp typ)
    := annotate "gen_exp_sz0" (resize_LLVM 0 (gen_exp t)).

  Definition gen_exp_possibly_non_deterministic_sz0 (t : typ) : GenLLVM (exp typ)
    := annotate "gen_exp_possibly_non_deterministic_sz0" (resize_LLVM 0 (gen_exp_possibly_non_deterministic t)).

  Definition gen_texp : GenLLVM (texp typ)
    := annotate "gen_texp"
         (t <- gen_typ;;
          e <- gen_exp t;;
          ret (t, e)).

  Definition gen_sized_texp : GenLLVM (texp typ)
    := annotate "gen_sized_texp"
         (t <- gen_sized_typ;;
          e <- gen_exp t;;
          ret (t, e)).

  Definition gen_op (t : typ) : GenLLVM (exp typ)
    := sized_LLVM
         (fun sz =>
            match t with
            | TYPE_I isz =>
                if Pos.eqb isz 1
                then
                  (* If I1 also allow ICmp and FCmp *)
                  oneOf_LLVM
                    [ gen_ibinop_exp gen_deterministic_global_ident gen_deterministic_ident isz
                      ; gen_icmp_exp gen_deterministic_global_ident gen_deterministic_ident
                      ; gen_fcmp_exp gen_deterministic_global_ident gen_deterministic_ident
                    ]
                else
                  gen_ibinop_exp gen_deterministic_global_ident gen_deterministic_ident isz
            | TYPE_Float => gen_fbinop_exp gen_deterministic_global_ident gen_deterministic_ident TYPE_Float
            | TYPE_Double => gen_fbinop_exp gen_deterministic_global_ident gen_deterministic_ident TYPE_Double
            | _ => failGen "gen_op"
            end).

  Definition gen_int_texp : GenLLVM (texp typ)
    := t <- gen_int_typ;;
       e <- gen_exp t;;
       ret (t, e).

End ExpGenerators.

Require Import Semantics.LLVMEvents.
Require Import Semantics.InterpretationStack.
Require Import Handlers.Handlers.
From ITree Require Import
  ITree
  Interp.Recursion
  Events.Exception.

Import TopLevel64BitIntptr.
Import DV.
Import MemoryModelImplementation.LLVMParams64BitIntptr.Events.


Section InstrGenerators.

  (* Generator GEP part *)
  (* Get index paths from array or vector*)
  Definition get_index_paths_from_AoV (sz: N) (t: typ) (pre_path: DList Z) (sub_paths: DList (typ * DList Z)) : DList (typ * DList Z) :=
    N.recursion DList_empty
      (fun ix acc =>
         let ix_sub_paths := DList_map (fun '(t, sub_path) => (t, DList_append pre_path (DList_cons (Z.of_N ix) sub_path))) sub_paths in
         DList_append acc ix_sub_paths)
      sz.

  (* Can work after extracting the pointer inside*)
  Fixpoint get_index_paths_aux (t_from : typ) (pre_path : DList Z) {struct t_from}: DList (typ * DList (Z)) :=
    match t_from with
    | TYPE_Array sz t =>
        let sub_paths := get_index_paths_aux t DList_empty in (* Get index path from the first element*)
        DList_cons (t_from, pre_path) (get_index_paths_from_AoV sz t pre_path sub_paths)
    | TYPE_Struct fields
    | TYPE_Packed_struct fields =>
        DList_cons (t_from, pre_path) (get_index_paths_from_struct pre_path fields)
    | _ => DList_singleton (t_from, pre_path)
    end with
  get_index_paths_from_struct (pre_path: DList Z) (fields: list typ) {struct fields}: DList (typ * DList Z) :=
    snd (fold_left
           (fun '(ix, paths) (fld_typ : typ) =>
              (ix + 1,
                (DList_append (get_index_paths_aux fld_typ (DList_append pre_path (DList_singleton ix)))
                   paths)))
           fields (0%Z, DList_empty : DList (typ * DList Z))).

  Definition DList_paths_to_list_paths (paths : DList (typ * DList (Z))) : list (typ * list (Z))
    := map (fun '(x, paths) => (x, DList_to_list paths)) (DList_to_list paths).

  Definition get_index_paths_ptr (t_from: typ) : list (typ * list (Z)) :=
    DList_paths_to_list_paths (get_index_paths_aux t_from (DList_singleton 0%Z)).

  (* Index path without getting into vector *)
  Fixpoint get_index_paths_agg_aux (t_from : typ) (pre_path : DList Z) {struct t_from}: DList (typ * DList (Z)) :=
    match t_from with
    | TYPE_Array sz t =>
        let sub_paths := get_index_paths_agg_aux t DList_empty in (* Get index path from the first element*)
        DList_cons (t_from, pre_path) (get_index_paths_from_AoV sz t pre_path sub_paths)
    | TYPE_Struct fields
    | TYPE_Packed_struct fields =>
        DList_cons (t_from, pre_path) (get_index_paths_agg_from_struct pre_path fields)
    | _ => DList_singleton (t_from, pre_path)
    end with
  get_index_paths_agg_from_struct (pre_path: DList Z) (fields: list typ) {struct fields}: DList (typ * DList Z) :=
    snd (fold_left
           (fun '(ix, paths) (fld_typ : typ) =>
              (ix + 1,
                (DList_append (get_index_paths_agg_aux fld_typ (DList_append pre_path (DList_singleton ix)))
                   paths)))
           fields (0%Z, DList_empty : DList (typ * DList Z))).

  (* The method is mainly used by extractvalue and insertvalue,
     which requires at least one index for getting inside the aggregate type.
     There is a possibility for us to get nil path. The filter below will get rid of that possibility.
     Given that the nilpath will definitely be at the beginning of a list of options, we can essentially get the tail. *)
  Definition get_index_paths_agg (t_from: typ) : list (typ * list (Z)) :=
    tl (DList_paths_to_list_paths (get_index_paths_agg_aux t_from DList_empty)).

  (* Index path without getting into vector *)
  (* t_from should already be normalized *)
  Fixpoint get_index_paths_insertvalue_aux (t_from : typ) (pre_path : DList Z) {struct t_from}: GenLLVM (bool * DList (typ * DList (Z))) :=
    match t_from with
    | TYPE_Array sz t =>
        '(has_subpaths, sub_paths) <- get_index_paths_insertvalue_aux t DList_empty;; (* Get index path from the first element*)
        if has_subpaths
        then ret (true, DList_cons (t_from, pre_path) (get_index_paths_from_AoV sz t pre_path sub_paths))
        else ret (false, DList_empty)
    | TYPE_Struct fields
    | TYPE_Packed_struct fields =>
        '(has_reach, reaches) <- get_index_paths_insertvalue_from_struct pre_path fields;;
        if has_reach
        then ret (true, DList_cons (t_from, pre_path) reaches)
        else ret (false, DList_empty)
    | TYPE_Pointer t =>
        in_ctx <- fmap is_some (genFind
                                 (use (gen_context' .@ variable_type'))
                                 (nt <- queryl normalized_type';;
                                  if (normalized_typ_eq t_from nt)
                                  then ret tt
                                  else mzero));;
        if in_ctx
        then ret (true, DList_singleton (t_from, pre_path))
        else ret (false, DList_empty)
    | TYPE_Vector _ t =>
        '(has_subpaths, sub_paths) <- get_index_paths_insertvalue_aux t DList_empty;; (* Get index path from the first element*)
        if has_subpaths
        then ret (true, DList_singleton (t_from, pre_path))
        else ret (false, DList_empty)
    | _ => ret (true, DList_singleton (t_from, pre_path))
    end with
  get_index_paths_insertvalue_from_struct (pre_path: DList Z) (fields: list typ) {struct fields}: GenLLVM (bool * DList (typ * DList Z)) :=
    fmap snd (fold_left
           (fun acc (fld_typ : typ) =>
              '(ix, (b, paths)) <- acc;;
              '(has_reach, reach) <- get_index_paths_insertvalue_aux fld_typ (DList_append pre_path (DList_singleton ix));;
              ret (ix + 1, (orb has_reach b, DList_append reach paths)))
           fields (ret (0%Z, (false, DList_empty : DList (typ * DList Z))))).

  Definition get_index_paths_insertvalue
    (t_from : typ)
    : GenLLVM (list (typ * list (Z)))
    :=
    paths <- get_index_paths_insertvalue_aux t_from DList_empty;;
    ret (tl (DList_paths_to_list_paths (snd paths))).

  Fixpoint has_paths_insertvalue_aux (t_from : typ) {struct t_from}: GenQuery bool :=
    match t_from with
    | TYPE_Array _ t
    | TYPE_Vector _ t => has_paths_insertvalue_aux t
    | TYPE_Struct fields
    | TYPE_Packed_struct fields =>
        fold_left (fun acc x =>
                     cnd_rest <- acc;;
                     cnd <- has_paths_insertvalue_aux x;;
                     ret (orb cnd_rest cnd)) fields (ret false)
    | TYPE_Pointer _ =>
        (* Check for the pointer type in the context *)
        nt <- queryl normalized_type';;
        ret (normalized_typ_eq nt t_from)
    | _ => ret true
    end.

  Definition gen_gep (tptr : typ) : GenLLVM (instr_id * instr typ) :=
    let get_typ_in_ptr (tptr : typ) :=
      match tptr with
      | TYPE_Pointer (Some t) => ret t
      (* TODO: What about opaque pointers? *)
      | _ => failGen "gen_gep"
      end in
    annotate "gen_gep"
      (t_in_ptr <- get_typ_in_ptr tptr;;
       (* [route-A chain-memory] fresh attribution for the base-pointer pick. *)
       _ <- cur_ent_take;;
       eptr <- gen_exp_sz0 tptr;;
       obase <- cur_ent_take;;
       let paths_in_ptr := get_index_paths_ptr t_in_ptr in (* Inner paths: Paths after removing the outer pointer *)
       '(ret_t, path) <- elems_LLVM paths_in_ptr;; (* Select one path from the paths *)
       let path_for_gep := map (fun x => (TYPE_I 32, EXP_Integer (x))) path in (* Turning the path to integer *)
       '(id, e) <- genInstrIdEnt (TYPE_Pointer (Some ret_t));;
       (* Default to non-deterministic for now. Need a way to look up whether the base pointer was deterministic *)
       (gen_context' .@ entl e .@ deterministic') .= false;;
       (* [route-A chain-memory] the gep result addresses the SAME memory object as
          its base (object granularity — offsets ignored) -> inherit the cell. *)
       (match obase with
        | None => ret tt
        | Some bp =>
            oc <- points_to_find bp;;
            match oc with
            | None => ret tt
            | Some c => points_to_set (unEnt e) c
            end
        end);;
       ret (id, INSTR_Op (OP_GetElementPtr t_in_ptr (TYPE_Pointer (Some t_in_ptr), eptr) path_for_gep))).

  Definition gen_extractvalue (tagg : typ): GenLLVM (instr_id * instr typ) :=
    annotate ("gen_extractvalue: " ++ show tagg)
      (eagg <- gen_exp_sz0 tagg;;
       ntagg <- normalize_type_GenLLVM tagg;;
       let paths_in_agg := get_index_paths_agg ntagg in
       '(t, path_for_extractvalue) <- elems_LLVM paths_in_agg;;
       id <- genInstrId t;;
       ret (id, INSTR_Op (OP_ExtractValue (tagg, eagg) path_for_extractvalue))).

  Definition gen_insertvalue (tagg: typ): GenLLVM (instr_id * instr typ) :=
    annotate "gen_insertvalue"
      (eagg <- gen_exp_sz0 tagg;;
       ctx <- get_ctx;;
       ntagg <- normalize_type_GenLLVM tagg;;
       paths_in_agg <- get_index_paths_insertvalue ntagg;;
       '(tsub, path_for_insertvalue) <- elems_LLVM paths_in_agg;;
       (* [Phase 1 channel-open] Was [hide_ctx (gen_exp_sz0 tsub)]: hide_ctx hid ALL locals,
          so the inserted element could only be a global/constant -> the aggregate could NEVER
          carry arg taint (agg-struct/array, extractval, insertval-elt/vec mutants all survived,
          "arg-unreachable"). Drop hide_ctx so an in-scope (arg-tainted) i32 local can be
          inserted; gen_exp_sz0 still falls back to a literal when no local of type tsub is in
          scope, so the old "type we want may not be in context" concern is handled. The i32
          pool is already dense-tainted, so this taints whatever aggregate type the generator
          builds (type-adaptive). No UB (insertvalue is total). *)
       esub <- gen_exp_sz0 tsub;;
       (* Generate all of the type*)
       id <- genInstrId tagg;;
       ret (id, INSTR_Op (OP_InsertValue (tagg, eagg) (tsub, esub) path_for_insertvalue))).

  (* [route-A chain-vector] extractelement's lane pick, chain-aware: if the vector we
     just picked (ovec, learned via the cur_ent side-channel) has recorded tainted
     lanes, read ONE OF THOSE lanes with probability w/(w+1) — completing the real
     dataflow [insertelement lane = extractelement lane] that a kill needs (a uniform
     pick matches only ~1/sz of the time). Any lane stays reachable via the uniform
     fallback. w = 0 or no record => exactly the original single [choose] (identical
     randomness consumed => stream-preserving). See ROUTE_A_IMPL §4-chain-vector. *)
  Definition gen_chain_lane (ovec : option Z) (sz : N) : GenLLVM Z :=
    let uniform := lift_GenLLVM (choose (0, Z.of_N sz - 1)%Z) in
    if Nat.eqb route_a_chain_w 0
    then uniform
    else
      match ovec with
      | None => uniform
      | Some ve =>
          lanes0 <- vec_lanes_find ve;;
          (* [obs-freeze D1] the recorded-lane read is a tainted-preferred tier
             (P0.c row 5): drop lanes whose mask is frozen-hit (carrier entity =
             the vector [ve]; head-exempt). Any mode <> 0; empty -> uniform. *)
          lanes <- (if Nat.eqb route_a_obs_freeze 0
                    then ret lanes0
                    else fz <- freeze_get;;
                         ret (List.filter
                                (fun (lm : Z * N) =>
                                   negb (freeze_hit_b (fz_bits fz) (fz_heads fz) ve (snd lm)))
                                lanes0));;
          match lanes with
          | [] => uniform
          | _ :: _ =>
              b <- lift_GenLLVM (choose (0%nat, route_a_chain_w));;
              if Nat.eqb b 0%nat
              then uniform
              else '(l, _) <- elems_LLVM lanes;; ret l
          end
      end.

  (* ExtractElement *)
  Definition gen_extractelement (tvec : typ): GenLLVM (instr_id * instr typ) :=
    annotate "gen_extractelement"
      ((* [route-A chain-vector] clear the side-channel so the vector pick below is
          attributed fresh (a stale entity from an earlier pick must not leak in). *)
       _ <- cur_ent_take;;
       evec <- gen_exp_sz0 tvec;;
       ovec <- cur_ent_take;;   (* entity of the picked vector (None for a literal) *)
       let get_size_ty (vType: typ) :=
         match tvec with
         | TYPE_Vector sz ty => (sz, ty)
         | _ => (0%N, TYPE_Void)
         end in
       let '(sz, t_in_vec) := get_size_ty tvec in
       index_for_extractelement <- gen_chain_lane ovec sz;;
       id <- genInstrId t_in_vec;;
       ret (id, INSTR_Op (OP_ExtractElement (tvec, evec) (TYPE_I 32, EXP_Integer index_for_extractelement)))).

  Definition gen_insertelement (tvec : typ) : GenLLVM (instr_id * instr typ) :=
    annotate "gen_insertelement"
      ((* [route-A chain-vector] see gen_extractelement; here we RECORD instead of read. *)
       _ <- cur_ent_take;;
       evec <- gen_exp_sz0 tvec;;
       ovec <- cur_ent_take;;   (* entity of the source vector (None for a literal) *)
       let get_size_ty (vType: typ) :=
         match tvec with
         | TYPE_Vector sz ty => (sz, ty)
         | _ => (0%N, TYPE_Void)
         end in
       let '(sz, t_in_vec) := get_size_ty tvec in
       value <- gen_exp_sz0 t_in_vec;;
       oelt <- cur_ent_take;;   (* entity of the inserted element (None for a literal) *)
       (* the element's OWN mask (exact for an ident pick; 0 for a literal) — the value
          this lane will really hold. NB: cur_mask (evec|value accumulated) is NOT used
          here; it keeps feeding arg_set[result] via add_to_local_ctx as before. *)
       eltm <- (match oelt with
                | Some z => arg_mask_lookup z
                | None => ret 0%N
                end);;
       index <- lift_GenLLVM (choose (0, Z.of_N (sz - 1)));;
       '(id, e) <- genInstrIdEnt tvec;;
       (* [route-A chain-vector] record: the new vector inherits the source's tainted
          lanes; lane [index] now holds the element (mask eltm). Consumed by
          gen_chain_lane. State-only, no randomness. *)
       vec_lanes_update (unEnt e) ovec index eltm;;
       ret (id, INSTR_Op (OP_InsertElement (tvec, evec) (t_in_vec, value) (TYPE_I 32, EXP_Integer index)))).

  Definition round_up_to_eight (n : N) : N :=
    if N.eqb 0 n
    then 0
    else (((n - 1) / 8) + 1) * 8.

  Fixpoint get_bit_size_from_typ (t : typ) : N :=
    match t with
    | TYPE_I sz => Npos sz
    | TYPE_IPTR => 64 (* TODO: probably kind of a lie... *)
    | TYPE_Pointer t => 64
    | TYPE_Void => 0
    | TYPE_Half => 16
    | TYPE_Float => 32
    | TYPE_Double => 64
    | TYPE_X86_fp80 => 80
    | TYPE_Fp128 => 128
    | TYPE_Ppc_fp128 => 128
    | TYPE_Metadata => 0
    | TYPE_X86_mmx => 64
    | TYPE_Array sz t => sz * (round_up_to_eight (get_bit_size_from_typ t))
    | TYPE_Function ret args vararg => 0
    | TYPE_Struct fields
    | TYPE_Packed_struct fields =>
        fold_right (fun x acc => (round_up_to_eight (get_bit_size_from_typ x) + acc)%N) 0%N fields
    | TYPE_Opaque => 0
    | TYPE_Vector sz t => sz * get_bit_size_from_typ t
    | TYPE_Identified id => 0
    end.

  Definition get_size_from_typ (t: typ) : N :=
    round_up_to_eight (get_bit_size_from_typ t) / 8.

  (* Assuming max_byte_sz for this function is greater than 0 *)
  Definition get_prim_typ_le_size (max_byte_sz: N) : list (GenLLVM typ) :=
    (if (1 <=? max_byte_sz)%N then [ret (TYPE_I 1); ret (TYPE_I 8)] else []) ++
      (if (4 <=? max_byte_sz)%N then [ret (TYPE_I 32); ret TYPE_Float] else []) ++
      (if (8 <=? max_byte_sz)%N then [ret (TYPE_I 64) (* ; ret TYPE_Double *)] else []).

  (* Version without problematic i1 type *)
  Definition get_prim_vector_typ_le_size (max_byte_sz: N) : list (GenLLVM typ) :=
    (if (1 <=? max_byte_sz)%N then [ret (TYPE_I 8)] else []) ++
      (if (4 <=? max_byte_sz)%N then [ret (TYPE_I 32); ret TYPE_Float] else []) ++
      (if (8 <=? max_byte_sz)%N then [ret (TYPE_I 64) (* ; ret TYPE_Double *)] else []).

  (* Main method, it will generate based on the max_byte_sz
  Currently we support, int (1,8,32,64), float, double
  pointer, vector, array, struct, packed struct
  Aggregate structures used the types above. *)
  Fixpoint gen_typ_le_size (max_byte_sz : N) : GenLLVM typ :=
    ctx <- get_ctx;;
    oneOf_LLVM
      ( (* Primitive types *)
        get_prim_typ_le_size max_byte_sz ++

          (* Vector type *)
          (if (max_byte_sz =? 0)%N then [] else
             [ sz' <- lift_GenLLVM (choose (1, BinIntDef.Z.of_N max_byte_sz ));;
               let sz' := BinIntDef.Z.to_N sz' in
               t <- oneOf_LLVM (get_prim_vector_typ_le_size (max_byte_sz / sz'));;
               ret (TYPE_Vector (sz') t)
          ]) ++

          (* Array type *)
          [ sz' <- lift_GenLLVM (choose (0, BinIntDef.Z.of_N max_byte_sz));;
            let sz' := BinIntDef.Z.to_N sz' in
            if (sz' =? 0)%N (* Catch 0 array*)
            then
              t <- oneOf_LLVM (get_prim_typ_le_size 64);; (* Only primitive type to enhance performance *)
              ret (TYPE_Array (sz') t)
            else
              t <- gen_typ_le_size (max_byte_sz / sz');;
              ret (TYPE_Array (sz') t)
          ] ++

          (* Struct type *)
          (* [fields <- gen_typ_from_size_struct max_byte_sz;;
       ret (TYPE_Struct fields)
      ] ++ *) (* Issue #260 *)

          (* Packed struct type *)
          [fields <- gen_typ_from_size_struct max_byte_sz;;
           ret (TYPE_Packed_struct fields)
      ])
  with gen_typ_from_size_struct (max_byte_sz : N) : GenLLVM (list typ) :=
         subtyp <- gen_typ_le_size max_byte_sz;;
         let sz' := (max_byte_sz - (get_size_from_typ subtyp))%N in
         if (sz' =? 0)%N (* If the remaining size available is 0, then it will shrink the test case to not have other subtyp appending at the end *)
         then
           ret [subtyp]
         else
           tl <- gen_typ_from_size_struct sz';;
           ret ([subtyp] ++ tl)%list.

  (* A Helper function that will detect if  the type has pointer *)
  Fixpoint typ_contains_pointer (old_ptr: typ) : bool :=
    match old_ptr with
    | TYPE_Pointer _ => true
    | TYPE_Array _ t
    | TYPE_Vector _ t =>
        typ_contains_pointer t
    | TYPE_Struct fields
    | TYPE_Packed_struct fields =>
        fold_left (fun acc x => orb acc (typ_contains_pointer x)) fields false
    | _ => false
    end.

  (* Try to find a variable that's the result of a cast from a pointer *)
  Definition gen_ptr_casted_var : GenLLVM (option Ent)
    := gen_entity_with (gen_context' .@ from_pointer').

  (* Generate an identity and type for a variable that was cast from a pointer, also grab the pointer entity *)
  Definition gen_inttoptr_info : GenLLVM (option (Ent * ident * typ))
    := genMatch
         (use (gen_context' .@ from_pointer'))
         (ptr <- queryl from_pointer';;
          t <- queryl variable_type';;
          n <- queryl name';;
          ret (ptr, n, t)).

  (* TODO: old_tptr checks for vectors of pointers...
     I don't think we will find those with the new generator queries?
   *)
  (* TODO: handle opaque pointers. *)
  Definition gen_inttoptr (ptrEnt : Ent) (id : ident) (typ_from_cast : typ) : GenLLVM (instr_id * instr typ) :=
    annotate "gen_inttoptr"
      (opt <- use (gen_context' .@ entl ptrEnt .@ normalized_type');;
       match opt with
       | None => failGen "gen_inttoptr: Pointer entity missing normalized type."
       | Some old_tptr =>
           (* In the following case, we will check whether there are double pointers in the old pointer type, we will not cast if the data structure has double pointer *)
           (* TODO: Better identify the pointer inside and cast without changing their location *)
           new_tptr <-
             match old_tptr with
             | TYPE_Pointer (Some old_typ) =>
                 if typ_contains_pointer old_typ || is_function_type_h old_typ
                 then
                   ret old_tptr
                 else
                   x <- gen_typ_le_size (get_size_from_typ old_typ);;
                   ret (TYPE_Pointer (Some x))
             | TYPE_Vector sz (TYPE_Pointer (Some old_typ)) =>
                 if typ_contains_pointer old_typ || is_function_type_h old_typ
                 then
                   ret old_tptr
                 else
                   x <- gen_typ_le_size (get_size_from_typ old_typ);;
                   ret (TYPE_Pointer (Some x))
             | _ => ret (TYPE_Void) (* Won't reach here... Hopefully *)
             end;;
           '(iid, e) <- genInstrIdEnt new_tptr;;
           d <- use (gen_context' .@ entl ptrEnt .@ deterministic');;
           (* TODO: for now consider all pointers nondeterministic *)
           (gen_context' .@ entl e .@ deterministic') .= false;;
           ret (iid, INSTR_Op (OP_Conversion Inttoptr typ_from_cast (EXP_Ident id) new_tptr))
       end).

  (* TODO: handle opaque pointers. *)
  Definition gen_bitcast_typ (t_from : typ) : GenLLVM typ :=
    let gen_typ_list :=
      match t_from with
      | TYPE_I 1 =>
          ret [TYPE_I 1]
      | TYPE_I 8 =>
          ret [TYPE_I 8 (* ; TYPE_Vector 8 (TYPE_I 1) *)]
      | TYPE_I 16 =>
          ret [TYPE_I 16; TYPE_Vector 2 (TYPE_I 8) (* ; TYPE_Vector 8 (TYPE_I 1) *)]
      | TYPE_I 32
      | TYPE_Float =>
          ret [TYPE_I 32; TYPE_Float; TYPE_Vector 4 (TYPE_I 8); TYPE_Vector 2 (TYPE_I 16); TYPE_Vector 1 (TYPE_I 32); TYPE_Vector 1 TYPE_Float (* ; TYPE_Vector 32 (TYPE_I 1) *)]
      | TYPE_I 64
      | TYPE_Double =>
          ret [TYPE_I 64; (* TYPE_Double; *) TYPE_Vector 8 (TYPE_I 8); TYPE_Vector 4 (TYPE_I 16); TYPE_Vector 2 (TYPE_I 32); TYPE_Vector 2 (TYPE_Float) (* ; TYPE_Vector 64 (TYPE_I 1) *)]
      | TYPE_Vector sz subtyp =>
          match subtyp with
          | TYPE_Pointer _ =>
              (* TODO: Clean up. Figure out what can subtyp of pointer be *)
              (* new_subtyp <- gen_bitcast_typ subtyp;; *)
              ret [TYPE_Vector sz subtyp]
          | _subtyp =>
              let trivial_typs := [(* (1%N, TYPE_I 1); *) (8%N, TYPE_I 8); (32%N, TYPE_I 32); (32%N, TYPE_Float); (64%N, TYPE_I 64) (* ; (64%N, TYPE_Double) *)] in
              let size_of_vec := get_bit_size_from_typ t_from in
              let choices := fold_left (fun acc '(s,t) => let sz' := (size_of_vec / s)%N in
                                                       let rem := (size_of_vec mod s)%N in
                                                       if ((sz' =? 0) || negb (rem =? 0))%N then acc else ((TYPE_Vector sz' t) :: acc)%list) trivial_typs [] in
              ret (t_from :: choices) (* I think adding t_from here slightly biases the generator sometimes *)
          end
      | TYPE_Pointer (Some subtyp) =>
          (* TODO: Clean up. Figure out what can subtyp of pointer be *)
          (* new_subtyp <- gen_bitcast_typ subtyp;; *)
          new_subtyp <- gen_sized_typ;;
          ret [TYPE_Pointer (Some new_subtyp)]
      | _ => ret [t_from] (* TODO: Add more types *) (* This currently is to prevent types like pointer of struct from failing *)
      end in
    typ_list <- gen_typ_list;;
    elems_LLVM typ_list.

  (* TODO: Another approach to form all first class types for bitcast
   If use this will get O(n^2) runtime where n is the length of the context
   but may make generating trivial types less likely to happen *)
  Fixpoint set_add_h {A} (dec : A -> A -> bool) (t : A) (prev next : list A) :=
    match next with
    | nil => (prev ++ [t])%list
    | hd::tl =>
        if dec hd t
        then (prev ++ next)%list
        else set_add_h dec t (prev ++ [hd]) tl
    end%list.

  Definition gen_trivial_typ : GenLLVM typ :=
    oneOf_LLVM [ret (TYPE_I 1)
                ; ret (TYPE_I 8)
                ; ret (TYPE_I 16)
                ; ret (TYPE_I 32)
                ; ret (TYPE_I 64)
                ; ret (TYPE_Float)
                (* ; ret (TYPE_Double) *)
                ; ret TYPE_Vector <*> lift_GenLLVM genPosN <*> gen_primitive_typ].

  Definition gen_first_class_typ_from_context : GenLLVM (option typ)
    := gen_type_matching_variable (withl is_first_class_type').

  Definition gen_non_aggregate_first_class_typ_from_context : GenLLVM (option typ)
    := gen_type_matching_variable (withl is_first_class_type';; withoutl is_aggregate').

  Definition gen_first_class_type_size : nat -> GenLLVM typ
    := gen_typ_size' gen_trivial_typ (fun subg sz => [fun _ => subg sz]) gen_first_class_typ_from_context.

  Definition gen_non_aggregate_first_class_type_size : nat -> GenLLVM typ
    := gen_typ_size' gen_trivial_typ (fun subg sz => [fun _ => subg sz]) gen_non_aggregate_first_class_typ_from_context.

  Definition gen_first_class_type : GenLLVM typ
    := sized_LLVM (fun sz => gen_first_class_type_size (min sz max_typ_size)).

  Definition gen_non_aggregate_first_class_type : GenLLVM typ
    := sized_LLVM (fun sz => gen_non_aggregate_first_class_type_size (min sz max_typ_size)).

  Definition gen_bitcast : GenLLVM (instr_id * instr typ) :=
    annotate "gen_bitcast"
      (tfc <- gen_trivial_typ;;
       efc <- gen_exp_sz0 tfc;;
       new_typ <- gen_bitcast_typ tfc;;
       id <- genInstrId new_typ;;
       ret (id, INSTR_Op (OP_Conversion Bitcast tfc efc new_typ))).

  Definition gen_call (tfun : typ) : GenLLVM (instr_id * instr typ) :=
    ctx <- use (gen_context' .@ @variable_type' (WorldOf _));;
    let blah := IM.Raw.elements ctx in
    annotate ("gen_call: " ++ show blah)
      match tfun with
      | TYPE_Pointer (Some (TYPE_Function ret_t args varargs)) =>
          args_texp <- map_monad
                        (fun (arg_typ:typ) =>
                           arg_exp <- gen_exp_sz0 arg_typ;;
                           ret (arg_typ, arg_exp))
                        args;;
          let args_with_params := map (fun arg => (arg, [])) args_texp in
          (* Otherwise we won't find function pointers *)
          efun <- gen_exp_possibly_non_deterministic_sz0 tfun;;
          id <- genInstrId ret_t;;
          ret (id, INSTR_Call (TYPE_Function ret_t args varargs, efun) args_with_params [])
      | _ => failGen "gen_call"
      end.

  (* TODO: move this. Also give a less confusing name because genOption is a thing? *)
  Definition gen_option {A} (g : G A) : G (option A)
    := freq_ (ret None) [(1%nat, ret None); (7%nat, liftM Some g)].

  (* TODO: move these *)
  Definition opt_add_state {A} {ST} (st : ST) (o : option (A * ST)) : (option A * ST)
    := match o with
       | None => (None, st)
       | (Some (a, st')) => (Some a, st')
       end.

  (* (* TODO: move these *) *)
  Definition either_add_state {A X} {ST} (st : ST) (o : X + (A * ST)) : ((X + A) * ST)
    := match o with
       | inl x => (inl x, st)
       | inr (a, st') => (inr a, st')
       end.

  Definition opt_err_add_state {A} {ST} (st:ST) (o : option (err A * list string * ST)) : err (option A) * list string * ST :=
    match o with
    | None => (inr None, [], st)
    | Some (inl msg, stack, st) => (inl msg, stack, st)
    | Some (inr a, stack, st) => (inr (Some a), stack, st)
    end.

  Definition get_typ_in_ptr (pt : typ) : GenLLVM typ :=
    match pt with
    | TYPE_Pointer (Some t) => ret t
    | _ => failGen "get_typ_in_ptr"
    end.

  (* [route-A chain-memory] biased pointer pick for LOAD (see route_a_mem_w). Scans
     points_to for in-scope, type-matching pointers whose cell content is tainted;
     keeps such a pick with probability w/(w+1). Bypasses gen_var_ent, so it
     replicates the §2/§4 bookkeeping (cur_mask accum + cur_ent) for the picked
     pointer. Returns None (=> the caller falls back to the ordinary pick, consuming
     exactly the pre-change randomness) when w = 0 / no candidate / the 1-in-(w+1)
     fallback fires. Candidate scan is pure state reads — randomness only on the
     biased path (choose + elems). *)
  Definition gen_mem_chain_ptr (tptr : typ) : GenLLVM (option ident) :=
    if Nat.eqb route_a_mem_w 0
    then ret None
    else
      ptm <- use (metadata .@ points_to');;
      am <- use (metadata .@ arg_set');;
      locals <- use (gen_context' .@ is_local');;
      globals <- use (gen_context' .@ is_global');;
      (* [obs-freeze D1] this cell scan is a tainted-preferred tier (P0.c row 2,
         one filter point covers all 3 callers): at any mode <> 0 exclude cells
         whose content mask is frozen-hit (head-exempt — a cell can be a head
         via the store->cell transfer). *)
      ofz <- (if Nat.eqb route_a_obs_freeze 0
              then ret (None : option FreezeState)
              else fz <- freeze_get;; ret (Some fz));;
      let tainted_cell (c : Z) : bool :=
        match IM.Raw.find c am with
        | Some m =>
            andb (negb (N.eqb m 0%N))
                 (match ofz with
                  | Some fz => negb (freeze_hit_b (fz_bits fz) (fz_heads fz) c m)
                  | None => true
                  end)
        | None => false
        end in
      let in_scope (p : Z) : bool :=
        match IM.Raw.find p locals with
        | Some _ => true
        | None => match IM.Raw.find p globals with
                  | Some _ => true
                  | None => false
                  end
        end in
      let cand0 := IM.Raw.fold
                     (fun p c acc => if andb (in_scope p) (tainted_cell c)
                                     then p :: acc else acc)
                     ptm [] in
      match cand0 with
      | [] => ret None
      | _ :: _ =>
          ntptr <- normalize_type_GenLLVM tptr;;
          typed <- map_monad
                     (fun p =>
                        ovt <- use (gen_context' .@ entl (mkEnt p) .@ variable_type');;
                        ret (p, match ovt with
                                | Some vt => normalized_typ_eq ntptr vt
                                | None => false
                                end))
                     cand0;;
          match List.filter snd typed with
          | [] => ret None
          | (_ :: _) as cands =>
              b <- lift_GenLLVM (choose (0%nat, route_a_mem_w));;
              if Nat.eqb b 0%nat
              then ret None
              else
                '(p, _) <- elems_LLVM cands;;
                onm <- use (gen_context' .@ entl (mkEnt p) .@ name');;
                match onm with
                | None => ret None
                | Some nm =>
                    cur_mask_accum p;;
                    cur_ent_set p;;
                    (* [obs-freeze D2 transfer] pointer-pick head consumption. *)
                    freeze_consume_pick p;;
                    ret (Some nm)
                end
          end
      end.

  (* [route-A ret-bridge] eligibility + conversion-source scan for the bridge arm.
     Some (normalized ret type, conversion sources) when: insertions remain, we are
     inside a helper whose ret type is scalar, and >= 1 tainted int-typed LOCAL of a
     usable width is in scope — the sources list guarantees the arm cannot fail even
     when the opportunistic load sub-arm finds nothing. Pure state reads, no
     randomness. Cost note: the arg_set fold runs only while a helper still has
     budget (main has budget 0 -> early None). *)
  Definition gen_ret_bridge_info : GenLLVM (option (typ * list (Z * typ))) :=
    if Nat.eqb route_a_ret_bridge 0
    then ret None
    else
      budget <- use (metadata .@ ret_bridge_budget');;
      if Nat.eqb budget 0
      then ret None
      else
        ort <- use (metadata .@ cur_ret_t');;
        match ort with
        | None => ret None
        | Some rt =>
            nrt <- normalize_type_GenLLVM rt;;
            match nrt with
            | TYPE_I _ | TYPE_Float | TYPE_Double
            | TYPE_Vector _ _ | TYPE_Array _ _
            | TYPE_Struct _ | TYPE_Packed_struct _ =>
                am <- use (metadata .@ arg_set');;
                locals <- use (gen_context' .@ is_local');;
                (* [obs-freeze D1] tainted-source scan = tainted-preferred tier
                   (P0.c row 4): any mode <> 0 excludes frozen-hit carriers
                   (head-exempt). *)
                ofz <- (if Nat.eqb route_a_obs_freeze 0
                        then ret (None : option FreezeState)
                        else fz <- freeze_get;; ret (Some fz));;
                let tainted_local (k : Z) (m : N) : bool :=
                  andb (andb (negb (N.eqb m 0%N))
                             (match IM.Raw.find k locals with
                              | Some _ => true
                              | None => false
                              end))
                       (match ofz with
                        | Some fz => negb (freeze_hit_b (fz_bits fz) (fz_heads fz) k m)
                        | None => true
                        end) in
                let cand0 := IM.Raw.fold
                               (fun k m acc => if tainted_local k m then k :: acc else acc)
                               am [] in
                typed <- map_monad
                           (fun k =>
                              ovt <- use (gen_context' .@ entl (mkEnt k) .@ variable_type');;
                              ret (k, ovt)) cand0;;
                let ok_src (p : Z * option typ) : list (Z * typ) :=
                  match p with
                  | (k, Some (TYPE_I n)) =>
                      match nrt with
                      | TYPE_I m => if Pos.eqb n m then [] else [(k, TYPE_I n)]
                      | _ => [(k, TYPE_I n)]  (* float/double: sitofp; composite: conv
                                                 targets the element/field type later *)
                      end
                  | _ => []
                  end in
                match List.concat (List.map ok_src typed) with
                | [] => ret None
                | srcs => ret (Some (nrt, srcs))
                end
            | _ => ret None
            end
        end.

  (* [route-A ret-bridge] the bridge instruction itself. Opportunistic LOAD from a
     tainted cell of pointee type rt (composes the memory chain: a killer can be
     store -> load -> ... -> ret), else a CONVERSION of a tainted int local to rt
     (guaranteed constructible by gen_ret_bridge_info). The result is bound
     normally: its mask flows via cur_mask/add_to_local_ctx, and it merely COMPETES
     for the eventual ret pick under 320:10 + §3 bias — nothing is forced. *)
  (* [route-A ret-bridge] one conversion of tainted int local [k] (type st) to a
     SCALAR target: returns (result ident, result entity, instruction). The result
     is context-bound, so it also competes on its own downstream. *)
  Definition gen_bridge_conv (k : Z) (st tgt : typ) : GenLLVM (option (ident * Ent * (instr_id * instr typ))) :=
    onm <- use (gen_context' .@ entl (mkEnt k) .@ name');;
    match onm with
    | None => ret None
    | Some nm =>
        cur_mask_accum k;;
        (* [obs-freeze D2 transfer] source consumption (P0.c row 6 sites draw via
           the row 3/4 pools; the pick itself lands here). Gated no-op at knobs 0. *)
        freeze_consume_pick k;;
        let cv := match st, tgt with
                  | TYPE_I n, TYPE_I m => if Pos.ltb m n then Trunc else Sext
                  | _, TYPE_Float | _, TYPE_Double => Sitofp
                  | _, _ => Sext
                  end in
        '(cnm, ce) <- genLocalEnt tgt;;
        ret (Some (cnm, ce, (IId (ident_to_raw_id cnm), INSTR_Op (OP_Conversion cv st (EXP_Ident nm) tgt))))
    end.

  (* Element/field-typed tainted value for a COMPOSITE bridge: the source directly
     when types already match, else one conversion (scalar targets only). *)
  Definition gen_bridge_elem (k : Z) (st elem : typ) : GenLLVM (option (ident * Ent * list (instr_id * instr typ))) :=
    if normalized_typ_eq st elem
    then onm <- use (gen_context' .@ entl (mkEnt k) .@ name');;
         match onm with
         | None => ret None
         | Some nm => ret (Some (nm, mkEnt k, []))
         end
    else match elem with
         | TYPE_I _ | TYPE_Float | TYPE_Double =>
             oc <- gen_bridge_conv k st elem;;
             match oc with
             | None => ret None
             | Some (nm, ce, ins) => ret (Some (nm, ce, [ins]))
             end
         | _ => ret None
         end.

  (* First struct field with a scalar type (with its index), if any. *)
  Fixpoint bridge_first_scalar (fs : list typ) (i : Z) {struct fs} : option (Z * typ) :=
    match fs with
    | [] => None
    | f :: tl => match f with
                 | TYPE_I _ | TYPE_Float | TYPE_Double => Some (i, f)
                 | _ => bridge_first_scalar tl (i + 1)%Z
                 end
    end.

  (* Always-valid single conversion — total fallback when the return type offers no
     scalar slot (burns the budget slot harmlessly instead of failing gen_instr). *)
  Definition gen_bridge_fallback (k : Z) (st : typ) : GenLLVM (list (instr_id * instr typ)) :=
    let tgt := match st with
               | TYPE_I n => if Pos.eqb n 64 then TYPE_I 32 else TYPE_I 64
               | _ => TYPE_I 64
               end in
    oc <- gen_bridge_conv k st tgt;;
    match oc with
    | Some (_, _, ins) => ret [ins]
    | None => failGen "gen_bridge_fallback: nameless candidate"
    end.

  (* Scalar return type: opportunistic load from a tainted cell (composes the memory
     chain), else a conversion of the tainted int source. *)
  Definition gen_bridge_scalar (rt : typ) (k : Z) (st : typ) : GenLLVM (list (instr_id * instr typ)) :=
    oload <- gen_mem_chain_ptr (TYPE_Pointer (Some rt));;
    match oload with
    | Some pnm =>
        op <- cur_ent_take;;
        (match op with
         | Some p => oc <- points_to_find p;;
                     match oc with
                     | None => ret tt
                     | Some c => cm <- arg_mask_lookup c;;
                                 cur_mask_accum_mask cm;;
                                 (* [obs-freeze D2 transfer] load from a head CELL:
                                    the load result binding takes the baton. *)
                                 freeze_consume_pick c
                     end
         | None => ret tt
         end);;
        id <- genInstrId rt;;
        ret [(id, INSTR_Load rt (TYPE_Pointer (Some rt), EXP_Ident pnm) [])]
    | None =>
        oc <- gen_bridge_conv k st rt;;
        match oc with
        | Some (_, _, ins) => ret [ins]
        | None => gen_bridge_fallback k st
        end
    end.

  (* Vector return type: [conv;] insertelement of a tainted element; the written
     lane is recorded in vec_lanes (composes with chain-vector). *)
  Definition gen_bridge_vector (rt : typ) (sz : N) (elem : typ) (k : Z) (st : typ)
    : GenLLVM (list (instr_id * instr typ)) :=
    oe <- gen_bridge_elem k st elem;;
    match oe with
    | None => gen_bridge_fallback k st
    | Some (enm, ee, ecode) =>
        _ <- cur_ent_take;;
        evec <- gen_exp_sz0 rt;;
        obase <- cur_ent_take;;
        lane <- lift_GenLLVM (choose (0, Z.of_N (sz - 1)));;
        cur_mask_accum (unEnt ee);;
        freeze_consume_pick (unEnt ee);;  (* [obs-freeze D2 transfer] *)
        em <- arg_mask_lookup (unEnt ee);;
        '(inm, ie) <- genLocalEnt rt;;
        vec_lanes_update (unEnt ie) obase lane em;;
        ret ((ecode ++ [(IId (ident_to_raw_id inm),
              INSTR_Op (OP_InsertElement (rt, evec) (elem, EXP_Ident enm)
                                         (TYPE_I 32, EXP_Integer lane)))])%list)
    end.

  (* Array/struct return type: [conv;] insertvalue of a tainted element at path
     [idx] whose field type is [ft]. *)
  Definition gen_bridge_insertvalue (rt ft : typ) (idx : Z) (k : Z) (st : typ)
    : GenLLVM (list (instr_id * instr typ)) :=
    oe <- gen_bridge_elem k st ft;;
    match oe with
    | None => gen_bridge_fallback k st
    | Some (enm, ee, ecode) =>
        eagg <- gen_exp_sz0 rt;;
        cur_mask_accum (unEnt ee);;
        freeze_consume_pick (unEnt ee);;  (* [obs-freeze D2 transfer] *)
        '(inm, _) <- genLocalEnt rt;;
        ret ((ecode ++ [(IId (ident_to_raw_id inm),
              INSTR_Op (OP_InsertValue (rt, eagg) (ft, EXP_Ident enm) [idx]))])%list)
    end.

  (* [route-A ret-bridge] the bridge arm: dispatch on the (normalized) return type's
     shape. Every path is total. *)
  Definition gen_ret_bridge_instr (info : typ * list (Z * typ)) : GenLLVM (list (instr_id * instr typ)) :=
    let '(rt, srcs) := info in
    budget <- use (metadata .@ ret_bridge_budget');;
    metadata .@ ret_bridge_budget' .= (budget - 1)%nat;;
    '(k, st) <- elems_LLVM srcs;;
    match rt with
    | TYPE_I _ | TYPE_Float | TYPE_Double => gen_bridge_scalar rt k st
    | TYPE_Vector sz elem => gen_bridge_vector rt sz elem k st
    | TYPE_Array sz elem =>
        (* [0 x T] arrays exist and are even common — choose(0, -1) crashes. *)
        if N.eqb sz 0
        then gen_bridge_fallback k st
        else idx <- lift_GenLLVM (choose (0, Z.of_N sz - 1)%Z);;
             gen_bridge_insertvalue rt elem idx k st
    | TYPE_Struct fields | TYPE_Packed_struct fields =>
        match bridge_first_scalar fields 0%Z with
        | None => gen_bridge_fallback k st
        | Some (fi, ft) => gen_bridge_insertvalue rt ft fi k st
        end
    | _ => gen_bridge_fallback k st
    end.

  Definition gen_load (tptr : typ) : GenLLVM (instr_id * instr typ)
    := obias <- gen_mem_chain_ptr tptr;;
       eptr <- (match obias with
                | Some nm => ret (EXP_Ident nm)
                | None =>
                    _ <- cur_ent_take;;   (* fresh attribution for the ordinary pick *)
                    gen_exp_sz0 tptr
                end);;
       (* [route-A chain-memory] whichever path picked the pointer, cur_ent now holds
          its entity. Propagate the cell content's provenance into the accumulator
          (-> the load RESULT's arg_set via the result binding) — GATED on the knob:
          this write feeds arg_set, which the always-on §3 bias reads, so ungated it
          would change generation even at w=0. *)
       optr <- cur_ent_take;;
       (if Nat.eqb route_a_mem_w 0
        then ret tt
        else match optr with
             | None => ret tt
             | Some p =>
                 oc <- points_to_find p;;
                 match oc with
                 | None => ret tt
                 | Some c => cm <- arg_mask_lookup c;;
                             cur_mask_accum_mask cm;;
                             (* [obs-freeze D2 transfer] load from a head CELL:
                                the load result binding takes the baton. *)
                             freeze_consume_pick c
                 end
             end);;
       vol <- lift (arbitrary : G bool);;
       ptr_typ <- get_typ_in_ptr tptr;;
       align <- ret (Some 1);;
       id <- genInstrId ptr_typ;;
       (* TODO: Fix parameters / generate more of them *)
       ret (id, INSTR_Load ptr_typ (tptr, eptr) []).

  (* TODO: handle opaque pointers?  *)
  Definition gen_store_to (ptr : texp typ) : GenLLVM (instr_id * instr typ)
    :=
    annotate "gen_store_to"
      match ptr with
      | (TYPE_Pointer (Some t), pexp) =>
          ctx <- get_ctx;;
          e <- (gen_exp_sz0 t);;
          let val := (t, e) in
          id <- genVoid;;
          ret (id, INSTR_Store val ptr [ANN_align 1])
      | _ => failGen "gen_store_to"
      end.

  Definition gen_store (tptr : typ) : GenLLVM (instr_id * instr typ)
    :=
    annotate "gen_store"
      ((* [route-A chain-memory] capture WHICH pointer was picked (cur_ent), then DROP
          the ptr pick's own mask from the accumulator, so that after gen_store_to the
          accumulator holds exactly the stored VALUE's mask (correct even for compound
          values with several ident picks — a single cur_ent lookup would only see the
          last one). Safe: store binds no result, so the discarded accumulator value
          was heading for the instruction-boundary reset anyway. See §5. *)
       _ <- cur_ent_take;;
       eptr <- gen_exp_sz0 tptr;;
       optr <- cur_ent_take;;
       _ <- cur_mask_take;;
       ptr_typ <- get_typ_in_ptr tptr;;
       s <- gen_store_to (tptr, eptr);;
       m <- cur_mask_take;;
       cell_mask_record optr m;;
       (* [obs-freeze D2 transfer] store of a head: the baton moves into the target
          CELL (bits outside the stored value's mask lapse at the boundary). *)
       freeze_transfer_store optr m;;
       ret s).

  (* [route-A ptr-arg] find a tainted int-typed LOCAL in scope usable as the source of
     a stored scalar of target type [tgt], EXCLUDING same-width TYPE_I sources when
     [tgt] is TYPE_I (a same-width sext is illegal — mirrors gen_ret_bridge_info's
     ok_src). Pure state reads; randomness ONLY via elems on a non-empty candidate set
     (an empty scan consumes none, so M2 is silent when no tainted int is available). *)
  Definition gen_ptrarg_int_source (tgt : typ) : GenLLVM (option (Z * typ)) :=
    am <- use (metadata .@ arg_set');;
    locals <- use (gen_context' .@ is_local');;
    (* [obs-freeze D1] tainted-source scan = tainted-preferred tier (P0.c row 3):
       any mode <> 0 excludes frozen-hit carriers (head-exempt). *)
    ofz <- (if Nat.eqb route_a_obs_freeze 0
            then ret (None : option FreezeState)
            else fz <- freeze_get;; ret (Some fz));;
    let tainted_local (k : Z) (m : N) : bool :=
      andb (andb (negb (N.eqb m 0%N))
                 (match IM.Raw.find k locals with
                  | Some _ => true
                  | None => false
                  end))
           (match ofz with
            | Some fz => negb (freeze_hit_b (fz_bits fz) (fz_heads fz) k m)
            | None => true
            end) in
    let cand0 := IM.Raw.fold
                   (fun k m acc => if tainted_local k m then k :: acc else acc)
                   am [] in
    typed <- map_monad
               (fun k =>
                  ovt <- use (gen_context' .@ entl (mkEnt k) .@ variable_type');;
                  ret (k, ovt)) cand0;;
    let ok_src (p : Z * option typ) : list (Z * typ) :=
      match p with
      | (k, Some (TYPE_I n)) =>
          match tgt with
          | TYPE_I m => if Pos.eqb n m then [] else [(k, TYPE_I n)]
          | _ => [(k, TYPE_I n)]
          end
      | _ => []
      end in
    match List.concat (List.map ok_src typed) with
    | [] => ret None
    | (_ :: _) as srcs => '(k, st) <- elems_LLVM srcs;; ret (Some (k, st))
    end.

  (* [route-A ptr-arg / c-fix] build a tainted VECTOR value of type [rt = <sz x elem>]
     bound to a fresh register; returns (register ident, entity, [conv?; insertelement]).
     STORE-side analogue of gen_bridge_vector (which returns only the list, for the ret
     pick) — kept SEPARATE so gen_bridge_vector's always-on-capable ret-bridge stream is
     untouched. None when no tainted element of type [elem] can be built. *)
  Definition gen_ptrarg_vec_val (rt : typ) (sz : N) (elem : typ) (k : Z) (st : typ)
    : GenLLVM (option (ident * Ent * list (instr_id * instr typ))) :=
    oe <- gen_bridge_elem k st elem;;
    match oe with
    | None => ret None
    | Some (enm, ee, ecode) =>
        _ <- cur_ent_take;;
        evec <- gen_exp_sz0 rt;;
        obase <- cur_ent_take;;
        lane <- lift_GenLLVM (choose (0, Z.of_N (sz - 1)));;
        cur_mask_accum (unEnt ee);;
        freeze_consume_pick (unEnt ee);;  (* [obs-freeze D2 transfer] *)
        em <- arg_mask_lookup (unEnt ee);;
        '(inm, ie) <- genLocalEnt rt;;
        vec_lanes_update (unEnt ie) obase lane em;;
        ret (Some (inm, ie, (ecode ++ [(IId (ident_to_raw_id inm),
              INSTR_Op (OP_InsertElement (rt, evec) (elem, EXP_Ident enm)
                                         (TYPE_I 32, EXP_Integer lane)))])%list))
    end.

  (* [route-A ptr-arg / c-fix] build a tainted ARRAY/STRUCT value of type [rt] bound to a
     fresh register via insertvalue of a tainted element/field [ft] at path [idx];
     returns (register ident, entity, [conv?; insertvalue]). Store-side analogue of
     gen_bridge_insertvalue. None when no tainted [ft] element can be built. *)
  Definition gen_ptrarg_agg_val (rt ft : typ) (idx : Z) (k : Z) (st : typ)
    : GenLLVM (option (ident * Ent * list (instr_id * instr typ))) :=
    oe <- gen_bridge_elem k st ft;;
    match oe with
    | None => ret None
    | Some (enm, ee, ecode) =>
        eagg <- gen_exp_sz0 rt;;
        cur_mask_accum (unEnt ee);;
        freeze_consume_pick (unEnt ee);;  (* [obs-freeze D2 transfer] *)
        '(inm, ie) <- genLocalEnt rt;;
        ret (Some (inm, ie, (ecode ++ [(IId (ident_to_raw_id inm),
              INSTR_Op (OP_InsertValue (rt, eagg) (ft, EXP_Ident enm) [idx]))])%list))
    end.

  (* [route-A ptr-arg / c-fix] build a tainted value of a STORABLE pointee type [t]
     (scalar OR composite) bound to a fresh register; returns (register ident, entity,
     build instructions). Finds its OWN tainted int source (gen_ptrarg_int_source on the
     relevant scalar target — the pointee for scalars, the element / first-scalar-field
     for composites) and reuses the shared bridge leaves. None when no tainted int source
     is in scope, or [t] offers no usable scalar slot ([0 x T] array, empty/scalar-less
     struct, non-scalar element). Same-width int sources are conservatively excluded by
     gen_ptrarg_int_source even where gen_bridge_elem could reuse them directly — a
     documented missed opportunity, never an illegal instruction. *)
  Definition gen_ptrarg_store_val (t : typ)
    : GenLLVM (option (ident * Ent * list (instr_id * instr typ))) :=
    match t with
    | TYPE_I _ | TYPE_Float | TYPE_Double =>
        osrc <- gen_ptrarg_int_source t;;
        match osrc with
        | None => ret None
        | Some (k, st) =>
            oconv <- gen_bridge_conv k st t;;
            match oconv with
            | None => ret None
            | Some (cnm, ce, convins) => ret (Some (cnm, ce, [convins]))
            end
        end
    | TYPE_Vector sz elem =>
        osrc <- gen_ptrarg_int_source elem;;
        match osrc with
        | None => ret None
        | Some (k, st) => gen_ptrarg_vec_val t sz elem k st
        end
    | TYPE_Array sz elem =>
        (* [0 x T] arrays are common — choose(0,-1) would crash (PLAN §5); skip M2. *)
        if N.eqb sz 0
        then ret None
        else
          osrc <- gen_ptrarg_int_source elem;;
          match osrc with
          | None => ret None
          | Some (k, st) =>
              idx <- lift_GenLLVM (choose (0, Z.of_N sz - 1)%Z);;
              gen_ptrarg_agg_val t elem idx k st
          end
    | TYPE_Struct fields | TYPE_Packed_struct fields =>
        match bridge_first_scalar fields 0%Z with
        | None => ret None
        | Some (fi, ft) =>
            osrc <- gen_ptrarg_int_source ft;;
            match osrc with
            | None => ret None
            | Some (k, st) => gen_ptrarg_agg_val t ft fi k st
            end
        end
    | _ => ret None
    end.

  (* [route-A callee-bias] scalar-param predicate (2a). Robust to an unwrapped
     TYPE_Function and to normalization (checked on the normalized signature).
     [obs-freeze] MOVED UP (textually) unchanged: gen_call_list's D2 mode-2
     plausibility check needs fptr_has_scalar_param before its old position. *)
  Definition is_scalar_typ (t : typ) : bool :=
    match t with
    | TYPE_I _ | TYPE_Float | TYPE_Double => true
    | _ => false
    end.

  Definition fptr_arg_typs (t : typ) : option (list typ) :=
    match t with
    | TYPE_Pointer (Some (TYPE_Function _ args _)) => Some args
    | TYPE_Function _ args _ => Some args
    | _ => None
    end.

  Definition fptr_has_scalar_param (t : typ) : bool :=
    match fptr_arg_typs t with
    | Some args => existsb is_scalar_typ args
    | None => false
    end.

  (* [route-A arg-deref] (PLAN §4.3c) core: OR the pointee cell's content mask
     (arg_set[points_to[p]] — ONE indirection level, the shadow's object granularity)
     into the cur_mask accumulator that add_to_local_ctx assigns to the call result, so
     the result's SSA mask reflects reachable-memory taint. State-only (no randomness);
     no-op when the pointer entity [p] has no known cell. *)
  Definition arg_deref_reflect_ent (p : Z) : GenLLVM unit :=
    oc <- points_to_find p;;
    match oc with
    | None => ret tt
    | Some c => m <- arg_mask_lookup c;;
                cur_mask_accum_mask m;;
                (* [obs-freeze D2 transfer] the pointee cell's mask flows into the
                   call result: a head CELL is consumed here (M1 / ordinary ptr-arg
                   paths); the call-result binding takes the baton. Gated no-op. *)
                freeze_consume_pick c
    end.

  (* [route-A arg-deref] (PLAN §4.3c) ordinary / retro-mint settle paths: [oent] is the
     pointer entity already captured by cur_ent_take. Since r7b BOTH paths deliver Some
     (ordinary pick via gen_var_ent; retro-mint via the mint-site cur_ent_set — retro
     globals DO have cells, minted by add_to_global_ctx); None is a defensive dead case.
     route_a_arg_deref = 0 gates every read/write (trivially stream-identical). Rides
     the knob-on call-arg path. *)
  Definition arg_deref_reflect (oent : option Z) : GenLLVM unit :=
    if Nat.eqb route_a_arg_deref 0
    then ret tt
    else match oent with
         | None => ret tt
         | Some p => arg_deref_reflect_ent p
         end.

  (* [route-A arg-deref] (PLAN §4.3c) M1 settle path: gen_mem_chain_ptr set cur_ent to the
     picked (already tainted-cell) pointer entity. Flag-gated PEEK — at 0 nothing is even
     read from cur_ent. *)
  Definition arg_deref_reflect_cur : GenLLVM unit :=
    if Nat.eqb route_a_arg_deref 0
    then ret tt
    else oent <- use (metadata .@ cur_ent');;
         match oent with
         | None => ret tt
         | Some p => arg_deref_reflect_ent p
         end.

  (* [route-A ptr-arg] generate ONE call argument (intervention (c)): returns the
     (type, expr) pair plus any PRE-CALL instructions to prepend (empty except on M2).
     Only reached on the knob-on path (route_a_ptrarg_w <> 0). *)
  Definition gen_call_arg (arg_typ : typ)
    : GenLLVM ((typ * exp typ) * list (instr_id * instr typ)) :=
    match arg_typ with
    | TYPE_Pointer (Some t) =>
        (* M1: reuse an in-scope pointer whose cell is already tainted. *)
        omem <- gen_mem_chain_ptr arg_typ;;
        match omem with
        | Some nm =>
            (* [route-A arg-deref] (PLAN §4.3c) settle path (a): M1 pick — the pointer
               entity is in cur_ent (gen_mem_chain_ptr set it); reflect its pointee mask
               into the call result. gen_mem_chain_ptr only picks TAINTED-cell pointers,
               so this is exactly the channel-B carrier the result was missing. *)
            arg_deref_reflect_cur;;
            ret ((arg_typ, EXP_Ident nm), [])
        | None =>
            (* fall through to the ORIGINAL arg generation (may retro-mint a global). *)
            _ <- cur_ent_take;;
            arg_exp <- gen_exp_sz0 arg_typ;;
            (* ptr entity: Some for an ordinary pick AND (since r7b) for a retro-minted
               global — the mint site sets cur_ent, so M2's cell_mask_record and the
               arg-deref act on retro pointers too (the ~100%-dominant path, Step-1 m4). *)
            optr <- cur_ent_take;;
            (* M2 (c-fix): pre-call tainted store of a value OF THE POINTEE TYPE [t]
               through the pointer — SCALAR or COMPOSITE pointee (v1 was scalar-only).
               The per-arg w/(w+1) draw gates M2 FIRST and uniformly across shapes; this
               moves the draw ahead of source-finding vs v1 (invisible at knob 0, where
               gen_call_arg is never reached; the knob-on stream has no baseline). *)
            b <- lift_GenLLVM (choose (0%nat, route_a_ptrarg_w));;
            if Nat.eqb b 0%nat
            then
              (* [route-A arg-deref] (PLAN §4.3c) settle paths (b)/(c): M2 not fired —
                 reflect the pointer's PRE-EXISTING pointee mask (ordinary pick and,
                 since r7b, retro-mint both give Some optr; a fresh retro cell's mask
                 is 0, so the OR is a no-op there). *)
              arg_deref_reflect optr;;
              ret ((arg_typ, arg_exp), [])
            else
              (* isolate the STORED VALUE's mask from the call RESULT's mask (which must
                 stay the OR of the ARG masks — the pointer's own, mask 0 for a retro
                 global): save the accumulator, let gen_ptrarg_store_val build+bind the
                 tainted value (its final genLocalEnt resets cur_mask to 0 — true for the
                 scalar gen_bridge_conv AND the composite builders), read the value's mask
                 off the bound register's arg_set, cell_mask_record the pointer's cell,
                 then RESTORE. Mirrors gen_store; multi-arg M2 firings compose (each
                 save/restore is local). *)
              saved <- cur_mask_take;;
              oval <- gen_ptrarg_store_val t;;
              match oval with
              | None =>
                  cur_mask_accum_mask saved;;
                  (* [route-A arg-deref] (PLAN §4.3c) settle paths (b)/(c): M2 built no
                     value — reflect the cell as-is. *)
                  arg_deref_reflect optr;;
                  ret ((arg_typ, arg_exp), [])
              | Some (vnm, ve, valins) =>
                  sid <- genVoid;;
                  vmask <- arg_mask_lookup (unEnt ve);;
                  cell_mask_record optr vmask;;
                  (* [obs-freeze D2 transfer] the M2 pre-call store moves the built
                     value's headship (if any) into the pointer's cell. *)
                  freeze_consume_pick (unEnt ve);;
                  freeze_transfer_store optr vmask;;
                  cur_mask_accum_mask saved;;
                  (* [route-A arg-deref] (PLAN §4.3c) settle path (b) with M2: this deref
                     runs AFTER cell_mask_record, so arg_set[points_to[optr]] already holds
                     vmask (the value M2 just stored through the pointer) — that just-stored
                     taint now feeds the call RESULT's mask. Since r7b this INCLUDES the
                     dominant retro-minted-pointer case: the mint site set cur_ent, so
                     optr = Some(retro entity) and its add_to_global_ctx-minted cell takes
                     the record; pre-r7b optr was None here and the whole M2 shadow write
                     was silently lost (lead review finding). *)
                  arg_deref_reflect optr;;
                  ret ((arg_typ, arg_exp),
                       (valins
                        ++ [(sid, INSTR_Store (t, EXP_Ident vnm) (arg_typ, arg_exp) [ANN_align 1])])%list)
              end
        end
    | _ =>
        arg_exp <- gen_exp_sz0 arg_typ;;
        ret ((arg_typ, arg_exp), [])
    end.

  (* [route-A ptr-arg] LIST-returning call generator emitting [pre-stores...; call].
     At route_a_ptrarg_w = 0 this is EXACTLY (fun x => [x]) <$> gen_call (byte-identical
     stream: same single gen_call call, same wrap). The gen_instr call arm uses this;
     gen_call itself is unchanged for any other caller. *)
  Definition gen_call_list (tfun : typ) : GenLLVM (list (instr_id * instr typ)) :=
    if Nat.eqb route_a_ptrarg_w 0
    then '(id, i) <- gen_call tfun;; ret [(id, i)]
    else
      annotate "gen_call_list"
        match tfun with
        | TYPE_Pointer (Some (TYPE_Function ret_t args varargs)) =>
            results <- map_monad gen_call_arg args;;
            let args_texp := map fst results in
            let prestores := List.concat (map snd results) in
            let args_with_params := map (fun arg => (arg, [])) args_texp in
            efun <- gen_exp_possibly_non_deterministic_sz0 tfun;;
            (* [obs-freeze D2] pending_ce: at this point cur_mask = OR of the
               scalar arg-pick masks + the arg_deref-reflected pointee-cell masks
               (P0.d verified) = exactly the union D2 wants. PEEK, not take — the
               accumulator must still feed the call result's arg_set below. *)
            pending_ce <- (if Nat.eqb route_a_ce_freeze 0
                           then ret 0%N
                           else use (metadata .@ cur_mask'));;
            (* stream-neutral swap genInstrId -> genInstrIdEnt (result entity is
               needed as the head; identical mint & randomness). *)
            '(id, res_e) <- genInstrIdEnt ret_t;;
            (* [obs-freeze D2] deferred application at call assembly (result
               entity minted, callee fixed). Mode 2 = signature-level
               plausibility: a type in loading_fn_types, or a scalar-param
               signature (over-approximation across same-signature helpers).
               Void result: bits freeze with NO head (headship lapses). *)
            (if Nat.eqb route_a_ce_freeze 0
             then ret tt
             else
               if N.eqb pending_ce 0%N
               then ret tt
               else
                 plausible <- (if Nat.eqb route_a_ce_freeze 2
                               then loading <- use (metadata .@ loading_fn_types');;
                                    ret (orb (existsb (fun lt => normalized_typ_eq tfun lt) loading)
                                             (fptr_has_scalar_param tfun))
                               else ret true);;
                 if (plausible : bool)
                 then
                   freeze_or_bits pending_ce;;
                   match ret_t with
                   | TYPE_Void => ret tt
                   | _ => freeze_set_heads pending_ce (unEnt res_e)
                   end
                 else ret tt);;
            ret ((prestores
                  ++ [(id, INSTR_Call (TYPE_Function ret_t args varargs, efun) args_with_params [])])%list)
        | _ => failGen "gen_call_list"
        end.

  (* Generate an instruction, as well as its type...

     The type is sometimes void for instructions that don't really
     compute a value, like void function calls, stores, etc.
   *)

  Definition gen_sized_ptr_type : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_sized_pointer'))
         (queryl variable_type').

  Definition gen_aggregate_type : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_aggregate'))
         (queryl variable_type').

  Definition gen_indexable_type : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_indexable'))
         (queryl variable_type').

  Definition gen_ptr_vecptr_type : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_ptr_vector'))
         (queryl variable_type').

  Definition gen_valid_ptr_vecptr_type : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_ptr_vector'))
         (t <- queryl variable_type';;
          nt <- queryl normalized_type';;
          if negb (contains_typ nt (TYPE_Struct []) soft)
          then ret t
          else mzero).

  Definition gen_valid_ptr_vecptr_ent : GenLLVM (option (Ent * typ))
    := genMatchEnt
         (use (gen_context' .@ is_ptr_vector'))
         (t <- queryl variable_type';;
          nt <- queryl normalized_type';;
          if negb (contains_typ nt (TYPE_Struct []) soft)
          then ret t
          else mzero).

  Definition gen_vec_type : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_vector'))
         (queryl variable_type').

  (* [route-A callee-bias] soft-prefer a function-pointer TYPE among candidates matching
     [filter]: with prob w/(w+1) return the filtered pick; on the 1/(w+1) draw OR an empty
     filtered subset, defer to [base]. w = 0 => [base] with NO candidate scan and NO draw,
     so composing these is stream-identical to [base] when every weight is 0. Reservoir
     pick over the is_function_pointer' candidates via genMatch, exactly like the ordinary
     pick — the §3-bias subset idea moved to the ofun_ptr_typ selection layer. *)
  Definition soft_prefer_fptr (w : nat) (filter : GenQuery typ)
      (base : GenLLVM (option typ)) : GenLLVM (option typ) :=
    if Nat.eqb w 0
    then base
    else
      obiased <- genMatch (use (gen_context' .@ is_function_pointer')) filter;;
      match obiased with
      | Some _ =>
          b <- lift_GenLLVM (choose (0%nat, w));;
          if Nat.eqb b 0%nat then base else ret obiased
      | None => base
      end.

  (* [route-A callee-bias] PLAN §4.3(b) (2a: scalar-param) + lead-adjudicated 2b
     (loading-ptr-param), at the ofun_ptr_typ / gen_function_pointer_type layer, BEFORE
     gen_call (which only draws a pointer VALUE of the already-fixed type). knob=0 (BOTH
     weights) => EXACTLY the original genMatch (byte-identical stream — no scan/draw/read).
     Otherwise compose 2b OUTSIDE 2a (channel-B priority, per the plan's (c)-then-(b)
     spirit): 2b soft-prefers loading-ptr helpers first; its fallback / empty-subset case
     defers to the 2a-biased pick (scalar-param helpers), which defers to the ordinary
     uniform pick. The `loading` state read consumes no randomness. *)
  Definition gen_function_pointer_type : GenLLVM (option typ)
    := let base0 : GenLLVM (option typ) :=
         genMatch (use (gen_context' .@ is_function_pointer')) (queryl variable_type') in
       if andb (Nat.eqb route_a_callee_w 0) (Nat.eqb route_a_callee_ptr_w 0)
       then base0
       else
         loading <- use (metadata .@ loading_fn_types');;
         let filt_scalar : GenQuery typ :=
           (t <- queryl variable_type';;
            nt <- queryl normalized_type';;
            if fptr_has_scalar_param nt then ret t else mzero) in
         let filt_loading : GenQuery typ :=
           (t <- queryl variable_type';;
            if existsb (fun lt => normalized_typ_eq t lt) loading then ret t else mzero) in
         soft_prefer_fptr route_a_callee_ptr_w filt_loading
           (soft_prefer_fptr route_a_callee_w filt_scalar base0).

  Definition gen_insertvalue_type : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_indexable'))
         (t <- queryl variable_type';;
          nt <- queryl normalized_type';;
          cnd <- has_paths_insertvalue_aux nt;;
          if cnd
          then ret t
          else mzero).

  (* Generate a pointer to a sized type (which some variable that exists in the context already has) *)
  Definition gen_sized_typ_in_context : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_sized'))
         (queryl variable_type').

  Definition gen_op_instr_of_typ (τ : typ) : GenLLVM (instr_id * instr typ)
    := i <- ret INSTR_Op <*> gen_op τ;;
       id <- genInstrId τ;;
       ret (id, i).

  (* [obs-freeze P0.a] Ent-returning variant — stream-neutral by construction:
     the same genLocalEnt mint via genInstrIdEnt, only additionally RETURNING the
     already-minted entity. Used by gen_loop_sz for loop_init (its arg_set mask is
     the ONE mask every loop-control value roots at). *)
  Definition gen_op_instr_of_typ_ent (τ : typ) : GenLLVM (instr_id * instr typ * Ent)
    := i <- ret INSTR_Op <*> gen_op τ;;
       '(id, e) <- genInstrIdEnt τ;;
       ret (id, i, e).

  Definition gen_op_instr : GenLLVM (instr_id * instr typ)
    := τ <- gen_op_typ;;
       gen_op_instr_of_typ τ.

  Definition gen_ptr_or_vector_ptr (τ : typ) : GenLLVM (option Ent) :=
    gen_var_of_typ_ent (gen_context' .@ is_ptr_vector') (ret true) τ.

  Definition gen_ptrtoint (ptr_ent : Ent) (tptr : typ) : GenLLVM (instr_id * instr typ) :=
    annotate "gen_ptrtoint"
      (let gen_typ_in_ptr (tptr : typ) :=
         match tptr with
         | TYPE_Pointer t =>
             gen_int_typ_for_ptr_cast (* TODO: Wait till IPTR is implemented *)
         | TYPE_Vector sz ty =>
             x <- gen_int_typ_for_ptr_cast;;
             ret (TYPE_Vector sz x)
         | _ =>
             ret (TYPE_Void) (* Won't get into this case *)
         end in
       typ_from_cast <- gen_typ_in_ptr tptr;;
       '(id, e) <- genInstrIdEnt typ_from_cast;;
       ptr_name <- use (gen_context' .@ entl ptr_ent .@ name');;
       match ptr_name with
       | None => failGen "gen_ptrtoint: unnamed pointer, shouldn't happen."
       | Some ptr_name =>
           let ptr_exp := EXP_Ident ptr_name in
           (* TODO: Copy whether the pointer is deterministic *)
           d <- use (gen_context' .@ entl ptr_ent .@ deterministic');;
           (* Consider pointers nondeterministic for now. Currently
              causes problems. E.g., a pointer returned from a function
              defaults to deterministic *)
           (gen_context' .@ entl e .@ deterministic') .= false;;
           (gen_context' .@ entl e .@ from_pointer') .= ret ptr_ent;;
           ret (id, INSTR_Op (OP_Conversion Ptrtoint tptr ptr_exp typ_from_cast))
       end).

  (* Generate basic instructions.
     Note: this function returns a list because when we generate an alloca we must initialize it...

     TODO: don't initialize alloca and flag it as non-deterministic?
   *)
  Definition gen_instr : GenLLVM (list (instr_id * instr typ)) :=
    annotate "gen_instr"
      (* [route-A propagation] reset the accumulator at each instruction boundary so a leaked
         mask from a preceding void instruction (e.g. store, which picks a value but binds no
         result) cannot bleed into this instruction's result. No randomness consumed. See §2. *)
      (_ <- cur_mask_take;;
       (* [route-A chain-vector] same boundary reset for the last-pick side-channel. *)
       _ <- cur_ent_take;;
       (* [obs-freeze D2 transfer] boundary lapse: moved bits that reached no
          result binding end their chains here (gated no-op at knobs 0). *)
       fz_moved_discard;;
       ointtoptr_info <- gen_inttoptr_info;;
       osized_ptr_typ <- gen_sized_ptr_type;;
       ovalid_ptr_vecptr <- gen_valid_ptr_vecptr_ent;;
       oagg_typ <- gen_indexable_type;;
       ovec_typ <- gen_vec_type;;
       oinsertvalue_typ <- gen_insertvalue_type;;
       ofun_ptr_typ <- gen_function_pointer_type;;
       osized_typ <- gen_sized_typ_in_context;;
       (* [route-A ret-bridge] conditional arm: only inside a helper with budget left,
          scalar ret type, and an available tainted source (see gen_ret_bridge_info). *)
       oret_bridge <- gen_ret_bridge_info;;
       oneOf_LLVM
         ([ op <- gen_op_instr;; t <- gen_op_typ;;
            ret [op]
            ; fmap ret gen_bitcast
           ]
            ++ (* TODO: generate multiple element allocas. Will involve changing initialization *)
            (* num_elems <- ret None;; (* gen_opt_LLVM (resize_LLVM 0 gen_int_texp);; *) *)
            (* align <- ret None;; *)
            maybe [] (fun t => ['(id, e) <- genLocalEnt (TYPE_Pointer (Some t));;
                             (* Allocas are non-deterministic *)
                             gen_context' .@ entl e .@ deterministic' .= false;;
                             (* [route-A chain-memory] fresh memory object -> mint its cell.
                                genLocalEnt's result binding just RESET cur_mask, so after the
                                init store below the accumulator holds exactly the stored
                                VALUE's mask -> record it as the cell content's provenance. *)
                             cell_mint (unEnt e);;
                             store <- gen_store_to (TYPE_Pointer (Some t), EXP_Ident id);;
                             m <- cur_mask_take;;
                             cell_mask_record (Some (unEnt e)) m;;
                             (* [obs-freeze D2 transfer] init store of a head value:
                                the baton moves into the fresh alloca's cell. *)
                             freeze_transfer_store (Some (unEnt e)) m;;
                             ret [(IId (ident_to_raw_id id), INSTR_Alloca t []); store]]) osized_typ
            ++ maybe [] (fun t => fmap (fun x => [x]) <$> [gen_load t; gen_store t; gen_gep t]) osized_ptr_typ
            ++ maybe [] (fun '(e, t) => [(fun x => [x]) <$> gen_ptrtoint e t]) ovalid_ptr_vecptr
            ++ maybe [] (fun '(e, id, t) => [(fun x => [x]) <$> gen_inttoptr e id t]) ointtoptr_info
            ++ maybe [] (fun t => [(fun x => [x]) <$> gen_extractvalue t]) oagg_typ
            ++ maybe [] (fun t => [(fun x => [x]) <$> gen_insertvalue t]) oinsertvalue_typ
            ++ maybe [] (fun t => fmap (fun x => [x]) <$> [gen_extractelement t; gen_insertelement t]) ovec_typ
            ++ maybe [] (fun t => [gen_call_list t]) ofun_ptr_typ
            ++ maybe [] (fun info => [gen_ret_bridge_instr info]) oret_bridge
         )).

  Fixpoint gen_code_length (n : nat) : GenLLVM (code typ)
    := match n with
       | O => ret []
       | S n' =>
           instr <- gen_instr;;
           rest  <- gen_code_length n';;
           ret (instr ++ rest)%list
       end.

  Definition block_size : nat := 20.

  Definition gen_code : GenLLVM (code typ)
    := annotate "gen_code"
         (n <- lift (resize block_size arbitrary);;
          gen_code_length n).

  Definition instr_id_to_raw_id (fail_msg : string) (i : instr_id) : raw_id :=
    match i with
    | IId id => id
    | IVoid n => Name ("fail (instr_id_to_raw_id): " ++ fail_msg)
    end.

  (* Returns a terminator and a list of new blocks that it reaches *)
  (* Need to make returns more likely than branches so we don't get an
     endless tree of blocks *)

  Definition gen_ret (τ : typ) : GenLLVM (terminator typ)
    := nt <- normalize_type_GenLLVM τ;;
       match nt with
       | TYPE_Void => ret TERM_Ret_void
       | _ =>
           e <- gen_exp_sz0%nat τ;;
           ret (TERM_Ret (τ, e))
       end.

  Fixpoint gen_terminator_sz
    (sz : nat)
    (t : typ) (* Return type *)
    (back_blocks : list block_id) (* Blocks that I'm allowed to jump back to *)
    {struct t} : GenLLVM (terminator typ * list (block typ))
    :=
    match sz with
    | 0%nat =>
        term <- gen_ret t;;
        ret (term, [])
    | S sz' =>
        (* Need to lift oneOf to GenLLVM ...*)
        freq_LLVM_thunked
          ([ (6%nat, fun _ => gen_terminator_sz 0 t back_blocks)
               (* Simple jump *)
             ; (min sz' 6%nat, fun _ => '(b, (bh, bs)) <- gen_blocks_sz sz' t back_blocks;; ret (TERM_Br_1 (blk_id b), (bh::bs)))
                 (* Conditional branch, with no backloops *)
             ; (min sz' 6%nat,
                 fun _ =>
                   (* [obs-freeze D1] bracketed cur_mask take around the condition
                      (NB3 discipline): discard the residue BEFORE, read the
                      condition's own mask AFTER, trigger the freeze. Gated: at
                      knob 0 nothing here runs. *)
                   (if Nat.eqb route_a_obs_freeze 0
                    then ret tt
                    else _ <- cur_mask_take;; ret tt);;
                   (* [param-obs-ban D1] S1: the cond-br condition is an
                      observation — arm the ban filter around its pick (its OWN
                      gate, not riding the freeze `if`). Every ident carrying a
                      param bit is dropped from the pool; the sz-0 TYPE_I fallback
                      always keeps the weight-10 EXP_Integer branch, so an empty
                      ident pool yields a constant, never a crash. *)
                   (if param_ban_on then pob_set_ctx true else ret tt);;
                   c <- gen_exp_sz0 (TYPE_I 1);;
                   (if param_ban_on then pob_set_ctx false else ret tt);;
                   (if Nat.eqb route_a_obs_freeze 0
                    then ret tt
                    else cm <- cur_mask_take;;
                         obs_freeze_trigger cm;;
                         (* the condition position consumes with NO result:
                            headship of consumed heads lapses (transfer table). *)
                         fz_moved_discard);;

                   (* Generate first branch *)
                   (* We backtrack contexts so blocks in second branch *)
                   (* don't refer to variables from the first *)
                   (* branch. *)
                   '(b1, (bh1, bs1)) <- backtrack_variable_ctxs (gen_blocks_sz (sz / 2) t back_blocks);;
                   '(b2, (bh2, bs2)) <- gen_blocks_sz (sz / 2) t back_blocks;;

                   ret (TERM_Br (TYPE_I 1, c) (blk_id b1) (blk_id b2), ((bh1::bs1) ++ (bh2::bs2))%list))
                 (* Sometimes generate a loop *)
             ; (min sz' 6%nat,
                 fun _ =>
                   '(t, (b, bs)) <- gen_loop_sz sz' t back_blocks 10;; (* TODO: Should I replace sz with sz' here*)
                   ret (t, (b :: bs)))
            ]
             ++
             (* Loop back sometimes *)
             match back_blocks with
             | (b::bs) =>
                 [(min sz' 1%nat,
                    fun _ =>
                      bid <- lift_GenLLVM (elems_ b back_blocks);;
                      ret (TERM_Br_1 bid, []))]
             | nil => []
             end)
    end
  with gen_blocks_sz
         (sz : nat)
         (t : typ) (* Return type *)
         (back_blocks : list block_id) (* Blocks that I'm allowed to jump back to *)
         {struct t} : GenLLVM (block typ * (block typ * list (block typ)))
       := bid <- new_block_id;;
          (* annotate_debug ("----Genblock: " ++ show bid);; *)
          code <- gen_code;;
          '(term, bs) <- gen_terminator_sz (sz - 1) t back_blocks;;
          let b := {| blk_id   := bid
                   ;  blk_phis := []
                   ;  blk_code := code
                   ;  blk_term := term
                   ;  blk_comments := None
                   |} in
          ret (b, (b, bs))
  with gen_loop_sz
         (sz : nat)
         (t : typ)
         (back_blocks : list block_id) (* Blocks that I'm allowed to jump back to *)
         (bound : LLVMAst.int_ast) {struct t} : GenLLVM (terminator typ * (block typ * list (block typ)))
       :=
         bid_entry <- new_block_id;;
         (* [obs-freeze D1/P0.a] residue guard: a trailing void-result instruction
            (e.g. a void call) can leave cur_mask residue that would inflate
            arg_set[loop_init]. Gated (knob 0: untouched). *)
         (if Nat.eqb route_a_obs_freeze 0
          then ret tt
          else _ <- cur_mask_take;; ret tt);;
         (* TODO: make it so I can generate constant expressions *)
         (* [obs-freeze P0.a] stream-neutral Ent-returning swap (loop_init's mask is
            ALREADY correct at HEAD — its operand picks pass gen_var_ent). *)
         (* [param-obs-ban D1] S2: every loop-control value roots at loop_init, so
            banning param-tainted operands from loop_init's gen_op picks cleans the
            whole loop-control chain (loop_cmp/select/loop_cond/next_cond). Arm the ban
            around the operand picks only; the ibinop leaves fall back to integer
            literals when the pool empties (gen_ibinop_exp_typ, sz-0 fallback). *)
         (if param_ban_on then pob_set_ctx true else ret tt);;
         '(loop_init_instr_id, loop_init_instr, loop_init_ent) <- gen_op_instr_of_typ_ent (TYPE_I 32) (* TODO: big ints *);;
         (if param_ban_on then pob_set_ctx false else ret tt);;
         let loop_init_instr_raw_id := instr_id_to_raw_id "loop init id" loop_init_instr_id in
         (* [obs-freeze D1/P0.a] the ONE mask that matters: every loop-control value
            roots at loop_init (+constants). Pure read; gated to 0 at knob 0. *)
         m_init <- (if Nat.eqb route_a_obs_freeze 0
                    then ret 0%N
                    else arg_mask_lookup (unEnt loop_init_ent));;
         bound' <- lift_GenLLVM (choose (0, bound));;
         let gen_icmp (τ : typ) : GenLLVM (instr_id * instr typ * Ent) :=
           '(iid, ie) <- genInstrIdEnt (TYPE_I 1);;
           ret (iid, INSTR_Op (OP_ICmp Ule τ (EXP_Ident (ID_Local loop_init_instr_raw_id)) (EXP_Integer bound')), ie)
         in
         '(loop_cmp_id, loop_cmp, loop_cmp_ent) <- gen_icmp (TYPE_I 32);; (* TODO: big ints *)
         (* [obs-freeze D1/P0.a] knob-gated mask propagation onto the hand-assembled
            temporaries (their operands bypass gen_var_ent, so their arg_set holds
            0 at HEAD; overwriting is REQUIRED for next_instr's spurious residue).
            Gated because arg_set feeds the always-on §3 bias. *)
         (if Nat.eqb route_a_obs_freeze 0 then ret tt
          else arg_mask_set (unEnt loop_cmp_ent) m_init);;
         let loop_cmp_raw_id := instr_id_to_raw_id "loop_cmp_id" loop_cmp_id in
         let gen_select (τ : typ) : GenLLVM (instr_id * instr typ * Ent) :=
           let lower_exp := OP_Select (TYPE_I 1, (EXP_Ident (ID_Local loop_cmp_raw_id)))
                              (τ, (EXP_Ident (ID_Local loop_init_instr_raw_id)))
                              (τ, EXP_Integer bound') in
           '(iid, ie) <- genInstrIdEnt τ;;
           ret (iid, INSTR_Op lower_exp, ie)
         in
         '(select_id, select_instr, select_ent) <- gen_select (TYPE_I 32);;
         (if Nat.eqb route_a_obs_freeze 0 then ret tt
          else arg_mask_set (unEnt select_ent) m_init);;
         let loop_final_init_id_raw := instr_id_to_raw_id "loop iterator id" select_id in
         '(loop_cond_id, loop_cond, loop_cond_ent) <-
           (let loop_cond_exp := INSTR_Op (OP_ICmp Ugt (TYPE_I 32 (* TODO: big ints *)) (EXP_Ident (ID_Local loop_final_init_id_raw)) (EXP_Integer 0)) in
           '(iid, ie) <- genInstrIdEnt (TYPE_I 1);;
           ret (iid, loop_cond_exp, ie));;
         (* [obs-freeze D1] GENUINE observation site #2: the entry-block br (blk_term
            below, on loop_cond). frozen_bits is function-global and MONOTONE in v0,
            so triggering here — where the br's condition data is fixed — equals
            triggering at assembly, and correctly precedes generation of every block
            beyond this br. The 4514-select condition (loop_cmp) is NOT an
            observation: no trigger there. The observation consumes the
            loop_init-rooted chain with no result: heads riding it lapse. *)
         (if Nat.eqb route_a_obs_freeze 0 then ret tt
          else arg_mask_set (unEnt loop_cond_ent) m_init;;
               obs_freeze_trigger m_init;;
               freeze_consume_pick (unEnt loop_init_ent);;
               fz_moved_discard);;

         let entry_code : list (instr_id * instr typ) := [(loop_init_instr_id, loop_init_instr); (loop_cmp_id, loop_cmp); (select_id, select_instr); (loop_cond_id, loop_cond)] in

         (* Generate end blocks *)
         '(loop_bid, phi_id, bid_entry, bid_next, next_instr_raw_id, next_block, end_bid, end_blocks) <- backtrack_variable_ctxs
                  ('(_, (end_b, end_bs)) <- gen_blocks_sz (sz / 2) t back_blocks;;
                   let end_blocks := end_b :: end_bs in
                   let end_bid := blk_id end_b in

                   bid_next <- new_block_id;;
                   loop_bid <- new_block_id;;
                   phi_id <- new_local_id;;

                   (* Block for controlling the next iteration of the loop *)
                   '(next_instr_id, next_instr) <-
                     ((* [obs-freeze D1/P0.a] residue guard: at HEAD next_instr's
                         arg_set takes whatever cur_mask the end-block generation
                         left (spurious-but-inert residue) — under the knob, discard
                         it and OVERWRITE with m_init below. *)
                      (if Nat.eqb route_a_obs_freeze 0
                       then ret tt
                       else _ <- cur_mask_take;; ret tt);;
                      '(iid, ie) <- genLocalEnt (TYPE_I 32);;   (* stream-neutral genLocal swap *)
                      (if Nat.eqb route_a_obs_freeze 0 then ret tt
                       else arg_mask_set (unEnt ie) m_init);;
                      let next_exp := OP_IBinop (Sub false false) (TYPE_I 32 (* TODO: big ints *)) (EXP_Ident (ID_Local phi_id)) (EXP_Integer 1) in
                      ret (IId (ident_to_raw_id iid), INSTR_Op next_exp));;
                   let next_instr_raw_id := instr_id_to_raw_id "next_exp" next_instr_id in

                   '(next_cond_id, next_cond) <-
                     (let next_cond_exp := OP_ICmp Ugt (TYPE_I 32 (* TODO: big ints *)) (EXP_Ident (ID_Local next_instr_raw_id)) (EXP_Integer 0) in
                      '(iid, ie) <- genInstrIdEnt (TYPE_I 1);;   (* stream-neutral swap *)
                      (* [obs-freeze D1] GENUINE observation site #3: the next-block
                         br (blk_term below, on next_cond). Same monotonicity
                         argument as the entry-block trigger. *)
                      (if Nat.eqb route_a_obs_freeze 0 then ret tt
                       else arg_mask_set (unEnt ie) m_init;;
                            obs_freeze_trigger m_init);;
                      ret (iid, INSTR_Op next_cond_exp));;
                   let next_cond_raw_id := instr_id_to_raw_id "next_cond_exp" next_cond_id in

                   let next_code := [(next_instr_id, next_instr); (next_cond_id, next_cond)] in
                   let next_block := {| blk_id   := bid_next
                                     ; blk_phis := []
                                     ; blk_code := next_code
                                     ; blk_term := TERM_Br (TYPE_I 1, (EXP_Ident (ID_Local next_cond_raw_id))) loop_bid end_bid
                                     ; blk_comments := None
                                     |} in
                   ret (loop_bid, phi_id, bid_entry, bid_next, next_instr_raw_id, next_block, end_bid, end_blocks));;

         (* Generate loop blocks *)
         '(loop_b, loop_bs) <- gen_loop_entry_sz (sz / 2) t loop_bid phi_id bid_entry bid_next (EXP_Ident (ID_Local loop_final_init_id_raw)) (EXP_Ident (ID_Local next_instr_raw_id)) back_blocks;;
         let loop_blocks := loop_b :: loop_bs in
         let loop_bid := blk_id loop_b in

         let entry_block := {| blk_id   := bid_entry
                            ; blk_phis := []
                            ; blk_code := entry_code
                            ; blk_term := TERM_Br (TYPE_I 1, (EXP_Ident (ID_Local (instr_id_to_raw_id "loop_cond_id" loop_cond_id)))) loop_bid end_bid
                            ; blk_comments := None
                            |} in

         ret (TERM_Br_1 bid_entry, (entry_block, loop_blocks ++ [next_block] ++ end_blocks))%list
  with gen_loop_entry_sz
         (sz : nat)
         (t : typ)
         (bid_loop : block_id)
         (phi_id : local_id)
         (bid_entry bid_next : block_id)
         (entry_exp next_exp : exp typ)
         (back_blocks : list block_id) (* Blocks that I'm allowed to jump back to *)
         {struct t} : GenLLVM (block typ * list (block typ))
       := (* This should basically be gen_blocks_sz, but the initial block contains loop control and phi nodes *)
         code <- gen_code;;
         '(term, bs) <- gen_terminator_sz (sz - 1) t (bid_next::back_blocks);;
         let b := {| blk_id   := bid_loop
                  ; blk_phis := [(phi_id, Phi (TYPE_I 32 (* TODO: big ints *)) [(bid_entry, entry_exp); (bid_next, next_exp)])]
                  ; blk_code := code
                  ; blk_term := term
                  ; blk_comments := None
                  |} in
         ret (b, bs).

  Definition gen_blocks (t : typ) : GenLLVM (block typ * list (block typ))
    := sized_LLVM (fun n => fmap snd (gen_blocks_sz n t [])).

  Definition is_main (name : global_id)
    := match name with
       | Name sname => String.eqb sname "main"%string
       | Anon _
       | Raw _ => false
       end.

  (* [route-A #2' arg-type routing] Convert each of main's (i32) args to a DISTINCT scalar type
     so that tainted values of several types EXIST in scope -- the operand-bias then has diverse
     tainted candidates to prefer (the measured bottleneck: arg=i32 but 83% of operands are
     non-i32, so the bias was starved). Generator-only synthesis of #3's benefit, spread one
     conversion per arg (less form-constraining than clustering 6 on one arg). The result %c is
     added to the ctx with arg #i's mask (2^i) since it is built manually (not via gen_var_ent).
     STOPGAP for #3-proper (diverse-typed args + vellvm binding). See ROUTE_A_IMPL §measure+bottleneck. *)
  Definition gen_arg_type_seed (arg_ents : list (ident * Ent)) : GenLLVM (list (instr_id * instr typ))
    := let cycle : list (typ * conversion_type) :=
         [ (TYPE_I 8, Trunc); (TYPE_I 16, Trunc); (TYPE_I 64, Sext); (TYPE_I 1, Trunc); (TYPE_Float, Sitofp) ] in
       let mk (p : nat * (ident * Ent)) : GenLLVM (list (instr_id * instr typ)) :=
         let '(i, ie) := p in
         let '(aid, _ae) := ie in
         match List.nth_error cycle (Nat.modulo i 5) with
         | None => ret []
         | Some te =>
             let '(tgt, conv) := te in
             '(cid, ce) <- genInstrIdEnt tgt;;
             arg_mask_set (unEnt ce) (N.shiftl 1 (N.of_nat i));;
             ret [(cid, INSTR_Op (OP_Conversion conv (TYPE_I 32) (EXP_Ident aid) tgt))]
         end in
       seeds <- map_monad mk (List.combine (List.seq 0 (List.length arg_ents)) arg_ents);;
       ret (List.concat seeds).
  (* Don't want to generate CFGs, actually. Want to generated TLEs *)

  (* [route-A callee-bias 2b] pure AST scan: does the body LOAD through one of its
     pointer PARAMS? A single forward pass per block threads a "param-derived pointer"
     set (a local is param-derived if it IS a param, or is bound by a gep / bitcast whose
     base is param-derived); a load whose pointer operand is param-derived counts.
     Direct-name match dominates (generated loads pick a pointer VARIABLE — often a param
     — directly); the gep/bitcast chain widens it. Approximations (honest): forward
     single-pass (sound for SSA: defs dominate uses); pointer-in-memory (a param stored
     then reloaded) is NOT traced; index/phi-mixed provenance is ignored. Over/under-
     approximation is harmless — 2b is bias-only (principle 3). *)
  Definition raw_id_eqb (a b : raw_id) : bool :=
    match a, b with
    | Name s1, Name s2 => String.eqb s1 s2
    | Anon n1, Anon n2 => Z.eqb n1 n2
    | Raw n1, Raw n2 => Z.eqb n1 n2
    | _, _ => false
    end.

  Definition exp_is_param_derived (roots : list raw_id) (e : exp typ) : bool :=
    match e with
    | EXP_Ident (ID_Local r) => existsb (raw_id_eqb r) roots
    | _ => false
    end.

  Definition scan_code_pd (params : list raw_id)
      (acc : list raw_id * bool) (c : list (instr_id * instr typ)) : (list raw_id * bool) :=
    fold_left
      (fun (st : list raw_id * bool) (ii : instr_id * instr typ) =>
         let '(derived, found) := st in
         match ii with
         | (IId _, INSTR_Load _ (_, ptr) _) =>
             (derived, orb found (exp_is_param_derived (params ++ derived) ptr))
         | (IId res, INSTR_Op (OP_GetElementPtr _ (_, base) _)) =>
             (if exp_is_param_derived (params ++ derived) base
              then res :: derived else derived, found)
         | (IId res, INSTR_Op (OP_Conversion Bitcast _ base _)) =>
             (if exp_is_param_derived (params ++ derived) base
              then res :: derived else derived, found)
         | _ => (derived, found)
         end)
      c acc.

  Definition body_loads_through_param (params : list raw_id)
      (bs : block typ * list (block typ)) : bool :=
    let '(entry, rest) := bs in
    snd (fold_left (fun (st : list raw_id * bool) (blk : block typ) =>
                      scan_code_pd params st (blk_code blk))
                   (entry :: rest) (@nil raw_id, false)).

  (* [route-A param-cell] (r6, PLAN §4.3b) seed the POINTEE cell of every pointer param.
     For param #i of type TYPE_Pointer (Some t): mint a synthetic cell for the param
     entity, then set arg_set[cell] := 2^i (the param's OWN bit — the same bit the value
     seed above assigns to the pointer register). cell_mint only writes points_to, so we
     mint, look the cell back up (points_to_find), then seed its mask. This makes the
     pointee memory a taint source (the live half; the pointer value is runtime-dead),
     so the always-on route_a_mem_w bias soft-prefers loads through the param, the load
     result inherits bit i, and the ret-bridge load-arm can pick the param. Applies to
     EVERY function (main has no pointer params today, so it is unaffected in practice).
     Flag route_a_param_cell = 0 gates BOTH the mint and the seed: no entity ids consumed,
     nothing written -> stream-identical. State-only ops, no randomness (§5). *)
  Definition seed_param_cells (arg_ents : list (ident * Ent)) (args_t : list typ) : GenLLVM unit
    := if Nat.eqb route_a_param_cell 0
       then ret tt
       else
         _ <- map_monad
                (fun (p : nat * (typ * (ident * Ent))) =>
                   let '(i, te) := p in
                   let '(t, ie) := te in
                   let '(_, e) := ie in
                   match t with
                   | TYPE_Pointer (Some _) =>
                       cell_mint (unEnt e);;
                       oc <- points_to_find (unEnt e);;
                       match oc with
                       | Some c => arg_mask_set c (N.shiftl 1 (N.of_nat i))
                       | None => ret tt
                       end
                   | _ => ret tt
                   end)
                (List.combine (List.seq 0 (List.length arg_ents))
                              (List.combine args_t arg_ents));;
         ret tt.

  Definition gen_definition_h (name : global_id) (ret_t : typ) (args_t : list typ) : GenLLVM (definition typ (block typ * list (block typ)))
    :=
    (* [obs-freeze] per-function freeze scoping (r2 Codex B1): reset at every
       definition entry — helper freeze events must not leak into main's freeze
       state and vice versa. Gated no-op at knobs 0. *)
    freeze_reset;;
    (* Generate argument variables *)
    arg_ents <- map_monad genLocalEnt args_t;;
    (* [route-A propagation] SEED: main's args ARE the taint sources -> arg #i gets bit i (2^i).
       See ROUTE_A_IMPL §2.
       [route-A chain-call] with route_a_call_seed <> 0, HELPER params are seeded the same
       way — as a FUNCTION-LOCAL synthetic marker, NOT a real taint source (the real
       sources are main's args only). Context scoping keeps helper-local bits invisible
       to other functions; main's call-result mask still comes from the call site's arg
       masks. This just makes the §2/§3 machinery treat "param-derived" as preferable
       INSIDE the callee, so helpers actually return param-derived values. *)
    (if orb (is_main name) (negb (Nat.eqb route_a_call_seed 0))
     then (_ <- map_monad (fun p => let '(i, ie) := p in
                                    let '(_, e) := ie in
                                    arg_mask_set (unEnt e) (N.shiftl 1 (N.of_nat i)))
                          (List.combine (List.seq 0 (List.length arg_ents)) arg_ents);;
           ret tt)
     else ret tt);;
    (* [param-obs-ban D1] capture this function's param bits (helpers only; main
       is never banned — observing its own args is the very leak under test).
       At route_a_call_seed<>0 each formal #i was just seeded bit 2^i above, so
       the union is exactly N.ones(#formals); at call_seed=0 nothing is seeded =>
       0 => the ban is vacuous (stated precondition). Also clears the transient
       observation-context flag for the new function. Gated on the ban knob: at
       knob 0 nothing is written, so the stream is byte-identical to HEAD. *)
    (if param_ban_on
     then pob_set_param (if is_main name then 0%N
                         else if Nat.eqb route_a_call_seed 0 then 0%N
                         else N.ones (N.of_nat (List.length arg_ents)))
     else ret tt);;
    (* [route-A param-cell] (r6, §4.3b) also seed the POINTEE cell of each pointer param —
       the live half of a pointer source. Gated by route_a_param_cell (0 = stream-identical). *)
    seed_param_cells arg_ents args_t;;
    (* [route-A #2' arg-type routing] for main, build one conversion per arg to a distinct scalar
       type (adds %c to the ctx so gen_blocks can pick them); the instrs are prepended below. *)
    seed_convs <- (if is_main name then gen_arg_type_seed arg_ents else ret []);;
    let args := map fst arg_ents in
    let f_type := TYPE_Function ret_t args_t false in
    let param_attr_slots := map (fun t => []) args in
    let prototype :=
      mk_declaration name f_type
        ([], param_attr_slots)
        []
        []
    in

    (* [route-A ret-bridge] arm this function's body: helpers carry their ret type +
       insertion budget into gen_instr (via state — gen_instr cannot see ret_t
       otherwise); main gets none (its ret value feeds no observation). *)
    _ <- use (metadata .@ cur_ret_t');;
    metadata .@ cur_ret_t' .= (if is_main name then (None : option typ) else Some ret_t);;
    metadata .@ ret_bridge_budget' .= (if is_main name then 0%nat else route_a_ret_bridge);;
    bs <- gen_blocks ret_t;;
    (* [route-A ret-bridge] disarm — don't leak into whatever is generated next. *)
    metadata .@ cur_ret_t' .= (None : option typ);;
    metadata .@ ret_bridge_budget' .= 0%nat;;
    (* [route-A #2'] prepend the arg-type conversions to main's entry block so the seeded
       tainted values (already in the ctx above) are actually defined at the top of main. *)
    let bs' := match seed_convs with
               | [] => bs
               | _ :: _ =>
                   let '(entry, rest) := bs in
                   ({| blk_id       := blk_id entry
                     ; blk_phis     := blk_phis entry
                     ; blk_code     := (seed_convs ++ blk_code entry)%list
                     ; blk_term     := blk_term entry
                     ; blk_comments := blk_comments entry |}, rest)
               end in
    ret (mk_definition (block typ * list (block typ)) prototype (map ident_to_raw_id args) bs').


  Definition gen_definition (name : global_id) (ret_t : typ) (args : list typ) : GenLLVM (definition typ (block typ * list (block typ)))
    :=
    annotate "gen_definition"
      (dfn <- backtrackMetadata (gen_definition_h name ret_t args);;
       e <- add_to_global_ctx (ID_Global name, TYPE_Pointer (Some dfn.(df_prototype).(dc_type)));;
       (gen_context' .@ entl e .@ deterministic') .= false;;
       (* [route-A callee-bias 2b] always-on recording (like vec_lanes): if this helper's
          body loads through a pointer param, remember its REGISTERED type (identical to
          the type just added to the ctx above) so the knob-gated 2b bias can soft-prefer
          it. Skip main (never a callee). A single top-level modify (pure, stream-neutral:
          prepends only when loading, identity otherwise) — invisible to knob=0
          generation (MD5-verified), which never reads loading_fn_types. *)
       let is_loading : bool :=
         andb (negb (is_main name))
              (body_loads_through_param dfn.(df_args) dfn.(df_instrs)) in
       metadata .@ loading_fn_types' %=
         (fun l => if is_loading
                   then TYPE_Pointer (Some dfn.(df_prototype).(dc_type)) :: l
                   else l);;
       ret dfn).

  Definition gen_new_definition (ret_t : typ) (args : list typ) : GenLLVM (definition typ (block typ * list (block typ)))
    :=
    name <- new_global_id;;
    gen_definition name ret_t args.

  Definition gen_helper_function: GenLLVM (definition typ (block typ * list (block typ)))
    :=
    ret_t <- hide_ctx gen_sized_typ;;
    args  <- listOf_LLVM (hide_ctx gen_sized_typ);;
    gen_new_definition ret_t args.

  Definition gen_helper_function_tle : GenLLVM (toplevel_entity typ (block typ * list (block typ)))
    := ret TLE_Definition <*> gen_helper_function.

  Definition gen_helper_function_tle_multiple : GenLLVM (list (toplevel_entity typ (block typ * list (block typ))))
    := listOf_LLVM gen_helper_function_tle.

  Definition gen_main : GenLLVM (definition typ (block typ * list (block typ)))
    := gen_definition (Name "main") (TYPE_I 8) [].

  Definition gen_main_tle : GenLLVM (toplevel_entity typ (block typ * list (block typ)))
    := ret TLE_Definition <*> gen_main.

  Definition gen_typ_tle : GenLLVM (toplevel_entity typ (block typ * list (block typ)))
    :=
    name <- new_local_id;;
    let id := ID_Local name in
    τ <- oneOf_LLVM_thunked
          [ (fun _ => ret TYPE_Struct <*> (k <- lift (choose (0, 5)%nat);;
                                        vectorOf_LLVM k gen_typ_non_void_wo_fn))
            ; (fun _ => ret TYPE_Packed_struct <*> (k <- lift (choose (0, 5)%nat);;
                                        vectorOf_LLVM k gen_typ_non_void_wo_fn))
          ];;
    add_to_typ_ctx (id, τ);;
    ret (TLE_Type_decl id τ).

  Definition gen_typ_tle_multiple : GenLLVM (list (toplevel_entity typ (block typ * list (block typ))))
    := listOf_LLVM gen_typ_tle.

  Definition gen_global_var : GenLLVM (global typ)
    :=
    name <- new_global_id;;
    t <- hide_ctx gen_sized_typ;;
    (* annotate_debug ("--Generate: Global: @" ++ show name ++ " " ++ show t);; *)
    opt_exp <- fmap Some (hide_ctx (gen_exp_sz0 t));;
    e <- add_to_global_ctx (ID_Global name, TYPE_Pointer (Some t));;
    (gen_context' .@ entl e .@ deterministic') .= false;;
    let ann_linkage : list (annotation typ) :=
      match opt_exp with
      | None => [ANN_linkage (LINKAGE_External)]
      | Some _ => []
      end in
    let annotations := ann_linkage in (* TODO: Add more flags *)

    ret (mk_global name t false opt_exp false annotations).

  Definition gen_global_tle : GenLLVM (toplevel_entity typ (block typ * list (block typ)))
    := ret TLE_Global <*> gen_global_var.

  Definition gen_global_tle_multiple : GenLLVM (list (toplevel_entity typ (block typ * list (block typ))))
    := listOf_LLVM  gen_global_tle.

  Definition list_high_level_dec : list (declaration typ) :=
    [
      let puts_id := Name "puts" in
      let puts_typ := TYPE_Function (TYPE_I 32) [(TYPE_Pointer (Some (TYPE_I 8)))] false in
      mk_declaration puts_id puts_typ ([], []) [] []
    ].

  Definition gen_list_high_level_tle : GenLLVM (list (toplevel_entity typ (block typ * list (block typ)))) :=
    ret (map TLE_Declaration list_high_level_dec).

  Definition gen_llvm : GenLLVM (list (toplevel_entity typ (block typ * list (block typ))))
    :=
    high_levels <- gen_list_high_level_tle;;
    defined_typs <- gen_typ_tle_multiple;;
    globals <- gen_global_tle_multiple;;
    functions <- gen_helper_function_tle_multiple;;
    main <- gen_main_tle;;
    res_globals <- get_global_memo;;
    let new_globals := (globals ++ map TLE_Global res_globals)%list in
    ret (high_levels ++ defined_typs ++ new_globals ++ functions ++ [main])%list.

  (** [main] with a size-scaled random number (>= 1) of [i32] arguments;
      the count grows with the QuickChick size parameter. Change [S sz] to
      tune the upper bound. *)
  Definition gen_main_with_args_n : GenLLVM (definition typ (block typ * list (block typ)))
    := (* [route-A #2'] min 5 args so the arg-type-routing (gen_arg_type_seed) covers all 5 cycle
          scalar types (i8/i16/i64/i1/float) + i32 (the args themselves). *)
       n <- sized_LLVM (fun sz => lift (choose (5%nat, (5 + sz)%nat)));;
       let args := List.repeat (TYPE_I 32) n in
       gen_definition (Name "main") (TYPE_I 8) args.

  Definition gen_main_with_args_n_tle : GenLLVM (toplevel_entity typ (block typ * list (block typ)))
    := ret TLE_Definition <*> gen_main_with_args_n.

  (** Full program whose [main] takes a size-scaled number (>= 1) of [i32]
      arguments, with NO helper functions -- the simpler, call-free program
      shape. (The [_withfun] variant adds helper functions to exercise the
      inter-procedural taint tracker; both are valid NI test generators.) *)
  Definition gen_llvm_with_args_nofun : GenLLVM (list (toplevel_entity typ (block typ * list (block typ))))
    :=
    high_levels <- gen_list_high_level_tle;;
    defined_typs <- gen_typ_tle_multiple;;
    globals <- gen_global_tle_multiple;;
    main <- gen_main_with_args_n_tle;;
    res_globals <- get_global_memo;;
    let new_globals := (globals ++ map TLE_Global res_globals)%list in
    ret (high_levels ++ defined_typs ++ new_globals ++ [main])%list.

  (** Full program whose [main] takes a size-scaled number (>= 1) of [i32]
      arguments AND which may contain helper functions (so [main] can emit
      [INSTR_Call]). This is the generator for the inter-procedural taint
      tracker; it mirrors [gen_llvm] but swaps [gen_main_tle] for the
      multi-arg [gen_main_with_args_n_tle]. *)
  Definition gen_llvm_with_args_withfun : GenLLVM (list (toplevel_entity typ (block typ * list (block typ))))
    :=
    high_levels <- gen_list_high_level_tle;;
    defined_typs <- gen_typ_tle_multiple;;
    globals <- gen_global_tle_multiple;;
    functions <- gen_helper_function_tle_multiple;;
    main <- gen_main_with_args_n_tle;;
    res_globals <- get_global_memo;;
    let new_globals := (globals ++ map TLE_Global res_globals)%list in
    ret (high_levels ++ defined_typs ++ new_globals ++ functions ++ [main])%list.

End InstrGenerators.
