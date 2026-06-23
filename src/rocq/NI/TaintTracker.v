(** * Vellvm NI Taint Tracker (partition design)

    Every SSA variable and every memory location is its own taint source.
    The output [ts_tobs] is the set of source identities that influenced
    an observation event (a Load/Store address, a branch direction, or a
    call target) during the execution.

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
      - Calls are inter-procedural:
        [denote_function_taint_rec] recurses into the callee, resolving the
        target address like the real [denote_mcfg] (so both direct and
        indirect calls work) and threading [tstate] through; a [debug_call]
        makes the call target observable (control-flow leakage). [fuel]
        bounds the call depth.
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
     Semantics.LangObs
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
    (* Aggregates: collect taint of every component.
       Category-1 (missing-taint) mutation sites below use the QuickChick
       (*! *) convention, driven by ni_mutation_run.py. Default code is
       correct; each mutant drops a data-flow operand's taint. *)
    | EXP_Cstring fields
    | EXP_Struct fields
    | EXP_Packed_struct fields =>
        (*! *)
        List.fold_left
          (fun acc '(_, e) => join_taints acc (calc_taint_exp e tr))
          fields []
        (*!! agg-struct-drop *)
        (*! [] *)
    | EXP_Array _ fields
    | EXP_Vector _ fields =>
        (*! *)
        List.fold_left
          (fun acc '(_, e) => join_taints acc (calc_taint_exp e tr))
          fields []
        (*!! agg-array-drop *)
        (*! [] *)
    | OP_IBinop _ _ v1 v2
    | OP_FBinop _ _ _ v1 v2 =>
        (*! *)
        join_taints (calc_taint_exp v1 tr) (calc_taint_exp v2 tr)
        (*!! ibinop-drop-v1 *)
        (*! calc_taint_exp v2 tr *)
        (*!! ibinop-drop-v2 *)
        (*! calc_taint_exp v1 tr *)
    | OP_ICmp _ _ v1 v2
    | OP_FCmp _ _ v1 v2 =>
        (*! *)
        join_taints (calc_taint_exp v1 tr) (calc_taint_exp v2 tr)
        (*!! icmp-drop-v1 *)
        (*! calc_taint_exp v2 tr *)
        (*!! icmp-drop-v2 *)
        (*! calc_taint_exp v1 tr *)
    | OP_Conversion _ _ v _ =>
        (*! *)
        calc_taint_exp v tr
        (*!! conv-drop *)
        (*! [] *)
    | OP_GetElementPtr _ (_, pv) idxs =>
        (*! *)
        List.fold_left
          (fun acc '(_, idx) => join_taints acc (calc_taint_exp idx tr))
          idxs (calc_taint_exp pv tr)
        (*!! gep-drop-base *)
        (*! List.fold_left (fun acc '(_, idx) => join_taints acc (calc_taint_exp idx tr)) idxs [] *)
        (*!! gep-drop-idxs *)
        (*! calc_taint_exp pv tr *)
    | OP_Select (_, cnd) (_, v1) (_, v2) =>
        (*! *)
        join_taints (calc_taint_exp cnd tr)
          (join_taints (calc_taint_exp v1 tr) (calc_taint_exp v2 tr))
        (*!! select-drop-cnd *)
        (*! join_taints (calc_taint_exp v1 tr) (calc_taint_exp v2 tr) *)
        (*!! select-drop-v1 *)
        (*! join_taints (calc_taint_exp cnd tr) (calc_taint_exp v2 tr) *)
        (*!! select-drop-v2 *)
        (*! join_taints (calc_taint_exp cnd tr) (calc_taint_exp v1 tr) *)
        (*!! select-drop-cnd-v1 *)
        (*! calc_taint_exp v2 tr *)
    | OP_ExtractElement (_, vec) (_, idx) =>
        (*! *)
        join_taints (calc_taint_exp vec tr) (calc_taint_exp idx tr)
        (*!! extractelt-drop-vec *)
        (*! calc_taint_exp idx tr *)
        (*!! extractelt-drop-idx *)
        (*! calc_taint_exp vec tr *)
    | OP_InsertElement (_, vec) (_, elt) (_, idx) =>
        (*! *)
        join_taints (calc_taint_exp vec tr)
          (join_taints (calc_taint_exp elt tr) (calc_taint_exp idx tr))
        (*!! insertelt-drop-vec *)
        (*! join_taints (calc_taint_exp elt tr) (calc_taint_exp idx tr) *)
        (*!! insertelt-drop-elt *)
        (*! join_taints (calc_taint_exp vec tr) (calc_taint_exp idx tr) *)
        (*!! insertelt-drop-idx *)
        (*! join_taints (calc_taint_exp vec tr) (calc_taint_exp elt tr) *)
    | OP_ShuffleVector (_, v1) (_, v2) (_, mask) =>
        (*! *)
        join_taints (calc_taint_exp v1 tr)
          (join_taints (calc_taint_exp v2 tr) (calc_taint_exp mask tr))
        (*!! shuffle-drop *)
        (*! [] *)
    | OP_ExtractValue (_, vec) _ =>
        (*! *)
        calc_taint_exp vec tr
        (*!! extractval-drop *)
        (*! [] *)
    | OP_InsertValue (_, vec) (_, elt) _ =>
        (*! *)
        join_taints (calc_taint_exp vec tr) (calc_taint_exp elt tr)
        (*!! insertval-drop-vec *)
        (*! calc_taint_exp elt tr *)
        (*!! insertval-drop-elt *)
        (*! calc_taint_exp vec tr *)
    | OP_Freeze (_, v) =>
        (*! *)
        calc_taint_exp v tr
        (*!! freeze-drop *)
        (*! [] *)
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
    (* Load and Store never reach here: [denote_instr_taint] intercepts them
       with dedicated semantic cases (they need the concrete address). A
       well-formed Load is always [IId _] and a Store always [IVoid _], so
       both are handled there and fall through to the catch-all below, which
       is therefore unreachable for them -- it only ever runs the AST-only
       no-op for the remaining instruction kinds (gep, bitcast, conv, ...). *)
    | _ => ts (* Load/Store: unreachable (overridden); others: AST-only no-op. *)
    end.

  (** Phi pickup: argument taint comes from the incoming block. *)
  Definition taint_phi_gen (id : local_id) (p : @phi T) (from_blk : block_id)
    (ts : tstate) : tstate :=
    let '(Phi _ args) := p in
    let te := match List.find (fun '(bid, _) => raw_id_eqb bid from_blk) args with
              | Some (_, e) => calc_taint_exp e (ts_tregs ts)
              | None        => []
              end in
    let rt :=
      (*! *)
      join_taints te (ts_tpc ts)
      (*!! phi-drop-te *)
      (*! ts_tpc ts *)
    in
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
    (* On return, stash the returned value's taint in [ts_tpc] so the
       caller's call site can read it back. The callee's pc is frame-local
       and discarded by the caller, so reusing it as the return-taint
       channel is safe (see [denote_instr_taint]'s INSTR_Call case). *)
    | TERM_Ret v =>
        (*! *)
        mk_tstate (join_taints (calc_taint_texp v tr) pc) tr ob tm
        (*!! ret-drop-val *)
        (*! mk_tstate pc tr ob tm *)
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
  (* LangObs, not Lang: the taint pipeline must denote function bodies
     with the observation-instrumented DenotationObs (branch/call debug
     events), mirroring what the real obs pipeline emits. The stock
     [-interpret] pipeline keeps using Lang/Denotation. *)
  Module LLVM := LangObs.Make LP MEM.
  Import LP.
  Import LP.Events.
  Import LLVM.D.

  (** Extract a concrete [Z] address from a [DVALUE_Addr]. *)
  Definition dvalue_to_addr_z (dv : dvalue) : option Z :=
    match dv with
    | DVALUE_Addr a => Some (LP.PTOI.ptr_to_int a)
    | _ => None
    end.

  (* ============================================================== *)
  (** *** Inter-procedural support                                    *)
  (* ============================================================== *)

  (** A call handler runs one call and returns [(tstate, retval)] with the
      callee's final memory/obs taint merged in and the return value's taint
      stashed in [ts_tpc] (see [taint_term_gen]'s TERM_Ret). It is built
      inside [denote_function_taint_rec], closing over the decremented fuel
      so the recursion stays structural.

      Arguments: call dtyp, the function-pointer taint, the evaluated
      function value [fv], the argument values + taints, and the caller's
      [tstate]. [ch] resolves [fv]'s concrete address against the function
      table (inline) -- handling *both* direct and indirect calls -- or
      falls back to [ExternalCall], exactly as the real [denote_mcfg] does. *)
  Definition CallHandler : Type :=
    dtyp -> taint -> uvalue -> list uvalue -> list taint -> tstate
      -> itree L0' (tstate * uvalue).

  (** Resolve a callee [definition] by its integer address, mirroring
      upstream [lookup_defn] (which keys an [IntMap] on [ptr_to_int addr]).
      The table is built once at entry from each function's global address,
      so indirect calls through [ptrtoint]/[inttoptr] round-trips resolve
      just like the real pipeline. *)
  Fixpoint lookup_defn_by_addr
    (tbl : list (Z * definition dtyp (cfg dtyp))) (a : Z)
    : option (definition dtyp (cfg dtyp)) :=
    match tbl with
    | [] => None
    | (z, df) :: rest =>
        if Z.eqb z a then Some df else lookup_defn_by_addr rest a
    end.

  (** Build a fresh callee register-taint map by binding each formal
      parameter to the corresponding argument taint (the taint analogue of
      upstream [combine_lists_varargs], which binds args to params by value).
      This is how the caller's argument taints cross the call boundary into
      the callee's parameters. (Self-tagging in [treg_lookup] still adds each
      register's own identity on read.) *)
  Fixpoint bind_param_taints (formals : list raw_id) (ats : list taint) : treg_map :=
    match formals, ats with
    | f :: fs, a :: rest => (f, a) :: bind_param_taints fs rest
    | _, _ => []
    end.

  (** Call-depth bound for the taint tracker's direct recursion. Generated
      programs have shallow call graphs; on exhaustion we [raise] (the run
      is then dropped, never counted as a pass). *)
  Definition taint_call_fuel : nat := 1000.

  (** Denote one instruction AND thread the taint state. Load and Store
      are duplicated so we can grab the concrete address [da] for
      memory-taint lookup / update; a direct [INSTR_Call] is inlined via
      the call handler [ch]; every other case delegates to [denote_instr]
      and applies the pure AST-only update. *)
  Definition denote_instr_taint (ch : CallHandler)
    (i : instr_id * instr dtyp) (varargs : option ADDR.addr)
    (ts : tstate) : itree L0' tstate :=
    let '(iid, instr_body) := i in
    let tr := ts_tregs ts in
    let pc := ts_tpc ts in
    let ob := ts_tobs ts in
    let tm := ts_tmem ts in
    match iid, instr_body with

    (* ---- LOAD: duplicate event sequence, capture concrete address ---- *)
    | IId id, INSTR_Load dt (du, ptr) _ =>
        ua <- translate exp_to_L0' (denote_exp (Some du) ptr) ;;
        da <- concretize_or_pick_unique ua ;;
        uv <- trigger (Load dt da) ;;
        trigger (LocalWrite id uv) ;;
        let addr_z    := dvalue_to_addr_z da in
        let ptr_taint := calc_taint_exp ptr tr in
        let mem_taint := match addr_z with
                         | Some z => tmem_lookup tm z
                         | None   => []
                         end in
        let result_taint :=
          (*! *)
          join_taints (join_taints ptr_taint mem_taint) pc
          (*!! load-result-drop-ptr *)
          (*! join_taints mem_taint pc *)
          (*!! load-result-drop-mem *)
          (*! join_taints ptr_taint pc *)
        in
        (* The load address is observable. Its determining inputs are
           [ptr_taint], which enter [tobs]. (The concrete cell label [inr z]
           is redundant -- the address-determining inputs are already in
           [ptr_taint], and cell-content leakage is tracked via the dest
           taint -- so it is not added.) *)
        let obs_taint :=
          join_taints (join_taints ptr_taint pc) ob in
        ret (mk_tstate pc (maybe_update_tregs iid result_taint tr) obs_taint tm)

    (* ---- STORE: duplicate event sequence, update memory taint ---- *)
    | IVoid _, INSTR_Store (dt, val) (du, ptr) _ =>
        uv <- translate exp_to_L0' (denote_exp (Some dt) val) ;;
        ua <- translate exp_to_L0' (denote_exp (Some du) ptr) ;;
        da <- concretize_or_pick_unique ua ;;
        match da with
        | DVALUE_Poison _ => raiseUB "Store to poisoned address."
        | _ => trigger (Store dt da uv)
        end ;;
        let addr_z    := dvalue_to_addr_z da in
        let ptr_taint := calc_taint_exp ptr tr in
        let val_taint := calc_taint_exp val tr in
        (* The store address is observable: its determining inputs ([ptr_taint])
           enter [tobs]. (The concrete cell label is redundant, so omitted.) *)
        let obs_taint :=
          join_taints (join_taints ptr_taint pc) ob in
        let stored_taint :=
          (*! *)
          join_taints val_taint pc
          (*!! store-drop-val *)
          (*! pc *)
        in
        let new_tmem  := match addr_z with
                         | Some z => tmem_update tm z stored_taint
                         | None   => tm
                         end in
        ret (mk_tstate pc tr obs_taint new_tmem)

    (* ---- CALL: intrinsics delegate (old behavior); any other call is
            handled via the call handler [ch], which resolves the target
            address -- inlining a defined function (direct or indirect) or
            falling back to ExternalCall. ---- *)
    | _, INSTR_Call (dt, f) cargs _ =>
        match intrinsic_exp f with
        | Some _ =>
            (* intrinsic (e.g. the llvm.va_start family): let denote_instr
               handle it, then apply the conservative AST-only call taint. *)
            translate instr_to_L0' (denote_instr (iid, instr_body) varargs) ;;
            ret (taint_instr_pure iid instr_body ts)
        | None =>
            (* evaluate the arguments and the function operand in the caller
               frame (their events and taints), exactly as the real
               [denote_instr] does, then hand off to [ch], which resolves
               [fv]'s address to a defined function (inline) or falls back to
               the same [ExternalCall] the real [denote_mcfg] uses. *)
            uvs <- map_monad
                     (fun '(t, op) => translate exp_to_L0' (denote_exp (Some t) op))
                     (List.map fst cargs) ;;
            let arg_taints :=
              List.map (fun '(_, op) => calc_taint_exp op tr) (List.map fst cargs) in
            fv <- translate exp_to_L0' (denote_exp None f) ;;
            let f_taint := calc_taint_exp f tr in
            '(tsc, rv) <- ch dt f_taint fv uvs arg_taints ts ;;
            (* make the return value available to subsequent instrs *)
            (match iid with
             | IId id  => trigger (LocalWrite id rv)
             | IVoid _ => ret tt
             end) ;;
            (* the dest taint was stashed in [ts_tpc tsc] (callee's return
               taint for an inlined call, or the conservative call taint for
               an external one); join with caller pc and write into dest.
               tobs/tmem are global -- take the callee's updated copies. *)
            let ret_taint :=
              (*! *)
              join_taints (ts_tpc tsc) pc
              (*!! call-drop-ret *)
              (*! pc *)
            in
            let regs' := match iid with
                         | IId id  => treg_update tr id ret_taint
                         | IVoid _ => tr
                         end in
            ret (mk_tstate pc regs' (ts_tobs tsc) (ts_tmem tsc))
        end

    (* ---- Other instructions: delegate to denote_instr, AST-only update ---- *)
    | _, _ =>
        translate instr_to_L0' (denote_instr (iid, instr_body) varargs) ;;
        ret (taint_instr_pure iid instr_body ts)
    end.

  (** Thread tstate through a list of instructions. *)
  Fixpoint denote_code_taint (ch : CallHandler) (c : code dtyp)
    (varargs : option ADDR.addr) (ts : tstate) : itree L0' tstate :=
    match c with
    | [] => ret ts
    | i :: rest =>
        ts' <- denote_instr_taint ch i varargs ts ;;
        denote_code_taint ch rest varargs ts'
    end.

  (** Denote a block (phis, code, terminator) and thread tstate. *)
  Definition denote_block_taint (ch : CallHandler) (b : block dtyp) (bid_from : block_id)
    (varargs : option ADDR.addr) (ts : tstate)
    : itree L0' (tstate * (block_id + uvalue)) :=
    translate instr_to_L0' (denote_phis bid_from (blk_phis b)) ;;
    let ts1 := List.fold_left
                 (fun ts' '(id, p) => taint_phi_gen id p bid_from ts')
                 (blk_phis b) ts in
    ts2 <- denote_code_taint ch (blk_code b) varargs ts1 ;;
    let ts3 := taint_term_gen (blk_term b) ts2 in
    r <- translate exp_to_L0' (denote_terminator (blk_term b)) ;;
    ret (ts3, r).

  Definition denote_ocfg_taint (ch : CallHandler) (bks : ocfg dtyp)
    (varargs : option ADDR.addr)
    : (tstate * (block_id * block_id))
      -> itree L0'
               ((tstate * (block_id * block_id)) + (tstate * uvalue)) :=
    iter (C := ktree _) (bif := sum)
      (fun '(ts, (bid_from, bid_src)) =>
        match find_block bks bid_src with
        | None => ret (inr (inl (ts, (bid_from, bid_src))))
        | Some block_src =>
            '(ts', bd) <- denote_block_taint ch block_src bid_from varargs ts ;;
            match bd with
            | inr dv => ret (inr (inr (ts', dv)))
            | inl bid_target => ret (inl (ts', (bid_src, bid_target)))
            end
        end).

  Definition denote_cfg_taint (ch : CallHandler) (f : cfg dtyp)
    (varargs : option ADDR.addr) (ts : tstate)
    : itree L0' (tstate * uvalue) :=
    r <- denote_ocfg_taint ch (blks f) varargs (ts, (init f, init f)) ;;
    match r with
    | inl (_ts', _bid) =>
        raise "Block not found in denote_cfg_taint"
    | inr (ts', uv) => ret (ts', uv)
    end.

  (** Denote a function with taint tracking, recursing through direct
      calls. [fuel] bounds the call depth.
      Mirrors upstream [denote_function]'s call-frame setup ([MemPush] /
      [StackPush] / [Alloca] for varargs / [Store] / ... / [StackPop] /
      [MemPop]). SSA frames save/restore for free via Gallina recursion
      (the caller's [tstate] stays in scope); only [ts_tobs]/[ts_tmem]
      (global) are merged back from the callee.

      [caller_ts] supplies the shared memory/obs taint and the control
      (pc) taint at the call site; the callee runs with a *fresh* register
      map whose parameters are bound to [arg_taints] (see
      [bind_param_taints]). *)
  Fixpoint denote_function_taint_rec
    (fundefs_t : list (Z * definition dtyp (cfg dtyp))) (fuel : nat)
    (df : definition dtyp (cfg dtyp)) (args : list uvalue)
    (arg_taints : list taint) (caller_ts : tstate)
    : itree L0' (tstate * uvalue) :=
    match fuel with
    | O => raise "Taint tracker: call-depth fuel exhausted."
    | S fuel' =>
        (* External / indirect call: mirror [denote_mcfg]'s [ExternalCall]
           fallback so the observation trace stays aligned with the real
           pipeline, and taint the result conservatively by the function
           pointer, the arguments, and the caller pc. [fv] is the
           already-evaluated function value, [f_taint] its taint. *)
        let external_call_taint : CallHandler :=
          fun dt f_taint fv uvs ats cts =>
            dargs <- map_monad (fun uv => concretize_or_pick_unique uv) uvs ;;
            rv <- fmap dvalue_to_uvalue (trigger (ExternalCall dt fv dargs)) ;;
            let call_taint :=
              List.fold_left join_taints ats (join_taints f_taint (ts_tpc cts)) in
            ret (mk_tstate call_taint (ts_tregs cts)
                           (join_taints (ts_tobs cts) call_taint) (ts_tmem cts), rv) in
        (* Call handler closes over the decremented fuel so the recursion
           stays structural for Coq's guard checker. Resolve [fv]'s concrete
           address against the function table (inline) exactly as the real
           [denote_mcfg]/[lookup_defn]; otherwise external. *)
        let ch : CallHandler :=
          fun dt f_taint fv uvs ats cts =>
            dfv <- concretize_or_pick fv ;;
            (* Call-target observation (control-flow leakage): which target
               is called is observable, like a branch direction. So the
               function pointer's taint enters the public partition, and
               [debug_call] emits the same call-target obs as the real
               [denote_mcfg] so the traces stay aligned. *)
            let cts' :=
              mk_tstate (ts_tpc cts) (ts_tregs cts)
                        (join_taints (ts_tobs cts) (join_taints f_taint (ts_tpc cts)))
                        (ts_tmem cts) in
            match dvalue_to_addr_z dfv with
            | Some a =>
                debug_call a ;;
                match lookup_defn_by_addr fundefs_t a with
                | Some cdf => denote_function_taint_rec fundefs_t fuel' cdf uvs ats cts'
                | None     => external_call_taint dt f_taint fv uvs ats cts'
                end
            | None => external_call_taint dt f_taint fv uvs ats cts'
            end in
        '(bs, vs) <- lift_err ret (combine_lists_varargs (df_args df) args) ;;
        dts <- lift_err ret (map_monad dtyp_of_uvalue_fun vs) ;;
        let dt := DTYPE_Packed_struct dts in
        trigger MemPush ;;
        trigger (StackPush bs) ;;
        varargs_dv <- trigger (Alloca dt 1 None) ;;
        trigger (Store dt varargs_dv (UVALUE_Packed_struct vs)) ;;
        match varargs_dv with
        | DVALUE_Addr varg =>
            let callee_ts :=
              mk_tstate (ts_tpc caller_ts)
                        (bind_param_taints (df_args df) arg_taints)
                        (ts_tobs caller_ts) (ts_tmem caller_ts) in
            '(ts_final, rv) <- denote_cfg_taint ch (df_instrs df) (Some varg) callee_ts ;;
            trigger StackPop ;;
            trigger MemPop ;;
            ret (ts_final, rv)
        | _ => raise "Non-address returned from alloca in denote_function_taint_rec"
        end
    end.

  (** Build the address-keyed function table by reading each function's
      global address (the same [GlobalRead] the real [address_one_function]
      uses), so direct *and* indirect calls resolve by concrete address. *)
  Definition build_fundefs_t (defs : list (definition dtyp (cfg dtyp)))
    : itree L0' (list (Z * definition dtyp (cfg dtyp))) :=
    map_monad
      (fun cdf =>
         fa <- translate exp_to_L0'
                 (denote_exp None
                    (EXP_Ident (ID_Global (dc_name (df_prototype cdf))))) ;;
         dfa <- concretize_or_pick fa ;;
         ret (match dvalue_to_addr_z dfa with
              | Some a => (a, cdf)
              | None   => ((-1)%Z, cdf)
              end))
      defs.

  (** Entry point: build the function table, then run [main] with taint
      tracking. Direct and indirect calls both resolve by concrete address,
      mirroring the real [denote_mcfg]. *)
  Definition denote_mcfg_taint
    (defs : list (definition dtyp (cfg dtyp)))
    (main : definition dtyp (cfg dtyp)) (args : list uvalue)
    : itree L0' (tstate * uvalue) :=
    fundefs_t <- build_fundefs_t defs ;;
    (* Mirror the entry call to [main] that the real [denote_vellvm] makes
       through [denote_mcfg], so the call-target obs stream aligns (the
       real pipeline emits a [debug_call] for the top-level main invocation;
       its target is constant, so it never leaks). *)
    ma <- translate exp_to_L0'
            (denote_exp None (EXP_Ident (ID_Global (dc_name (df_prototype main))))) ;;
    dma <- concretize_or_pick ma ;;
    (match dvalue_to_addr_z dma with
     | Some a => debug_call a
     | None   => ret tt
     end) ;;
    denote_function_taint_rec fundefs_t taint_call_fuel main args
      (List.map (fun _ => @nil taint_src) args) init_tstate.

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
      2. [TaintTrackerBigIntptr.denote_mcfg_taint]   (inlines calls itself)
      3. [Recursion.interp_mrec]   (L0' → L0; trivial since no CallE -- the
         taint tracker resolves and inlines every call, so the tree has none)
      4. [InterpreterStackBigIntptr.interp_mcfg4_exec_obs]

    See [src/NI_ARCHITECTURE.md]. *)
