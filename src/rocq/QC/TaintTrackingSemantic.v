(** * Taint Tracking for Vellvm NI Testing

    This file provides:
    1. Core taint types and operations (taint, tstate, join_taints, etc.)
    2. Polymorphic expression/instruction taint calculators (calc_taint_exp, taint_instr_pure)
       — shared by both the pure AST analysis (Layer 1, see TaintTrackingPure.v)
       and the semantic analysis (Layer 2 / Option B, below)
    3. Option B: semantic taint tracking with memory taint via
       duplicated Load/Store cases that access concrete addresses
       (Module SemanticTaint)

    The pure AST analysis (Layer 1 legacy) is in TaintTrackingPure.v.
*)

From Stdlib Require Import List String ZArith Bool.
Import ListNotations.

From Vellvm Require Import
  Syntax.LLVMAst
  Syntax.AstLib.

(* ================================================================= *)
(** ** Core Taint Types and Operations (polymorphic in T)             *)
(* ================================================================= *)

(** Taint = set of source variables (local ids) that a value depends on. *)
Definition taint := list raw_id.

(** Boolean equality on raw_id using the existing RelDec instance. *)
Definition raw_id_eqb (x y : raw_id) : bool :=
  if RawIDOrd.eq_dec x y then true else false.

(** Remove duplicates from a list using a boolean equality. *)
Fixpoint remove_dupes {A} (eqb : A -> A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs =>
      if existsb (eqb x) xs then remove_dupes eqb xs
      else x :: remove_dupes eqb xs
  end.

(** Join two taints (union, deduplicated). *)
Definition join_taints (t1 t2 : taint) : taint :=
  remove_dupes raw_id_eqb (t1 ++ t2).

(** Look up a register's taint in the register taint map. *)
Fixpoint treg_lookup (tr : list (raw_id * taint)) (id : raw_id) : taint :=
  match tr with
  | [] => []
  | (k, v) :: rest =>
      if raw_id_eqb k id then v else treg_lookup rest id
  end.

(** Prepend a binding to the register taint map. *)
Definition treg_update (tr : list (raw_id * taint)) (id : raw_id) (t : taint)
  : list (raw_id * taint) :=
  (id, t) :: tr.

(** Memory taint map: address (Z) -> taint *)
Definition tmem_map := list (Z * taint).

(** Look up memory taint at a given address. *)
Fixpoint tmem_lookup (tm : tmem_map) (addr : Z) : taint :=
  match tm with
  | [] => []
  | (a, t) :: rest =>
      if Z.eqb a addr then t else tmem_lookup rest addr
  end.

(** Update memory taint at a given address. *)
Definition tmem_update (tm : tmem_map) (addr : Z) (t : taint) : tmem_map :=
  (addr, t) :: tm.

(* ================================================================= *)
(** ** Taint State                                                     *)
(* ================================================================= *)

(** Full taint state for semantic taint tracking.
    Includes memory taint map for Option B (memory taint tracking). *)
Record tstate := mk_tstate {
  ts_tpc   : taint;                       (** PC taint *)
  ts_tregs : list (raw_id * taint);       (** register taint map *)
  ts_tobs  : taint;                       (** accumulated observation taint *)
  ts_tmem  : tmem_map;                    (** memory taint map *)
}.

Definition init_tstate : tstate :=
  mk_tstate [] [] [] [].

(** Initialize tstate with secret parameters marked as tainted. *)
Definition init_tstate_with_secrets (secret_args : list raw_id) : tstate :=
  let init_tregs := List.map (fun id => (id, [id])) secret_args in
  mk_tstate [] init_tregs [] [].

(* ================================================================= *)
(** ** Polymorphic Expression Taint Calculator                         *)
(* ================================================================= *)

(** Calculate taint of an LLVM expression.
    Polymorphic in T so it works for both (exp typ) and (exp dtyp).
    Only examines expression structure, not type annotations. *)
Section CalcTaint.
  Context {T : Set}.

  Fixpoint calc_taint_exp (e : @exp T) (tr : list (raw_id * taint)) : taint :=
    match e with
    (* Variable references *)
    | EXP_Ident (ID_Local id) => treg_lookup tr id
    | EXP_Ident (ID_Global _) => []

    (* Literals are taint-free *)
    | EXP_Integer _ | EXP_Float _ | EXP_Double _ | EXP_Hex _
    | EXP_Bool _ | EXP_Null | EXP_Zero_initializer
    | EXP_Undef | EXP_Poison => []

    (* Binary operations: join both operands *)
    | OP_IBinop _ _ v1 v2 => join_taints (calc_taint_exp v1 tr) (calc_taint_exp v2 tr)
    | OP_ICmp _ _ v1 v2   => join_taints (calc_taint_exp v1 tr) (calc_taint_exp v2 tr)
    | OP_FBinop _ _ _ v1 v2 => join_taints (calc_taint_exp v1 tr) (calc_taint_exp v2 tr)
    | OP_FCmp _ _ v1 v2   => join_taints (calc_taint_exp v1 tr) (calc_taint_exp v2 tr)

    (* Conversion: taint passes through *)
    | OP_Conversion _ _ v _ => calc_taint_exp v tr

    (* GEP: join pointer and all index taints *)
    | OP_GetElementPtr _ (_, pv) idxs =>
        List.fold_left (fun acc '(_, idx) => join_taints acc (calc_taint_exp idx tr))
                       idxs (calc_taint_exp pv tr)

    (* Select: join condition and both branches *)
    | OP_Select (_, cnd) (_, v1) (_, v2) =>
        join_taints (calc_taint_exp cnd tr)
                    (join_taints (calc_taint_exp v1 tr) (calc_taint_exp v2 tr))

    (* Extract/Insert element *)
    | OP_ExtractElement (_, vec) (_, idx) =>
        join_taints (calc_taint_exp vec tr) (calc_taint_exp idx tr)
    | OP_InsertElement (_, vec) (_, elt) (_, idx) =>
        join_taints (calc_taint_exp vec tr)
                    (join_taints (calc_taint_exp elt tr) (calc_taint_exp idx tr))
    | OP_ShuffleVector (_, v1) (_, v2) (_, mask) =>
        join_taints (calc_taint_exp v1 tr)
                    (join_taints (calc_taint_exp v2 tr) (calc_taint_exp mask tr))

    (* Extract/Insert value *)
    | OP_ExtractValue (_, vec) _ => calc_taint_exp vec tr
    | OP_InsertValue (_, vec) (_, elt) _ =>
        join_taints (calc_taint_exp vec tr) (calc_taint_exp elt tr)

    (* Freeze: taint passes through *)
    | OP_Freeze (_, v) => calc_taint_exp v tr

    (* Aggregate literals: join taints of all elements *)
    | EXP_Struct fields | EXP_Packed_struct fields | EXP_Cstring fields =>
        List.fold_left (fun acc '(_, e) => join_taints acc (calc_taint_exp e tr))
                       fields []
    | EXP_Array _ elts | EXP_Vector _ elts =>
        List.fold_left (fun acc '(_, e) => join_taints acc (calc_taint_exp e tr))
                       elts []
    end.

  (** Calculate taint of a typed expression (T * exp T). *)
  Definition calc_taint_texp (te : @texp T) (tr : list (raw_id * taint)) : taint :=
    calc_taint_exp (snd te) tr.

End CalcTaint.

(* ================================================================= *)
(** ** Instruction-Level Taint Propagation (polymorphic in T)          *)
(* ================================================================= *)

(** Extract local_id from an instr_id, if it names a register. *)
Definition instr_id_to_raw_id (iid : instr_id) : option raw_id :=
  match iid with
  | IId id => Some id
  | IVoid _ => None
  end.

(** Optionally update tregs if the instruction produces a named result. *)
Definition maybe_update_tregs (iid : instr_id) (t : taint)
  (tr : list (raw_id * taint)) : list (raw_id * taint) :=
  match instr_id_to_raw_id iid with
  | Some id => treg_update tr id t
  | None => tr
  end.

Section TaintInstr.
  Context {T : Set}.

  (** Propagate taint through a single LLVM instruction.
      This is the pure AST-based version (no concrete address access).
      Used as fallback for non-critical instructions in Option B. *)
  Definition taint_instr_pure (iid : instr_id) (i : @instr T) (ts : tstate) : tstate :=
    let tr := ts_tregs ts in
    let pc := ts_tpc ts in
    let ob := ts_tobs ts in
    let tm := ts_tmem ts in
    match i with
    | INSTR_Comment _ => ts

    | INSTR_Op op =>
        let te := calc_taint_exp op tr in
        let rt := join_taints te pc in
        mk_tstate pc (maybe_update_tregs iid rt tr) ob tm

    (* Load: WITHOUT concrete address, we fall back to AST-only taint.
       Option B will override this with concrete address access. *)
    | INSTR_Load _ ptr _ =>
        let te := calc_taint_texp ptr tr in
        let rt := join_taints te pc in
        let ob' := join_taints (join_taints te pc) ob in
        mk_tstate pc (maybe_update_tregs iid rt tr) ob' tm

    (* Store: WITHOUT concrete address, we fall back to AST-only taint. *)
    | INSTR_Store _val ptr _ =>
        let te := calc_taint_texp ptr tr in
        let ob' := join_taints (join_taints te pc) ob in
        mk_tstate pc tr ob' tm

    | INSTR_Alloca _ _ =>
        mk_tstate pc (maybe_update_tregs iid pc tr) ob tm

    | INSTR_Call fn args _ =>
        let fn_t := calc_taint_texp fn tr in
        let args_t := List.fold_left
                        (fun acc '(te, _) => join_taints acc (calc_taint_texp te tr))
                        args [] in
        let rt := join_taints (join_taints fn_t args_t) pc in
        mk_tstate pc (maybe_update_tregs iid rt tr) ob tm

    | INSTR_Fence _ _
    | INSTR_AtomicCmpXchg _
    | INSTR_AtomicRMW _
    | INSTR_VAArg _ _
    | INSTR_LandingPad => ts
    end.

  (** Compute taint update for Load with a concrete address (Option B).
      addr_z: the concrete memory address (from concretize_or_pick_unique).
      ptr: the pointer expression AST (for computing address taint). *)
  Definition taint_load_with_addr (iid : instr_id) (ptr : @exp T)
    (addr_z : Z) (ts : tstate) : tstate :=
    let tr := ts_tregs ts in
    let pc := ts_tpc ts in
    let ob := ts_tobs ts in
    let tm := ts_tmem ts in
    (* Address taint from the pointer expression *)
    let ptr_taint := calc_taint_exp ptr tr in
    (* Memory taint from what was previously stored at this address *)
    let mem_taint := tmem_lookup tm addr_z in
    (* Result taint = ptr taint + memory taint + PC taint *)
    let result_taint := join_taints (join_taints ptr_taint mem_taint) pc in
    (* Observation taint: address is observable *)
    let obs_taint := join_taints (join_taints ptr_taint pc) ob in
    mk_tstate pc (maybe_update_tregs iid result_taint tr) obs_taint tm.

  (** Compute taint update for Store with a concrete address (Option B).
      addr_z: the concrete memory address.
      val_exp: the value expression AST (for computing value taint).
      ptr: the pointer expression AST. *)
  Definition taint_store_with_addr (ptr : @exp T) (val_exp : @exp T)
    (addr_z : Z) (ts : tstate) : tstate :=
    let tr := ts_tregs ts in
    let pc := ts_tpc ts in
    let ob := ts_tobs ts in
    let tm := ts_tmem ts in
    (* Address taint from the pointer expression *)
    let ptr_taint := calc_taint_exp ptr tr in
    (* Value taint from the value expression *)
    let val_taint := calc_taint_exp val_exp tr in
    (* Observation taint: address is observable *)
    let obs_taint := join_taints (join_taints ptr_taint pc) ob in
    (* Store value taint into memory taint map at the concrete address *)
    let new_tmem := tmem_update tm addr_z (join_taints val_taint pc) in
    mk_tstate pc tr obs_taint new_tmem.

  (** Propagate taint through a phi node (polymorphic in T). *)
  Definition taint_phi_gen (id : local_id) (p : @phi T) (from_blk : block_id)
    (ts : tstate) : tstate :=
    let '(Phi _ args) := p in
    let te := match List.find (fun '(bid, _) => raw_id_eqb bid from_blk) args with
              | Some (_, e) => calc_taint_exp e (ts_tregs ts)
              | None => []
              end in
    let rt := join_taints te (ts_tpc ts) in
    mk_tstate (ts_tpc ts) (treg_update (ts_tregs ts) id rt) (ts_tobs ts) (ts_tmem ts).

  (** Propagate taint through a terminator (polymorphic in T). *)
  Definition taint_term_gen (t : @terminator T) (ts : tstate) : tstate :=
    let tr := ts_tregs ts in
    let pc := ts_tpc ts in
    let ob := ts_tobs ts in
    let tm := ts_tmem ts in
    match t with
    | TERM_Br v _ _ =>
        let te := calc_taint_texp v tr in
        let pc' := join_taints te pc in
        let ob' := join_taints pc' ob in
        mk_tstate pc' tr ob' tm

    | TERM_Br_1 _ => ts

    | TERM_Switch v _ _ =>
        let te := calc_taint_texp v tr in
        let pc' := join_taints te pc in
        let ob' := join_taints pc' ob in
        mk_tstate pc' tr ob' tm

    | TERM_Ret _
    | TERM_Ret_void
    | TERM_IndirectBr _ _
    | TERM_Resume _
    | TERM_Invoke _ _ _ _
    | TERM_Unreachable => ts
    end.

  (* ================================================================= *)
  (** ** Block and CFG Level Taint Analysis (polymorphic in T)          *)
  (* ================================================================= *)

  (** Process one block (pure AST analysis, no concrete addresses). *)
  Definition taint_block_gen (b : @block T) (from_blk : block_id) (ts : tstate) : tstate :=
    let ts1 := List.fold_left
                 (fun ts' '(id, p) => taint_phi_gen id p from_blk ts')
                 (blk_phis b) ts in
    let ts2 := List.fold_left
                 (fun ts' '(iid, i) => taint_instr_pure iid i ts')
                 (blk_code b) ts1 in
    taint_term_gen (blk_term b) ts2.

  (** Find a block by its id in a list of blocks. *)
  Definition find_block_gen (blocks : list (@block T)) (bid : block_id)
    : option (@block T) :=
    List.find (fun b => raw_id_eqb (blk_id b) bid) blocks.

  (** Get successor block ids from a terminator. *)
  Definition term_successors_gen (t : @terminator T) : list block_id :=
    match t with
    | TERM_Br _ br1 br2 => [br1; br2]
    | TERM_Br_1 br => [br]
    | TERM_Switch _ default_dest brs => default_dest :: List.map snd brs
    | TERM_IndirectBr _ brs => brs
    | TERM_Invoke _ _ to_label unwind_label => [to_label; unwind_label]
    | TERM_Ret _ | TERM_Ret_void | TERM_Resume _ | TERM_Unreachable => []
    end.

  (** Worklist-based taint analysis over a CFG with fuel.
      NOTE: This is the pure AST version. The semantic version with memory
      taint operates at the itree level, defined in the SemanticTaint module below. *)
  Fixpoint taint_cfg_gen (fuel : nat) (blocks : list (@block T))
                         (worklist : list (block_id * block_id))
                         (ts : tstate) : tstate :=
    match fuel, worklist with
    | _, [] => ts
    | O, _ => ts
    | S fuel', (cur, from) :: rest =>
        match find_block_gen blocks cur with
        | None => taint_cfg_gen fuel' blocks rest ts
        | Some b =>
            let ts' := taint_block_gen b from ts in
            let succs := term_successors_gen (blk_term b) in
            let new_work := List.map (fun s => (s, blk_id b)) succs in
            taint_cfg_gen fuel' blocks (rest ++ new_work) ts'
        end
    end.

  (** Taint-analyze a function definition. *)
  Definition taint_function_gen (d : definition T (@block T * list (@block T)))
                                (secret_args : list raw_id) : taint :=
    let '(entry, rest) := df_instrs d in
    let blocks := entry :: rest in
    let entry_id := blk_id entry in
    let ts0 := init_tstate_with_secrets secret_args in
    let fuel := 100 * List.length blocks in
    let final_ts := taint_cfg_gen fuel blocks [(entry_id, entry_id)] ts0 in
    ts_tobs final_ts.

  (** Top-level: taint-analyze a program (pure AST). *)
  Definition taint_program_gen
    (prog : list (toplevel_entity T (@block T * list (@block T)))) : taint :=
    match List.find (fun tle =>
      match tle with
      | TLE_Definition d => raw_id_eqb (dc_name (df_prototype d)) (Name "main")
      | _ => false
      end) prog with
    | Some (TLE_Definition d) => taint_function_gen d (df_args d)
    | _ => []
    end.

  (** Does the program leak the secret? (pure AST analysis) *)
  Definition secret_is_leaked_gen
    (prog : list (toplevel_entity T (@block T * list (@block T)))) : bool :=
    match taint_program_gen prog with
    | [] => false
    | _ => true
    end.

End TaintInstr.

(* ================================================================= *)
(** ** Instantiations for typ and dtyp                                 *)
(* ================================================================= *)

(** For typ (used with generator output / existing TaintTracking.v compat) *)
Definition calc_taint_exp_typ := @calc_taint_exp typ.
Definition taint_instr_typ := @taint_instr_pure typ.
Definition secret_is_leaked_typ := @secret_is_leaked_gen typ.

(** For dtyp (used with denotation-level types) *)
From Vellvm Require Import Syntax.DynamicTypes.
Definition calc_taint_exp_dtyp := @calc_taint_exp dtyp.
Definition taint_instr_dtyp := @taint_instr_pure dtyp.
Definition secret_is_leaked_dtyp := @secret_is_leaked_gen dtyp.

(** Backward-compatible alias *)
Definition secret_is_leaked_semantic := secret_is_leaked_typ.

(** Return the leaked variable names (not just bool). *)
Definition taint_program_typ := @taint_program_gen typ.

(** Check if a specific raw_id is in the taint list. *)
Definition is_tainted (id : raw_id) (t : taint) : bool :=
  existsb (raw_id_eqb id) t.

(* ================================================================= *)
(** ** Option B: Semantic Taint Module with Memory Taint               *)
(** ** (Wraps real denotation, accesses concrete Load/Store addresses)  *)
(* ================================================================= *)

From ExtLib Require Import
  Structures.Monads
  Structures.Functor.

From ITree Require Import
  ITree
  Interp.Recursion
  Events.Exception.

From Vellvm Require Import
  Utilities
  Syntax
  Semantics.LLVMEvents
  Semantics.LLVMParams
  Semantics.MemoryParams
  Semantics.Memory.MemBytes
  Semantics.ConcretizationParams
  DynamicValues
  Handlers.Concretization
  Semantics.Lang.

Require Import Ceres.Ceres.

From Vellvm.Handlers Require Import
  MemoryModel
  MemoryModelImplementation.

Import Sum.
Import Subevent.
Import ListNotations.
Import MonadNotation.

Open Scope monad_scope.

Module SemanticTaint (LP : LLVMParams) (MEM : Memory LP).
  Module LLVM := Lang.Make LP MEM.
  Import LP.
  Import LP.Events.
  Import LLVM.D.

  (** Extract a Z address from a dvalue, if it is a pointer. *)
  Definition dvalue_to_addr_z (dv : dvalue) : option Z :=
    match dv with
    | DVALUE_Addr a => Some (LP.PTOI.ptr_to_int a)
    | _ => None
    end.

  (* ================================================================= *)
  (** ** denote_instr_taint: Option B with memory taint                 *)
  (* ================================================================= *)

  (** Denote an instruction AND compute taint update.
      For Load/Store, duplicates the real event logic to access the
      concrete address (da) for memory taint lookup/update.
      For other instructions, calls denote_instr as black box. *)
  Definition denote_instr_taint
    (i : instr_id * instr dtyp) (varargs : option ADDR.addr)
    (ts : tstate) : itree instr_E tstate :=
    let '(iid, instr_body) := i in
    match iid, instr_body with

    (* ---- LOAD (Option B): duplicate events, access concrete address ---- *)
    | IId id, INSTR_Load dt (du, ptr) _ =>
      (* 1. Run the real events — same sequence as denote_instr *)
      ua <- translate exp_to_instr (denote_exp (Some du) ptr) ;;
      da <- concretize_or_pick_unique ua ;;
      uv <- trigger (Load dt da) ;;
      trigger (LocalWrite id uv) ;;
      (* 2. Compute taint using the concrete address *)
      let addr_z := dvalue_to_addr_z da in
      let tr := ts_tregs ts in
      let pc := ts_tpc ts in
      let ob := ts_tobs ts in
      let tm := ts_tmem ts in
      let ptr_taint := calc_taint_exp ptr tr in
      let mem_taint := match addr_z with
                       | Some z => tmem_lookup tm z
                       | None => []
                       end in
      let result_taint := join_taints (join_taints ptr_taint mem_taint) pc in
      let obs_taint := join_taints (join_taints ptr_taint pc) ob in
      ret (mk_tstate pc (maybe_update_tregs iid result_taint tr) obs_taint tm)

    (* ---- STORE (Option B): duplicate events, access concrete address ---- *)
    | IVoid _, INSTR_Store (dt, val) (du, ptr) _ =>
      (* 1. Run the real events — same sequence as denote_instr *)
      uv <- translate exp_to_instr (denote_exp (Some dt) val) ;;
      ua <- translate exp_to_instr (denote_exp (Some du) ptr) ;;
      da <- concretize_or_pick_unique ua ;;
      match da with
      | DVALUE_Poison dt => raiseUB "Store to poisoned address."
      | _ => trigger (Store dt da uv)
      end ;;
      (* 2. Compute taint using the concrete address *)
      let addr_z := dvalue_to_addr_z da in
      let tr := ts_tregs ts in
      let pc := ts_tpc ts in
      let ob := ts_tobs ts in
      let tm := ts_tmem ts in
      let ptr_taint := calc_taint_exp ptr tr in
      let val_taint := calc_taint_exp val tr in
      let obs_taint := join_taints (join_taints ptr_taint pc) ob in
      let new_tmem := match addr_z with
                      | Some z => tmem_update tm z (join_taints val_taint pc)
                      | None => tm
                      end in
      ret (mk_tstate pc tr obs_taint new_tmem)

    (* ---- All other instructions: black-box wrapper ---- *)
    | _, _ =>
      denote_instr i varargs ;;
      ret (taint_instr_pure iid instr_body ts)
    end.

  (* ================================================================= *)
  (** ** denote_code_taint: thread tstate through instruction list       *)
  (* ================================================================= *)

  Fixpoint denote_code_taint (c : code dtyp) (varargs : option ADDR.addr)
    (ts : tstate) : itree instr_E tstate :=
    match c with
    | [] => ret ts
    | i :: rest =>
        ts' <- denote_instr_taint i varargs ts ;;
        denote_code_taint rest varargs ts'
    end.

  (* ================================================================= *)
  (** ** denote_block_taint: phis + code + terminator with taint         *)
  (* ================================================================= *)

  Definition denote_block_taint (b : block dtyp) (bid_from : block_id)
    (varargs : option ADDR.addr) (ts : tstate)
    : itree instr_E (tstate * (block_id + uvalue)) :=
    (* 1. Process phis: run real phi denotation AND compute taint *)
    denote_phis bid_from (blk_phis b) ;;
    let ts1 := List.fold_left
                 (fun ts' '(id, p) => taint_phi_gen id p bid_from ts')
                 (blk_phis b) ts in
    (* 2. Process code with taint threading *)
    ts2 <- denote_code_taint (blk_code b) varargs ts1 ;;
    (* 3. Process terminator: run real terminator AND compute taint *)
    let ts3 := taint_term_gen (blk_term b) ts2 in
    r <- translate exp_to_instr (denote_terminator (blk_term b)) ;;
    ret (ts3, r).

  (* ================================================================= *)
  (** ** denote_ocfg_taint / denote_cfg_taint: CFG loop with taint      *)
  (* ================================================================= *)

  Definition denote_ocfg_taint (bks : ocfg dtyp) (varargs : option ADDR.addr)
    : (tstate * (block_id * block_id)) ->
      itree instr_E ((tstate * (block_id * block_id)) + (tstate * uvalue)) :=
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
    (ts : tstate) : itree instr_E (tstate * uvalue) :=
    r <- denote_ocfg_taint (blks f) varargs (ts, (init f, init f)) ;;
    match r with
    | inl (ts', bid) =>
        raise ("Can't find block in denote_cfg_taint " ++ to_string (snd bid))
    | inr (ts', uv) => ret (ts', uv)
    end.

  (* ================================================================= *)
  (** ** denote_function_taint: function entry with parameter taint      *)
  (* ================================================================= *)

  (** Denote a function with taint tracking.
      secret_args: list of parameter names that are secret (tainted by themselves).
      All other parameters start untainted. *)
  Definition denote_function_taint
    (df : definition dtyp (cfg dtyp)) (args : list uvalue)
    (secret_args : list raw_id) : itree L0' (tstate * uvalue) :=
    (* Match arguments to parameters *)
    '(bs, vs) <- lift_err ret (combine_lists_varargs (df_args df) args) ;;
    dts <- lift_err ret (map_monad dtyp_of_uvalue_fun vs) ;;
    let dt := DTYPE_Packed_struct dts in
    trigger MemPush ;;
    trigger (StackPush bs) ;;
    varargs_dv <- trigger (Alloca dt 1 None) ;;
    trigger (Store dt varargs_dv (UVALUE_Packed_struct vs)) ;;
    match varargs_dv with
    | DVALUE_Addr varg =>
        (* Initialize taint state: mark secret parameters *)
        let ts0 := init_tstate_with_secrets secret_args in
        '(ts_final, rv) <- translate instr_to_L0' (denote_cfg_taint (df_instrs df) (Some varg) ts0) ;;
        trigger StackPop ;;
        trigger MemPop ;;
        ret (ts_final, rv)
    | _ => raise "Non-address returned from alloca in denote_function_taint"
    end.

End SemanticTaint.

(* ================================================================= *)
(** ** 64-bit Instantiation                                             *)
(* ================================================================= *)

Module SemanticTaint64 := SemanticTaint
  MemoryModelImplementation.LLVMParams64BitIntptr
  Memory64BitIntptr.

Module SemanticTaintBigIntptr := SemanticTaint
  MemoryModelImplementation.LLVMParamsBigIntptr
  MemoryBigIntptr.

(** NOTE: The full taint pipeline (interpreter_gen_taint_obs) is built
    in OCaml (interpreter.ml) by composing:
    1. TopLevelBigIntptr.build_global_environment (setup global env)
    2. SemanticTaintBigIntptr.denote_function_taint (taint-tracked denotation)
    3. Recursion.interp_mrec (convert L0' -> L0)
    4. InterpreterStackBigIntptr.interp_mcfg4_exec_obs (observation collection)

    This is done in OCaml rather than Coq to avoid extraction type mismatch
    between module instantiations (a known limitation of Coq extraction). *)
