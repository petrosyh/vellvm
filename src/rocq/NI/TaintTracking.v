(** * Taint Tracking for Vellvm NI Testing
    Tracks which values depend on the secret input.
    Adapted from SpecIBT-old/TaintTracking.v for LLVM IR. *)

From Stdlib Require Import List String ZArith Bool.
Import ListNotations.

From Vellvm Require Import
  Syntax.LLVMAst
  Syntax.AstLib.

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

(** Look up a register's taint in the register taint map.
    Returns [] if the register is not found. *)
Fixpoint treg_lookup (tr : list (raw_id * taint)) (id : raw_id) : taint :=
  match tr with
  | [] => []
  | (k, v) :: rest =>
      if raw_id_eqb k id then v else treg_lookup rest id
  end.

(** Taint configuration for a function execution. *)
Record tcfg := mk_tcfg {
  tpc  : taint;                        (** PC taint: implicit flow from branch conditions *)
  treg : list (raw_id * taint);        (** register taint map: SSA name -> taint *)
  tobs : taint;                        (** accumulated observation taint *)
}.

(** Calculate taint of an LLVM expression by looking up free variables
    and joining taints of sub-expressions. *)
Fixpoint calc_taint_exp (e : exp typ) (tr : list (raw_id * taint)) : taint :=
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

(** Calculate taint of a typed expression (typ * exp typ). *)
Definition calc_taint_texp (te : texp typ) (tr : list (raw_id * taint)) : taint :=
  calc_taint_exp (snd te) tr.

(* ================================================================= *)
(** ** Instruction and Terminator Taint Propagation                    *)
(* ================================================================= *)

(** Extract local_id from an instr_id, if it names a register. *)
Definition instr_id_to_raw_id (iid : instr_id) : option raw_id :=
  match iid with
  | IId id => Some id
  | IVoid _ => None
  end.

(** Prepend a binding to the register taint map.
    SSA guarantees single assignment, so shadowing is correct. *)
Definition treg_update (tr : list (raw_id * taint)) (id : raw_id) (t : taint)
  : list (raw_id * taint) :=
  (id, t) :: tr.

(** Optionally update treg if the instruction produces a named result. *)
Definition maybe_update_treg (iid : instr_id) (t : taint) (tr : list (raw_id * taint))
  : list (raw_id * taint) :=
  match instr_id_to_raw_id iid with
  | Some id => treg_update tr id t
  | None => tr
  end.

(** Propagate taint through a single LLVM instruction.
    Analogous to SpecIBT's taint_step. *)
Definition taint_instr (iid : instr_id) (i : instr typ) (tc : tcfg) : tcfg :=
  let tr := treg tc in
  let pc := tpc tc in
  let ob := tobs tc in
  match i with
  (* No-op *)
  | INSTR_Comment _ => tc

  (* Op: result taint = expression taint + PC taint *)
  | INSTR_Op op =>
      let te := calc_taint_exp op tr in
      let rt := join_taints te pc in
      mk_tcfg pc (maybe_update_treg iid rt tr) ob

  (* Load: address is observable; loaded value tainted by address + PC *)
  | INSTR_Load _ ptr _ =>
      let te := calc_taint_texp ptr tr in
      let rt := join_taints te pc in
      let ob' := join_taints (join_taints te pc) ob in
      mk_tcfg pc (maybe_update_treg iid rt tr) ob'

  (* Store: address is observable; no register result *)
  | INSTR_Store _val ptr _ =>
      let te := calc_taint_texp ptr tr in
      let ob' := join_taints (join_taints te pc) ob in
      mk_tcfg pc tr ob'

  (* Alloca: fresh pointer, tainted only by PC *)
  | INSTR_Alloca _ _ =>
      mk_tcfg pc (maybe_update_treg iid pc tr) ob

  (* Call: result tainted by fn + all args + PC *)
  | INSTR_Call fn args _ =>
      let fn_t := calc_taint_texp fn tr in
      let args_t := List.fold_left
                      (fun acc '(te, _) => join_taints acc (calc_taint_texp te tr))
                      args [] in
      let rt := join_taints (join_taints fn_t args_t) pc in
      mk_tcfg pc (maybe_update_treg iid rt tr) ob

  (* Unhandled: no taint effect *)
  | INSTR_Fence _ _
  | INSTR_AtomicCmpXchg _
  | INSTR_AtomicRMW _
  | INSTR_VAArg _ _
  | INSTR_LandingPad => tc
  end.

(** Propagate taint through a phi node.
    Selects the incoming value matching from_blk. *)
Definition taint_phi (id : local_id) (p : phi typ) (from_blk : block_id) (tc : tcfg) : tcfg :=
  let '(Phi _ args) := p in
  let te := match List.find (fun '(bid, _) => raw_id_eqb bid from_blk) args with
            | Some (_, e) => calc_taint_exp e (treg tc)
            | None => []
            end in
  let rt := join_taints te (tpc tc) in
  mk_tcfg (tpc tc) (treg_update (treg tc) id rt) (tobs tc).

(** Propagate taint through a terminator. *)
Definition taint_term (t : terminator typ) (tc : tcfg) : tcfg :=
  let tr := treg tc in
  let pc := tpc tc in
  let ob := tobs tc in
  match t with
  (* Conditional branch: condition is observable, taints PC *)
  | TERM_Br v _ _ =>
      let te := calc_taint_texp v tr in
      let pc' := join_taints te pc in
      let ob' := join_taints pc' ob in
      mk_tcfg pc' tr ob'

  (* Unconditional branch: no taint effect *)
  | TERM_Br_1 _ => tc

  (* Switch: condition is observable, taints PC *)
  | TERM_Switch v _ _ =>
      let te := calc_taint_texp v tr in
      let pc' := join_taints te pc in
      let ob' := join_taints pc' ob in
      mk_tcfg pc' tr ob'

  (* Return, indirect branch, resume, invoke, unreachable: no taint effect *)
  | TERM_Ret _
  | TERM_Ret_void
  | TERM_IndirectBr _ _
  | TERM_Resume _
  | TERM_Invoke _ _ _ _
  | TERM_Unreachable => tc
  end.

(* ================================================================= *)
(** ** Block, Function, and Program-Level Taint Analysis               *)
(* ================================================================= *)

(** Process one block: phis, then instructions, then terminator. *)
Definition taint_block (b : block typ) (from_blk : block_id) (tc : tcfg) : tcfg :=
  let tc1 := List.fold_left
               (fun tc '(id, p) => taint_phi id p from_blk tc)
               (blk_phis b) tc in
  let tc2 := List.fold_left
               (fun tc '(iid, i) => taint_instr iid i tc)
               (blk_code b) tc1 in
  taint_term (blk_term b) tc2.

(** Find a block by its id in a list of blocks. *)
Definition find_block (blocks : list (block typ)) (bid : block_id)
  : option (block typ) :=
  List.find (fun b => raw_id_eqb (blk_id b) bid) blocks.

(** Get successor block ids from a terminator. *)
Definition term_successors (t : terminator typ) : list block_id :=
  match t with
  | TERM_Br _ br1 br2 => [br1; br2]
  | TERM_Br_1 br => [br]
  | TERM_Switch _ default_dest brs => default_dest :: List.map snd brs
  | TERM_IndirectBr _ brs => brs
  | TERM_Invoke _ _ to_label unwind_label => [to_label; unwind_label]
  | TERM_Ret _ | TERM_Ret_void | TERM_Resume _ | TERM_Unreachable => []
  end.

(** Worklist-based taint analysis over a CFG with fuel.
    Processes blocks in BFS order, adding successors to the worklist.
    Both branches of conditionals are explored (may-analysis). *)
Fixpoint taint_cfg (fuel : nat) (blocks : list (block typ))
                   (worklist : list (block_id * block_id))
                   (tc : tcfg) : tcfg :=
  match fuel, worklist with
  | _, [] => tc
  | O, _ => tc
  | S fuel', (cur, from) :: rest =>
      match find_block blocks cur with
      | None => taint_cfg fuel' blocks rest tc
      | Some b =>
          let tc' := taint_block b from tc in
          let succs := term_successors (blk_term b) in
          let new_work := List.map (fun s => (s, blk_id b)) succs in
          taint_cfg fuel' blocks (rest ++ new_work) tc'
      end
  end.

(** Taint-analyze a function definition.
    secret_args: list of parameter raw_ids that are secret (tainted by themselves). *)
Definition taint_function (d : definition typ (block typ * list (block typ)))
                          (secret_args : list raw_id) : taint :=
  let '(entry, rest) := df_instrs d in
  let blocks := entry :: rest in
  let entry_id := blk_id entry in
  let init_treg := List.map (fun id => (id, [id])) secret_args in
  let init_tc := mk_tcfg [] init_treg [] in
  let fuel := 100 * List.length blocks in
  let final_tc := taint_cfg fuel blocks [(entry_id, entry_id)] init_tc in
  tobs final_tc.

(** Top-level: taint-analyze a program by finding main and treating
    all its arguments as secret. Returns the final tobs. *)
Definition taint_program
  (prog : list (toplevel_entity typ (block typ * list (block typ)))) : taint :=
  match List.find (fun tle =>
    match tle with
    | TLE_Definition d => raw_id_eqb (dc_name (df_prototype d)) (Name "main")
    | _ => false
    end) prog with
  | Some (TLE_Definition d) => taint_function d (df_args d)
  | _ => []
  end.

(** Does the program leak the secret through observable behavior? *)
Definition secret_is_leaked
  (prog : list (toplevel_entity typ (block typ * list (block typ)))) : bool :=
  match taint_program prog with
  | [] => false
  | _ => true
  end.
