(** * Unit Tests for Taint Tracker
    Tests the pure functions in TaintTrackingSemantic.v:
    - tmem_lookup / tmem_update (memory taint map)
    - treg_lookup / treg_update (register taint map)
    - join_taints (taint union)
    - calc_taint_exp (expression taint)
    - @taint_instr_pure typ (instruction taint)
    - taint_term_gen (terminator taint)
    - taint_phi_gen (phi node taint)
    - taint_load_with_addr / taint_store_with_addr (Option B memory taint)
    - taint_block_gen / taint_cfg_gen (block/CFG level)
    - init_tstate_with_sources / taint_program_gen (end-to-end)
*)

From Stdlib Require Import List String ZArith Bool.
Import ListNotations.

From Vellvm Require Import
  Syntax.LLVMAst
  Syntax.AstLib.

From Vellvm.QC Require Import TaintTrackingSemantic.

Open Scope string_scope.
Open Scope Z_scope.

(* ================================================================= *)
(** ** Helper abbreviations for constructing test data                 *)
(* ================================================================= *)

Definition x := Name "x".
Definition y := Name "y".
Definition secret := Name "secret".
Definition arg1 := Name "arg1".
Definition arg2 := Name "arg2".
Definition p := Name "p".

(** Shorthand for typed expression with dummy type *)
Definition texp_local (id : raw_id) : texp typ :=
  (TYPE_I 32, EXP_Ident (ID_Local id)).

Definition texp_int (n : int_ast) : texp typ :=
  (TYPE_I 32, EXP_Integer n).

(** Build a simple tstate *)
Definition ts_with_regs (regs : list (raw_id * taint)) : tstate :=
  mk_tstate [] regs [] [].

Definition ts_with_regs_pc (regs : list (raw_id * taint)) (pc : taint) : tstate :=
  mk_tstate pc regs [] [].

Definition ts_with_regs_mem (regs : list (raw_id * taint)) (mem : tmem_map) : tstate :=
  mk_tstate [] regs [] mem.

Definition ts_full (pc : taint) (regs : list (raw_id * taint))
  (obs : taint) (mem : tmem_map) : tstate :=
  mk_tstate pc regs obs mem.

(* ================================================================= *)
(** ** 1. Memory Taint Map (tmem_lookup / tmem_update)                 *)
(* ================================================================= *)

(** Lookup in empty map returns empty taint. *)
Example tmem_lookup_empty :
  tmem_lookup [] 100 = [].
Proof. reflexivity. Qed.

(** After update, lookup at same address returns the stored taint. *)
Example tmem_update_then_lookup_same :
  tmem_lookup (tmem_update [] 100 [secret]) 100 = [secret].
Proof. reflexivity. Qed.

(** Lookup at different address still returns empty. *)
Example tmem_update_then_lookup_diff :
  tmem_lookup (tmem_update [] 100 [secret]) 200 = [].
Proof. reflexivity. Qed.

(** Multiple updates: most recent wins (shadowing). *)
Example tmem_update_shadow :
  let tm := tmem_update (tmem_update [] 100 [secret]) 100 [arg1] in
  tmem_lookup tm 100 = [arg1].
Proof. reflexivity. Qed.

(** Multiple updates at different addresses are independent. *)
Example tmem_update_independent :
  let tm := tmem_update (tmem_update [] 100 [secret]) 200 [arg1] in
  (tmem_lookup tm 100 = [secret]) /\ (tmem_lookup tm 200 = [arg1]).
Proof. split; reflexivity. Qed.

(* ================================================================= *)
(** ** 2. Register Taint Map (treg_lookup / treg_update)               *)
(* ================================================================= *)

(** Lookup in empty register map returns empty taint. *)
Example treg_lookup_empty :
  treg_lookup [] x = [].
Proof. reflexivity. Qed.

(** After update, lookup returns the stored taint. *)
Example treg_update_then_lookup :
  treg_lookup (treg_update [] x [secret]) x = [secret].
Proof. reflexivity. Qed.

(** Lookup of a different register returns empty. *)
Example treg_update_then_lookup_diff :
  treg_lookup (treg_update [] x [secret]) y = [].
Proof. reflexivity. Qed.

(** Most recent update shadows earlier ones. *)
Example treg_update_shadow :
  let tr := treg_update (treg_update [] x [secret]) x [arg1] in
  treg_lookup tr x = [arg1].
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** 3. Taint Join (join_taints)                                     *)
(* ================================================================= *)

(** Join of two empty taints is empty. *)
Example join_empty :
  join_taints [] [] = [].
Proof. reflexivity. Qed.

(** Join with empty is identity. *)
Example join_left_id :
  join_taints [secret] [] = [secret].
Proof. reflexivity. Qed.

Example join_right_id :
  join_taints [] [secret] = [secret].
Proof. reflexivity. Qed.

(** Join of two different taints produces union. *)
Example join_different :
  let result := join_taints [secret] [arg1] in
  existsb (raw_id_eqb secret) result = true /\
  existsb (raw_id_eqb arg1) result = true.
Proof. split; reflexivity. Qed.

(** Join deduplicates. *)
Example join_dedup :
  join_taints [secret] [secret] = [secret].
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** 4. Expression Taint (calc_taint_exp)                            *)
(* ================================================================= *)

(** Integer constant has no taint. *)
Example exp_integer_no_taint :
  calc_taint_exp_typ (EXP_Integer 42) [] = [].
Proof. reflexivity. Qed.

(** Null has no taint. *)
Example exp_null_no_taint :
  calc_taint_exp_typ EXP_Null [] = [].
Proof. reflexivity. Qed.

(** Undef has no taint. *)
Example exp_undef_no_taint :
  calc_taint_exp_typ EXP_Undef [] = [].
Proof. reflexivity. Qed.

(** Local variable reference looks up register taint. *)
Example exp_local_var_tainted :
  calc_taint_exp_typ (EXP_Ident (ID_Local secret)) [(secret, [secret])] = [secret].
Proof. reflexivity. Qed.

(** Local variable not in register map has no taint. *)
Example exp_local_var_untainted :
  calc_taint_exp_typ (EXP_Ident (ID_Local x)) [] = [].
Proof. reflexivity. Qed.

(** Global variable reference has no taint. *)
Example exp_global_no_taint :
  calc_taint_exp_typ (EXP_Ident (ID_Global (Name "foo"))) [(Name "foo", [secret])] = [].
Proof. reflexivity. Qed.

(** Binary op: taint is union of operands. *)
Example exp_binop_joins :
  let tr := [(x, [secret]); (y, [arg1])] in
  let result := calc_taint_exp_typ (OP_IBinop (Add false false) (TYPE_I 32)
                  (EXP_Ident (ID_Local x)) (EXP_Ident (ID_Local y))) tr in
  existsb (raw_id_eqb secret) result = true /\
  existsb (raw_id_eqb arg1) result = true.
Proof. split; reflexivity. Qed.

(** Binary op with constant: only variable's taint. *)
Example exp_binop_with_const :
  let tr := [(x, [secret])] in
  calc_taint_exp_typ (OP_IBinop (Add false false) (TYPE_I 32)
                  (EXP_Ident (ID_Local x)) (EXP_Integer 42)) tr = [secret].
Proof. reflexivity. Qed.

(** ICmp: taint is union of operands. *)
Example exp_icmp_joins :
  let tr := [(x, [secret])] in
  calc_taint_exp_typ (OP_ICmp Sgt (TYPE_I 32)
                  (EXP_Ident (ID_Local x)) (EXP_Integer 50)) tr = [secret].
Proof. reflexivity. Qed.

(** Conversion: taint passes through. *)
Example exp_conversion_passthrough :
  let tr := [(x, [secret])] in
  calc_taint_exp_typ (OP_Conversion Sext (TYPE_I 32)
                  (EXP_Ident (ID_Local x)) (TYPE_I 64)) tr = [secret].
Proof. reflexivity. Qed.

(** Select: joins condition and both branches. *)
Example exp_select_joins_all :
  let tr := [(x, [secret]); (y, [arg1])] in
  let result := calc_taint_exp_typ
    (OP_Select (TYPE_I 1, EXP_Ident (ID_Local x))
               (TYPE_I 32, EXP_Integer 1)
               (TYPE_I 32, EXP_Ident (ID_Local y))) tr in
  existsb (raw_id_eqb secret) result = true /\
  existsb (raw_id_eqb arg1) result = true.
Proof. split; reflexivity. Qed.

(* ================================================================= *)
(** ** 5. Instruction Taint (@taint_instr_pure typ)                         *)
(* ================================================================= *)

(** Add: result taint = operand taints + pc taint. *)
Example instr_add_taint :
  let ts := ts_with_regs [(x, [secret])] in
  let ts' := @taint_instr_pure typ (IId y) (INSTR_Op
    (OP_IBinop (Add false false) (TYPE_I 32)
      (EXP_Ident (ID_Local x)) (EXP_Integer 1))) ts in
  treg_lookup (ts_tregs ts') y = [secret].
Proof. reflexivity. Qed.

(** Add with pc taint: result includes pc taint. *)
Example instr_add_with_pc :
  let ts := ts_with_regs_pc [(x, [])] [secret] in
  let ts' := @taint_instr_pure typ (IId y) (INSTR_Op
    (OP_IBinop (Add false false) (TYPE_I 32)
      (EXP_Ident (ID_Local x)) (EXP_Integer 1))) ts in
  treg_lookup (ts_tregs ts') y = [secret].
Proof. reflexivity. Qed.

(** Add of two tainted values: result joins both. *)
Example instr_add_joins :
  let ts := ts_with_regs [(x, [secret]); (y, [arg1])] in
  let ts' := @taint_instr_pure typ (IId p) (INSTR_Op
    (OP_IBinop (Add false false) (TYPE_I 32)
      (EXP_Ident (ID_Local x)) (EXP_Ident (ID_Local y)))) ts in
  let rt := treg_lookup (ts_tregs ts') p in
  existsb (raw_id_eqb secret) rt = true /\
  existsb (raw_id_eqb arg1) rt = true.
Proof. split; reflexivity. Qed.

(** Alloca: result taint = pc taint only. *)
Example instr_alloca_pc_only :
  let ts := ts_with_regs_pc [] [secret] in
  let ts' := @taint_instr_pure typ (IId p) (INSTR_Alloca (TYPE_I 32) []) ts in
  treg_lookup (ts_tregs ts') p = [secret].
Proof. reflexivity. Qed.

(** Alloca with no pc taint: result is empty. *)
Example instr_alloca_no_pc :
  let ts := ts_with_regs [(x, [secret])] in
  let ts' := @taint_instr_pure typ (IId p) (INSTR_Alloca (TYPE_I 32) []) ts in
  treg_lookup (ts_tregs ts') p = [].
Proof. reflexivity. Qed.

(** Load (pure, no memory taint): result = ptr taint + pc.
    Also updates tobs because address is observable. *)
Example instr_load_pure_tainted_ptr :
  let ts := ts_with_regs [(p, [secret])] in
  let ts' := @taint_instr_pure typ (IId x) (INSTR_Load (TYPE_I 32)
    (TYPE_Pointer (Some (TYPE_I 32)), EXP_Ident (ID_Local p)) []) ts in
  (* Result register gets ptr taint *)
  treg_lookup (ts_tregs ts') x = [secret] /\
  (* Observation taint updated because address is observable *)
  ts_tobs ts' = [secret].
Proof. split; reflexivity. Qed.

(** Load (pure) with untainted ptr: no taint propagated. *)
Example instr_load_pure_untainted :
  let ts := ts_with_regs [(p, [])] in
  let ts' := @taint_instr_pure typ (IId x) (INSTR_Load (TYPE_I 32)
    (TYPE_Pointer (Some (TYPE_I 32)), EXP_Ident (ID_Local p)) []) ts in
  treg_lookup (ts_tregs ts') x = [] /\
  ts_tobs ts' = [].
Proof. split; reflexivity. Qed.

(** Store (pure): only address taint flows to tobs. *)
Example instr_store_pure_tainted_addr :
  let ts := ts_with_regs [(p, [secret]); (x, [arg1])] in
  let ts' := @taint_instr_pure typ (IVoid 0%Z) (INSTR_Store
    (TYPE_I 32, EXP_Ident (ID_Local x))
    (TYPE_Pointer (Some (TYPE_I 32)), EXP_Ident (ID_Local p)) []) ts in
  (* Address is observable: ptr taint flows to tobs *)
  ts_tobs ts' = [secret] /\
  (* Pure store does NOT update tmem *)
  ts_tmem ts' = [].
Proof. split; reflexivity. Qed.

(** Store (pure) with untainted address: no tobs update. *)
Example instr_store_pure_untainted_addr :
  let ts := ts_with_regs [(p, []); (x, [secret])] in
  let ts' := @taint_instr_pure typ (IVoid 0%Z) (INSTR_Store
    (TYPE_I 32, EXP_Ident (ID_Local x))
    (TYPE_Pointer (Some (TYPE_I 32)), EXP_Ident (ID_Local p)) []) ts in
  (* Untainted address: nothing flows to tobs *)
  ts_tobs ts' = [] /\
  (* Pure store does NOT update tmem *)
  ts_tmem ts' = [].
Proof. split; reflexivity. Qed.

(** Void instruction (IVoid) does not create register binding. *)
Example instr_void_no_reg :
  let ts := ts_with_regs [] in
  let ts' := @taint_instr_pure typ (IVoid 0%Z) (INSTR_Op (EXP_Integer 42)) ts in
  ts_tregs ts' = [].
Proof. reflexivity. Qed.

(** Comment instruction is a no-op. *)
Example instr_comment_noop :
  let ts := ts_with_regs_pc [(x, [secret])] [arg1] in
  let ts' := @taint_instr_pure typ (IVoid 0%Z) (INSTR_Comment "hello") ts in
  ts' = ts.
Proof. reflexivity. Qed.

(** Call: conservatively taints result with all arg taints + fn taint + pc. *)
Example instr_call_conservative :
  let ts := ts_with_regs [(x, [secret]); (y, [arg1])] in
  let ts' := @taint_instr_pure typ (IId p)
    (INSTR_Call (TYPE_I 32, EXP_Ident (ID_Global (Name "f")))
      [((TYPE_I 32, EXP_Ident (ID_Local x)), []);
       ((TYPE_I 32, EXP_Ident (ID_Local y)), [])] []) ts in
  let rt := treg_lookup (ts_tregs ts') p in
  existsb (raw_id_eqb secret) rt = true /\
  existsb (raw_id_eqb arg1) rt = true.
Proof. split; reflexivity. Qed.

(* ================================================================= *)
(** ** 6. Terminator Taint (taint_term_gen)                            *)
(* ================================================================= *)

(** Conditional branch: condition taint flows to tpc and tobs. *)
Example term_br_tainted_cond :
  let ts := ts_with_regs [(x, [secret])] in
  let ts' := @taint_term_gen typ
    (TERM_Br (TYPE_I 1, EXP_Ident (ID_Local x))
             (Name "then") (Name "else")) ts in
  (* Condition taint flows to PC taint *)
  ts_tpc ts' = [secret] /\
  (* Branch direction is observable *)
  ts_tobs ts' = [secret].
Proof. split; reflexivity. Qed.

(** Conditional branch with untainted condition: no tpc/tobs update. *)
Example term_br_untainted_cond :
  let ts := ts_with_regs [(x, [])] in
  let ts' := @taint_term_gen typ
    (TERM_Br (TYPE_I 1, EXP_Ident (ID_Local x))
             (Name "then") (Name "else")) ts in
  ts_tpc ts' = [] /\
  ts_tobs ts' = [].
Proof. split; reflexivity. Qed.

(** Conditional branch with existing pc taint: pc taint is joined. *)
Example term_br_joins_pc :
  let ts := ts_with_regs_pc [(x, [secret])] [arg1] in
  let ts' := @taint_term_gen typ
    (TERM_Br (TYPE_I 1, EXP_Ident (ID_Local x))
             (Name "then") (Name "else")) ts in
  existsb (raw_id_eqb secret) (ts_tpc ts') = true /\
  existsb (raw_id_eqb arg1) (ts_tpc ts') = true.
Proof. split; reflexivity. Qed.

(** Unconditional branch: no taint change. *)
Example term_br1_noop :
  let ts := ts_with_regs_pc [(x, [secret])] [arg1] in
  let ts' := @taint_term_gen typ (TERM_Br_1 (Name "next")) ts in
  ts' = ts.
Proof. reflexivity. Qed.

(** Ret: no taint change. *)
Example term_ret_noop :
  let ts := ts_with_regs [(x, [secret])] in
  let ts' := @taint_term_gen typ (TERM_Ret (TYPE_I 32, EXP_Ident (ID_Local x))) ts in
  ts' = ts.
Proof. reflexivity. Qed.

(** Switch: condition taint flows to tpc and tobs (like br). *)
Example term_switch_tainted :
  let ts := ts_with_regs [(x, [secret])] in
  let ts' := @taint_term_gen typ
    (TERM_Switch (TYPE_I 32, EXP_Ident (ID_Local x))
                 (Name "default") []) ts in
  ts_tpc ts' = [secret] /\
  ts_tobs ts' = [secret].
Proof. split; reflexivity. Qed.

(* ================================================================= *)
(** ** 7. Option B: Memory Taint (taint_load/store_with_addr)          *)
(* ================================================================= *)

(** Store with addr: value taint stored in tmem. *)
Example store_with_addr_stores_taint :
  let ts := ts_with_regs [(x, [secret]); (p, [])] in
  let ts' := @taint_store_with_addr typ
    (EXP_Ident (ID_Local p)) (EXP_Ident (ID_Local x)) 100 ts in
  tmem_lookup (ts_tmem ts') 100 = [secret].
Proof. reflexivity. Qed.

(** Store with addr: pc taint also stored in tmem. *)
Example store_with_addr_includes_pc :
  let ts := ts_with_regs_pc [(x, []); (p, [])] [secret] in
  let ts' := @taint_store_with_addr typ
    (EXP_Ident (ID_Local p)) (EXP_Ident (ID_Local x)) 100 ts in
  tmem_lookup (ts_tmem ts') 100 = [secret].
Proof. reflexivity. Qed.

(** Store with tainted address: address taint flows to tobs. *)
Example store_with_addr_tainted_ptr_obs :
  let ts := ts_with_regs [(x, []); (p, [secret])] in
  let ts' := @taint_store_with_addr typ
    (EXP_Ident (ID_Local p)) (EXP_Ident (ID_Local x)) 100 ts in
  ts_tobs ts' = [secret].
Proof. reflexivity. Qed.

(** Store with untainted address and value: no tobs, no tmem taint. *)
Example store_with_addr_all_clean :
  let ts := ts_with_regs [(x, []); (p, [])] in
  let ts' := @taint_store_with_addr typ
    (EXP_Ident (ID_Local p)) (EXP_Ident (ID_Local x)) 100 ts in
  ts_tobs ts' = [] /\
  tmem_lookup (ts_tmem ts') 100 = [].
Proof. split; reflexivity. Qed.

(** Load with addr: memory taint propagates to result. *)
Example load_with_addr_reads_tmem :
  let tm := tmem_update [] 100 [secret] in
  let ts := ts_with_regs_mem [(p, [])] tm in
  let ts' := @taint_load_with_addr typ (IId x) (EXP_Ident (ID_Local p)) 100 ts in
  treg_lookup (ts_tregs ts') x = [secret].
Proof. reflexivity. Qed.

(** Load with addr: untainted memory = no result taint. *)
Example load_with_addr_clean_mem :
  let ts := ts_with_regs [(p, [])] in
  let ts' := @taint_load_with_addr typ (IId x) (EXP_Ident (ID_Local p)) 100 ts in
  treg_lookup (ts_tregs ts') x = [].
Proof. reflexivity. Qed.

(** Load with tainted pointer: ptr taint in result AND tobs. *)
Example load_with_addr_tainted_ptr :
  let ts := ts_with_regs [(p, [secret])] in
  let ts' := @taint_load_with_addr typ (IId x) (EXP_Ident (ID_Local p)) 100 ts in
  treg_lookup (ts_tregs ts') x = [secret] /\
  ts_tobs ts' = [secret].
Proof. split; reflexivity. Qed.

(** Load with addr: result = join(ptr_taint, mem_taint, pc). *)
Example load_with_addr_joins_all :
  let tm := tmem_update [] 100 [arg1] in
  let ts := ts_full [arg2] [(p, [secret])] [] tm in
  let ts' := @taint_load_with_addr typ (IId x) (EXP_Ident (ID_Local p)) 100 ts in
  let rt := treg_lookup (ts_tregs ts') x in
  existsb (raw_id_eqb secret) rt = true /\  (* from ptr *)
  existsb (raw_id_eqb arg1) rt = true /\    (* from mem *)
  existsb (raw_id_eqb arg2) rt = true.      (* from pc *)
Proof. split; [|split]; reflexivity. Qed.

(* ================================================================= *)
(** ** 8. Store-then-Load: memory taint round-trip                     *)
(* ================================================================= *)

(** Secret stored then loaded back: taint propagates through memory. *)
Example store_then_load_propagates :
  let ts0 := ts_with_regs [(x, [secret]); (p, [])] in
  (* Store secret value at address 100 *)
  let ts1 := @taint_store_with_addr typ
    (EXP_Ident (ID_Local p)) (EXP_Ident (ID_Local x)) 100 ts0 in
  (* Load from address 100 into y *)
  let ts2 := @taint_load_with_addr typ (IId y) (EXP_Ident (ID_Local p)) 100 ts1 in
  (* y should carry secret's taint (from memory) *)
  treg_lookup (ts_tregs ts2) y = [secret].
Proof. reflexivity. Qed.

(** Public stored then loaded: no taint propagates. *)
Example store_then_load_public :
  let ts0 := ts_with_regs [(x, []); (p, [])] in
  let ts1 := @taint_store_with_addr typ
    (EXP_Ident (ID_Local p)) (EXP_Ident (ID_Local x)) 100 ts0 in
  let ts2 := @taint_load_with_addr typ (IId y) (EXP_Ident (ID_Local p)) 100 ts1 in
  treg_lookup (ts_tregs ts2) y = [].
Proof. reflexivity. Qed.

(** Secret stored, then overwritten with public, then loaded: taint gone. *)
Example store_overwrite_clears_taint :
  let ts0 := ts_with_regs [(x, [secret]); (y, []); (p, [])] in
  (* Store secret at 100 *)
  let ts1 := @taint_store_with_addr typ
    (EXP_Ident (ID_Local p)) (EXP_Ident (ID_Local x)) 100 ts0 in
  (* Overwrite with public value at 100 *)
  let ts2 := @taint_store_with_addr typ
    (EXP_Ident (ID_Local p)) (EXP_Ident (ID_Local y)) 100 ts1 in
  (* Load from 100 *)
  let ts3 := @taint_load_with_addr typ (IId (Name "z"))
    (EXP_Ident (ID_Local p)) 100 ts2 in
  (* z should be clean — overwrite cleared the taint *)
  treg_lookup (ts_tregs ts3) (Name "z") = [].
Proof. reflexivity. Qed.

(** Two different addresses: taint is independent. *)
Example store_different_addrs :
  let ts0 := ts_with_regs [(x, [secret]); (y, [arg1]); (p, [])] in
  let ts1 := @taint_store_with_addr typ
    (EXP_Ident (ID_Local p)) (EXP_Ident (ID_Local x)) 100 ts0 in
  let ts2 := @taint_store_with_addr typ
    (EXP_Ident (ID_Local p)) (EXP_Ident (ID_Local y)) 200 ts1 in
  (* Load from 100: gets secret *)
  let ts3a := @taint_load_with_addr typ (IId (Name "a"))
    (EXP_Ident (ID_Local p)) 100 ts2 in
  (* Load from 200: gets arg1 *)
  let ts3b := @taint_load_with_addr typ (IId (Name "b"))
    (EXP_Ident (ID_Local p)) 200 ts2 in
  treg_lookup (ts_tregs ts3a) (Name "a") = [secret] /\
  treg_lookup (ts_tregs ts3b) (Name "b") = [arg1].
Proof. split; reflexivity. Qed.

(* ================================================================= *)
(** ** 9. PC Taint (implicit flow through branches)                    *)
(* ================================================================= *)

(** After secret-dependent branch, store in branch body
    has its tobs tainted by tpc. *)
Example pc_taint_contaminates_store_obs :
  (* Simulate: br i1 %cmp (where cmp depends on secret) *)
  let ts0 := ts_with_regs [(x, [secret])] in
  let ts1 := @taint_term_gen typ
    (TERM_Br (TYPE_I 1, EXP_Ident (ID_Local x))
             (Name "then") (Name "else")) ts0 in
  (* Now in branch body, tpc = [secret] *)
  (* Store with public address — tpc should flow to tobs *)
  let ts2 := @taint_store_with_addr typ
    (EXP_Ident (ID_Local p)) (EXP_Integer 42) 100 ts1 in
  (* tobs should contain secret because of tpc *)
  existsb (raw_id_eqb secret) (ts_tobs ts2) = true.
Proof. reflexivity. Qed.

(** After secret-dependent branch, store value is tainted by tpc in tmem. *)
Example pc_taint_contaminates_stored_value :
  let ts0 := ts_with_regs [(x, [secret]); (p, [])] in
  let ts1 := @taint_term_gen typ
    (TERM_Br (TYPE_I 1, EXP_Ident (ID_Local x))
             (Name "then") (Name "else")) ts0 in
  (* Store public value with public ptr — but tpc is [secret] *)
  let ts2 := @taint_store_with_addr typ
    (EXP_Ident (ID_Local p)) (EXP_Integer 42) 100 ts1 in
  (* Memory at 100 should carry tpc taint *)
  tmem_lookup (ts_tmem ts2) 100 = [secret].
Proof. reflexivity. Qed.

(** After secret-dependent branch, load propagates tpc to result. *)
Example pc_taint_contaminates_load_result :
  let ts0 := ts_with_regs_pc [(p, [])] [secret] in
  let ts' := @taint_load_with_addr typ (IId x) (EXP_Ident (ID_Local p)) 100 ts0 in
  treg_lookup (ts_tregs ts') x = [secret].
Proof. reflexivity. Qed.

(** After secret-dependent branch, arithmetic result carries tpc. *)
Example pc_taint_contaminates_arithmetic :
  let ts0 := ts_with_regs_pc [] [secret] in
  let ts' := @taint_instr_pure typ (IId x) (INSTR_Op
    (OP_IBinop (Add false false) (TYPE_I 32)
      (EXP_Integer 1) (EXP_Integer 2))) ts0 in
  treg_lookup (ts_tregs ts') x = [secret].
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** 10. Phi Node Taint (taint_phi_gen)                              *)
(* ================================================================= *)

(** Phi selects taint from the correct predecessor. *)
Example phi_selects_from_pred :
  let ts := ts_with_regs [(x, [secret]); (y, [arg1])] in
  let phi := Phi (TYPE_I 32)
    [(Name "bb1", EXP_Ident (ID_Local x));
     (Name "bb2", EXP_Ident (ID_Local y))] in
  (* Coming from bb1: should pick x's taint *)
  let ts1 := @taint_phi_gen typ (Name "result") phi (Name "bb1") ts in
  treg_lookup (ts_tregs ts1) (Name "result") = [secret].
Proof. reflexivity. Qed.

Example phi_selects_from_other_pred :
  let ts := ts_with_regs [(x, [secret]); (y, [arg1])] in
  let phi := Phi (TYPE_I 32)
    [(Name "bb1", EXP_Ident (ID_Local x));
     (Name "bb2", EXP_Ident (ID_Local y))] in
  (* Coming from bb2: should pick y's taint *)
  let ts2 := @taint_phi_gen typ (Name "result") phi (Name "bb2") ts in
  treg_lookup (ts_tregs ts2) (Name "result") = [arg1].
Proof. reflexivity. Qed.

(** Phi with pc taint: result includes tpc. *)
Example phi_includes_pc :
  let ts := ts_with_regs_pc [(x, [])] [secret] in
  let phi := Phi (TYPE_I 32) [(Name "bb1", EXP_Ident (ID_Local x))] in
  let ts' := @taint_phi_gen typ (Name "result") phi (Name "bb1") ts in
  treg_lookup (ts_tregs ts') (Name "result") = [secret].
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** 11. Init State                                                  *)
(* ================================================================= *)

(** Init state with no sources: everything empty. *)
Example init_empty :
  let ts := init_tstate in
  ts_tpc ts = [] /\ ts_tregs ts = [] /\ ts_tobs ts = [] /\ ts_tmem ts = [].
Proof. split; [|split; [|split]]; reflexivity. Qed.

(** Init state with sources: each source labeled with its own identity. *)
Example init_with_sources :
  let ts := init_tstate_with_sources [secret; arg1] in
  treg_lookup (ts_tregs ts) secret = [secret] /\
  treg_lookup (ts_tregs ts) arg1 = [arg1] /\
  treg_lookup (ts_tregs ts) x = [] /\
  ts_tpc ts = [] /\
  ts_tobs ts = [] /\
  ts_tmem ts = [].
Proof. split; [|split; [|split; [|split; [|split]]]]; reflexivity. Qed.

(* ================================================================= *)
(** ** 12. End-to-End: Tiny Programs (taint_program_gen)                *)
(* ================================================================= *)

(** Helper to build a minimal function definition. *)
Definition mk_test_fn (args : list raw_id) (entry : block typ) (rest : list (block typ))
  : definition typ (block typ * list (block typ)) :=
  mk_definition _
    (mk_declaration
      (Name "main")                          (* name *)
      (TYPE_Function (TYPE_I 32) (List.map (fun _ => TYPE_I 32) args) false) (* type *)
      ([], [])                               (* param_attrs *)
      []                                     (* attrs *)
      []                                     (* annotations *)
    )
    args                                     (* args *)
    (entry, rest).                           (* body *)

(** Build a block without comments *)
Definition mk_blk (id : block_id) (phis : list (local_id * phi typ))
  (code : code typ) (term : terminator typ) : block typ :=
  mk_block id phis code term None.

Definition mk_test_prog (d : definition typ (block typ * list (block typ)))
  : list (toplevel_entity typ (block typ * list (block typ))) :=
  [TLE_Definition d].

(** Program: main(%a) { ret 0 }
    %a not used → not public (= secret, can vary freely). *)
Example e2e_unused_arg :
  let entry := mk_blk (Name "entry") [] []
    (TERM_Ret (TYPE_I 32, EXP_Integer 0)) in
  let prog := mk_test_prog (mk_test_fn [Name "a"] entry []) in
  @taint_public_args_gen typ prog = nil.
Proof. reflexivity. Qed.

(** Program: main(%a) { br %a, then, else }
    %a used in branch → public (affects observations). *)
Example e2e_arg_in_branch :
  let a := Name "a" in
  let entry := mk_blk (Name "entry") []
    []
    (TERM_Br (TYPE_I 1, EXP_Ident (ID_Local a))
             (Name "then") (Name "else")) in
  let blk_then := mk_blk (Name "then") [] []
    (TERM_Ret (TYPE_I 32, EXP_Integer 1)) in
  let blk_else := mk_blk (Name "else") [] []
    (TERM_Ret (TYPE_I 32, EXP_Integer 0)) in
  let prog := mk_test_prog (mk_test_fn [a] entry [blk_then; blk_else]) in
  is_tainted a (@taint_public_args_gen typ prog) = true.
Proof. reflexivity. Qed.

(** Program: main(%a) { %x = add %a, 1; ret %x }
    %a used in arithmetic but not in branch/load/store address → not public. *)
Example e2e_arg_arithmetic_only :
  let a := Name "a" in
  let entry := mk_blk (Name "entry") []
    [(IId x, INSTR_Op (OP_IBinop (Add false false) (TYPE_I 32)
        (EXP_Ident (ID_Local a)) (EXP_Integer 1)))]
    (TERM_Ret (TYPE_I 32, EXP_Ident (ID_Local x))) in
  let prog := mk_test_prog (mk_test_fn [a] entry []) in
  @taint_public_args_gen typ prog = nil.
Proof. reflexivity. Qed.

(** Program: main(%a) { %cmp = icmp %a, 50; br %cmp; then: load %p }
    %a flows into branch → tpc tainted →
    load in branch body has tobs tainted → %a is public. *)
Example e2e_arg_branch_then_load :
  let a := Name "a" in
  let entry := mk_blk (Name "entry") []
    [(IId (Name "cmp"), INSTR_Op (OP_ICmp Sgt (TYPE_I 32)
        (EXP_Ident (ID_Local a)) (EXP_Integer 50)))]
    (TERM_Br (TYPE_I 1, EXP_Ident (ID_Local (Name "cmp")))
             (Name "then") (Name "else")) in
  let blk_then := mk_blk (Name "then") []
    [(IId x, INSTR_Load (TYPE_I 32)
        (TYPE_Pointer (Some (TYPE_I 32)), EXP_Ident (ID_Local p)) [])]
    (TERM_Ret (TYPE_I 32, EXP_Ident (ID_Local x))) in
  let blk_else := mk_blk (Name "else") []
    []
    (TERM_Ret (TYPE_I 32, EXP_Integer 0)) in
  let prog := mk_test_prog (mk_test_fn [a] entry [blk_then; blk_else]) in
  is_tainted a (@taint_public_args_gen typ prog) = true.
Proof. reflexivity. Qed.

(** Program: main(%a, %b) { br %b; then: ret 1; else: ret 0 }
    Only %b used in branch → %b is public, %a is secret. *)
Example e2e_per_arg_classification :
  let a := Name "a" in
  let b := Name "b" in
  let entry := mk_blk (Name "entry") []
    []
    (TERM_Br (TYPE_I 1, EXP_Ident (ID_Local b))
             (Name "then") (Name "else")) in
  let blk_then := mk_blk (Name "then") [] []
    (TERM_Ret (TYPE_I 32, EXP_Integer 1)) in
  let blk_else := mk_blk (Name "else") [] []
    (TERM_Ret (TYPE_I 32, EXP_Integer 0)) in
  let prog := mk_test_prog (mk_test_fn [a; b] entry [blk_then; blk_else]) in
  let public := @taint_public_args_gen typ prog in
  is_tainted b public = true /\   (* %b is public: affects observations *)
  is_tainted a public = false.    (* %a is secret: does not affect observations *)
Proof. split; reflexivity. Qed.

(** Program: main(%a) { store %a, %p }
    %a used as store VALUE — address is public constant.
    Pure AST: address is public → %a not public (pure doesn't track tmem). *)
Example e2e_arg_as_store_value_pure :
  let a := Name "a" in
  let entry := mk_blk (Name "entry") []
    [(IVoid 0%Z, INSTR_Store
        (TYPE_I 32, EXP_Ident (ID_Local a))
        (TYPE_Pointer (Some (TYPE_I 32)), EXP_Ident (ID_Local p)) [])]
    (TERM_Ret (TYPE_I 32, EXP_Integer 0)) in
  let prog := mk_test_prog (mk_test_fn [a] entry []) in
  @taint_public_args_gen typ prog = nil.
Proof. reflexivity. Qed.

(** Program: main(%a) { store 42, %a }
    %a used as store ADDRESS → %a is public (address is observable). *)
Example e2e_arg_as_store_addr :
  let a := Name "a" in
  let entry := mk_blk (Name "entry") []
    [(IVoid 0%Z, INSTR_Store
        (TYPE_I 32, EXP_Integer 42)
        (TYPE_Pointer (Some (TYPE_I 32)), EXP_Ident (ID_Local a)) [])]
    (TERM_Ret (TYPE_I 32, EXP_Integer 0)) in
  let prog := mk_test_prog (mk_test_fn [a] entry []) in
  is_tainted a (@taint_public_args_gen typ prog) = true.
Proof. reflexivity. Qed.

(** Program: main(%a) { %x = load %a }
    %a used as load ADDRESS → %a is public. *)
Example e2e_arg_as_load_addr :
  let a := Name "a" in
  let entry := mk_blk (Name "entry") []
    [(IId x, INSTR_Load (TYPE_I 32)
        (TYPE_Pointer (Some (TYPE_I 32)), EXP_Ident (ID_Local a)) [])]
    (TERM_Ret (TYPE_I 32, EXP_Ident (ID_Local x))) in
  let prog := mk_test_prog (mk_test_fn [a] entry []) in
  is_tainted a (@taint_public_args_gen typ prog) = true.
Proof. reflexivity. Qed.
