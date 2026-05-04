(** * Pure AST Taint Tracking for Vellvm NI Testing (Legacy — Layer 1)

    This file contains the original static (pure AST) taint tracker.
    It walks LLVM IR AST without executing and computes taint purely
    from syntactic structure. No memory taint tracking (tmem is always empty).

    LEGACY: This file is kept for reference. The active taint tracker
    is TaintTrackingSemantic.v which uses dynamic (execution-based) taint
    tracking with memory taint via concrete addresses (Option B).

    Limitations of this approach:
    - No memory taint: Load taint uses addr_taint + pc_taint only, not tmem[addr]
    - Explores both branches of conditionals (over-approximate may-analysis)
    - Cannot generate per-arg public-equivalent inputs (coarse bool result)

    For the shared types and core taint operations (taint, tstate, calc_taint_exp,
    join_taints, etc.), see TaintTrackingSemantic.v which defines them and is
    imported by this file.
*)

From Stdlib Require Import List String ZArith Bool.
Import ListNotations.

From Vellvm Require Import
  Syntax.LLVMAst
  Syntax.AstLib.

From Vellvm.NI Require Import TaintTrackingSemantic.

(* ================================================================= *)
(** ** Legacy Layer 1: Pure AST Taint Analysis                        *)
(* ================================================================= *)

(** These are re-exports / aliases for the polymorphic functions
    defined in TaintTrackingSemantic.v. They are provided here for
    backward compatibility with code that imported TaintTrackingPure. *)

(** Instantiations for typ *)
Definition calc_taint_exp_typ_legacy := @calc_taint_exp typ.
Definition taint_instr_pure_typ := @taint_instr_pure typ.
Definition taint_block_gen_typ := @taint_block_gen typ.
Definition taint_cfg_gen_typ := @taint_cfg_gen typ.
Definition taint_function_gen_typ := @taint_function_gen typ.
Definition taint_program_gen_typ := @taint_program_gen typ.
Definition secret_is_leaked_gen_typ := @secret_is_leaked_gen typ.

(** Instantiations for dtyp *)
From Vellvm Require Import Syntax.DynamicTypes.
Definition calc_taint_exp_dtyp_legacy := @calc_taint_exp dtyp.
Definition taint_instr_pure_dtyp := @taint_instr_pure dtyp.
Definition secret_is_leaked_gen_dtyp := @secret_is_leaked_gen dtyp.
