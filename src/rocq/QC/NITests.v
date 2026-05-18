(** * NI Soundness QuickChick Test (partition-style)

    Property under test:
      For each randomly generated program [P] with [main(i32 %secret)],
      run the partition-style taint tracker on [P] with one secret value.
      It outputs [TOBS_REGS] (the set of register names in the public
      partition) and [TOBS_ADDRS] (the set of memory addresses).

      The complement of [TOBS_REGS] is the set of register names whose
      values may be varied without changing the observation trace.

      Soundness check:
        if [secret] (the name of [main]'s i32 parameter) is *not* in
        [TOBS_REGS], then two runs with two different secret values
        must produce identical observation traces.

      Counterexample on this property = the tracker is unsound.

    The harness shells out to the [./vellvm] binary because Coq
    extraction cannot directly call the pipeline (different module
    instantiations of [itree L0] generate incompatible OCaml types).
    See [../NI_ARCHITECTURE.md].
*)

From Stdlib Require Import List String ZArith.
Import ListNotations.

From ITree Require Import ITree.

From ExtLib Require Import
     Structures.Monads.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

From Vellvm Require Import
     Utilities
     Syntax
     Syntax.LLVMAst
     Syntax.AstLib
     Semantics
     Handlers.Handlers
     QC.ShowAST
     QC.ReprAST
     QC.GenAST.

Import MonadNotation.
Open Scope monad_scope.

(* Coq's [string] extracts to OCaml's [char list]; this axiom packs that
   list back into a real OCaml [string], suitable for [output_string] etc. *)
Axiom to_caml_str : string -> string.
Extract Constant to_caml_str =>
"fun (s: char list) ->
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
  | [] -> r
  | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)".

(* ================================================================= *)
(** ** Local generator wrapper (mirrors QCVellvm.v's PROG, kept local
       to avoid forcing a build-time QuickChick run from QCVellvm.v).  *)
(* ================================================================= *)

Inductive PROG :=
| Prog : list (toplevel_entity typ (block typ * list (block typ))) -> PROG.

#[global] Instance Show_PROG : Show PROG :=
  { show p := "" (* avoid expensive printing during QC *) }.

Definition gen_PROG_with_secret_nofun : GenLLVM PROG :=
  prog <- gen_llvm_with_secret_nofun ;;
  ret (Prog prog).

(* ================================================================= *)
(** ** Observation trace type                                         *)
(* ================================================================= *)

(** Decoded observation events (see [event_obs] in InterpretationStack.v
    for the encoding). *)
Inductive observation :=
| OLoad   (addr : Z)
| OStore  (addr : Z)
| OBranch (b : bool).

Definition obs_eqb (o1 o2 : observation) : bool :=
  match o1, o2 with
  | OLoad   a1, OLoad   a2 => Z.eqb a1 a2
  | OStore  a1, OStore  a2 => Z.eqb a1 a2
  | OBranch b1, OBranch b2 => Bool.eqb b1 b2
  | _, _ => false
  end.

Fixpoint obs_trace_eqb (t1 t2 : list observation) : bool :=
  match t1, t2 with
  | [], [] => true
  | o1 :: r1, o2 :: r2 => obs_eqb o1 o2 && obs_trace_eqb r1 r2
  | _, _ => false
  end.

Definition show_observation (o : observation) : string :=
  match o with
  | OLoad   a       => "L("  ++ show a ++ ")"
  | OStore  a       => "S("  ++ show a ++ ")"
  | OBranch true    => "Br(T)"
  | OBranch false   => "Br(F)"
  end.

Definition show_obs_trace (t : list observation) : string :=
  "[" ++ String.concat ", " (List.map show_observation t) ++ "]".

(** Decode the [list Z] returned from the framed `OBS_TRACE` section.
    See [event_obs] / [observe_L2] in InterpretationStack.v for the
    encoding convention. *)
Definition z_to_obs (zs : list Z) : list observation :=
  List.map (fun z =>
    if Z.eqb z 1000000 then OBranch true
    else if Z.eqb z 1000001 then OBranch false
    else if Z.ltb z 0 then OStore (Z.opp z)
    else OLoad z) zs.

(* ================================================================= *)
(** ** Shell-out axioms                                               *)
(* ================================================================= *)

(** Take a pre-rendered [.ll] program text (as an OCaml [string]), write
    it to a temp file, run [./vellvm -interpret-obs-args <args> <file>],
    and parse the [---OBS_TRACE_BEGIN/END---] section. Returns [list Z]
    of encoded observation events.

    We pass the program as a [string] (rendered via Coq's [show]
    instance) rather than as a value to avoid pulling [LLVMAst] /
    [Llvm_printer] into the QuickChick-generated OCaml file — those
    modules aren't on QC's compile path. *)
Axiom vellvm_collect_obs_args_str : string -> list Z -> list Z.

Extract Constant vellvm_collect_obs_args_str =>
  "fun prog_str args ->
     let llvm_file =
       Filename.(concat (get_temp_dir_name ()) ""ni_qc_obs.ll"")
     in
     let oc = open_out llvm_file in
     output_string oc prog_str;
     close_out oc;
     let args_str =
       String.concat "","" (List.map
         (fun z -> string_of_int (Big_int_Z.int_of_big_int z)) args)
     in
     let vellvm = try Sys.getenv ""VELLVM_BIN"" with Not_found -> ""./vellvm"" in
     let cmd =
       ""timeout 5 "" ^ vellvm ^ "" -interpret-obs-args "" ^ args_str ^
       "" "" ^ llvm_file ^ "" 2>&1""
     in
     let ic = Unix.open_process_in cmd in
     let buf = Buffer.create 256 in
     (try while true do Buffer.add_channel buf ic 1 done
      with End_of_file -> ());
     let _ = Unix.close_process_in ic in
     let output = Buffer.contents buf in
     let lines = String.split_on_char '\n' output in
     let in_trace = ref false in
     let result = ref [] in
     List.iter (fun line ->
       if line = ""---OBS_TRACE_BEGIN---"" then in_trace := true
       else if line = ""---OBS_TRACE_END---"" then in_trace := false
       else if !in_trace then
         (try result := (Big_int_Z.big_int_of_int (int_of_string line)) :: !result
          with _ -> ())
     ) lines;
     List.rev !result".

Definition vellvm_collect_obs_args
  (prog : list (toplevel_entity typ (block typ * list (block typ))))
  (args : list Z) : list Z :=
  vellvm_collect_obs_args_str (to_caml_str (show prog)) args.

(** Same shell-out shape as above, but for [-taint-track-args]. Parses
    the [---TOBS_REGS_BEGIN/END---] section into a list of Coq strings.
    The companion `TOBS_ADDRS` section is currently ignored — only the
    register-level partition is needed for the soundness check on a
    single-secret-arg program. *)
Axiom vellvm_taint_public_reg_names_str :
  string -> list Z -> list string.

Extract Constant vellvm_taint_public_reg_names_str =>
  "fun prog_str args ->
     let llvm_file =
       Filename.(concat (get_temp_dir_name ()) ""ni_qc_taint.ll"")
     in
     let oc = open_out llvm_file in
     output_string oc prog_str;
     close_out oc;
     let args_str =
       String.concat "","" (List.map
         (fun z -> string_of_int (Big_int_Z.int_of_big_int z)) args)
     in
     let vellvm = try Sys.getenv ""VELLVM_BIN"" with Not_found -> ""./vellvm"" in
     let cmd =
       ""timeout 5 "" ^ vellvm ^ "" -taint-track-args "" ^ args_str ^
       "" "" ^ llvm_file ^ "" 2>&1""
     in
     let ic = Unix.open_process_in cmd in
     let buf = Buffer.create 256 in
     (try while true do Buffer.add_channel buf ic 1 done
      with End_of_file -> ());
     let _ = Unix.close_process_in ic in
     let output = Buffer.contents buf in
     let lines = String.split_on_char '\n' output in
     let in_regs = ref false in
     let regs = ref [] in
     List.iter (fun line ->
       if line = ""---TOBS_REGS_BEGIN---"" then in_regs := true
       else if line = ""---TOBS_REGS_END---"" then in_regs := false
       else if !in_regs && String.length line > 0 then
         let chars = List.init (String.length line)
                       (fun i -> String.get line i)
         in
         regs := chars :: !regs
     ) lines;
     List.rev !regs".

Definition vellvm_taint_public_regs
  (prog : list (toplevel_entity typ (block typ * list (block typ))))
  (args : list Z) : list raw_id :=
  let names :=
    vellvm_taint_public_reg_names_str (to_caml_str (show prog)) args
  in
  List.map LLVMAst.Name names.

(* ================================================================= *)
(** ** Helpers                                                        *)
(* ================================================================= *)

(** Find the name of [main]'s sole [i32] argument, if any. The active
    generator [gen_PROG_with_secret_nofun] produces such a program. *)
Definition find_secret_arg
  (prog : list (toplevel_entity typ (block typ * list (block typ))))
  : option raw_id :=
  let mains :=
    List.fold_left (fun acc tle =>
      match tle with
      | TLE_Definition d =>
          match d.(df_prototype).(dc_name) with
          | LLVMAst.Name s =>
              if String.eqb s "main" then d :: acc else acc
          | _ => acc
          end
      | _ => acc
      end) prog []
  in
  match mains with
  | d :: _ =>
      match d.(df_args) with
      | id :: _ => Some id
      | _ => None
      end
  | _ => None
  end.

Definition raw_id_eqb (x y : raw_id) : bool :=
  if RawIDOrd.eq_dec x y then true else false.

Definition raw_id_in_list (id : raw_id) (l : list raw_id) : bool :=
  List.existsb (raw_id_eqb id) l.

(* ================================================================= *)
(** ** Soundness property                                             *)
(* ================================================================= *)

(** For a generated [P] with [main(i32 %secret)]:
    - Pick two distinct secret values S1, S2.
    - Run the taint tracker with S1 → public register set [pub_regs].
    - If [secret] is in [pub_regs], the program is allowed to behave
      differently across secrets — skip (or check S1 = S1 trivially).
    - If [secret] is *not* in [pub_regs], the tracker claims it's safe.
      Then the observation traces under S1 and S2 must be equal. *)
Definition vellvm_taint_soundness_partition (p : string + PROG) : Checker :=
  match p with
  | inl _msg => checker true     (* generator failure: skip *)
  | inr (Prog prog) =>
      match find_secret_arg prog with
      | None =>
          (* No secret parameter — should not happen with
             gen_PROG_with_secret_nofun, but skip defensively. *)
          checker true
      | Some secret_id =>
          let pub_regs := vellvm_taint_public_regs prog [42%Z] in
          let trace1 := z_to_obs (vellvm_collect_obs_args prog [42%Z]) in
          let trace2 := z_to_obs (vellvm_collect_obs_args prog [137%Z]) in
          if raw_id_in_list secret_id pub_regs then
            (* Tracker says secret is in the public partition — the
               property doesn't constrain trace1 vs trace2. Accept. *)
            checker true
          else
            (* Tracker says secret is NOT public — traces must match
               across different secret values, otherwise unsound. *)
            if obs_trace_eqb trace1 trace2 then checker true
            else whenFail
                   ("Traces differ on safe input. trace(42) = "
                    ++ show_obs_trace trace1
                    ++ " | trace(137) = " ++ show_obs_trace trace2
                    ++ " | Ast: " ++ ReprAST.repr prog)
                   false
      end
  end.

(* ================================================================= *)
(** ** QuickChick invocation                                          *)
(* ================================================================= *)

Extract Constant defNumTests => "1000".

QuickChick
  (forAll (run_GenLLVM gen_PROG_with_secret_nofun)
          vellvm_taint_soundness_partition).
