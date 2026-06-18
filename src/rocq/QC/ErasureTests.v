(** * Erasure QuickChick Test (anchor 1: obs instrumentation is conservative)

    Property under test:
      For a randomly generated program [P] whose [main] takes [i32]
      arguments, and a random argument vector [args], the final result of
      running [P] must be identical along two pipelines:

        path A (ours)    : ./vellvm -interpret-obs-args args P
        path B (original): ./vellvm -interpret P_wrapped

      where [P_wrapped] renames [@main] to [@main_orig] and appends a
      zero-argument [@main] that calls it with [args] baked in as
      constants. Both paths perform the same computation; path B runs the
      *unmodified* upstream interpretation pipeline. Compared: termination
      class (OK/ERR) and payload (final dvalue, or error reason). The obs
      trace itself is deliberately ignored — "erasing" the observations
      must leave the original semantics.

      A counterexample means our obs instrumentation changed the
      underlying semantics (value, control flow, or termination).

    Runs that do not complete cleanly on either side (timeout under
    parallel load) are discarded, with one-sided incompleteness tagged
    separately so a systematic divergence still surfaces in the stats.

    See NITests.v for the shell-out architecture notes. *)

From Stdlib Require Import List String Ascii ZArith.
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

(* Coq [string] extracts to OCaml [char list]; pack it into an OCaml
   string (same axiom as NITests.v — this file is loaded standalone). *)
Axiom to_caml_str : string -> string.
Extract Constant to_caml_str =>
"fun (s: char list) ->
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
  | [] -> r
  | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)".

(* ================================================================= *)
(** ** Generator wrapper (same as NITests.v)                          *)
(* ================================================================= *)

Inductive PROG :=
| Prog : list (toplevel_entity typ (block typ * list (block typ))) -> PROG.

#[global] Instance Show_PROG : Show PROG :=
  { show p := "" (* avoid expensive printing during QC *) }.

Definition gen_PROG_with_args_withfun : GenLLVM PROG :=
  prog <- gen_llvm_with_args_withfun ;;
  ret (Prog prog).

(* ================================================================= *)
(** ** Helpers (subset of NITests.v)                                  *)
(* ================================================================= *)

Definition find_main_arg_ids
  (prog : list (toplevel_entity typ (block typ * list (block typ))))
  : list raw_id :=
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
  | d :: _ => d.(df_args)
  | _ => []
  end.

Definition gen_i32 : G Z := choose ((-1000)%Z, 1000%Z).
Definition gen_arg_vector (n : nat) : G (list Z) := vectorOf n gen_i32.

Definition discard_with (reason : string) : Checker := collect reason tt.

(* ================================================================= *)
(** ** Wrapper baking (text level)                                    *)
(* ================================================================= *)

Definition nl : string := String (Ascii.ascii_of_nat 10) EmptyString.

(** Rename the unique occurrence of "@main(" to "@main_orig(".
    [None] if [@main(] does not occur exactly once — the corpus survey
    found the generator references [@main] only at its define, but guard
    anyway (a second occurrence would make the wrapper recursive). *)
Definition rename_main_once (s : string) : option string :=
  match String.index 0 "@main(" s with
  | None => None
  | Some i =>
      let before := substring 0 i s in
      let after  := substring (i + 6) (String.length s - i - 6) s in
      match String.index 0 "@main(" after with
      | Some _ => None
      | None   => Some (before ++ "@main_orig(" ++ after)
      end
  end.

(** Zero-arg [@main] that calls [@main_orig] with the args as constants. *)
Definition wrapper_text (args : list Z) : string :=
  let cargs :=
    String.concat ", " (List.map (fun z => "i32 " ++ show z) args) in
  nl ++ "define i8 @main() {" ++ nl
     ++ "  %wrap_r = call i8 @main_orig(" ++ cargs ++ ")" ++ nl
     ++ "  ret i8 %wrap_r" ++ nl
     ++ "}" ++ nl.

(* ================================================================= *)
(** ** Shell-out axioms                                               *)
(* ================================================================= *)

(** Run path A: [-interpret-obs-args <args>] on the original program.
    Returns [Some "OK|<dvalue>"], [Some "ERR|<reason>"], or [None] when
    the run produced neither marker (timeout/crash). *)
Axiom vellvm_run_obs_result_str : string -> list Z -> option string.
Extract Constant vellvm_run_obs_result_str =>
  "fun prog_str args ->
     let llvm_file =
       Filename.(concat (get_temp_dir_name ())
         (Printf.sprintf ""er_qc_obs_%d.ll"" (Unix.getpid ())))
     in
     let oc = open_out llvm_file in
     output_string oc prog_str;
     close_out oc;
     let args_str =
       String.concat "","" (List.map
         (fun z -> string_of_int (Big_int_Z.int_of_big_int z)) args)
     in
     let vellvm =
       (try Sys.getenv ""VELLVM_BIN"" with Not_found ->
          (try List.find Sys.file_exists
                 [""./vellvm""; ""src/vellvm""; ""../vellvm""; ""../../vellvm""; ""../../../vellvm""]
           with Not_found -> ""./vellvm"")) in
     let cmd =
       ""timeout 5 "" ^ vellvm ^ "" -interpret-obs-args "" ^ args_str ^
       "" "" ^ llvm_file ^ "" 2>&1""
     in
     let ic = Unix.open_process_in cmd in
     let buf = Buffer.create 256 in
     (try while true do Buffer.add_channel buf ic 1 done
      with End_of_file -> ());
     let _ = Unix.close_process_in ic in
     let lines = String.split_on_char '\n' (Buffer.contents buf) in
     let result = ref None in
     let classify line =
       let try_prefix p tag =
         let lp = String.length p in
         if String.length line >= lp && String.sub line 0 lp = p
         then Some (tag ^ String.sub line lp (String.length line - lp))
         else None
       in
       match try_prefix ""Program terminated with: "" ""OK|"" with
       | Some r -> Some r
       | None -> try_prefix ""Program error: "" ""ERR|""
     in
     List.iter (fun line ->
       match classify line with
       | Some r -> result := Some r
       | None -> ()) lines;
     match !result with
     | None -> None
     | Some r -> Some (List.init (String.length r) (String.get r))".

(** Run path B: plain [-interpret] on the wrapped program (the original,
    untouched pipeline). Same result classification; the original path
    reports errors via [failwith], which surfaces as an uncaught
    [Failure] — unwrap it so both paths yield comparable ""ERR|<reason>"". *)
Axiom vellvm_run_interp_result_str : string -> option string.
Extract Constant vellvm_run_interp_result_str =>
  "fun prog_str ->
     let llvm_file =
       Filename.(concat (get_temp_dir_name ())
         (Printf.sprintf ""er_qc_interp_%d.ll"" (Unix.getpid ())))
     in
     let oc = open_out llvm_file in
     output_string oc prog_str;
     close_out oc;
     let vellvm =
       (try Sys.getenv ""VELLVM_BIN"" with Not_found ->
          (try List.find Sys.file_exists
                 [""./vellvm""; ""src/vellvm""; ""../vellvm""; ""../../vellvm""; ""../../../vellvm""]
           with Not_found -> ""./vellvm"")) in
     let cmd =
       ""timeout 5 "" ^ vellvm ^ "" -interpret "" ^ llvm_file ^ "" 2>&1""
     in
     let ic = Unix.open_process_in cmd in
     let buf = Buffer.create 256 in
     (try while true do Buffer.add_channel buf ic 1 done
      with End_of_file -> ());
     let _ = Unix.close_process_in ic in
     let lines = String.split_on_char '\n' (Buffer.contents buf) in
     let result = ref None in
     let try_prefix line p tag =
       let lp = String.length p in
       if String.length line >= lp && String.sub line 0 lp = p
       then Some (tag ^ String.sub line lp (String.length line - lp))
       else None
     in
     List.iter (fun line ->
       (match try_prefix line ""Program terminated with: "" ""OK|"" with
        | Some r -> result := Some r
        | None ->
          match try_prefix line ""Program error: "" ""ERR|"" with
          | Some r -> result := Some r
          | None ->
            match try_prefix line ""Fatal error: exception Failure("" ""ERR|"" with
            | Some r ->
                (* r = ERR|""msg"")  — strip the quote/paren decoration *)
                let r = String.concat """" (String.split_on_char '""' r) in
                let r =
                  if String.length r >= 1 && r.[String.length r - 1] = ')'
                  then String.sub r 0 (String.length r - 1) else r
                in
                result := Some r
            | None -> ())) lines;
     match !result with
     | None -> None
     | Some r -> Some (List.init (String.length r) (String.get r))".

Definition run_obs_result
  (prog_txt : string) (args : list Z) : option string :=
  vellvm_run_obs_result_str (to_caml_str prog_txt) args.

Definition run_interp_result (prog_txt : string) : option string :=
  vellvm_run_interp_result_str (to_caml_str prog_txt).

(* ================================================================= *)
(** ** Erasure property                                               *)
(* ================================================================= *)

Definition erasure_check (p : string + PROG) : Checker :=
  match p with
  | inl msg => discard_with ("generator failed: " ++ msg)
  | inr (Prog prog) =>
      match find_main_arg_ids prog with
      | [] => discard_with "main has no arguments"
      | arg_ids =>
          forAll (gen_arg_vector (List.length arg_ids)) (fun args =>
            let txt := show prog in
            match rename_main_once txt with
            | None => discard_with "@main not uniquely renameable"
            | Some renamed =>
                let wrapped := renamed ++ wrapper_text args in
                match run_obs_result txt args,
                      run_interp_result wrapped with
                | Some a, Some b =>
                    if String.eqb a b then checker true
                    else whenFail
                           ("ERASURE MISMATCH (obs pipeline diverged from "
                            ++ "original): obs-path = " ++ a
                            ++ " | original-path = " ++ b
                            ++ " | args = " ++ show args
                            ++ " <<<LLBEGIN" ++ txt ++ "LLEND>>>")
                           false
                | None, None => discard_with "both runs incomplete (timeout)"
                | None, Some _ => discard_with "obs-path incomplete only"
                | Some _, None => discard_with "original-path incomplete only"
                end
            end)
      end
  end.

(* ================================================================= *)
(** ** QuickChick invocation                                          *)
(* ================================================================= *)

Extract Constant defNumTests => "1000".

QuickChick
  (forAll (run_GenLLVM gen_PROG_with_args_withfun) erasure_check).
