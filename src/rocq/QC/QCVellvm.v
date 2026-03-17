 (** Framework for running QC vellvm tests.

    This sets up a step function which mimics the step function in
    interpreter.ml in Coq. This function may not terminate (e.g., when
    given an LLVM program that loops forever), and as such we need to
    disable the Coq termination checker to define it.
 *)
Require Import Semantics.LLVMEvents.
Require Import Semantics.InterpretationStack.
Require Import Handlers.Handlers.

From Stdlib Require Import String.
From Stdlib Require Import ZArith.

From ITree Require Import
     ITree
     Interp.Recursion
     Events.Exception.

(* Require Import ExtrOcamlBasic. *)
(* Require Import ExtrOcamlString. *)

(* From QuickChick Require Import QuickChick. *)
From QuickChick Require Import Show Checker Generators Producer Test.
From Vellvm Require Import ShowAST ReprAST GenAST TopLevel LLVMAst DynamicValues VellvmIntegers.

Extraction Blacklist String List Char Core Z Format int.

(* TODO: Use the existing vellvm version of this? Might actually just be ocaml result type. *)
Inductive MlResult a e :=
| MlOk : a -> MlResult a e
| MlError : e -> MlResult a e.

Extract Inductive MlResult => "result" [ "Ok" "Error" ].

#[global] Instance MlResultShow {a e} `{Show a} `{Show e} : Show (MlResult a e).
Proof.
  split.
  exact
    (fun res =>
       match res with
       | MlOk _ _ a => ("Ok " ++ show a)%string
       | MlError _ _ e => ("Error " ++ show e)%string
       end).
Defined.

Import TopLevel64BitIntptr.
(* Import TopLevelBigIntptr. *)
Import DV.
Import MemoryModelImplementation.LLVMParams64BitIntptr.Events.
(* Import MemoryModelImplementation.LLVMParamsBigIntptr.Events. *)

#[global] Instance showdv : Show dvalue.
Proof.
  split.
  apply show_dvalue.
Defined.

Unset Guard Checking.
CoFixpoint step (t : ITreeDefinition.itree L4 res_L4) : MlResult dvalue string
  := match observe t with
     | RetF (_,(_,(_,(_,x)))) => MlOk _ string x
     | TauF t => step t
     | VisF (inl1 e) k =>
         MlError _ string "Uninterpreted external call"
     | VisF (inr1 (inl1 (ThrowOOM msg))) k =>
         MlError _ string ("OOM")%string
     | VisF (inr1 (inr1 (inl1 (ThrowUB msg)))) k =>
         MlError _ string ("UB")%string
     | VisF (inr1 (inr1 (inr1 (inl1 (Debug msg))))) k =>
         MlError _ string ("Debug")%string
     | VisF (inr1 (inr1 (inr1 (inr1 (LLVMEvents.Throw msg))))) k =>
         MlError _ string ("Failure")%string
     end.
Set Guard Checking.

(** Top level interpreter to run LLVM programs. Yields either a uvalue, or an error string. *)
Definition interpret (prog : list (toplevel_entity typ (block typ * list (block typ)))) : MlResult dvalue string
  := step (interpreter nil prog).

Axiom to_caml_str : string -> string.
Extract Constant to_caml_str =>
"fun (s: char list) ->
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
  | [] -> r
  | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)".

(** Ocaml integers *)
Axiom oint : Type. (* ocaml int type *)
Extract Inlined Constant oint => "int".

Axiom oint_to_Z : oint -> Z.
Extract Inlined Constant oint_to_Z => "Big_int_Z.big_int_of_int".

Axiom oneq : oint -> oint -> bool.
Extract Inlined Constant oneq => "(<>)".

Axiom oeq : oint -> oint -> bool.
Extract Inlined Constant oeq => "(=)".

Axiom ozero : oint.
Extract Inlined Constant ozero => "0".

(** Processes *)
Inductive process_status : Type :=
| WEXITED   : oint -> process_status
| WSIGNALED : oint -> process_status
| WSTOPPED  : oint -> process_status
.
Extract Inductive process_status => "process_status" [ "WEXITED" "WSIGNALED" "WSTOPPED" ].

#[global] Instance Show_process_status : Show process_status.
Proof.
  split.
  intros STATUS. destruct STATUS as [EXIT | SIGNAL | STOPPED].
  - exact ("Exited with " ++ show (oint_to_Z EXIT))%string.
  - exact ("Signaled with " ++ show (oint_to_Z SIGNAL))%string.
  - exact ("Stopped with " ++ show (oint_to_Z STOPPED))%string.
Qed.

Axiom fork : unit -> oint.
Extract Inlined Constant fork => "Unix.fork".

Axiom wait : unit -> (oint * process_status)%type.
Extract Inlined Constant wait => "Unix.wait".

Axiom wait_flag : Type.
Extract Inlined Constant wait_flag => "Unix.wait_flag".

Axiom waitpid : list wait_flag -> oint -> (oint * process_status)%type.
Extract Inlined Constant waitpid => "Unix.waitpid".

Axiom exit : forall {A}, oint -> A.
Extract Inlined Constant exit => "exit".

(** Write our LLVM program to a file ("temporary_vellvm.ll"), and then
    use clang to compile this file to an executable, which we then run in
    order to get the return code. *)
Axiom llc_command_ocaml : string -> oint.
Extract Constant llc_command_ocaml =>
          "fun prog ->
              let llvm_file_name = Filename.(concat (get_temp_dir_name ()) ""temporary_vellvm.ll"") in
              let test_binary = Filename.(concat (get_temp_dir_name ()) ""vellvmqc"") in
              let f = open_out llvm_file_name in
                Printf.fprintf f ""%s"" prog;
                close_out f;
                Sys.command (""clang -lm -Wno-everything "" ^ llvm_file_name ^ "" -o "" ^ test_binary ^ "" && "" ^ test_binary)".

(** Write our LLVM program to a file ("temporary_vellvm.ll"), and then
    use the vellvm binary in the path to interpret this file in order
    to get the return code. *)
Axiom vellvm_binary_command_ocaml : string -> oint.
Extract Constant vellvm_binary_command_ocaml =>
          "fun prog ->
              let llvm_file_name = Filename.(concat (get_temp_dir_name ()) ""temporary_vellvm.ll"") in
              let test_binary = Filename.(concat (get_temp_dir_name ()) ""vellvmqc"") in
              let f = open_out llvm_file_name in
                Printf.fprintf f ""%s"" prog;
                close_out f;
                Sys.command (""./vellvm -interpret "" ^ llvm_file_name ^ "" | grep terminated | awk '{ exit $NF }'"")".

Definition llc_command (prog : string) : int_ast
  := oint_to_Z (llc_command_ocaml prog).

Definition vellvm_binary_command (prog : string) : int_ast
  := oint_to_Z (vellvm_binary_command_ocaml prog).

Axiom vellvm_print_ll : list (toplevel_entity typ (block typ * list (block typ))) -> string.
Extract Constant vellvm_print_ll => "fun prog -> Llvm_printer.toplevel_entities Format.str_formatter prog; Format.flush_str_formatter".

(** Use the *llc_command* Axiom to run a Vellvm program with clang,
    and wrap up the exit code as a dvalue. *)
Definition run_llc (prog : list (toplevel_entity typ (block typ * list (block typ)))) : dvalue
  := @DVALUE_I 8 (VellvmIntegers.repr (llc_command (to_caml_str (show prog)))).

(** Use the *vellvm_binary_command* Axiom to run a Vellvm program with
    the vellvm interpreter in the user's path, and wrap up the exit
    code as a dvalue. *)
Definition run_vellvm_binary (prog : list (toplevel_entity typ (block typ * list (block typ)))) : dvalue
  := @DVALUE_I 8 (VellvmIntegers.repr (vellvm_binary_command (to_caml_str (show prog)))).

(* Hide show instance... *)
Inductive PROG :=
| Prog : list (toplevel_entity typ (block typ * list (block typ))) -> PROG
.

#[global] Instance Show_PROG : Show PROG :=
  { show p := "" (* PROG: avoiding inefficient printing in QC, see #253 *) }.


(** Basic property to make sure that Vellvm and Clang agree when they
    both produce values *)
Definition vellvm_agrees_with_clang_parallel (p : PROG) : Checker
  :=
  (* collect (show prog) *)
  let '(Prog prog) := p in
  let pid := fork tt in
  if oeq pid ozero
  then (* Child *)
    exit (llc_command_ocaml (to_caml_str (show prog)))
  else (* Parent *)
    let vellvm_res := interpret prog in
    let clang_res := snd (waitpid nil pid) in
    match vellvm_res, clang_res with
    | MlOk _ _ (@DVALUE_I sz x), (WEXITED ocaml_y) =>
        let y := repr (oint_to_Z ocaml_y) in
        if equ x y
        then checker true
        else whenFail ("Vellvm: " ++ show (unsigned x) ++ " | Clang: " ++ show (unsigned y) ++ " | Ast: " ++ ReprAST.repr prog) false
    | _, (WSIGNALED ocaml_y) =>
        whenFail ("clang process signaled") false
    | _, (WSTOPPED ocaml_y) =>
        whenFail ("clang process stopped") false
    | _, _ =>
        whenFail ("Something else went wrong... Vellvm: " ++ show vellvm_res ++ " | Clang: " ++ show clang_res) false
    end.

#[global] Instance Show_sum {A B} `{Show A} `{Show B} : Show (A + B) :=
  { show :=  (fun x =>
    match x with
    | inl a => ("inl " ++ show a)%string
    | inr b => ("inr " ++ show b)%string
    end) }.

(** Basic property to make sure that Vellvm and Clang agree when they
    both produce values *)
Definition vellvm_agrees_with_clang (p : string + PROG) : Checker.
  refine
    (match p with
     | inl msg => checker false
     | inr p =>
         (* collect (show prog) *)
         let '(Prog prog) := p in
         let clang_res := run_llc prog in
         let vellvm_res := interpret prog in
         match clang_res, vellvm_res with
         | @DVALUE_I sz1 y, MlOk _ _ (@DVALUE_I sz2 x) =>
             _
         | _, _ =>
             whenFail ("Something else went wrong... Vellvm: " ++ show vellvm_res ++ " | Clang: " ++ show clang_res) false
         end
     end).

  destruct ((Pos.eqb sz1 8%positive && Pos.eqb sz2 8%positive)%bool) eqn:SZ.
  - invert_bools.
    apply Peqb_true_eq in H, H0; subst.
    destruct (equ x y) eqn:EQ.
    + exact (checker true).
    + exact (whenFail ("Vellvm: " ++ show (unsigned x) ++ " | Clang: " ++ show (unsigned y) ++ " | Ast: " ++ ReprAST.repr prog) false).
  - exact (whenFail ("Vellvm: " ++ show (unsigned x) ++ " | Clang: " ++ show (unsigned y) ++ " | Ast: " ++ ReprAST.repr prog) false).
Defined.

(** This version runs the vellvm binary in your path instead...  This
    will be slower (has to read and parse a file), and will not
    guarantee you're running the tests with same version of vellvm, but
    this can be helpful for testing the parser (note the more direct
    vellvm_agrees_with_clang is also helpful in that it bypasses the
    parser for vellvm, but clang parses the file so it can detect bugs
    in the pretty printer for LLVM ASTs), and this can also be helpful
    for skirting around extraction bugs which are easier to patch up
    outside of QC. *)
Definition vellvm_binary_agrees_with_clang (p : string + PROG) : Checker.
  refine
    (match p with
     | inl msg => checker false
     | inr p =>
         (* collect (show prog) *)
         let '(Prog prog) := p in
         let clang_res := run_llc prog in
         let vellvm_res := run_vellvm_binary prog in
         match clang_res, vellvm_res with
         | @DVALUE_I sz1 y, @DVALUE_I sz2 x =>
             _
         | _, _ =>
             whenFail ("Something else went wrong... Vellvm: " ++ show vellvm_res ++ " | Clang: " ++ show clang_res) false
         end
     end).

  destruct ((Pos.eqb sz1 8%positive && Pos.eqb sz2 8%positive)%bool) eqn:SZ.
  - invert_bools.
    apply Peqb_true_eq in H, H0; subst.
    destruct (equ x y) eqn:EQ.
    + exact (checker true).
    + exact (whenFail ("Vellvm: " ++ show (unsigned x) ++ " | Clang: " ++ show (unsigned y) ++ " | Ast: " ++ ReprAST.repr prog) false).
  - exact (whenFail ("Vellvm: " ++ show (unsigned x) ++ " | Clang: " ++ show (unsigned y) ++ " | Ast: " ++ ReprAST.repr prog) false).
Defined.

Definition gen_PROG : GenLLVM PROG
  := fmap Prog gen_llvm.

(** Generator for programs where main takes one i32 argument (the secret). *)
Definition gen_PROG_with_secret : GenLLVM PROG
  := fmap Prog gen_llvm_with_secret.

(* ================================================================= *)
(** ** Non-Interference Testing                                       *)
(* ================================================================= *)

(** An observation is a memory event visible to an attacker.
    We only consider Load and Store addresses (not values). *)
Inductive observation : Type :=
| OLoad  (addr : Z)   (* address read from *)
| OStore (addr : Z).  (* address written to *)

Definition obs_trace := list observation.

Definition show_observation (o : observation) : string :=
  match o with
  | OLoad addr => "L(" ++ show addr ++ ")"
  | OStore addr => "S(" ++ show addr ++ ")"
  end.

#[global] Instance Show_observation : Show observation :=
  {| show := show_observation |}.

Definition show_obs_trace (t : obs_trace) : string :=
  "[" ++ String.concat ", " (List.map show_observation t) ++ "]".

#[global] Instance Show_obs_trace : Show obs_trace :=
  {| show := show_obs_trace |}.

Definition obs_eqb (o1 o2 : observation) : bool :=
  match o1, o2 with
  | OLoad a1, OLoad a2 => Z.eqb a1 a2
  | OStore a1, OStore a2 => Z.eqb a1 a2
  | _, _ => false
  end.

Fixpoint obs_trace_eqb (t1 t2 : obs_trace) : bool :=
  match t1, t2 with
  | nil, nil => true
  | o1 :: t1', o2 :: t2' => obs_eqb o1 o2 && obs_trace_eqb t1' t2'
  | _, _ => false
  end.

Definition z_to_obs (zs : list Z) : obs_trace :=
  List.map (fun z => if Z.ltb z 0 then OStore (Z.opp z) else OLoad z) zs.

(** Collect Load/Store observations via the Rocq-native pipeline.
    Shells out to: ./vellvm -interpret-obs-secret <secret> <file>
    The binary uses interpreter_gen_obs (observe_L2 at L2) internally.

    Note: shell-out is required because QuickChick's extraction
    cannot handle direct calls to the pipeline (exec_correct_post issue). *)
Axiom vellvm_collect_obs :
  list (toplevel_entity typ (block typ * list (block typ))) -> Z -> list Z.

Extract Constant vellvm_collect_obs =>
  "fun prog secret ->
     let llvm_file_name = Filename.(concat (get_temp_dir_name ()) ""temporary_vellvm_obs.ll"") in
     let oc = open_out llvm_file_name in
     let fmt = Format.formatter_of_out_channel oc in
     Llvm_printer.toplevel_entities fmt prog;
     Format.pp_print_flush fmt ();
     close_out oc;
     let secret_int = Big_int_Z.int_of_big_int secret in
     let cmd = ""timeout 5 ./vellvm -interpret-obs-secret "" ^ string_of_int secret_int ^ "" "" ^ llvm_file_name ^ "" 2>&1"" in
     let ic = Unix.open_process_in cmd in
     let buf = Buffer.create 256 in
     (try while true do Buffer.add_channel buf ic 1 done with End_of_file -> ());
     let _ = Unix.close_process_in ic in
     let output = Buffer.contents buf in
     let lines = String.split_on_char '\n' output in
     let int_to_z n = Big_int_Z.big_int_of_int n in
     let in_trace = ref false in
     let result = ref [] in
     List.iter (fun line ->
       if line = ""---OBS_TRACE_BEGIN---"" then in_trace := true
       else if line = ""---OBS_TRACE_END---"" then in_trace := false
       else if !in_trace then
         (try result := (int_to_z (int_of_string line)) :: !result
          with _ -> ())
     ) lines;
     List.rev !result".

(** NI test: generate a program with a secret i32 argument,
    run with two different secrets, compare observation traces.
    If traces differ, the program leaks information about the secret
    through its memory access pattern. *)
Definition vellvm_ni (p : string + PROG) : Checker :=
  match p with
  | inl msg => checker tt
  | inr (Prog prog) =>
      forAll (choose (-100%Z, 100%Z)) (fun secret1 : Z =>
      forAll (choose (-100%Z, 100%Z)) (fun secret2 : Z =>
        let obs1 := z_to_obs (vellvm_collect_obs prog secret1) in
        let obs2 := z_to_obs (vellvm_collect_obs prog secret2) in
        if obs_trace_eqb obs1 obs2
        then checker true
        else whenFail ("NI violation!"
                    ++ " secret1=" ++ show secret1
                    ++ " secret2=" ++ show secret2
                    ++ " | trace1=" ++ show obs1
                    ++ " | trace2=" ++ show obs2) false))
  end.

(* Definition agrees := (forAll (run_GenLLVM gen_llvm) vellvm_agrees_with_clang). *)

Extract Constant defNumTests    => "1000".

(* SAZ: These paths are relative to where the coqc command that runs the extraction is executed.
   For invoking `make qc-tests` from the `/src` directory, we need these:
*)
QCInclude "ml/*".
QCInclude "ml/libvellvm/*".

(* QCInclude "../../ml/libvellvm/llvm_printer.ml". *)
(* QCInclude "../../ml/libvellvm/Camlcoq.ml". *)
(* QCInclude "../../ml/extracted/*ml". *)
Extract Inlined Constant Error.failwith => "(fun _ -> raise)".
QuickChick (forAll (run_GenLLVM gen_PROG_with_secret) vellvm_ni).
(*! QuickChick agrees. *)
