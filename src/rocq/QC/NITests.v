(** * NI Soundness QuickChick Test (partition-style)

    Property under test (a partition-style analogue of Triosecuris's
    [test_ni]):
      For each randomly generated program [P] whose [main] takes a vector
      of [i32] arguments, draw a random baseline argument vector and run the
      partition-style taint tracker on [P] with it. The tracker outputs
      [TOBS_REGS] (the register names in the public partition) and
      [TOBS_ADDRS] (the memory addresses).

      Then draw a *public-equivalent* partner argument vector: arguments
      whose register is in [TOBS_REGS] are held equal, the rest (the
      tracker's "safe to vary" complement) are re-randomised.

      Soundness check:
        the two argument vectors must produce identical observation traces
        (they agree on everything the tracker called public).

      Counterexample on this property = the tracker is unsound (it missed a
      flow from a supposedly-non-public argument into an observation).

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

(* [SERIALIZE TIMER] times one [.ll output] = [to_caml_str (show prog)]: turning
   the generated AST into .ll text. The [bool -> string] thunk delays that work
   to inside the timer. NB: [show prog] also FORCES the whole AST, so if the
   generator built it lazily, the deferred generation is paid (and timed) here.
   One line per call → /tmp/ni_serialize.txt *)
Axiom timed_str : (bool -> string) -> string.
Extract Constant timed_str =>
  "fun thunk ->
     let t0 = Unix.gettimeofday () in
     let s = thunk true in
     (let oc = open_out_gen [Open_append; Open_creat] 0o644 ""/tmp/ni_serialize.txt"" in
      Printf.fprintf oc ""%f\n"" (Unix.gettimeofday () -. t0); close_out oc);
     s".

(* [SHOW TIMER] times JUST [show prog] (building the Coq char-list string),
   nested inside [timed_str] so that: to_caml_str time = serialize - show.
   → /tmp/ni_show.txt *)
Axiom time_show : (bool -> string) -> string.
Extract Constant time_show =>
  "fun thunk ->
     let t0 = Unix.gettimeofday () in
     let s = thunk true in
     (let oc = open_out_gen [Open_append; Open_creat] 0o644 ""/tmp/ni_show.txt"" in
      Printf.fprintf oc ""%f\n"" (Unix.gettimeofday () -. t0); close_out oc);
     s".

(* ================================================================= *)
(** ** Local generator wrapper (mirrors QCVellvm.v's PROG, kept local
       to avoid forcing a build-time QuickChick run from QCVellvm.v).  *)
(* ================================================================= *)

Inductive PROG :=
| Prog : list (toplevel_entity typ (block typ * list (block typ))) -> PROG.

#[global] Instance Show_PROG : Show PROG :=
  { show p := "" (* avoid expensive printing during QC *) }.

(** Wraps [gen_llvm_with_args_nofun]: [main] takes a size-scaled number
    (>= 1) of [i32] arguments and the program has no helper functions. The
    NI property below works over the whole argument vector. *)
Definition gen_PROG_with_args_nofun : GenLLVM PROG :=
  prog <- gen_llvm_with_args_nofun ;;
  ret (Prog prog).

(** Wraps [gen_llvm_with_args_withfun]: like [gen_PROG_with_args_nofun] but
    the program may contain helper functions, so [main] can emit
    [INSTR_Call]. This is the generator the QuickChick invocation below
    uses, now that the inter-procedural taint tracker handles calls. *)
Definition gen_PROG_with_args_withfun : GenLLVM PROG :=
  prog <- gen_llvm_with_args_withfun ;;
  ret (Prog prog).

(* ================================================================= *)
(** ** Observation trace type                                         *)
(* ================================================================= *)

(** Decoded observation events (see [event_obs] in InterpretationStack.v
    for the encoding). *)
Inductive observation :=
| OLoad   (addr : Z)
| OStore  (addr : Z)
| OBranch (b : bool)
| OCall   (target : Z).   (* call-target observation (control-flow leakage) *)

Definition obs_eqb (o1 o2 : observation) : bool :=
  match o1, o2 with
  | OLoad   a1, OLoad   a2 => Z.eqb a1 a2
  | OStore  a1, OStore  a2 => Z.eqb a1 a2
  | OBranch b1, OBranch b2 => Bool.eqb b1 b2
  | OCall   t1, OCall   t2 => Z.eqb t1 t2
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
  | OCall   t       => "Call(" ++ show t ++ ")"
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
    else if Z.leb 2000000 z then OCall (z - 2000000)
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
(** Returns [Some trace] if the run completed cleanly (the
    [---OBS_TRACE_END---] marker was emitted), or [None] if it aborted
    before that -- a timeout (the [timeout 5] below, which under *parallel
    load* can fire on a slow-but-well-defined program), UB, or failure.
    Comparing leakage is only valid when both runs complete, so an
    incomplete run is discarded (see [obs_agree_on]). *)
Axiom vellvm_collect_obs_args_str : string -> list Z -> option (list Z).

Extract Constant vellvm_collect_obs_args_str =>
  "fun prog_str args ->
     let llvm_file =
       (* PID in the name so parallel test processes don't clobber each
          other's .ll (the file is rewritten per shell-out). *)
       Filename.(concat (get_temp_dir_name ())
         (Printf.sprintf ""ni_qc_obs_%d.ll"" (Unix.getpid ())))
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
     (* [TIMER A start] SHELL-OUT phase = spawn ./vellvm + run it (the binary
        parses the .ll and obs-interprets it) + read its whole stdout into buf.
        __t0..(close_process) is exactly what the OLD 2026-06-16 experiment
        timed as CHECK; everything outside it fell into the mislabelled
        GENERATION residual. *)
     let __t0 = Unix.gettimeofday () in
     let ic = Unix.open_process_in cmd in
     let buf = Buffer.create 256 in
     (try while true do Buffer.add_channel buf ic 1 done
      with End_of_file -> ());
     let _ = Unix.close_process_in ic in
     let output = Buffer.contents buf in
     (* [TIMER A end] write the shell-out duration (one line per call). *)
     (let __oc = open_out_gen [Open_append; Open_creat] 0o644 ""/tmp/ni_obs_shell.txt"" in
      Printf.fprintf __oc ""%f\n"" (Unix.gettimeofday () -. __t0); close_out __oc);
     (* [TIMER B start] STDOUT-PARSE phase (harness glue, OCaml side): split the
        captured stdout into lines, scan for the ---OBS_TRACE_BEGIN/END---
        markers, and turn each trace line into a big-int. Pure post-processing
        of the binary's output -- NOT the shell-out, NOT generation. This is
        part of what the old experiment lumped into GENERATION. *)
     let __tp = Unix.gettimeofday () in
     let lines = String.split_on_char '\n' output in
     let in_trace = ref false in
     let saw_end = ref false in
     let result = ref [] in
     List.iter (fun line ->
       if line = ""---OBS_TRACE_BEGIN---"" then in_trace := true
       else if line = ""---OBS_TRACE_END---"" then (in_trace := false; saw_end := true)
       else if !in_trace then
         (try result := (Big_int_Z.big_int_of_int (int_of_string line)) :: !result
          with _ -> ())
     ) lines;
     (* [TIMER B end] write the stdout-parse duration. → /tmp/ni_obs_parse.txt *)
     (let __oc2 = open_out_gen [Open_append; Open_creat] 0o644 ""/tmp/ni_obs_parse.txt"" in
      Printf.fprintf __oc2 ""%f\n"" (Unix.gettimeofday () -. __tp); close_out __oc2);
     if !saw_end then Some (List.rev !result) else None".

Definition vellvm_collect_obs_args
  (prog : list (toplevel_entity typ (block typ * list (block typ))))
  (args : list Z) : option (list Z) :=
  vellvm_collect_obs_args_str (timed_str (fun _ => to_caml_str (show prog))) args.

(** Same shell-out shape as above, but for [-taint-track-args]. Parses
    the [---TOBS_REGS_BEGIN/END---] section into a list of Coq strings.
    The companion `TOBS_ADDRS` section is currently ignored — the soundness
    check varies [main]'s argument *registers*, so only the register-level
    partition is needed (the held/varied decision is per argument). *)
(** Returns [Some regs] if the taint run completed cleanly (the
    [---TOBS_REGS_END---] marker was emitted), or [None] if the program
    aborted before producing it -- Undefined Behavior, a failure, or the
    5s timeout. A [None] baseline is *discarded*: UB has no defined
    semantics, so comparing its leakage is meaningless. *)
Axiom vellvm_taint_public_reg_names_str :
  string -> list Z -> option (list string).

Extract Constant vellvm_taint_public_reg_names_str =>
  "fun prog_str args ->
     let llvm_file =
       (* PID in the name so parallel test processes don't clobber each
          other's .ll (the file is rewritten per shell-out). *)
       Filename.(concat (get_temp_dir_name ())
         (Printf.sprintf ""ni_qc_taint_%d.ll"" (Unix.getpid ())))
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
     let saw_end = ref false in
     let regs = ref [] in
     List.iter (fun line ->
       if line = ""---TOBS_REGS_BEGIN---"" then in_regs := true
       else if line = ""---TOBS_REGS_END---"" then (in_regs := false; saw_end := true)
       else if !in_regs && String.length line > 0 then
         let chars = List.init (String.length line)
                       (fun i -> String.get line i)
         in
         regs := chars :: !regs
     ) lines;
     if !saw_end then Some (List.rev !regs) else None".

Definition vellvm_taint_public_regs
  (prog : list (toplevel_entity typ (block typ * list (block typ))))
  (args : list Z) : option (list raw_id) :=
  match vellvm_taint_public_reg_names_str (to_caml_str (show prog)) args with
  | Some names => Some (List.map LLVMAst.Name names)
  | None       => None
  end.

(** Collect the observation trace from the *taint* pipeline: [-taint-track-args]
    emits an [---OBS_TRACE_BEGIN/END---] section (after the partition), the same
    encoding as [-interpret-obs-args]. [Some trace] if it completed cleanly,
    [None] otherwise (timeout/UB/failure). Used by [taint_obs_matches_real] to
    check the taint denotation is observationally equivalent to the real one. *)
Axiom vellvm_collect_taint_obs_args_str : string -> list Z -> option (list Z).

Extract Constant vellvm_collect_taint_obs_args_str =>
  "fun prog_str args ->
     let llvm_file =
       Filename.(concat (get_temp_dir_name ())
         (Printf.sprintf ""ni_qc_tobs_%d.ll"" (Unix.getpid ())))
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
     let in_trace = ref false in
     let saw_end = ref false in
     let result = ref [] in
     List.iter (fun line ->
       if line = ""---OBS_TRACE_BEGIN---"" then in_trace := true
       else if line = ""---OBS_TRACE_END---"" then (in_trace := false; saw_end := true)
       else if !in_trace then
         (try result := (Big_int_Z.big_int_of_int (int_of_string line)) :: !result
          with _ -> ())
     ) lines;
     if !saw_end then Some (List.rev !result) else None".

Definition vellvm_collect_taint_obs_args
  (prog : list (toplevel_entity typ (block typ * list (block typ))))
  (args : list Z) : option (list Z) :=
  vellvm_collect_taint_obs_args_str (to_caml_str (show prog)) args.

(** Run the taint pipeline ONCE and return BOTH the public partition
    ([TOBS_REGS] register names) and the observation trace ([OBS_TRACE]) --
    [-taint-track-args] emits both. [None] if the run didn't complete
    cleanly (no final [---OBS_TRACE_END---]: timeout/UB/failure).

    This lets the soundness test compute the partition AND read the
    baseline's observation from a *single* shell-out, instead of a separate
    [-taint-track-args] (partition) + [-interpret-obs-args] (baseline obs) --
    one fewer process per test case. The baseline obs is thus the *taint*
    pipeline's; the partner ([args']) obs still comes from the *real* pipeline
    ([vellvm_collect_obs_args]). This cross-pipeline comparison is valid iff
    the taint denotation is observationally equivalent to the real one, which
    [taint_obs_matches_real] checks independently. *)
Axiom vellvm_taint_run_str : string -> list Z -> option (list string * list Z).

Extract Constant vellvm_taint_run_str =>
  "fun prog_str args ->
     let llvm_file =
       Filename.(concat (get_temp_dir_name ())
         (Printf.sprintf ""ni_qc_trun_%d.ll"" (Unix.getpid ())))
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
       ""timeout 5 "" ^ vellvm ^ "" -taint-track-args "" ^ args_str ^
       "" "" ^ llvm_file ^ "" 2>&1""
     in
     (* [TIMER A start] SHELL-OUT phase = spawn ./vellvm -taint-track-args + run
        it (binary parses .ll, taint-tracks it) + read its whole stdout. This is
        the heavier shell-out: it emits BOTH the partition and the obs trace.
        Same boundary the old 2026-06-16 experiment timed as CHECK. *)
     let __t0 = Unix.gettimeofday () in
     let ic = Unix.open_process_in cmd in
     let buf = Buffer.create 256 in
     (try while true do Buffer.add_channel buf ic 1 done
      with End_of_file -> ());
     let _ = Unix.close_process_in ic in
     (* [TIMER A end] write shell-out duration. → /tmp/ni_taint_shell.txt *)
     (let __oc = open_out_gen [Open_append; Open_creat] 0o644 ""/tmp/ni_taint_shell.txt"" in
      Printf.fprintf __oc ""%f\n"" (Unix.gettimeofday () -. __t0); close_out __oc);
     (* [TIMER B start] STDOUT-PARSE phase (harness glue, OCaml side): scan the
        captured stdout for ---TOBS_REGS_BEGIN/END--- (public partition =
        register names) and ---OBS_TRACE_BEGIN/END--- (observation trace),
        building both lists. For loop-heavy programs the trace is long, so this
        scan is a prime suspect for the old mislabelled 'generation' cost. *)
     let __tp = Unix.gettimeofday () in
     let lines = String.split_on_char '\n' (Buffer.contents buf) in
     let in_regs = ref false in
     let in_obs = ref false in
     let saw_obs_end = ref false in
     let regs = ref [] in
     let obs = ref [] in
     List.iter (fun line ->
       if line = ""---TOBS_REGS_BEGIN---"" then in_regs := true
       else if line = ""---TOBS_REGS_END---"" then in_regs := false
       else if line = ""---OBS_TRACE_BEGIN---"" then in_obs := true
       else if line = ""---OBS_TRACE_END---"" then (in_obs := false; saw_obs_end := true)
       else if !in_regs && String.length line > 0 then
         (regs := (List.init (String.length line)
                     (fun i -> String.get line i)) :: !regs)
       else if !in_obs then
         (try obs := (Big_int_Z.big_int_of_int (int_of_string line)) :: !obs
          with _ -> ())
     ) lines;
     (* [TIMER B end] write stdout-parse duration. → /tmp/ni_taint_parse.txt *)
     (let __oc2 = open_out_gen [Open_append; Open_creat] 0o644 ""/tmp/ni_taint_parse.txt"" in
      Printf.fprintf __oc2 ""%f\n"" (Unix.gettimeofday () -. __tp); close_out __oc2);
     if !saw_obs_end then Some (List.rev !regs, List.rev !obs) else None".

Definition vellvm_taint_run
  (prog : list (toplevel_entity typ (block typ * list (block typ))))
  (args : list Z) : option (list raw_id * list Z) :=
  match vellvm_taint_run_str (timed_str (fun _ => to_caml_str (show prog))) args with
  | Some (names, obs) => Some (List.map LLVMAst.Name names, obs)
  | None              => None
  end.

(** Cached variants: take the *pre-serialized* .ll text, so a program is
    serialized ([show prog]) ONLY ONCE per test and reused for both shell-outs
    (taint + obs) instead of serialized twice. *)
Definition vellvm_taint_run_cached (prog_str : string) (args : list Z)
  : option (list raw_id * list Z) :=
  match vellvm_taint_run_str prog_str args with
  | Some (names, obs) => Some (List.map LLVMAst.Name names, obs)
  | None              => None
  end.
Definition vellvm_collect_obs_args_cached (prog_str : string) (args : list Z)
  : option (list Z) :=
  vellvm_collect_obs_args_str prog_str args.

(* ================================================================= *)
(** ** Helpers                                                        *)
(* ================================================================= *)

(** The register names of [main]'s arguments, in order. This is the full
    set of inputs the harness can vary from outside: the args vector passed
    to [-interpret-obs-args] / [-taint-track-args] maps positionally onto
    these. The generator emits a size-scaled number (>= 1) of [i32]
    arguments; we return the whole [df_args] so the soundness test varies
    each argument independently (held-or-varied per its taint).
    Empty if there is no [main] or it takes no arguments. *)
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

Definition raw_id_eqb (x y : raw_id) : bool :=
  if RawIDOrd.eq_dec x y then true else false.

Definition raw_id_in_list (id : raw_id) (l : list raw_id) : bool :=
  List.existsb (raw_id_eqb id) l.

(** Positional equality of two argument vectors. *)
Fixpoint list_Z_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: r1, y :: r2 => Z.eqb x y && list_Z_eqb r1 r2
  | _, _ => false
  end.

(* ================================================================= *)
(** ** Soundness property                                             *)
(* ================================================================= *)

(** Range for randomly-drawn [i32] argument values. Tunable — wider ranges
    exercise more branch conditions, narrower ones collide on paths. *)
Definition gen_i32 : G Z := choose ((-1000)%Z, 1000%Z).

(** A random baseline argument vector of length [n]. *)
Definition gen_arg_vector (n : nat) : G (list Z) := vectorOf n gen_i32.

(** Generate an argument vector that is *public-equivalent* to [base]: at
    each position whose argument register is in [pub] (the tracker's public
    partition) keep [base]'s value, otherwise draw a fresh random value.
    This is the [main]-argument analogue of Triosecuris's
    [gen_pub_equiv_same_ty] (TestingLib.v): hold the tainted/public inputs
    equal, randomise the complement. *)
Definition gen_pub_equiv_args
  (arg_ids : list raw_id) (pub : list raw_id) (base : list Z) : G (list Z) :=
  sequenceGen
    (List.map (fun '(id, b) =>
        if raw_id_in_list id pub then returnGen b else gen_i32)
      (List.combine arg_ids base)).

(** Leakage-match helper — the reusable core NI check on an input PAIR: run
    [prog] on two argument vectors and require their observation traces (the
    attacker-visible leakage) to agree. The property below feeds it a
    public-equivalent pair, but it works for any two inputs. *)
Definition obs_agree_on
  (prog : list (toplevel_entity typ (block typ * list (block typ))))
  (args1 args2 : list Z) : Checker :=
  match vellvm_collect_obs_args prog args1, vellvm_collect_obs_args prog args2 with
  | Some z1, Some z2 =>
      let t1 := z_to_obs z1 in
      let t2 := z_to_obs z2 in
      if obs_trace_eqb t1 t2 then checker true
      else whenFail
             ("NI unsound: public-equivalent inputs leak differently. args1 = "
              ++ show args1 ++ " -> " ++ show_obs_trace t1
              ++ " | args2 = " ++ show args2 ++ " -> " ++ show_obs_trace t2
              ++ " <<<LLBEGIN" ++ show prog ++ "LLEND>>>")
             false
  | _, _ =>
      (* one of the two runs did not complete cleanly (timeout under load,
         UB, or failure): leakage of an incomplete/undefined execution is
         not comparable, so discard rather than report a false divergence. *)
      collect "obs run incomplete (timeout/error)"%string tt
  end.

(** Discard (not pass) a non-testable sample, recording [reason] in the
    QuickChick run summary. [tt : unit] is QuickChick's discard result
    ([testUnit] yields [rejected], the same outcome a false [==>] premise
    produces); [collect] tags the discarded case with its reason so it
    surfaces in the stats instead of being silently counted as a success. *)
Definition discard_with (reason : string) : Checker := collect reason tt.

(* [GLUE TIMERS] split the Coq-side residual (the old mislabelled 'generation').
   time_findargs: times [find_main_arg_ids prog] = walking the program AST to
   find main's argument ids. time_cmp: times the trace decode+compare
   ([z_to_obs] x2 + [obs_trace_eqb]). Whatever residual is left after these (and
   gen / serialize / shell-out) is QuickChick's own per-test machinery + the two
   nested arg-generators (gen_arg_vector / gen_pub_equiv_args). *)
Axiom time_findargs : forall {A}, (bool -> A) -> A.
Extract Constant time_findargs =>
  "fun thunk ->
     let t0 = Unix.gettimeofday () in
     let r = thunk true in
     (let oc = open_out_gen [Open_append; Open_creat] 0o644 ""/tmp/ni_findargs.txt"" in
      Printf.fprintf oc ""%f\n"" (Unix.gettimeofday () -. t0); close_out oc);
     r".
Axiom time_cmp : forall {A}, (bool -> A) -> A.
Extract Constant time_cmp =>
  "fun thunk ->
     let t0 = Unix.gettimeofday () in
     let r = thunk true in
     (let oc = open_out_gen [Open_append; Open_creat] 0o644 ""/tmp/ni_cmp.txt"" in
      Printf.fprintf oc ""%f\n"" (Unix.gettimeofday () -. t0); close_out oc);
     r".
(* Times BUILDING the partner generator = gen_pub_equiv_args with the REAL
   pub_regs: the List.map + List.combine + raw_id_in_list (List.existsb over the
   public partition) checks, one per argument. calibration3 passed [] for
   pub_regs, which makes those checks trivial -- so THIS is the honest test of
   "is gen_pub_equiv_args itself (called via forAll) expensive?". Within-run, so
   not confounded by program-size variance. *)
Axiom time_genpartner : forall {A}, (bool -> A) -> A.
Extract Constant time_genpartner =>
  "fun thunk ->
     let t0 = Unix.gettimeofday () in
     let r = thunk true in
     (let oc = open_out_gen [Open_append; Open_creat] 0o644 ""/tmp/ni_genpartner.txt"" in
      Printf.fprintf oc ""%f\n"" (Unix.gettimeofday () -. t0); close_out oc);
     r".

(** NI soundness check, structured like Triosecuris [test_ni]
    ([Triosecuris/TestingLib.v:285]). The inputs we can vary are exactly
    [main]'s argument vector (a size-scaled number of [i32]s):

    1. Draw a random baseline argument vector [base_args] — the random
       "initial state".
    2. Run the taint tracker once on it → [pub_regs]; this output *drives*
       which arguments count as public (held) vs secret (varied), exactly
       as [test_ni] builds [P] from the tracked [tvars].
    3. Draw a public-equivalent partner [args']: arguments the tracker calls
       public are held equal to [base_args], the rest are re-randomised
       (the analogue of [gen_pub_equiv_same_ty]).
    4. [obs_agree_on] requires the two traces to match; any divergence is a
       flow the tracker missed (unsoundness).

    Generator failures and non-testable programs are *discarded* (with a
    reason), not counted as passes. When every argument is public,
    [args' = base_args] and the pair trivially agrees — the "held equal"
    case, so no separate gate is needed. (Memory is not varied: this
    generator has no memory input; secret-dependent addresses still surface
    in the trace.) *)
Definition vellvm_taint_soundness_partition (p : string + PROG) : Checker :=
  match p with
  | inl msg => discard_with ("generator failed: " ++ msg)
  | inr (Prog prog) =>
      match find_main_arg_ids prog with
      | [] => discard_with "main has no arguments to vary"
      | arg_ids =>
          forAll (gen_arg_vector (List.length arg_ids)) (fun base_args =>
            match vellvm_taint_public_regs prog base_args with
            | None =>
                (* baseline hit UB / failure / timeout: no defined semantics
                   to compare leakage against, so discard. *)
                discard_with "UB or error on baseline"
            | Some pub_regs =>
                forAll (gen_pub_equiv_args arg_ids pub_regs base_args)
                  (fun args' =>
                     if list_Z_eqb args' base_args
                     then
                       (* the public-equivalent partner came out identical to
                          the baseline (every argument is public, or the
                          non-public draws happened to match): there is no
                          real pair to compare, so discard. *)
                       discard_with "partner identical to baseline"
                     else obs_agree_on prog base_args args')
            end)
      end
  end.

(** Faster variant of [vellvm_taint_soundness_partition]: instead of a
    separate [-taint-track-args] (partition) and [-interpret-obs-args]
    (baseline obs), do ONE [vellvm_taint_run] on [base_args] that yields both
    the partition AND the baseline's observation trace. Only the partner
    [args'] needs its own [-interpret-obs-args]. So 2 shell-outs per test
    instead of 3 (~1/3 fewer).

    The baseline obs here is the *taint* pipeline's; [args'] obs is the *real*
    pipeline's. This cross-pipeline comparison is sound exactly when the two
    denotations are observationally equivalent -- the invariant
    [taint_obs_matches_real] tests separately. Concretely:
      (partition predicts *taint*-obs invariance)  [this property]
      AND (taint obs == real obs)                  [taint_obs_matches_real]
      => (partition predicts *real*-obs invariance) [the original property].
    A divergence flagged here is therefore either a missed flow (unsound
    partition) OR a taint/real obs divergence -- run [taint_obs_matches_real]
    to disambiguate. *)
Definition vellvm_taint_soundness_partition_fast (p : string + PROG) : Checker :=
  match p with
  | inl msg => discard_with ("generator failed: " ++ msg)
  | inr (Prog prog) =>
      (* serialize the program ONCE here and reuse for BOTH shell-outs below.
         [time_show] splits out the [show prog] (char-list build) cost. *)
      let prog_str := timed_str (fun _ => to_caml_str (time_show (fun _ => show prog))) in
      match time_findargs (fun _ => find_main_arg_ids prog) with
      | [] => discard_with "main has no arguments to vary"
      | arg_ids =>
          forAll (gen_arg_vector (List.length arg_ids)) (fun base_args =>
            (* ONE run: partition + baseline observation together. *)
            match vellvm_taint_run_cached prog_str base_args with
            | None =>
                discard_with "UB or error on baseline"
            | Some (pub_regs, base_obs_raw) =>
                (* [time_genpartner] wraps building the partner generator with the
                   REAL pub_regs (the membership-check part calibration3 skipped). *)
                forAll (time_genpartner (fun _ =>
                          gen_pub_equiv_args arg_ids pub_regs base_args))
                  (fun args' =>
                     if list_Z_eqb args' base_args
                     then discard_with "partner identical to baseline"
                     else
                       match vellvm_collect_obs_args_cached prog_str args' with
                       | None =>
                           discard_with "obs run incomplete (timeout/error)"
                       | Some args_obs_raw =>
                           if time_cmp (fun _ =>
                                obs_trace_eqb (z_to_obs base_obs_raw) (z_to_obs args_obs_raw))
                           then checker true
                           else whenFail
                                  ("NI unsound (or taint/real obs diverge). "
                                   ++ "base = " ++ show base_args
                                   ++ " -> " ++ show_obs_trace (z_to_obs base_obs_raw)
                                   ++ " | args' = " ++ show args'
                                   ++ " -> " ++ show_obs_trace (z_to_obs args_obs_raw)
                                   ++ " <<<LLBEGIN" ++ show prog ++ "LLEND>>>")
                                  false
                       end)
            end)
      end
  end.

(* ================================================================= *)
(** ** [RESTRUCTURED / FLAT] one forAll; partner derived inline         *)
(* ================================================================= *)

(** Same test as [vellvm_taint_soundness_partition_fast], but restructured to
    use a SINGLE forAll: the generator emits (program, base_args, raw) together
    (the two i32 vectors sized to main's arg count), and the partner is DERIVED
    in the body (public arg -> base value, secret arg -> raw value) instead of
    via an inner forAll.  3 Checker layers -> 1.  Semantics identical (the
    "fresh random for secret args" is just pre-generated as [raw]). *)
Definition gen_prog_base_raw : G ((string + PROG) * (list Z * list Z)) :=
  bindGen (run_GenLLVM gen_PROG_with_args_withfun) (fun p =>
    match p with
    | inr (Prog prog) =>
        let n := List.length (find_main_arg_ids prog) in
        bindGen (gen_arg_vector n) (fun base =>
        bindGen (gen_arg_vector n) (fun raw =>
        returnGen (p, (base, raw))))
    | inl _ => returnGen (p, (nil, nil))
    end).

(* trivial Show for the generated tuple (the whenFail below dumps everything
   useful anyway) -- keeps forAll's printTestCase cheap and avoids needing a
   derived Show instance. *)
#[local] Instance show_pbr : Show ((string + PROG) * (list Z * list Z)) :=
  {| show _ := ""%string |}.

Definition vellvm_taint_soundness_flat
  (pbr : (string + PROG) * (list Z * list Z)) : Checker :=
  let '(p, br) := pbr in
  let '(base_args, raw) := br in
  match p with
  | inl msg => discard_with ("generator failed: " ++ msg)
  | inr (Prog prog) =>
      let prog_str := to_caml_str (show prog) in
      match find_main_arg_ids prog with
      | [] => discard_with "main has no arguments to vary"
      | arg_ids =>
          match vellvm_taint_run_cached prog_str base_args with
          | None => discard_with "UB or error on baseline"
          | Some (pub_regs, base_obs_raw) =>
              (* derive partner inline: public arg -> base value, secret -> raw *)
              let args' :=
                List.map (fun '(id, br2) =>
                            let '(b, r) := br2 in
                            if raw_id_in_list id pub_regs then b else r)
                  (List.combine arg_ids (List.combine base_args raw)) in
              if list_Z_eqb args' base_args
              then discard_with "partner identical to baseline"
              else
                match vellvm_collect_obs_args_cached prog_str args' with
                | None => discard_with "obs run incomplete (timeout/error)"
                | Some args_obs_raw =>
                    if obs_trace_eqb (z_to_obs base_obs_raw) (z_to_obs args_obs_raw)
                    then checker true
                    else whenFail
                           ("NI unsound (or taint/real obs diverge). "
                            ++ "base = " ++ show base_args
                            ++ " -> " ++ show_obs_trace (z_to_obs base_obs_raw)
                            ++ " | args' = " ++ show args'
                            ++ " -> " ++ show_obs_trace (z_to_obs args_obs_raw)
                            ++ " <<<LLBEGIN" ++ show prog ++ "LLEND>>>")
                           false
                end
          end
      end
  end.

Definition exp_full_flat : Checker :=
  forAll gen_prog_base_raw vellvm_taint_soundness_flat.

(* ================================================================= *)
(** ** Differential-oracle property: taint obs == real obs            *)
(* ================================================================= *)

(** The taint denotation ([denote_mcfg_taint], a *second* denotation that
    re-implements execution to thread the partition) must be *observationally
    equivalent* to the real denotation ([denote_mcfg]). This is the invariant
    the whole partition test relies on: the partition is computed from the
    taint pipeline's execution, but the leakage comparison uses the real
    pipeline's trace -- so if the two diverge, the partition is meaningless.

    Here we test it directly: for a random program and a *single* random
    argument vector, the observation trace from [-interpret-obs-args] (real)
    must equal the trace from [-taint-track-args] (taint). A mismatch points
    at a divergence in the taint tracker's re-implemented parts (Load/Store
    duplication, call resolution/inlining), exactly the class of bug that
    "A1/A2" were. Runs that don't complete cleanly (timeout/UB) are discarded
    -- an incomplete execution isn't comparable. *)
Definition taint_obs_matches_real (p : string + PROG) : Checker :=
  match p with
  | inl msg => discard_with ("generator failed: " ++ msg)
  | inr (Prog prog) =>
      match find_main_arg_ids prog with
      | [] => discard_with "main has no arguments"
      | arg_ids =>
          forAll (gen_arg_vector (List.length arg_ids)) (fun args =>
            match vellvm_collect_obs_args prog args,
                  vellvm_collect_taint_obs_args prog args with
            | Some r, Some t =>
                let real_tr  := z_to_obs r in
                let taint_tr := z_to_obs t in
                if obs_trace_eqb real_tr taint_tr then checker true
                else whenFail
                       ("taint/real obs DIVERGE (taint denotation not "
                        ++ "observationally equivalent). args = " ++ show args
                        ++ " | real  = " ++ show_obs_trace real_tr
                        ++ " | taint = " ++ show_obs_trace taint_tr
                        ++ " <<<LLBEGIN" ++ show prog ++ "LLEND>>>")
                       false
            | _, _ =>
                (* one of the two pipelines didn't complete cleanly
                   (timeout/UB): not comparable, so discard. *)
                discard_with "a pipeline run did not complete cleanly"
            end)
      end
  end.

(* ================================================================= *)
(** ** QuickChick invocation                                          *)
(* ================================================================= *)

Extract Constant defNumTests => "1000".
(* For deterministic A/B experiments, override the seed (otherwise random):
   [Extract Constant newRandomSeed => "(Random.State.make [| 12345 |])".] *)

(* Faster soundness check: 2 shell-outs/test (one [vellvm_taint_run] for the
   partition + baseline obs, one [-interpret-obs-args] for the partner)
   instead of 3. Relies on the taint/real obs-equivalence invariant, which
   [taint_obs_matches_real] tests separately -- run that too for full
   coverage. *)
(* [NO-GEN TESTING] read previously-generated .ll files and run ONLY the testing
   (2 shell-outs + decode + compare) -- NO generation, NO serialization. perf on
   this isolates whether the ~186ms residual is in TESTING (reducible) or
   GENERATION (hard). *)
Axiom read_next_ll : bool -> string.
Extract Constant read_next_ll =>
  "let __llc = ref 0 in
   fun _ ->
     incr __llc;
     let i = ((!__llc - 1) mod 10000) + 1 in
     let fn = Printf.sprintf ""/home/yonghyunkim/works/vellvm/private_notes/gen_samples/ni_N10000/p%05d.ll"" i in
     let ic = open_in fn in
     let n = in_channel_length ic in
     let s = really_input_string ic n in
     close_in ic; s".
(* count main's i32 arguments by scanning the @main(...) signature *)
Axiom ll_argc : string -> Z.
Extract Constant ll_argc =>
  "fun ll ->
     let fs hay needle start =
       let hl = String.length hay and nl = String.length needle in
       let rec go i = if i + nl > hl then raise Not_found
                      else if String.sub hay i nl = needle then i else go (i + 1) in
       go start in
     let c = (try
       let i = fs ll ""@main("" 0 in
       let close = String.index_from ll i ')' in
       let s = String.sub ll i (close - i) in
       let cnt = ref 0 in let p = ref 0 in
       (try while true do
          let q = fs s ""i32"" !p in incr cnt; p := q + 3
        done with Not_found -> ());
       !cnt
     with _ -> 1) in
     Big_int_Z.big_int_of_int c".
(* force a bool (defeat dead-code elim) but always return true *)
Axiom keep_bool : bool -> bool.
Extract Constant keep_bool => "fun b -> let _ = Sys.opaque_identity b in true".
(* force a string's full evaluation (e.g. the serialized program) *)
Axiom force_str : string -> bool.
Extract Constant force_str => "fun s -> let _ = Sys.opaque_identity (String.length s) in true".

(* ===================================================================== *)
(*  Predefined experiments.  To run one, set the single [QuickChick]      *)
(*  line at the very bottom to the chosen [exp_*] identifier.             *)
(* ===================================================================== *)

(* [FULL] real NI soundness: gen + 2 shell-outs + partition + partner + compare *)
Definition exp_full : Checker :=
  forAll (run_GenLLVM gen_PROG_with_args_withfun) vellvm_taint_soundness_partition_fast.

(* [FULL-SLOW] original 3-shell-out soundness check (no invariant dependency) *)
Definition exp_full_slow : Checker :=
  forAll (run_GenLLVM gen_PROG_with_args_withfun) vellvm_taint_soundness_partition.

(* [TAINT-OBS] differential oracle: taint obs == real obs *)
Definition exp_taint_obs : Checker :=
  forAll (run_GenLLVM gen_PROG_with_args_withfun) taint_obs_matches_real.

(* [GEN-ONLY] calibration: generate a program and ignore it (no testing).
   NB: always-true does NOT force the program -> under-measures generation. *)
Definition exp_gen_only : Checker :=
  forAll (run_GenLLVM gen_PROG_with_args_withfun) (fun _ => true).

(* [FORCE-CALIB] gen + force full serialization (show prog) but NO shell-out.
   Tests whether forcing the lazy program closes the 40ms-vs-263ms gap. *)
Definition exp_force_calib : Checker :=
  forAll (run_GenLLVM gen_PROG_with_args_withfun)
         (fun p => match p with
                   | inr (Prog l) => checker (force_str (to_caml_str (show l)))
                   | inl _ => checker true
                   end).

(* [NO-GEN] read previously-generated .ll files and run ONLY the testing
   (2 shell-outs + decode + compare) -- no generation, no serialization. *)
Definition exp_nogen_testing : Checker :=
  forAll (returnGen true)
    (fun _ =>
       let ll := read_next_ll true in
       let n := Z.to_nat (ll_argc ll) in
       match vellvm_taint_run_str ll (repeat 1%Z n) with
       | Some (_, base_obs) =>
           match vellvm_collect_obs_args_str ll (repeat 2%Z n) with
           | Some args_obs =>
               checker (keep_bool (obs_trace_eqb (z_to_obs base_obs) (z_to_obs args_obs)))
           | None => checker true
           end
       | None => checker true
       end).

(* ----- run one experiment (swap the identifier) ----- *)
QuickChick exp_full_flat.
