(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

open Printf
open Base

open InterpretationStack.InterpreterStackBigIntptr.LP.Events

let of_str = Camlcoq.camlstring_of_coqstring

let string_of_dvalue (d : DV.dvalue) = of_str (DV.show_dvalue d)

let interpret = ref false

(* NI testing flags: comma-separated lists of i32 arguments to pass to main.
   None means the flag wasn't given on this invocation. *)
let interpret_obs_args : string option ref = ref None
let taint_track_args : string option ref = ref None

let transform
    (prog :
      ( LLVMAst.typ
      , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
      LLVMAst.toplevel_entity
      list ) :
    ( LLVMAst.typ
    , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
    LLVMAst.toplevel_entity
    list =
  Transform.transform prog

let print_banner s =
  let rec dashes n = if n = 0 then "" else "-" ^ dashes (n - 1) in
  printf "%s %s\n%!" (dashes (79 - String.length s)) s

(* Todo add line count information *)
let parse_tests filename =
  let assertions = ref [] in
  let channel = open_in filename in
  Assertion.reset_parsing_mode () ;
  (* Put the parser into "NormalMode" *)
  try
    while true do
      let line = input_line channel in
      assertions := Assertion.parse_assertion filename line @ !assertions
    done ;
    []
  with End_of_file -> close_in channel ; List.rev !assertions

let string_of_file (f : in_channel) : string =
  let rec _string_of_file (stream : string list) (f : in_channel) :
      string list =
    try
      let s = input_line f in
      _string_of_file (s :: stream) f
    with End_of_file -> stream
  in
  String.concat "\n" (List.rev (_string_of_file [] f))

(* file processing
   ---------------------------------------------------------- *)
let link_files : string list ref = ref []

let add_link_file path = link_files := path :: !link_files

(* Parse a comma-separated list of decimal integers (e.g. "5,3,-7"). *)
let parse_int_args (s : string) : int list =
  List.map int_of_string (String.split_on_char ',' s)

(* Print a list of Coq Z observation events between framed markers. *)
let print_obs_trace (obs : BinNums.coq_Z list) =
  Printf.printf "---OBS_TRACE_BEGIN---\n";
  List.iter (fun z -> Printf.printf "%d\n" (Camlcoq.Z.to_int z)) obs;
  Printf.printf "---OBS_TRACE_END---\n"

(* Print a single raw_id in human-readable form. *)
let print_raw_id (id : LLVMAst.raw_id) =
  match id with
  | LLVMAst.Name s ->
      List.iter (fun c -> Printf.printf "%c" c) s;
      Printf.printf "\n"
  | LLVMAst.Anon n -> Printf.printf "anon_%d\n" (Camlcoq.Z.to_int n)
  | LLVMAst.Raw  n -> Printf.printf "raw_%d\n"  (Camlcoq.Z.to_int n)

(* Print the public partition output of the taint tracker: register
   names that influenced an observation, and memory addresses that
   influenced an observation, each in its own framed section. *)
let print_tobs_partition (ts : TaintTracker.tstate) =
  let ids, addrs = TaintTracker.split_taint ts.TaintTracker.ts_tobs in
  Printf.printf "---TOBS_REGS_BEGIN---\n";
  List.iter print_raw_id ids;
  Printf.printf "---TOBS_REGS_END---\n";
  Printf.printf "---TOBS_ADDRS_BEGIN---\n";
  List.iter (fun z -> Printf.printf "%d\n" (Camlcoq.Z.to_int z)) addrs;
  Printf.printf "---TOBS_ADDRS_END---\n"

let process_ll_file command_line_arguments path file =
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  (* [BINARY TIMER] runs INSIDE the ./vellvm process, once per shell-out.
     __tparse = time to PARSE the .ll text back into an AST (IO.parse_file) --
     i.e. the cost of reconstructing the program the harness already had, paid
     only because we cross a process boundary. __t1 marks the start of the
     actual run (interpret / obs / taint) below. *)
  let __t0 = Unix.gettimeofday () in
  let ll_ast = IO.parse_file path in
  let __tparse = Unix.gettimeofday () -. __t0 in
  let __t1 = Unix.gettimeofday () in
  let _ =
    if !interpret then
      match Interpreter.interpret command_line_arguments ll_ast with
      | Ok dv ->
          Printf.printf "Program terminated with: %s\n" (string_of_dvalue dv)
      | Error e -> failwith (Result.string_of_exit_condition e)
  in
  (* -interpret-obs-args <n1,n2,…> *)
  (match !interpret_obs_args with
   | Some args_str ->
       let args = parse_int_args args_str in
       (match Interpreter.interpret_with_args_obs args ll_ast with
        | Ok (obs, dv) ->
            Printf.printf "Program terminated with: %s\n" (string_of_dvalue dv);
            print_obs_trace obs
        | Error e ->
            Printf.printf "Program error: %s\n" (Result.string_of_exit_condition e))
   | None -> ());
  (* -taint-track-args <n1,n2,…> *)
  (match !taint_track_args with
   | Some args_str ->
       let args = parse_int_args args_str in
       (match Interpreter.interpret_with_args_taint_obs args ll_ast with
        | Ok (obs, ts, dv) ->
            Printf.printf "Program terminated with: %s\n" (string_of_dvalue dv);
            print_tobs_partition ts;
            print_obs_trace obs
        | Error e ->
            Printf.printf "Program error: %s\n" (Result.string_of_exit_condition e))
   | None -> ());
  (* __trun = the ACTUAL run = interpret / obs-interpret / taint-track (only one
     mode fires per invocation). This is the "실제 실험" phase, after parsing,
     still inside the binary. Dominated by the program's runtime (loop counts),
     so it varies wildly. *)
  let __trun = Unix.gettimeofday () -. __t1 in
  let __mode = (match !taint_track_args with
                | Some _ -> "taint"
                | None -> (match !interpret_obs_args with Some _ -> "obs" | None -> "interp")) in
  (* Log "<mode> <parse_secs> <run_secs>" per binary invocation → /tmp/ni_phases.txt.
     The harness's TIMER A (NITests.v) times the WHOLE process, so the
     process-spawn + stdout-transfer overhead = (TIMER A) − (__tparse + __trun). *)
  (let __oc = Stdlib.open_out_gen [Stdlib.Open_append; Stdlib.Open_creat] 0o644 "/tmp/ni_phases.txt" in
   Printf.fprintf __oc "%s %f %f\n" __mode __tparse __trun; Stdlib.close_out __oc);
  let ll_ast' = transform ll_ast in
  let vll_file = Platform.gen_name !Platform.output_path file ".v.ll" in
  let _ = IO.output_file vll_file ll_ast' in
  ()

let process_file command_line_arguments path =
  let _ = Printf.printf "Processing: %s\n" path in
  let basename, ext = Platform.path_to_basename_ext path in
  match ext with
  | "ll" -> process_ll_file command_line_arguments path basename
  | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path

let process_files command_line_args files =
  List.iter (process_file command_line_args) files

(* file running ---------------------------------------------------------- *)
(* Parses and runs the ll file at the given path, returning the dvalue
   produced. *)
let run_ll_file command_line_arguments path : (DV.dvalue, Result.exit_condition) result =
  let _ = Platform.verb @@ Printf.sprintf "* running file: %s\n" path in
  let ll_ast = IO.parse_file path in
  Interpreter.interpret command_line_arguments ll_ast
