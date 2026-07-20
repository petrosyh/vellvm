(* -------------------------------------------------------------------------- *
 *   select-probe : impure realization of the SELECT_EVAL probe primitives     *
 *   (Vellvm DenotationObs.sel_probe_on / sel_probe_emit, PLAN §5 Step-1).      *
 *                                                                             *
 *   Stdlib-only, so this module can be a dependency of the extracted library. *
 *   The probe build is a diagnostic pass: it is NEVER used for kill runs or   *
 *   the UB gate. With [enabled = false] the Coq-side gate never enters the    *
 *   probe path, so the normal binary is byte-identical.                       *
 * -------------------------------------------------------------------------- *)

(* Runtime flag, flipped by the driver's -select-probe option. Read by the
   extracted [sel_probe_on] (Extract.v: "(fun _ -> !Selprobe.enabled)"). *)
let enabled : bool ref = ref false

(* Per-run, per-sid dynamic-occurrence counter (the SELECT_EVAL [occ] field). *)
let occ_tbl : (int, int) Hashtbl.t = Hashtbl.create 64

(* Reset the occ counters at the start of each program run (the driver calls
   this before each obs interpretation, so counts do not leak across programs). *)
let reset () = Hashtbl.clear occ_tbl

(* Coq [string] extracts to [char list]; pack it into a native OCaml string. *)
let camlstring_of_coqstring (s : char list) : string =
  let b = Buffer.create (List.length s) in
  List.iter (Buffer.add_char b) s;
  Buffer.contents b

(* Parse the numeric sid from a "sel<N>" register name; -1 if it does not match. *)
let sid_of_name (nm : string) : int =
  let n = String.length nm in
  if n > 3 && String.sub nm 0 3 = "sel"
  then (try int_of_string (String.sub nm 3 (n - 3)) with _ -> -1)
  else -1

(* Emit one SELECT_EVAL line. [name] is the %sel<N> register name; [rest] is the
   pre-formatted "cond=.. arm=.. v1=.. v2=.." tail built on the Coq side. Both
   arrive as Coq [char list]s (the extracted representation of [string]). The
   line is flushed immediately and carries its own "SELECT_EVAL " prefix, so it
   is cleanly separable from the driver's OBS_TRACE section. *)
let emit (name : char list) (rest : char list) : unit =
  let nm = camlstring_of_coqstring name in
  let sid = sid_of_name nm in
  let occ = try Hashtbl.find occ_tbl sid with Not_found -> 0 in
  Hashtbl.replace occ_tbl sid (occ + 1);
  Printf.printf "SELECT_EVAL sid=%d occ=%d %s\n%!" sid occ (camlstring_of_coqstring rest)
