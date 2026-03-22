(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

open InterpretationStack.InterpreterStackBigIntptr.LLVM.MEM

open InterpretationStack.InterpreterStackBigIntptr.LLVM.Local

open InterpretationStack.InterpreterStackBigIntptr.LLVM.Stack

open InterpretationStack.InterpreterStackBigIntptr.LLVM.Global

open InterpretationStack.InterpreterStackBigIntptr.LP.Events

open Format
open ITreeDefinition
open Result

(* TODO: probably should be part of ADDRESS module interface*)
let pp_addr :
    Format.formatter -> MemoryModelImplementation.InfAddr.addr -> unit =
 fun ppf _ -> fprintf ppf "UVALUE_Addr(?)"

(* Converts `float` to a `string` at max precision. Both OCaml `printf` and
   `string_of_float` truncate and do not print all significat digits. *)
let string_of_float_full f =
  (* Due to the limited number of bits in the representation of doubles, the
     maximal precision is 324. See Wikipedia. *)
  let s = sprintf "%.350f" f in
  Str.global_replace (Str.regexp "0+$") "" s

let rec pp_uvalue : Format.formatter -> DV.uvalue -> unit =
  let open Camlcoq in
  let pp_comma_space ppf () = pp_print_string ppf ", " in
  fun ppf -> function
    | UVALUE_Addr _x -> fprintf ppf "UVALUE_Addr"
    | UVALUE_I (sz, x) ->
        fprintf ppf "UVALUE_I%d(%d)"
          (Camlcoq.P.to_int sz) (Camlcoq.Z.to_int (Integers.unsigned sz x))
    | UVALUE_IPTR x ->
        fprintf ppf "UVALUE_IPTR(%d)"
          (Camlcoq.Z.to_int
             (InterpretationStack.InterpreterStackBigIntptr.LP.IP.to_Z x) )
    | UVALUE_Double x ->
        fprintf ppf "UVALUE_Double(%s)"
          (string_of_float_full (camlfloat_of_coqfloat x))
    | UVALUE_Float x ->
        fprintf ppf "UVALUE_Float(%s)"
          (string_of_float_full (camlfloat_of_coqfloat32 x))
    | UVALUE_Poison _ -> fprintf ppf "UVALUE_Poison"
    | UVALUE_None -> fprintf ppf "UVALUE_None"
    | UVALUE_Undef _ -> fprintf ppf "UVALUE_Undef"
    | UVALUE_Struct l ->
        fprintf ppf "UVALUE_Struct(%a)"
          (pp_print_list ~pp_sep:pp_comma_space pp_uvalue)
          l
    | UVALUE_Packed_struct l ->
        fprintf ppf "UVALUE_Packet_struct(%a)"
          (pp_print_list ~pp_sep:pp_comma_space pp_uvalue)
          l
    | UVALUE_Array (t, l) ->
        fprintf ppf "UVALUE_Array(%a)"
          (pp_print_list ~pp_sep:pp_comma_space pp_uvalue)
          l
    | UVALUE_Vector (t, l) ->
        fprintf ppf "UVALUE_Vector(%a)"
          (pp_print_list ~pp_sep:pp_comma_space pp_uvalue)
          l
    | _ -> fprintf ppf "pp_uvalue: todo"

let char_of_I8 x =
  char_of_int (Camlcoq.Z.to_int (Integers.unsigned (Camlcoq.P.of_int 8) x))

(* Converts a list of VellvmIntegers.Int8 values to OCaml string *)
let string_of_bytes (bytes : Integers.bit_int list) : bytes =
  List.map char_of_I8 bytes |> List.to_seq |> Bytes.of_seq

let debug_flag = ref false

(** Print a debug message to stdout if the `debug_flag` is enabled.

    This is used to implement `debugE` events.
*)
let debug (msg : string) =
  if !debug_flag then Printf.printf "DEBUG: %s\n%!" msg

(** The `step` function walks through an itree and handles some
    remaining events.

    In particular, `step` handles `debugE`, `failE`, and
    `ExternalCallE` events, which are not handled by the
    TopLevel.interpreter function extracted from Coq.

    Calling `step` could either loop forever, return an error,
    or return the dvalue result returned from the itree.
 *)
let rec step
    (m :
      ( 'a coq_L4
      , MMEP.MMSP.coq_MemState
        * ( StoreId.store_id
          * ((local_env * lstack) * (global_env * DV.dvalue)) ) )
      itree ) : (DV.dvalue, exit_condition) result =
  let open ITreeDefinition in
  match observe m with
  (* Internal steps compute as nothing *)
  | TauF x -> step x
  (* SAZ: Could inspect the memory or stack here too. *)
  (* We finished the computation *)
  | RetF (_, (_, (_, (_, v)))) -> Ok v
  (* The ExternalCallE effect *)
  | VisF (Sum.Coq_inl1 (ExternalCall (t, _, dvs)), _) ->
      Error (UninterpretedCall ("Call with return type "
       ^ (Camlcoq.camlstring_of_coqstring (ReprAST.repr_dtyp t))
       ^ ", " ^ (string_of_int (List.length dvs)) ^ " dvalues."))
  (* Still TODO: Integrate 2nd argument *)
  (* The IO_stdout effect *)
  | VisF (Sum.Coq_inl1 (IO_stdout bytes), k) ->
      let str = string_of_bytes bytes in
      output_bytes stdout str ;
      step (k (Obj.magic ()))
  (* The IO_stderr effect *)
  | VisF (Sum.Coq_inl1 (IO_stderr bytes), k) ->
      let str = string_of_bytes bytes in
      output_bytes stderr str ;
      step (k (Obj.magic ()))
  (* The OOME effect *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inl1 msg), _k) ->
     Error (OutOfMemory "")

  (* UBE event *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 msg)), _k) ->
     Error (UndefinedBehavior "")

  (* The DebugE effect *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 msg))), k) ->
     (debug "";
      step (k (Obj.magic DV.DVALUE_None)))

  (* The FailureE effect is a failure *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 msg))), _) ->
     Error (Failed "")

(* The only visible effects from LLVMIO that should propagate to the
   interpreter are: - Call to external functions - Debug *)

(* | Call(_, f, _) ->
 *   (Printf.printf "UNINTERPRETED EXTERNAL CALL: %s - returning 0l to the caller\n"
 *      (Camlcoq.camlstring_of_coqstring f));
 *   step (k (Obj.magic (DV.DVALUE_I64 VellvmIntegers.Int64.zero))) *)

(** Interpret an LLVM program, returning a result that contains either the
    dvalue result returned by the LLVM program, or an error message.

    Note: programs consist of a non-empty list of blocks, represented by a
    tuple of a single block, and a possibly empty list of blocks.
 *)
let interpret
      (args : string list)
      (prog :
         ( LLVMAst.typ
         , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
           LLVMAst.toplevel_entity
           list )
    : (DV.dvalue, exit_condition) result =
  step (TopLevel.TopLevelBigIntptr.interpreter (List.map Camlcoq.coqstring_of_camlstring args) prog)

(** Interpret a program where main takes a single i32 argument (the "secret" for NI testing).
    The secret integer is passed directly as a UVALUE_I 32 to main, bypassing the
    standard argc/argv mechanism. *)
let interpret_with_i32
      (secret : int)
      (prog :
         ( LLVMAst.typ
         , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
           LLVMAst.toplevel_entity
           list )
    : (DV.dvalue, exit_condition) result =
  (* Build positive for 32: 2^5 = 32 = xO(xO(xO(xO(xO(xH))))) *)
  let sz32 = BinNums.Coq_xO (BinNums.Coq_xO (BinNums.Coq_xO (BinNums.Coq_xO (BinNums.Coq_xO BinNums.Coq_xH)))) in
  let secret_uval = DV.UVALUE_I (sz32, Integers.repr sz32 (Camlcoq.Z.of_sint secret)) in
  (* itree that immediately returns [secret_uval] *)
  let args_itree = lazy (ITreeDefinition.Coq_go (ITreeDefinition.RetF (Obj.magic [secret_uval]))) in
  step (TopLevel.TopLevelBigIntptr.interpreter_gen
    (DynamicTypes.DTYPE_I sz32)
    ('m'::('a'::('i'::('n'::[]))))
    args_itree
    prog)

(** Like interpret_with_i32 but collects Load/Store observations using
    the Rocq-native observe_L2 pipeline (no MemoryModel.ml patching needed).
    Returns (observation_list, dvalue_result). *)
let interpret_with_i32_obs
      (secret : int)
      (prog :
         ( LLVMAst.typ
         , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
           LLVMAst.toplevel_entity
           list )
    : (BinNums.coq_Z list * DV.dvalue, exit_condition) result =
  let sz32 = BinNums.Coq_xO (BinNums.Coq_xO (BinNums.Coq_xO (BinNums.Coq_xO (BinNums.Coq_xO BinNums.Coq_xH)))) in
  let secret_uval = DV.UVALUE_I (sz32, Integers.repr sz32 (Camlcoq.Z.of_sint secret)) in
  let args_itree = lazy (ITreeDefinition.Coq_go (ITreeDefinition.RetF (Obj.magic [secret_uval]))) in
  let t = TopLevel.TopLevelBigIntptr.interpreter_gen_obs
    (DynamicTypes.DTYPE_I sz32)
    ('m'::('a'::('i'::('n'::[]))))
    args_itree
    prog in
  (* step_obs: like step but extracts (obs, dvalue) from the deeper nesting *)
  let rec step_obs m =
    let open ITreeDefinition in
    match observe m with
    | TauF x -> step_obs x
    (* Result: (MemState, (store_id, (obs, (local_env * stack, (global_env, dvalue))))) *)
    | RetF (_, (_, (obs, (_, (_, v))))) -> Ok (obs, v)
    | VisF (Sum.Coq_inl1 (ExternalCall (_, _, _)), _) ->
        Error (UninterpretedCall "Uninterpreted external call")
    | VisF (Sum.Coq_inl1 (IO_stdout bytes), k) ->
        let str = string_of_bytes bytes in
        output_bytes stdout str ;
        step_obs (k (Obj.magic ()))
    | VisF (Sum.Coq_inl1 (IO_stderr bytes), k) ->
        let str = string_of_bytes bytes in
        output_bytes stderr str ;
        step_obs (k (Obj.magic ()))
    | VisF (Sum.Coq_inr1 (Sum.Coq_inl1 _), _) ->
        Error (OutOfMemory "")
    | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _)), _) ->
        Error (UndefinedBehavior "")
    | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _))), k) ->
        step_obs (k (Obj.magic DV.DVALUE_None))
    | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 _))), _) ->
        Error (Failed "")
  in
  step_obs t

(** Like interpret_with_i32_obs but accepts a list of i32 arguments.
    Each integer in the list is passed as a UVALUE_I 32 to main. *)
let interpret_with_args_obs
      (args : int list)
      (prog :
         ( LLVMAst.typ
         , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
           LLVMAst.toplevel_entity
           list )
    : (BinNums.coq_Z list * DV.dvalue, exit_condition) result =
  let sz32 = BinNums.Coq_xO (BinNums.Coq_xO (BinNums.Coq_xO (BinNums.Coq_xO (BinNums.Coq_xO BinNums.Coq_xH)))) in
  let arg_uvals = List.map (fun v ->
    DV.UVALUE_I (sz32, Integers.repr sz32 (Camlcoq.Z.of_sint v))
  ) args in
  let args_itree = lazy (ITreeDefinition.Coq_go (ITreeDefinition.RetF (Obj.magic arg_uvals))) in
  let t = TopLevel.TopLevelBigIntptr.interpreter_gen_obs
    (DynamicTypes.DTYPE_I sz32)
    ('m'::('a'::('i'::('n'::[]))))
    args_itree
    prog in
  let rec step_obs m =
    let open ITreeDefinition in
    match observe m with
    | TauF x -> step_obs x
    | RetF (_, (_, (obs, (_, (_, v))))) -> Ok (obs, v)
    | VisF (Sum.Coq_inl1 (ExternalCall (_, _, _)), _) ->
        Error (UninterpretedCall "Uninterpreted external call")
    | VisF (Sum.Coq_inl1 (IO_stdout bytes), k) ->
        let str = string_of_bytes bytes in
        output_bytes stdout str ;
        step_obs (k (Obj.magic ()))
    | VisF (Sum.Coq_inl1 (IO_stderr bytes), k) ->
        let str = string_of_bytes bytes in
        output_bytes stderr str ;
        step_obs (k (Obj.magic ()))
    | VisF (Sum.Coq_inr1 (Sum.Coq_inl1 _), _) ->
        Error (OutOfMemory "")
    | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _)), _) ->
        Error (UndefinedBehavior "")
    | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _))), k) ->
        step_obs (k (Obj.magic DV.DVALUE_None))
    | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 _))), _) ->
        Error (Failed "")
  in
  step_obs t

(** Run taint analysis on a program (pure AST, Layer 1).
    Returns the list of leaked variable names as raw_id list. *)
let taint_analyze
      (prog :
         ( LLVMAst.typ
         , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
           LLVMAst.toplevel_entity
           list )
    : LLVMAst.raw_id list =
  TaintTrackingSemantic.taint_program_gen (Obj.magic prog)

(** Semantic taint tracking (Option B) with observation collection.
    Uses denote_function_taint from TaintTrackingSemantic.v, which
    tracks taint through the real denotation pipeline including
    concrete memory addresses for Load/Store.

    Pipeline:
    1. build_global_environment (set up globals)
    2. denote_function_taint (returns itree L0' (tstate * uvalue))
    3. interp_mrec (convert L0' -> L0, trivial handler for no calls)
    4. interp_mcfg4_exec_obs (observation collection at L2)

    Returns (obs_list, tstate, dvalue) or error. *)
let interpret_with_i32_taint_obs
      (secret : int)
      (prog :
         ( LLVMAst.typ
         , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
           LLVMAst.toplevel_entity
           list )
    : (BinNums.coq_Z list * TaintTrackingSemantic.tstate * DV.dvalue, exit_condition) result =
  let sz32 = BinNums.Coq_xO (BinNums.Coq_xO (BinNums.Coq_xO (BinNums.Coq_xO (BinNums.Coq_xO BinNums.Coq_xH)))) in
  let secret_uval = DV.UVALUE_I (sz32, Integers.repr sz32 (Camlcoq.Z.of_sint secret)) in
  (* Convert program to dtyp mcfg *)
  let mcfg = TypToDtyp.convert_types
    (CFG.mcfg_of_tle
      (TopLevel.TopLevelBigIntptr.link
        TopLevel.TopLevelBigIntptr.coq_PREDEFINED_FUNCTIONS prog)) in
  (* Find main's definition in the mcfg *)
  let main_name = 'm'::('a'::('i'::('n'::[]))) in
  let find_main defs =
    List.find_opt (fun df ->
      match LLVMAst.(df.df_prototype.dc_name) with
      | LLVMAst.Name s -> s = main_name
      | _ -> false
    ) defs
  in
  match find_main mcfg.CFG.m_definitions with
  | None -> Error (Failed "main function not found for taint tracking")
  | Some main_def ->
    (* Build the itree L0 pipeline:
       1. build_global_environment
       2. denote_function_taint (returns itree L0')
       3. interp_mrec converts L0' -> L0 *)
    let secret_args = main_def.LLVMAst.df_args in
    let t : _ ITreeDefinition.itree =
      Obj.magic (
        Monad.bind (Obj.magic ITreeDefinition.coq_Monad_itree)
          (Obj.magic (TopLevel.TopLevelBigIntptr.build_global_environment mcfg))
          (fun (_ : unit) ->
            let t_L0' = TaintTrackingSemantic.SemanticTaintBigIntptr.denote_function_taint
              main_def (Obj.magic [secret_uval]) secret_args in
            (* interp_mrec: trivial handler that raises on any CallE.
               The handler is never actually called for nofun programs. *)
            Recursion.interp_mrec (fun _ _ ->
              (* Return a dummy itree — this path should never be taken *)
              Obj.magic (lazy (ITreeDefinition.Coq_go (ITreeDefinition.RetF (Obj.magic ()))))
            ) (Obj.magic t_L0')
          )
      )
    in
    (* Feed through interp_mcfg4_exec_obs *)
    let t_obs = InterpretationStack.InterpreterStackBigIntptr.interp_mcfg4_exec_obs
      (Obj.magic t) [] ([], []) BinNums.N0
      InterpretationStack.InterpreterStackBigIntptr.MEM.MMEP.MMSP.initial_memory_state
    in
    (* Step through the result itree *)
    let rec step_taint_obs m =
      let open ITreeDefinition in
      match observe m with
      | TauF x -> step_taint_obs x
      (* Result: (MemState, (store_id, (obs, (local_env * stack, (global_env, (tstate, uvalue)))))) *)
      | RetF (_, (_, (obs, (_, (_, (ts, uv)))))) ->
          let dv = Obj.magic uv in
          Ok (obs, ts, dv)
      | VisF (Sum.Coq_inl1 (ExternalCall (_, _, _)), _) ->
          Error (UninterpretedCall "Uninterpreted external call")
      | VisF (Sum.Coq_inl1 (IO_stdout bytes), k) ->
          let str = string_of_bytes bytes in
          output_bytes stdout str ;
          step_taint_obs (k (Obj.magic ()))
      | VisF (Sum.Coq_inl1 (IO_stderr bytes), k) ->
          let str = string_of_bytes bytes in
          output_bytes stderr str ;
          step_taint_obs (k (Obj.magic ()))
      | VisF (Sum.Coq_inr1 (Sum.Coq_inl1 _), _) ->
          Error (OutOfMemory "")
      | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _)), _) ->
          Error (UndefinedBehavior "")
      | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _))), k) ->
          step_taint_obs (k (Obj.magic DV.DVALUE_None))
      | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 _))), _) ->
          Error (Failed "")
    in
    step_taint_obs (Obj.magic t_obs)
