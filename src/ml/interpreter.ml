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

open InterpretationStack.InterpreterStackBigIntptr.LLVM.Stack

open InterpretationStack.InterpreterStackBigIntptr.LLVM.Global

open InterpretationStack.InterpreterStackBigIntptr.LP

open LLVMEvents

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
    | UVALUE_Array (_, l) ->
        fprintf ppf "UVALUE_Array(%a)"
          (pp_print_list ~pp_sep:pp_comma_space pp_uvalue)
          l
    | UVALUE_Vector (_, l) ->
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

let current_line = ref (Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()))

let single_step (m :
      ( ('a, 'b, 'c) coq_L4
      , MMEP.MMSP.coq_MemState
        * ( StoreId.store_id
          * ((lstack_frame * lstack) * (global_env * DV.dvalue)) ) )
        itree ) : (( ('a, 'b, 'c) coq_L4
      , MMEP.MMSP.coq_MemState
        * ( StoreId.store_id
          * ((lstack_frame * lstack) * (global_env * DV.dvalue)) ) )
        itree, (DV.dvalue, exit_condition) result) Either.t =
  let open ITreeDefinition in
  match observe m with
  (* Internal steps compute as nothing *)
  | TauF x ->
     if !debug_flag then begin
         let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
         if loc_str <> !current_line then begin 
             Printf.printf "%s\n%!" loc_str;
             current_line := loc_str
           end
     end;
     Either.left x
  (* SAZ: Could inspect the memory or stack here too. *)
  (* We finished the computation *)
  | RetF (_, (_, (_, (_, v)))) -> Either.right (Ok v)
  (* The ExternalCallE effect *)
  | VisF (Sum.Coq_inl1 (ExternalCall (t, _, dvs)), _) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     let typ_str = Camlcoq.camlstring_of_coqstring (ReprAST.repr_dtyp t) in
     let args_str = string_of_int (List.length dvs) in
     Either.right
       (Error (UninterpretedCall
                 (Printf.sprintf "%s: Call with return type %s, %s dvalues."
                    loc_str typ_str args_str)))
  (* Still TODO: Integrate 2nd argument *)
  (* The IO_stdout effect *)
  | VisF (Sum.Coq_inl1 (IO_stdout bytes), k) ->
      let str = string_of_bytes bytes in
      output_bytes stdout str ;
      Either.left (k (Obj.magic ()))
  (* The IO_stderr effect *)
  | VisF (Sum.Coq_inl1 (IO_stderr bytes), k) ->
      let str = string_of_bytes bytes in
      output_bytes stderr str ;
      Either.left (k (Obj.magic ()))
  (* The OOME effect *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inl1 _msg), _k) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     Either.right (Error (OutOfMemory loc_str))

  (* LLVM Exception event *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _uv)), _k) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     Either.right (Error (LLVMException loc_str))

  (* UBE event *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _msg))), _k) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     Either.right (Error (UndefinedBehavior loc_str))

  (* The DebugE effect *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _msg)))), k) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     (debug loc_str;
      Either.left ((k (Obj.magic DV.DVALUE_None))))

  (* The FailureE effect is a failure *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 _msg)))), _) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     Either.right (Error (Failed loc_str))

let rec step
    (m :
      ( ('a, 'b, 'c) coq_L4
      , MMEP.MMSP.coq_MemState
        * ( StoreId.store_id
          * ((lstack_frame * lstack) * (global_env * DV.dvalue)) ) )
      itree ) : (DV.dvalue, exit_condition) result =
  match single_step m with
  | Either.Left x -> step x
  | Either.Right res -> res

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
  Out_channel.set_buffered stdout false;
  Out_channel.set_buffered stderr false;
  step (TopLevel.TopLevelBigIntptr.interpreter (List.map Camlcoq.coqstring_of_camlstring args) prog)

(* ========================================================================= *)
(* NI testing entry points                                                    *)
(* ========================================================================= *)

(* sz32 = positive 32, used to construct [DTYPE_I 32] and [UVALUE_I 32 _]. *)
let sz32 =
  BinNums.Coq_xO (BinNums.Coq_xO (BinNums.Coq_xO (BinNums.Coq_xO (BinNums.Coq_xO BinNums.Coq_xH))))

let i32_uvalue_of_int (v : int) : DV.uvalue =
  DV.UVALUE_I (sz32, Integers.repr sz32 (Camlcoq.Z.of_sint v))

(* Step an [interp_mcfg4_exec_obs]-shaped itree.
   Compared with [single_step], the [RetF] case carries the [list Z]
   observation list, and the result is [(obs * dvalue)] rather than [dvalue].
   Other event cases mirror [single_step] verbatim. *)
let rec step_obs m =
  match observe m with
  | TauF x -> step_obs x
  | RetF (_, (_, (obs, (_, (_, v))))) -> Ok (obs, v)
  | VisF (Sum.Coq_inl1 (ExternalCall (_, _, _)), _) ->
      Error (UninterpretedCall "Uninterpreted external call")
  | VisF (Sum.Coq_inl1 (IO_stdout bytes), k) ->
      output_bytes stdout (string_of_bytes bytes);
      step_obs (k (Obj.magic ()))
  | VisF (Sum.Coq_inl1 (IO_stderr bytes), k) ->
      output_bytes stderr (string_of_bytes bytes);
      step_obs (k (Obj.magic ()))
  | VisF (Sum.Coq_inr1 (Sum.Coq_inl1 _), _) ->
      Error (OutOfMemory "")
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _)), _) ->
      Error (LLVMException "")
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _))), _) ->
      Error (UndefinedBehavior "")
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _)))), k) ->
      step_obs (k (Obj.magic DV.DVALUE_None))
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 _)))), _) ->
      Error (Failed "")

(** Run [interpreter_gen_obs] with a list of [i32] arguments fed to
    [main(i32, …, i32)]. Returns the observation trace and the final
    dvalue. *)
let interpret_with_args_obs
      (args : int list)
      (prog :
         ( LLVMAst.typ
         , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
           LLVMAst.toplevel_entity
           list )
    : (BinNums.coq_Z list * DV.dvalue, exit_condition) result =
  Out_channel.set_buffered stdout false;
  Out_channel.set_buffered stderr false;
  let arg_uvals = List.map i32_uvalue_of_int args in
  let args_itree =
    lazy (ITreeDefinition.Coq_go (ITreeDefinition.RetF (Obj.magic arg_uvals)))
  in
  let t =
    TopLevel.TopLevelBigIntptr.interpreter_gen_obs
      (DynamicTypes.DTYPE_I sz32)
      (LLVMAst.Name ('m' :: 'a' :: 'i' :: 'n' :: []))
      args_itree
      prog
  in
  step_obs t

(* Step the taint-augmented itree.
   Same shape as [step_obs] but the RetF carries an extra [tstate], so
   the final value is [(obs * tstate * dvalue)]. *)
let rec step_taint_obs m =
  match observe m with
  | TauF x -> step_taint_obs x
  | RetF (_, (_, (obs, (_, (_, (ts, v)))))) -> Ok (obs, ts, v)
  | VisF (Sum.Coq_inl1 (ExternalCall (_, _, _)), _) ->
      Error (UninterpretedCall "Uninterpreted external call")
  | VisF (Sum.Coq_inl1 (IO_stdout bytes), k) ->
      output_bytes stdout (string_of_bytes bytes);
      step_taint_obs (k (Obj.magic ()))
  | VisF (Sum.Coq_inl1 (IO_stderr bytes), k) ->
      output_bytes stderr (string_of_bytes bytes);
      step_taint_obs (k (Obj.magic ()))
  | VisF (Sum.Coq_inr1 (Sum.Coq_inl1 _), _) ->
      Error (OutOfMemory "")
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _)), _) ->
      Error (LLVMException "")
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _))), _) ->
      Error (UndefinedBehavior "")
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _)))), k) ->
      step_taint_obs (k (Obj.magic DV.DVALUE_None))
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 _)))), _) ->
      Error (Failed "")

(** Run the partition-style taint tracker with a list of [i32] arguments.
    Returns the observation trace, the final [tstate] (containing the
    public partition in [ts_tobs]), and the dvalue.

    The pipeline composes:
      1. [TopLevelBigIntptr.build_global_environment] (set up global env)
      2. [TaintTrackerBigIntptr.denote_function_taint] (taint denotation)
      3. [Recursion.interp_mrec] (L0' → L0, trivial since no calls)
      4. [InterpreterStackBigIntptr.interp_mcfg4_exec_obs] (obs collection)

    Built in OCaml rather than Rocq because extraction generates
    incompatible (but isomorphic) [itree] types across module instances. *)
let interpret_with_args_taint_obs
      (args : int list)
      (prog :
         ( LLVMAst.typ
         , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
           LLVMAst.toplevel_entity
           list )
    : (BinNums.coq_Z list * TaintTracker.tstate * DV.dvalue, exit_condition) result =
  Out_channel.set_buffered stdout false;
  Out_channel.set_buffered stderr false;
  let arg_uvals = List.map i32_uvalue_of_int args in
  let mcfg =
    TypToDtyp.convert_types
      (CFG.mcfg_of_tle
         (TopLevel.TopLevelBigIntptr.link
            TopLevel.TopLevelBigIntptr.coq_PREDEFINED_FUNCTIONS prog))
  in
  let main_name = 'm' :: 'a' :: 'i' :: 'n' :: [] in
  let find_main defs =
    List.find_opt
      (fun df ->
        match LLVMAst.(df.df_prototype.dc_name) with
        | LLVMAst.Name s -> s = main_name
        | _ -> false)
      defs
  in
  match find_main mcfg.CFG.m_definitions with
  | None -> Error (Failed "main function not found for taint tracking")
  | Some main_def ->
      let t : _ ITreeDefinition.itree =
        Obj.magic (
          Monad.bind (Obj.magic ITreeDefinition.coq_Monad_itree)
            (Obj.magic (TopLevel.TopLevelBigIntptr.build_global_environment mcfg))
            (fun (_ : unit) ->
               let t_L0' =
                 TaintTracker.TaintTrackerBigIntptr.denote_function_taint
                   main_def (Obj.magic arg_uvals)
               in
               (* No CallE expected for [_nofun] programs; if the handler
                  is ever called, return a dummy unit. *)
               Recursion.interp_mrec
                 (fun _ _ ->
                    Obj.magic
                      (lazy
                         (ITreeDefinition.Coq_go
                            (ITreeDefinition.RetF (Obj.magic ())))))
                 (Obj.magic t_L0'))
        )
      in
      let t_obs =
        InterpretationStack.InterpreterStackBigIntptr.interp_mcfg4_exec_obs
          (Obj.magic t) []
          ({ stack_vars = []; stack_handler = None; stack_exc = None; stack_loc = None }, [])
          BinNums.N0
          InterpretationStack.InterpreterStackBigIntptr.MEM.MMEP.MMSP.initial_memory_state
      in
      step_taint_obs t_obs
