(** * LangObs: language assembly for the observation-instrumented pipeline

    Identical to [Lang.v] except that the denotation module is
    [DenotationObs] (branch/call debug events emitted) instead of the
    stock [Denotation]. The [Memory] module type is reused from
    [Lang.v]. Used by the NI pipelines (TaintTracker, the
    [-interpret-obs-args] entry); the stock [-interpret] pipeline keeps
    using [Lang.Make]. *)

From Vellvm Require Import
     Semantics.Memory.MemBytes
     Semantics.Memory.DvalueBytes
     Semantics.LLVMParams
     Semantics.GepM
     Semantics.DenotationObs
     Semantics.Lang

     Handlers.Global
     Handlers.Stack
     Handlers.Intrinsics
     Handlers.Pick
     Handlers.MemoryModel
     Handlers.MemoryInterpreters.

  Module Type LangObs (LP: LLVMParams).
    Export LP.

    (* Handlers *)
    Module Global     := Global.Make ADDR IP SIZEOF LP.Events.
    Module Local      := Local.Make ADDR IP SIZEOF LP.Events.
    Module Stack      := Stack.Make ADDR IP SIZEOF LP.Events.
    Module Intrinsics := Intrinsics.Make ADDR IP SIZEOF LP.Events.

    (* Memory (same module type as Lang.v) *)
    Declare Module MEM : Memory LP.
    Export MEM.

    (* Pick handler (depends on memory / concretization) *)
    Module Pick := Pick.Make LP MP ByteM CP.

    (* Denotation: the observation-instrumented variant *)
    Module D := DenotationObs LP MP ByteM CP.

    Export Events Events.DV Global Local Stack Pick Intrinsics
           CP.CONC D.
  End LangObs.

  Module Make (LP : LLVMParams) (MEM' : Memory LP) <: LangObs LP with Module MEM := MEM'.
    Include LangObs LP with Module MEM := MEM'.
  End Make.
