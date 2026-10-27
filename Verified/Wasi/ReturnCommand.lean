import Verified.Wasi.Return
import Verified.Wasi.CommandSpec

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem wp_command_ret {World : Type} {host : Host World}
    {S : List Sig} {effects : List EffectSig} {context : List Ty} {type : Ty}
    {source target : Wasm.Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
    {fits : Fits S} {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)}
    {pool : Bytes.LiteralPool} {value : Expr S context type} {env : Env context}
    {slots : List Slot} {paid : List Bool} {live : Nat → Bool} {params : List Value}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {h base : Nat}
    {aborts : Bool}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source)
    (spec : CodeSpec source funs flags bounds fits sourceHost params value env slots paid live pool)
    (form : Encoding.ProgramForm (value.code (pool := pool) h slots base live ++
      coerceCode h type (value.mode (slots.map Slot.mode)) .owned base))
    (closed : Relocation.programClosed source.funcs.length
      (value.code (pool := pool) h slots base live ++
        coerceCode h type (value.mode (slots.map Slot.mode)) .owned base) = true)
    (positions : locals.positions = h) (parameters : locals.params = params)
    (vars : Holds env slots (fun i => live i || value.uses i) base heap
      (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (safe : pool.Safe env slots (fun i => live i || value.uses i) heap
      (PureTransport.erase initial) locals)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (room : base + max value.width (copyWidth type) ≤ h)
    (place : value.placeArgs = true)
    (allowed : (!(value.fits funs fits env) || !decide
        (heap.Within (PureTransport.erase initial) source
          (returnCost funs flags bounds value env slots paid live
            (PureTransport.erase initial) locals))) = true → aborts = true) :
    wp target ((Command.ret value : Command S effects context (.value type)).code
        (pool := pool) source h slots base live)
      (CommandResult host env slots (fun i => live i || value.uses i) live base (.value type)
        (.pure (value.denote funs env)) heap initial locals aborts)
      initial locals targetHost := by
  change wp target (Relocation.program (value.code (pool := pool) h slots base live ++
    coerceCode h type (value.mode (slots.map Slot.mode)) .owned base)) _ initial locals targetHost
  have execution := wp_return runtime layout profile spec form closed positions parameters vars
    at_ safe cap low room place (rest := [])
    (targetHost := targetHost)
    (Q := CommandResult host env slots (fun i => live i || value.uses i) live base (.value type)
      (.pure (value.denote funs env)) heap initial locals aborts)
    (fun failure final same => CommandResult.resource_refl (allowed failure) same)
    (fun finalHeap finalStore finalLocals words after same _ => by
      rw [wp_nil]
      exact CommandResult.returned (result := .value type) (value.denote funs env)
        finalHeap finalStore finalLocals words []
        (by
          rw [same]
          exact Exec.pure (α := (ResultTy.value type).denote) initial.host
            (value.denote funs env)) after)
  simpa only [List.append_nil] using execution

end Verified.Wasi
