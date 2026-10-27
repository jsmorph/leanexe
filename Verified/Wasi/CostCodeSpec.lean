import Verified.Wasi.CommandCodeSpec
import Verified.Wasi.CostResults

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

def CostCommandCodeSpec (source target : Wasm.Module) (pure : Resource.PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (pool : Bytes.LiteralPool)
    (command : Command pureSigs effectSigs context result) : Prop :=
  ∀ (World : Type) (host : Host World) (targetHost : HostEnv (Observed World))
    (depth : UInt64) (env : Env context) (slots : List Slot) (live : Nat → Bool)
    (h base : Nat) (heap : Heap) (initial : Store (Observed World)) (locals : Locals)
    (budget : Nat) (aborts : Bool),
    targetHost.Satisfies target (hostSpec host) →
    depth < depthLimit → locals.params.head? = some (.i64 depth) →
    locals.positions = h →
    Holds env slots (fun i => live i || command.uses i) base heap
      (PureTransport.erase initial) locals →
    heap.At (PureTransport.erase initial) →
    pool.Safe env slots (fun i => live i || command.uses i) heap
      (PureTransport.erase initial) locals →
    Holds.ApartFrom env slots (fun i => live i || command.uses i)
      (PureTransport.erase initial) locals ABI.scratch →
    (PureTransport.erase initial).memoryCap source 0 ≤ 65535 →
    locals.params.length ≤ base → base + command.width ≤ h →
    command.Ready source h slots base live pool →
    command.Covered pool → command.placeArgs = true →
    (aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      Resource.PrefixBound (observedHost host) pure program depth (slots.map Slot.mode) live
        command env initial.host budget) →
    wp target (command.code (pool := pool) source h slots base live)
      (CostCommandResult host pure program command depth env slots
        (fun i => live i || command.uses i) live base heap initial locals aborts)
      initial locals targetHost

theorem CostCommandCodeSpec.safety {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {command : Command pureSigs effectSigs context result}
    (spec : CostCommandCodeSpec source target pure program pool command) :
    CommandCodeSpec source target pure (program.funs pure.funs) pool command := by
  intro World host targetHost depth env slots live h base heap initial locals
    valid below parameters positions vars at_ safe scratch cap low room ready covered place
  exact wp.conseq (fun _ classification => classification.erase)
    (spec World host targetHost depth env slots live h base heap initial locals 0 true
      valid below parameters positions vars at_ safe scratch cap low room ready covered place
      (fun impossible => Bool.noConfusion impossible))

end Verified.Wasi
