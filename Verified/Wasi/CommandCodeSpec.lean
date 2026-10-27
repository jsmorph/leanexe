import Verified.Wasi.CommandSpec
import Verified.Wasi.CommandReady
import Verified.Wasi.ResourceCost

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

def CommandCodeSpec (source target : Wasm.Module) (pure : Resource.PureContext pureSigs)
    (effects : EffectFuns effectSigs) (pool : Bytes.LiteralPool)
    (command : Command pureSigs effectSigs context result) : Prop :=
  ∀ (World : Type) (host : Host World) (targetHost : HostEnv (Observed World))
    (depth : UInt64) (env : Env context) (slots : List Slot) (live : Nat → Bool)
    (h base : Nat) (heap : Heap) (initial : Store (Observed World)) (locals : Locals),
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
    wp target (command.code (pool := pool) source h slots base live)
      (CommandResult host env slots (fun i => live i || command.uses i) live base result
        (command.denote pure.funs effects env) heap initial locals true)
      initial locals targetHost

end Verified.Wasi
