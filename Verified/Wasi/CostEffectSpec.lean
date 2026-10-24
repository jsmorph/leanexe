import Verified.Wasi.CostResults

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

def CostEffectSpec (source target : Wasm.Module) (pure : Resource.PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (callee : EffectVar effectSigs signature)
    (index : Nat) (pool : Bytes.LiteralPool) : Prop :=
  ∀ (World : Type) (host : Host World) (targetHost : HostEnv (Observed World))
    (depth : UInt64) (heap : Heap) (initial : Store (Observed World))
    (params : List Value) (args : Env signature.params) (budget : Nat) (aborts : Bool),
    targetHost.Satisfies target (hostSpec host) →
    heap.At (PureTransport.erase initial) →
    Env.Rep signature.mode heap (PureTransport.erase initial) params args →
    Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) signature.mode params args)
      (Env.reads (PureTransport.erase initial) signature.mode params args) →
    @Bytes.LiteralPool.Input (Env signature.params)
      (Env.represent signature.params signature.modes) pool heap (PureTransport.erase initial)
      params args →
    (∀ region ∈ Env.reads (PureTransport.erase initial) signature.mode params args,
      regionsDisjoint ABI.scratch region) →
    (PureTransport.erase initial).memoryCap target 0 ≤ 65535 →
    (aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      Resource.CallPrefixBound (observedHost host) pure program callee depth args
        initial.host budget) →
    ∃ bound, ∀ fuel ≥ bound,
      CostFunctionResult host pure program callee depth args params heap initial aborts
        (run fuel target index initial ((.i64 depth :: params).reverse) targetHost)

theorem CostEffectSpec.budget {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {callee : EffectVar effectSigs signature} {index : Nat} {pool : Bytes.LiteralPool}
    (spec : CostEffectSpec source target pure program callee index pool) :
    BudgetEffectSpec source target pure program callee index pool := by
  intro World host targetHost depth heap initial params args budget aborts
    valid at_ rep separate input scratch cap resources
  obtain ⟨bound, proof⟩ := spec World host targetHost depth heap initial params args budget aborts
    valid at_ rep separate input scratch cap resources
  exact ⟨bound, fun fuel enough => (proof fuel enough).erase⟩

def CostEffectCalls (source target : Wasm.Module) (pure : Resource.PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (pool : Bytes.LiteralPool) : Prop :=
  ∀ {signature : EffectSig} (callee : EffectVar effectSigs signature),
    CostEffectSpec source target pure program callee (Wrappers.effectIndex source callee.index) pool

theorem CostEffectCalls.safety {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} (calls : CostEffectCalls source target pure program pool) :
    EffectCalls source target (program.funs pure.funs) pool :=
  fun callee => (calls callee).budget.safety

end Verified.Wasi
