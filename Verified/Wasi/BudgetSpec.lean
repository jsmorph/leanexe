import Verified.Wasi.EffectSpec
import Verified.Wasi.ResourceBudget

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

def BudgetEffectSpecWith (calls : List LeanExe.Wasi.Call) (source target : Wasm.Module) (pure : Resource.PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (callee : EffectVar effectSigs signature)
    (index : Nat) (pool : Bytes.LiteralPool) : Prop :=
  ∀ (World : Type) (host : Host World) (targetHost : HostEnv (Observed World))
    (depth : UInt64) (heap : Heap) (initial : Store (Observed World))
    (params : List Value) (args : Env signature.params) (budget : Nat) (aborts : Bool),
    targetHost.Satisfies target (hostSpecWith host calls) →
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
      FunctionResult host signature ((program.funs pure.funs).get callee args)
        args params heap initial aborts
        (run fuel target index initial ((.i64 depth :: params).reverse) targetHost)

def BudgetEffectSpec (source target : Wasm.Module) (pure : Resource.PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (callee : EffectVar effectSigs signature)
    (index : Nat) (pool : Bytes.LiteralPool) : Prop :=
  BudgetEffectSpecWith [] source target pure program callee index pool

theorem BudgetEffectSpecWith.safety {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {callee : EffectVar effectSigs signature} {index : Nat} {pool : Bytes.LiteralPool}
    (spec : BudgetEffectSpecWith calls source target pure program callee index pool) :
    EffectSpecWith calls target signature index ((program.funs pure.funs).get callee) pool := by
  intro World host targetHost depth heap initial params args valid at_ rep separate input scratch cap
  exact spec World host targetHost depth heap initial params args 0 true valid at_ rep separate
    input scratch cap (fun impossible => Bool.noConfusion impossible)

theorem BudgetEffectSpec.safety {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {callee : EffectVar effectSigs signature} {index : Nat} {pool : Bytes.LiteralPool}
    (spec : BudgetEffectSpec source target pure program callee index pool) :
    EffectSpec target signature index ((program.funs pure.funs).get callee) pool := by
  layout_instance BudgetEffectSpecWith.safety

def BudgetEffectCallsWith (calls : List LeanExe.Wasi.Call) (source target : Wasm.Module) (pure : Resource.PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (pool : Bytes.LiteralPool) : Prop :=
  ∀ {signature : EffectSig} (callee : EffectVar effectSigs signature),
    BudgetEffectSpecWith calls source target pure program callee
      (Wrappers.effectIndexWith calls source callee.index) pool

def BudgetEffectCalls (source target : Wasm.Module) (pure : Resource.PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (pool : Bytes.LiteralPool) : Prop :=
  BudgetEffectCallsWith [] source target pure program pool

theorem BudgetEffectCallsWith.safety {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} (budget : BudgetEffectCallsWith calls source target pure program pool) :
    EffectCallsWith calls source target (program.funs pure.funs) pool :=
  fun callee => (budget callee).safety

theorem BudgetEffectCalls.safety {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} (calls : BudgetEffectCalls source target pure program pool) :
    EffectCalls source target (program.funs pure.funs) pool := by
  layout_instance BudgetEffectCallsWith.safety

end Verified.Wasi
