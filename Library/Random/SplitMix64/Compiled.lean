import Library.Random.SplitMix64.Program
import Verified.Reflect.Command

/-! The verified compiler's module of `splitMix` and `unitFloat`.  `prng_module` combines the
module's bytes with the generated `compiled.splitMix.pure` and `compiled.unitFloat.pure`. -/

namespace Library.Random.SplitMix64

open LeanExe.Pipeline

verified_compile compiled := [splitMix, unitFloat]

/-- The module's bytes decode to the module, whose exports `splitMix` and `unitFloat` are functions
2 and 3, and from every store each function returns its Lean result without a trap and keeps the
store. -/
theorem prng_module :
    (∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok compiled.module) ∧
      ({ name := "splitMix", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports ∧
      ({ name := "unitFloat", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports ∧
      ImplementsPureA false compiled.module 2 splitMix ∧
      ImplementsPureA false compiled.module 3 unitFloat := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  exact ⟨⟨bytes, henc, hdec⟩, by decide +kernel, by decide +kernel, compiled.splitMix.pure,
    compiled.unitFloat.pure⟩

#print axioms prng_module

end Library.Random.SplitMix64
