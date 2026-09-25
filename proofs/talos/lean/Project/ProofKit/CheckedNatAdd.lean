import Project.ProofKit.CheckedNatAddArithmetic
import Project.TalosCompat

namespace Project.ProofKit.CheckedNatAdd
open Wasm

/-- The overflow guard after an emitted checked Nat addition. -/
theorem guard_spec (resultLocal : Nat) (module_ : Wasm.Module)
    (env : HostEnv α) (store : Store α) (frame : Locals)
    (left right : Nat) (tail : List Value)
    (hValues : frame.values = .i32
      (if UInt64.ofNat left + UInt64.ofNat right < UInt64.ofNat left then 1 else 0) :: tail)
    (hResult : frame.get resultLocal = some (.i64 (UInt64.ofNat (left + right))))
    (hFit : left + right < UInt64.size)
    (Q : Assertion α) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store
      { frame with values := .i64 (UInt64.ofNat (left + right)) :: tail } env) :
    wp module_ (.iff 0 1 [.unreachable] [.localGet resultLocal] :: rest)
      Q store frame env := by
  have hGuard := guard_of_fits left right hFit
  simp only [hGuard, ↓reduceIte] at hValues
  refine wp_iff_cons hValues ?_
  have hRead := hResult
  simp only [Locals.get] at hRead
  simpa [wp_simp, Locals.get, hRead] using hNext

#print axioms guard_spec
end Project.ProofKit.CheckedNatAdd
