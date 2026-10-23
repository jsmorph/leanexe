import Library.Hashing.Sha2.Impl.SHA256
import Library.Hashing.Sha2.Spec.HashAlgorithms

/-!
# Round-constant bridge: `K32 ↔ K`

The implementation pulls round constants from a `Vector UInt32 64`
named `Impl.K32`; the spec pulls them from an `Array (BitVec 32)`
named `SHS.SHA256.K`, accessed via the panicking `K[t]!`.  Both
contain the same 64 NIST-specified values, so a single `decide`
discharges the elementwise equality.

The two flavours below cover the two index shapes that come up: a
`Fin 64` index (in fold-style proofs over rounds) and a `Nat` index
with a side bound (after `interval_cases` or similar enumerations).
-/

open SHS.SHA256

namespace SHS.Equiv.SHA256.Constants

open scoped SHS.SHA256

/-- `Fin 64`-indexed bridge: `K32[i].toBitVec = K[i.val]!`. -/
@[simp] theorem K32_toBitVec (i : Fin 64) :
    Impl.K32[i].toBitVec = SHS.SHA256.K[i.val]! :=
  (by decide : ∀ k : Fin 64, Impl.K32[k].toBitVec = SHS.SHA256.K[k.val]!) i

/-- `Nat`-indexed variant of `K32_toBitVec`, useful after `interval_cases`
when the goal carries a `Nat`-with-bound access.  Reduces to the
`Fin`-indexed form via `simpa`. -/
theorem K32_toBitVec_nat (n : Nat) (hn : n < 64) :
    (Impl.K32[n]'(by simp [hn])).toBitVec = SHS.SHA256.K[n]! := by
  simpa using K32_toBitVec ⟨n, hn⟩

end SHS.Equiv.SHA256.Constants
