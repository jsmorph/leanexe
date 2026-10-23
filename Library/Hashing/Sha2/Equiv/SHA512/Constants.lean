import Library.Hashing.Sha2.Impl.SHA512
import Library.Hashing.Sha2.Spec.HashAlgorithms

/-!
# Round-constant bridge: `K64 ↔ K`

Parallel to `equiv/SHA256/Constants.lean`: 80 64-bit constants, lifted
elementwise from `Impl.K64 : Vector UInt64 80` to
`SHS.SHA512.K : Vector (BitVec 64) 80`.

The two flavours below cover the two index shapes that come up: a
`Fin 80` index (in fold-style proofs over rounds) and a `Nat` index
with a side bound (after `interval_cases` or similar enumerations). -/

open SHS.SHA512

namespace SHS.Equiv.SHA512.Constants

open scoped SHS.SHA512

/-- `Fin 80`-indexed bridge: `K64[i].toBitVec = K[i.val]!`. -/
@[simp] theorem K64_toBitVec (i : Fin 80) :
    Impl.K64[i].toBitVec = SHS.SHA512.K[i.val]! :=
  (by decide : ∀ k : Fin 80, Impl.K64[k].toBitVec = SHS.SHA512.K[k.val]!) i

/-- `Nat`-indexed variant of `K64_toBitVec`, useful after `interval_cases`
when the goal carries a `Nat`-with-bound access.  Reduces to the
`Fin`-indexed form via `simpa`. -/
theorem K64_toBitVec_nat (n : Nat) (hn : n < 80) :
    (Impl.K64[n]'(by simp [hn])).toBitVec = SHS.SHA512.K[n]! := by
  simpa using K64_toBitVec ⟨n, hn⟩

end SHS.Equiv.SHA512.Constants
