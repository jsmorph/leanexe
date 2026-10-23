import Library.Hashing.Sha2.Impl.SHA256
import Library.Hashing.Sha2.Spec.HashAlgorithms

/-!
# `UInt32` ↔ `BitVec 32` operator bridge

The intermediate implementation (`impl/Sha256.lean`) operates over
`UInt32`; the NIST-style spec (`spec/`) operates over `BitVec 32`.
`UInt32` is a one-field structure wrapping `BitVec 32`, so all bitwise
operations are *definitionally* equal to their `BitVec 32` counterparts
modulo the projection `UInt32.toBitVec`.

This module collects those bridge lemmas and tags them `@[simp]` where
appropriate, so that downstream proofs (`Functions.lean`, `Compress.lean`)
can reduce mixed `UInt32`/`BitVec 32` expressions by `simp` alone.

## Contents

* `toBitVec_{xor,and,not,add}` — pointwise `rfl` bridges (always defeq).
* `toBitVec_shr_of_lt` — shift bridge (needs `n.toNat < 32` because of
  the implicit `% 32` baked into `UInt32.>>>`).
* `toBitVec_rotr` / `ROTR_eq_rotateRight` — rotation bridges; the
  bigSigma/smallSigma proofs in `Functions.lean` chain them.
* `SHR_eq_shr` — spec `SHR n` is just `>>> n` on `BitVec`.

## Operator-notation map (spec ↔ equiv/impl)

The spec/ layer uses the mathematical Unicode operators on `BitVec 32`
(matching FIPS 180-4 notation):

  spec    ⊕   ∧   ¬     (xor, and, not on `BitVec`)

The equiv/ layer (and the underlying impl/) instead uses the ASCII
bitwise operators on `UInt32`, which is what the Lean core provides for
machine-word types:

  equiv  ^^^  &&&  ~~~

Both denote the same bit operations; the `toBitVec_{xor,and,not}`
lemmas in this file (and the `_toBitVec` family in `Functions.lean`)
are the bridges that line them up. -/

open SHS.SHA256

namespace SHS.Equiv.SHA256.Bridge

open SHS

/-! ## Pointwise bitwise / arithmetic bridges

All four are `rfl` because `UInt32` is a one-field structure over
`BitVec 32` and the corresponding instances forward through that field. -/

@[simp] theorem toBitVec_xor (x y : UInt32) :
    (x ^^^ y).toBitVec = x.toBitVec ^^^ y.toBitVec := rfl

@[simp] theorem toBitVec_and (x y : UInt32) :
    (x &&& y).toBitVec = x.toBitVec &&& y.toBitVec := rfl

@[simp] theorem toBitVec_not (x : UInt32) :
    (~~~ x).toBitVec = ~~~ x.toBitVec := rfl

@[simp] theorem toBitVec_add (x y : UInt32) :
    (x + y).toBitVec = x.toBitVec + y.toBitVec := rfl

/-! ## Shift bridge

`UInt32.>>>` carries an implicit `% 32` on the shift amount (because the
amount is itself a `UInt32`), so the bridge to `BitVec.>>>` requires
proving the amount is in range. -/

/-- For an in-range shift amount, `UInt32.>>>` agrees with `BitVec.>>>`
on the underlying bitvector. -/
theorem toBitVec_shr_of_lt (x : UInt32) (n : UInt32) (h : n.toNat < 32) :
    (x >>> n).toBitVec = x.toBitVec >>> n.toNat := by
  rw [UInt32.toBitVec_shiftRight, BitVec.ushiftRight_eq', BitVec.toNat_umod]
  congr 1
  simp [Nat.mod_eq_of_lt h]

/-! ## Shift-left bridge

Companion to `toBitVec_shr_of_lt`: needed because the new fast `rotr`
implementation uses `<<<` and `>>>` directly. -/

/-- For an in-range shift amount, `UInt32.<<<` agrees with `BitVec.<<<`
on the underlying bitvector. -/
theorem toBitVec_shl_of_lt (x : UInt32) (n : UInt32) (h : n.toNat < 32) :
    (x <<< n).toBitVec = x.toBitVec <<< n.toNat := by
  rw [UInt32.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.toNat_umod]
  congr 1
  simp [Nat.mod_eq_of_lt h]

/-! ## Rotation bridges

`Impl.UInt32.rotr` is now defined directly via primitive `UInt32` shift/or
ops (for ~50× perf), so the bridge to `BitVec.rotateRight` is no longer
`rfl`; we prove it via Lean core's `BitVec.rotateRight_def`.  All
callsites (the four `_toBitVec` lemmas in `Functions.lean`, plus
`ROTR_eq_u32_rotr`) discharge `n.toNat < 32` from a literal `n`. -/

/-- For `n.toNat < 32`, `Impl.UInt32.rotr` agrees with `BitVec.rotateRight`
on the underlying bitvector.  The bound is essential: for `n.toNat ≥ 32`
the impl rotr (using primitive `UInt32` shifts which mask the amount via
`% 2^32`) diverges from the recursive `BitVec.rotateRightAux`. -/
theorem toBitVec_rotr (x : UInt32) (n : UInt32) (h0 : 0 < n.toNat) (h : n.toNat < 32) :
    (Impl.UInt32.rotr x n).toBitVec = x.toBitVec.rotateRight n.toNat := by
  unfold Impl.UInt32.rotr
  have hn_le : n ≤ (32 : UInt32) := by
    rw [UInt32.le_iff_toNat_le]; exact Nat.le_of_lt h
  have h32n : ((32 : UInt32) - n).toNat = 32 - n.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ hn_le]; rfl
  have h32n_lt : ((32 : UInt32) - n).toNat < 32 := by rw [h32n]; omega
  rw [UInt32.toBitVec_or, toBitVec_shr_of_lt _ _ h, toBitVec_shl_of_lt _ _ h32n_lt,
      h32n, BitVec.rotateRight_def, Nat.mod_eq_of_lt h]

/-- For `n < 32`, the spec's `SHS.ROTR n` matches `BitVec.rotateRight n`. -/
theorem ROTR_eq_rotateRight (n : Nat) (x : BitVec 32) (h : n < 32) :
    SHS.ROTR n x = x.rotateRight n := by
  unfold SHS.ROTR
  rw [BitVec.rotateRight_eq_rotateRightAux_of_lt h]
  unfold BitVec.rotateRightAux
  rfl

/-! ## SHR bridge -/

/-- The spec's `SHR n` is `BitVec`'s `>>> n` on the nose. -/
theorem SHR_eq_shr (n : Nat) (x : BitVec 32) :
    SHS.SHR n x = x >>> n := rfl

end SHS.Equiv.SHA256.Bridge
