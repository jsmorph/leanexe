import Library.Hashing.Sha2.Impl.SHA512
import Library.Hashing.Sha2.Spec.HashAlgorithms

/-!
# `UInt64` ↔ `BitVec 64` operator bridge

Parallel to `equiv/SHA256/Bridge.lean` at 64-bit width.  `UInt64` is a
one-field structure wrapping `BitVec 64`, so the pointwise bridges are
all `rfl`; the shift and rotation bridges carry a `n.toNat < 64`
hypothesis discharged from literal rotation counts at the callsites in
`Functions.lean`.

## Operator-notation map (spec ↔ equiv/impl)

The spec/ layer uses the mathematical Unicode operators on `BitVec 64`
(matching FIPS 180-4 notation):

  spec    ⊕   ∧   ¬     (xor, and, not on `BitVec`)

The equiv/ layer (and the underlying impl/) instead uses the ASCII
bitwise operators on `UInt64`, which is what the Lean core provides for
machine-word types:

  equiv  ^^^  &&&  ~~~

Both denote the same bit operations; the `toBitVec_{xor,and,not}`
lemmas in this file (and the `_toBitVec` family in `Functions.lean`)
are the bridges that line them up. -/

open SHS.SHA512

namespace SHS.Equiv.SHA512.Bridge

open SHS

/-! ## Pointwise bitwise / arithmetic bridges

All four are `rfl` because `UInt64` is a one-field structure over
`BitVec 64` and the corresponding instances forward through that field. -/

@[simp] theorem toBitVec_xor (x y : UInt64) :
    (x ^^^ y).toBitVec = x.toBitVec ^^^ y.toBitVec := rfl

@[simp] theorem toBitVec_and (x y : UInt64) :
    (x &&& y).toBitVec = x.toBitVec &&& y.toBitVec := rfl

@[simp] theorem toBitVec_not (x : UInt64) :
    (~~~ x).toBitVec = ~~~ x.toBitVec := rfl

@[simp] theorem toBitVec_add (x y : UInt64) :
    (x + y).toBitVec = x.toBitVec + y.toBitVec := rfl

/-! ## Shift bridges

`UInt64.>>>` and `UInt64.<<<` carry an implicit `% 64` on the shift
amount (because the amount is itself a `UInt64`), so each bridge to
`BitVec.>>>` / `BitVec.<<<` requires proving the amount is in range. -/

/-- For an in-range shift amount, `UInt64.>>>` agrees with `BitVec.>>>`
on the underlying bitvector. -/
theorem toBitVec_shr_of_lt (x : UInt64) (n : UInt64) (h : n.toNat < 64) :
    (x >>> n).toBitVec = x.toBitVec >>> n.toNat := by
  rw [UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', BitVec.toNat_umod]
  congr 1
  simp [Nat.mod_eq_of_lt h]

/-- For an in-range shift amount, `UInt64.<<<` agrees with `BitVec.<<<`
on the underlying bitvector.  Companion to `toBitVec_shr_of_lt`. -/
theorem toBitVec_shl_of_lt (x : UInt64) (n : UInt64) (h : n.toNat < 64) :
    (x <<< n).toBitVec = x.toBitVec <<< n.toNat := by
  rw [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.toNat_umod]
  congr 1
  simp [Nat.mod_eq_of_lt h]

/-! ## Rotation bridges

`Impl.UInt64.rotr` is defined directly via primitive `UInt64` shift/or
ops (for codegen efficiency).  The bridge to `BitVec.rotateRight` goes
via Lean core's `BitVec.rotateRight_def`.  All callsites (the four
`_toBitVec` lemmas in `Functions.lean`, plus `ROTR_eq_u64_rotr`)
discharge `n.toNat < 64` from a literal `n`. -/

/-- For `n.toNat < 64`, `Impl.UInt64.rotr` agrees with `BitVec.rotateRight`
on the underlying bitvector.  The bound is essential: for `n.toNat ≥ 64`
the impl rotr (using primitive `UInt64` shifts which mask the amount via
`% 2^64`) diverges from the recursive `BitVec.rotateRightAux`. -/
theorem toBitVec_rotr (x : UInt64) (n : UInt64) (h0 : 0 < n.toNat) (h : n.toNat < 64) :
    (Impl.UInt64.rotr x n).toBitVec = x.toBitVec.rotateRight n.toNat := by
  unfold Impl.UInt64.rotr
  have hn_le : n ≤ (64 : UInt64) := by
    rw [UInt64.le_iff_toNat_le]; exact Nat.le_of_lt h
  have h64n : ((64 : UInt64) - n).toNat = 64 - n.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hn_le]; rfl
  have h64n_lt : ((64 : UInt64) - n).toNat < 64 := by rw [h64n]; omega
  rw [UInt64.toBitVec_or, toBitVec_shr_of_lt _ _ h, toBitVec_shl_of_lt _ _ h64n_lt,
      h64n, BitVec.rotateRight_def, Nat.mod_eq_of_lt h]

/-- For `n < 64`, the spec's `SHS.ROTR n` matches `BitVec.rotateRight n`. -/
theorem ROTR_eq_rotateRight (n : Nat) (x : BitVec 64) (h : n < 64) :
    SHS.ROTR n x = x.rotateRight n := by
  unfold SHS.ROTR
  rw [BitVec.rotateRight_eq_rotateRightAux_of_lt h]
  unfold BitVec.rotateRightAux
  rfl

/-! ## SHR bridge -/

theorem SHR_eq_shr (n : Nat) (x : BitVec 64) :
    SHS.SHR n x = x >>> n := rfl

end SHS.Equiv.SHA512.Bridge
