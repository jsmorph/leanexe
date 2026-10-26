import Library.Hashing.Sha2.Equiv.SHA512.Bridge

/-!
# Bridge lemmas for the SHA-512 round functions

Parallel to `equiv/SHA256/Functions.lean` at 64-bit width with the
SHA-512 rotation constants (FIPS 180-4 §4.1.3):

* `Σ₀` rotates by 28, 34, 39
* `Σ₁` rotates by 14, 18, 41
* `σ₀` rotates by 1, 8; shifts right by 7
* `σ₁` rotates by 19, 61; shifts right by 6

`Ch` and `Maj` are width-agnostic and follow the SHA-256 shape.

For each spec function we prove a `@[simp]` lemma rewriting a call on
*lifted* `UInt64` arguments to the lifting of the implementation's
expression.  Together with the operator bridges from `Bridge.lean`,
this lets the round-body equivalence in `Compress/Match.lean` reduce
to `simp`.

Proof shape (for all six lemmas): unfold the spec definition, then
`simp only` with the operator bridges from `Bridge.lean` to push
`toBitVec` to the leaves; what remains closes by `ac_rfl`. -/

open SHS.Equiv.SHA512.Bridge

open SHS.SHA512

namespace SHS.Equiv.SHA512.Functions

/-- `Ch x y z = (x ∧ y) ⊕ (¬x ∧ z)`, lifted. (FIPS 180-4 §4.1.3, eq. 4.8) -/
@[simp] theorem Ch_toBitVec (x y z : UInt64) :
    SHS.SHA512.Ch x.toBitVec y.toBitVec z.toBitVec =
      ((x &&& y) ^^^ ((~~~ x) &&& z)).toBitVec := by
  simp [SHS.SHA512.Ch]

/-- `Maj x y z = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`, lifted. (FIPS 180-4 §4.1.3, eq. 4.9) -/
@[simp] theorem Maj_toBitVec (x y z : UInt64) :
    SHS.SHA512.Maj x.toBitVec y.toBitVec z.toBitVec =
      ((x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)).toBitVec := by
  simp only [SHS.SHA512.Maj, toBitVec_xor, toBitVec_and]
  ac_rfl

/-- `Σ₀ x = ROTR²⁸ x ⊕ ROTR³⁴ x ⊕ ROTR³⁹ x`, lifted. (eq. 4.10) -/
@[simp] theorem bigSigma0_toBitVec (x : UInt64) :
    SHS.SHA512.bigSigma0 x.toBitVec =
      ((Impl.UInt64.rotr x 28) ^^^ (Impl.UInt64.rotr x 34)
        ^^^ (Impl.UInt64.rotr x 39)).toBitVec := by
  simp only [SHS.SHA512.bigSigma0, toBitVec_xor,
    toBitVec_rotr _ _ (by decide : 0 < (28 : UInt64).toNat) (by decide : (28 : UInt64).toNat < 64),
    toBitVec_rotr _ _ (by decide : 0 < (34 : UInt64).toNat) (by decide : (34 : UInt64).toNat < 64),
    toBitVec_rotr _ _ (by decide : 0 < (39 : UInt64).toNat) (by decide : (39 : UInt64).toNat < 64),
    ROTR_eq_rotateRight _ _ (by decide : 28 < 64),
    ROTR_eq_rotateRight _ _ (by decide : 34 < 64),
    ROTR_eq_rotateRight _ _ (by decide : 39 < 64),
    show (28 : UInt64).toNat = 28 from rfl,
    show (34 : UInt64).toNat = 34 from rfl,
    show (39 : UInt64).toNat = 39 from rfl]
  ac_rfl

/-- `Σ₁ x = ROTR¹⁴ x ⊕ ROTR¹⁸ x ⊕ ROTR⁴¹ x`, lifted. (eq. 4.11) -/
@[simp] theorem bigSigma1_toBitVec (x : UInt64) :
    SHS.SHA512.bigSigma1 x.toBitVec =
      ((Impl.UInt64.rotr x 14) ^^^ (Impl.UInt64.rotr x 18)
        ^^^ (Impl.UInt64.rotr x 41)).toBitVec := by
  simp only [SHS.SHA512.bigSigma1, toBitVec_xor,
    toBitVec_rotr _ _ (by decide : 0 < (14 : UInt64).toNat) (by decide : (14 : UInt64).toNat < 64),
    toBitVec_rotr _ _ (by decide : 0 < (18 : UInt64).toNat) (by decide : (18 : UInt64).toNat < 64),
    toBitVec_rotr _ _ (by decide : 0 < (41 : UInt64).toNat) (by decide : (41 : UInt64).toNat < 64),
    ROTR_eq_rotateRight _ _ (by decide : 14 < 64),
    ROTR_eq_rotateRight _ _ (by decide : 18 < 64),
    ROTR_eq_rotateRight _ _ (by decide : 41 < 64),
    show (14 : UInt64).toNat = 14 from rfl,
    show (18 : UInt64).toNat = 18 from rfl,
    show (41 : UInt64).toNat = 41 from rfl]
  ac_rfl

/-- `σ₀ x = ROTR¹ x ⊕ ROTR⁸ x ⊕ SHR⁷ x`, lifted. (eq. 4.12) -/
@[simp] theorem smallSigma0_toBitVec (x : UInt64) :
    SHS.SHA512.smallSigma0 x.toBitVec =
      ((Impl.UInt64.rotr x 1) ^^^ (Impl.UInt64.rotr x 8) ^^^ (x >>> 7)).toBitVec := by
  simp only [SHS.SHA512.smallSigma0, toBitVec_xor,
    toBitVec_rotr _ _ (by decide : 0 < (1 : UInt64).toNat) (by decide : (1 : UInt64).toNat < 64),
    toBitVec_rotr _ _ (by decide : 0 < (8 : UInt64).toNat) (by decide : (8 : UInt64).toNat < 64),
    toBitVec_shr_of_lt _ _ (by decide : (7 : UInt64).toNat < 64),
    ROTR_eq_rotateRight _ _ (by decide : 1 < 64),
    ROTR_eq_rotateRight _ _ (by decide : 8 < 64),
    SHR_eq_shr,
    show (1 : UInt64).toNat = 1 from rfl,
    show (7 : UInt64).toNat = 7 from rfl,
    show (8 : UInt64).toNat = 8 from rfl]
  ac_rfl

/-- `σ₁ x = ROTR¹⁹ x ⊕ ROTR⁶¹ x ⊕ SHR⁶ x`, lifted. (eq. 4.13) -/
@[simp] theorem smallSigma1_toBitVec (x : UInt64) :
    SHS.SHA512.smallSigma1 x.toBitVec =
      ((Impl.UInt64.rotr x 19) ^^^ (Impl.UInt64.rotr x 61) ^^^ (x >>> 6)).toBitVec := by
  simp only [SHS.SHA512.smallSigma1, toBitVec_xor,
    toBitVec_rotr _ _ (by decide : 0 < (19 : UInt64).toNat) (by decide : (19 : UInt64).toNat < 64),
    toBitVec_rotr _ _ (by decide : 0 < (61 : UInt64).toNat) (by decide : (61 : UInt64).toNat < 64),
    toBitVec_shr_of_lt _ _ (by decide : (6 : UInt64).toNat < 64),
    ROTR_eq_rotateRight _ _ (by decide : 19 < 64),
    ROTR_eq_rotateRight _ _ (by decide : 61 < 64),
    SHR_eq_shr,
    show (6 : UInt64).toNat = 6 from rfl,
    show (19 : UInt64).toNat = 19 from rfl,
    show (61 : UInt64).toNat = 61 from rfl]
  ac_rfl

end SHS.Equiv.SHA512.Functions
