import Library.Hashing.Sha2.Equiv.SHA256.Bridge

/-!
# Bridge lemmas for the SHA-256 round functions

The spec (`spec/Functions.lean`) defines six auxiliary functions on
`BitVec 32` — `Ch`, `Maj`, `bigSigma0`, `bigSigma1`, `smallSigma0`,
`smallSigma1` — that the compression function calls each round.  The
implementation inlines the same operations, but on `UInt32`.

For each spec function we prove a `@[simp]` lemma rewriting a call on
*lifted* `UInt32` arguments to the lifting of the implementation's
expression.  Together with the operator bridges from `Bridge.lean`,
this lets the round-body equivalence in `Compress.lean` reduce to
`simp`.

Proof shape (for all six lemmas): unfold the spec definition, then
`simp only` with the operator bridges from `Bridge.lean` to push
`toBitVec` to the leaves; what remains closes by `ac_rfl` (or by `simp`
in the `Ch` case, which is `rfl` up to instance unfolding).
-/

open SHS.Equiv.SHA256.Bridge

open SHS.SHA256

namespace SHS.Equiv.SHA256.Functions

/-- `Ch x y z = (x ∧ y) ⊕ (¬x ∧ z)`, lifted. (FIPS 180-4 §4.1.2, eq. 4.2) -/
@[simp] theorem Ch_toBitVec (x y z : UInt32) :
    SHS.SHA256.Ch x.toBitVec y.toBitVec z.toBitVec =
      ((x &&& y) ^^^ ((~~~ x) &&& z)).toBitVec := by
  simp [SHS.SHA256.Ch]

/-- `Maj x y z = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`, lifted. (FIPS 180-4 §4.1.2, eq. 4.3) -/
@[simp] theorem Maj_toBitVec (x y z : UInt32) :
    SHS.SHA256.Maj x.toBitVec y.toBitVec z.toBitVec =
      ((x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)).toBitVec := by
  simp only [SHS.SHA256.Maj, toBitVec_xor, toBitVec_and]
  ac_rfl

/-- `Σ₀ x = ROTR² x ⊕ ROTR¹³ x ⊕ ROTR²² x`, lifted. (FIPS 180-4 §4.1.2, eq. 4.4) -/
@[simp] theorem bigSigma0_toBitVec (x : UInt32) :
    SHS.SHA256.bigSigma0 x.toBitVec =
      ((Impl.UInt32.rotr x 2) ^^^ (Impl.UInt32.rotr x 13)
        ^^^ (Impl.UInt32.rotr x 22)).toBitVec := by
  simp only [SHS.SHA256.bigSigma0, toBitVec_xor,
    toBitVec_rotr _ _ (by decide : 0 < (2 : UInt32).toNat) (by decide : (2 : UInt32).toNat < 32),
    toBitVec_rotr _ _ (by decide : 0 < (13 : UInt32).toNat) (by decide : (13 : UInt32).toNat < 32),
    toBitVec_rotr _ _ (by decide : 0 < (22 : UInt32).toNat) (by decide : (22 : UInt32).toNat < 32),
    ROTR_eq_rotateRight _ _ (by decide : 2 < 32),
    ROTR_eq_rotateRight _ _ (by decide : 13 < 32),
    ROTR_eq_rotateRight _ _ (by decide : 22 < 32),
    show (2 : UInt32).toNat = 2 from rfl,
    show (13 : UInt32).toNat = 13 from rfl,
    show (22 : UInt32).toNat = 22 from rfl]
  ac_rfl

/-- `Σ₁ x = ROTR⁶ x ⊕ ROTR¹¹ x ⊕ ROTR²⁵ x`, lifted. (FIPS 180-4 §4.1.2, eq. 4.5) -/
@[simp] theorem bigSigma1_toBitVec (x : UInt32) :
    SHS.SHA256.bigSigma1 x.toBitVec =
      ((Impl.UInt32.rotr x 6) ^^^ (Impl.UInt32.rotr x 11)
        ^^^ (Impl.UInt32.rotr x 25)).toBitVec := by
  simp only [SHS.SHA256.bigSigma1, toBitVec_xor,
    toBitVec_rotr _ _ (by decide : 0 < (6 : UInt32).toNat) (by decide : (6 : UInt32).toNat < 32),
    toBitVec_rotr _ _ (by decide : 0 < (11 : UInt32).toNat) (by decide : (11 : UInt32).toNat < 32),
    toBitVec_rotr _ _ (by decide : 0 < (25 : UInt32).toNat) (by decide : (25 : UInt32).toNat < 32),
    ROTR_eq_rotateRight _ _ (by decide : 6 < 32),
    ROTR_eq_rotateRight _ _ (by decide : 11 < 32),
    ROTR_eq_rotateRight _ _ (by decide : 25 < 32),
    show (6 : UInt32).toNat = 6 from rfl,
    show (11 : UInt32).toNat = 11 from rfl,
    show (25 : UInt32).toNat = 25 from rfl]
  ac_rfl

/-- `σ₀ x = ROTR⁷ x ⊕ ROTR¹⁸ x ⊕ SHR³ x`, lifted. (FIPS 180-4 §4.1.2, eq. 4.6) -/
@[simp] theorem smallSigma0_toBitVec (x : UInt32) :
    SHS.SHA256.smallSigma0 x.toBitVec =
      ((Impl.UInt32.rotr x 7) ^^^ (Impl.UInt32.rotr x 18) ^^^ (x >>> 3)).toBitVec := by
  simp only [SHS.SHA256.smallSigma0, toBitVec_xor,
    toBitVec_rotr _ _ (by decide : 0 < (7 : UInt32).toNat) (by decide : (7 : UInt32).toNat < 32),
    toBitVec_rotr _ _ (by decide : 0 < (18 : UInt32).toNat) (by decide : (18 : UInt32).toNat < 32),
    toBitVec_shr_of_lt _ _ (by decide : (3 : UInt32).toNat < 32),
    ROTR_eq_rotateRight _ _ (by decide : 7 < 32),
    ROTR_eq_rotateRight _ _ (by decide : 18 < 32),
    SHR_eq_shr,
    show (3 : UInt32).toNat = 3 from rfl,
    show (7 : UInt32).toNat = 7 from rfl,
    show (18 : UInt32).toNat = 18 from rfl]
  ac_rfl

/-- `σ₁ x = ROTR¹⁷ x ⊕ ROTR¹⁹ x ⊕ SHR¹⁰ x`, lifted. (FIPS 180-4 §4.1.2, eq. 4.7) -/
@[simp] theorem smallSigma1_toBitVec (x : UInt32) :
    SHS.SHA256.smallSigma1 x.toBitVec =
      ((Impl.UInt32.rotr x 17) ^^^ (Impl.UInt32.rotr x 19) ^^^ (x >>> 10)).toBitVec := by
  simp only [SHS.SHA256.smallSigma1, toBitVec_xor,
    toBitVec_rotr _ _ (by decide : 0 < (17 : UInt32).toNat) (by decide : (17 : UInt32).toNat < 32),
    toBitVec_rotr _ _ (by decide : 0 < (19 : UInt32).toNat) (by decide : (19 : UInt32).toNat < 32),
    toBitVec_shr_of_lt _ _ (by decide : (10 : UInt32).toNat < 32),
    ROTR_eq_rotateRight _ _ (by decide : 17 < 32),
    ROTR_eq_rotateRight _ _ (by decide : 19 < 32),
    SHR_eq_shr,
    show (10 : UInt32).toNat = 10 from rfl,
    show (17 : UInt32).toNat = 17 from rfl,
    show (19 : UInt32).toNat = 19 from rfl]
  ac_rfl

end SHS.Equiv.SHA256.Functions
