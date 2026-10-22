import Library.Random.Lcg.Lattice
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-! These theorems give the spectral test of the LCG of `Examples/Lcg/Program.lean`: the squared
length `ν_t²` of the shortest nonzero vector of `Dual t`, for `t = 2, …, 6`.  Knuth shows that
`1 / ν_t` is the largest distance between adjacent hyperplanes, over all families of parallel
hyperplanes that cover the `t`-tuples of successive states, scaled to the unit cube.  These
theorems state `ν_t²`.  `dual_eq_vecMul` writes every vector of `Dual t` as an integer combination
`y C` of the rows of the canonical basis `C`.  `le_of_certificate` gives a lower bound on the
squared length of every nonzero `y C` from a certificate: integer matrices `U`, `B`, and `A` with
`U B = C` and `B A = δ I`, bounds `b_i` with `(N - 1) ∑_k A_{k i}² < (b_i + 1)² δ²`, and the
check that every nonzero `z` with `|z_i| ≤ b_i` has `N ≤ |z B|²`.  The certificates take an
LLL-reduced basis `B` of `Dual t`, the matrix `U`, the adjugate `A` of `B`, and
`δ = det B = ±2^64`, which `Examples/Lcg/certificates.py` computes, and the kernel checks each of
them, so the theorems do not depend on the script. -/

namespace Library.Random.Lcg

open Matrix

/-- The canonical basis of `Dual (t + 1)`: the row `(2^64, 0, …, 0)` and, for `k = 1, …, t`, the
row `-(a^k mod 2^64) e_0 + e_k`. -/
def canonical (t : Nat) : Matrix (Fin (t + 1)) (Fin (t + 1)) ℤ := fun i j =>
  if i = 0 then (if j = 0 then 2 ^ 64 else 0)
  else if j = 0 then -((multiplier.toNat ^ (i : Nat) % 2 ^ 64 : ℕ) : ℤ)
  else if j = i then 1 else 0

/-- Every vector of `Dual (t + 1)` is an integer combination of the rows of `canonical t`. -/
theorem dual_eq_vecMul {t : Nat} {s : Fin (t + 1) → ℤ} (hs : Dual (t + 1) s) :
    ∃ y, vecMul y (canonical t) = s := by
  set r : Fin (t + 1) → ℤ := fun k => ((multiplier.toNat ^ (k : Nat) % 2 ^ 64 : ℕ) : ℤ) with hr
  have hdvd : (2 ^ 64 : ℤ) ∣ ∑ k, s k * r k := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (∑ k, s k * (multiplier.toNat : ℤ) ^ (k : Nat)) (2 ^ 64)).mpr (by
        have := Int.dvd_of_emod_eq_zero hs
        exact_mod_cast this)
    have h1 : ((∑ k, s k * r k : ℤ) : ZMod (2 ^ 64)) =
        ((∑ k, s k * (multiplier.toNat : ℤ) ^ (k : Nat) : ℤ) : ZMod (2 ^ 64)) := by
      rw [Int.cast_sum, Int.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hr, Int.cast_mul, Int.cast_natCast, ZMod.natCast_mod, Int.cast_pow, Nat.cast_pow]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ 64)).mp (h1.trans h0)
    exact_mod_cast this
  refine ⟨fun i => if i = 0 then (∑ k, s k * r k) / 2 ^ 64 else s i, ?_⟩
  funext j
  simp only [vecMul, dotProduct, canonical]
  rw [Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [↓reduceIte, Fin.succ_ne_zero]
    rw [Int.ediv_mul_cancel hdvd, Fin.sum_univ_succ (f := fun k => s k * r k)]
    have hr0 : r 0 = 1 := by simp [hr]
    rw [hr0, mul_one]
    simp only [hr, mul_neg, Finset.sum_neg_distrib]
    ring
  · simp only [Fin.succ_ne_zero, ↓reduceIte, mul_zero, zero_add, Fin.succ_inj]
    simp

/-- When `U B = C`, `B A = δ I`, the bounds `b`, and the check over the box hold, every nonzero
`y C` has squared length at least `N`. -/
theorem le_of_certificate {n : Type} [Fintype n] [DecidableEq n] (C U B A : Matrix n n ℤ)
    (δ N : ℤ) (b : n → ℕ) (hUB : U * B = C) (hBA : B * A = δ • (1 : Matrix n n ℤ))
    (hb : ∀ i, (N - 1) * ∑ k, A k i ^ 2 < ((b i : ℤ) + 1) ^ 2 * δ ^ 2)
    (hbox : ∀ z ∈ Fintype.piFinset (fun i => Finset.Icc (-(b i : ℤ)) (b i)), z ≠ 0 →
      N ≤ ∑ j, vecMul z B j ^ 2)
    (y : n → ℤ) (hs : vecMul y C ≠ 0) : N ≤ ∑ j, vecMul y C j ^ 2 := by
  have hsz : vecMul y C = vecMul (vecMul y U) B := by rw [← hUB, vecMul_vecMul]
  set z := vecMul y U with hz
  by_contra hlt
  rw [not_le] at hlt
  have hz0 : z ≠ 0 := by
    rintro h0
    apply hs
    rw [hsz, h0, zero_vecMul]
  have hsA : vecMul (vecMul y C) A = δ • z := by
    rw [hsz, vecMul_vecMul, hBA, vecMul_smul, vecMul_one]
  have hzi : ∀ i, δ * z i = ∑ k, vecMul y C k * A k i := fun i => by
    have := congrFun hsA i
    simp only [vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hbound : ∀ i, z i ∈ Finset.Icc (-(b i : ℤ)) (b i) := fun i => by
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (vecMul y C) (fun k => A k i)
    rw [← hzi] at cs
    have hA : 0 ≤ ∑ k, A k i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h1 : (δ * z i) ^ 2 < ((b i : ℤ) + 1) ^ 2 * δ ^ 2 :=
      lt_of_le_of_lt (cs.trans (mul_le_mul_of_nonneg_right (by omega) hA)) (hb i)
    have h2 : z i ^ 2 < ((b i : ℤ) + 1) ^ 2 := by
      rw [mul_pow, mul_comm] at h1
      exact lt_of_mul_lt_mul_right h1 (sq_nonneg δ)
    have h3 := abs_lt_of_sq_lt_sq' h2 (by positivity)
    rw [Finset.mem_Icc]
    constructor <;> omega
  have := hbox z (Fintype.mem_piFinset.mpr hbound) hz0
  rw [← hsz] at this
  omega

/-! ### The values for two to six successive states

The definitions and theorems from here to the end of the file are the output of
`uv run Examples/Lcg/certificates.py`. -/

/-- A reduced basis of `Dual 2`. -/
def basis2 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1381628436, 2627121436; -5803484695, 2316313811]
/-- The matrix whose product with `basis2` is `canonical 1`. -/
def unimodular2 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2316313811, -2627121436; -799129460, 906358251]
/-- The adjugate of `basis2`. -/
def adjugate2 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2316313811, -2627121436; 5803484695, 1381628436]
/-- The bounds of the box of coefficients for `t = 2`. -/
def bounds2 : Fin 2 → ℕ := ![1, 0]
-- The shortest vector of `Dual 2`, `shortest2` of Lattice.lean: ![1381628436, 2627121436]

/-- The spectral test value `ν_2² = 8810664174654508192`: every nonzero vector of `Dual 2` has
squared length at least 8810664174654508192, which `shortest2` attains. -/
theorem spectral_two :
    (∀ s : Fin 2 → ℤ, Dual 2 s → s ≠ 0 → 8810664174654508192 ≤ ∑ k, s k ^ 2) ∧
      Dual 2 shortest2 ∧ ∑ k, shortest2 k ^ 2 = 8810664174654508192 := by
  refine ⟨fun s hs h0 => ?_, by decide +kernel, by decide +kernel⟩
  obtain ⟨y, rfl⟩ := dual_eq_vecMul (t := 1) hs
  exact le_of_certificate (canonical 1) unimodular2 basis2 adjugate2 (18446744073709551616)
    8810664174654508192 bounds2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) y h0

/-- A reduced basis of `Dual 3`. -/
def basis3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-2498093, -397201, 8218; 993613, -1313894, -1941511; 789167, 2349913, -2090292]
/-- The matrix whose product with `basis3` is `canonical 2`. -/
def unimodular3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-7308804055591, 810954487658, -781967691603; 2521541170481, -279779716690, 269779257094;
    2979862872791, -330633185801, 318815017369]
/-- The adjugate of `basis3`. -/
def adjugate3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![7308804055591, -810954487658, 781967691603; 544764893659, 5215258438750, -4841909526889;
    3371785891967, 5556843294342, 3676893481355]
/-- The bounds of the box of coefficients for `t = 3`. -/
def bounds3 : Fin 3 → ℕ := ![1, 1, 0]
-- The shortest vector of `Dual 3`, `shortest3` of Lattice.lean: ![-2498093, -397201, 8218]

/-- The spectral test value `ν_3² = 6398304806574`: every nonzero vector of `Dual 3` has
squared length at least 6398304806574, which `shortest3` attains. -/
theorem spectral_three :
    (∀ s : Fin 3 → ℤ, Dual 3 s → s ≠ 0 → 6398304806574 ≤ ∑ k, s k ^ 2) ∧
      Dual 3 shortest3 ∧ ∑ k, shortest3 k ^ 2 = 6398304806574 := by
  refine ⟨fun s hs h0 => ?_, by decide +kernel, by decide +kernel⟩
  obtain ⟨y, rfl⟩ := dual_eq_vecMul (t := 2) hs
  exact le_of_certificate (canonical 2) unimodular3 basis3 adjugate3 (-18446744073709551616)
    6398304806574 bounds3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) y h0

/-- A reduced basis of `Dual 4`. -/
def basis4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![28729, 22523, -11836, 51380; 46980, 11528, -35935, -23937; -13121, 28799, -61976, 18670;
    -22652, -71927, -25229, 2508]
/-- The matrix whose product with `basis4` is `canonical 3`. -/
def unimodular4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![178586928026037, 242513036984482, -183412778687379, 21353581504438; -61612582318841,
    -83667122895020, 63277503287116, -7366996637360; -72811441152742, -98874670819098,
    74778982368239, -8706040583687; -7685679774598, -10436808360107, 7893365427927, -918974256951]
/-- The adjugate of `basis4`. -/
def adjugate4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![178586928026037, 242513036984482, -183412778687379, 21353581504438; -54522069325871,
    -41440388203910, 127683850795561, -229055879117570; 23779586240189, -113878546363022,
    -199276674133963, -90594258066778; 288547605461561, -143667996316918, 677377041489,
    67599939350830]
/-- The bounds of the box of coefficients for `t = 4`. -/
def bounds4 : Fin 4 → ℕ := ![1, 1, 1, 0]
-- The shortest vector of `Dual 4`, `shortest4` of Lattice.lean: ![28729, 22523, -11836, 51380]

/-- The spectral test value `ν_4² = 4112636266`: every nonzero vector of `Dual 4` has
squared length at least 4112636266, which `shortest4` attains. -/
theorem spectral_four :
    (∀ s : Fin 4 → ℤ, Dual 4 s → s ≠ 0 → 4112636266 ≤ ∑ k, s k ^ 2) ∧
      Dual 4 shortest4 ∧ ∑ k, shortest4 k ^ 2 = 4112636266 := by
  refine ⟨fun s hs h0 => ?_, by decide +kernel, by decide +kernel⟩
  obtain ⟨y, rfl⟩ := dual_eq_vecMul (t := 3) hs
  exact le_of_certificate (canonical 3) unimodular4 basis4 adjugate4 (18446744073709551616)
    4112636266 bounds4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) y h0

/-- A reduced basis of `Dual 5`. -/
def basis5 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1079, -547, 5024, -4057, 1581; 6187, -2679, 1723, -588, -3655; 5333, 4546, 1987, 2190,
    -1104; -4384, 1372, 3386, 5682, -688; -177, 348, -1161, 5213, 7141]
/-- The matrix whose product with `basis5` is `canonical 4`. -/
def unimodular5 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![-33819487410534, 1385966143227370, 1056505473952720, -1006512671595865, 783234307278804;
    11667740607301, -478159034564238, -364494933664617, 347247391055495, -270216240155719;
    13788498657914, -565070430365316, -430746454931141, 410363955343399, -319331427577526;
    1455457872821, -59646537812259, -45467844946225, 43316351137599, -33707327522574;
    33198804676007, -1360529765517155, -1037115626358180, 988040332563677, -768859754355635]
/-- The adjugate of `basis5`. -/
def adjugate5 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![-33819487410534, 1385966143227370, 1056505473952720, -1006512671595865, 783234307278804;
    -65055508566254, -2666153888161758, 2693350202352528, -462790245994405, -978417696125884;
    2288010549294122, 632343699112954, 152684820148304, 1641320395613439, -1167341345804;
    -1220630249782942, 1257498459797746, 58898900954640, 1502782007181779, 1067765257395684;
    1265394063514682, -650896355667830, -123240063858480, -832590864220393, 1870641413561620]
/-- The bounds of the box of coefficients for `t = 5`. -/
def bounds5 : Fin 5 → ℕ := ![1, 1, 1, 0, 0]
-- The shortest vector of `Dual 5`, `shortest5` of Lattice.lean: ![1079, -547, 5024, -4057, 1581]

/-- The spectral test value `ν_5² = 45662836`: every nonzero vector of `Dual 5` has
squared length at least 45662836, which `shortest5` attains. -/
theorem spectral_five :
    (∀ s : Fin 5 → ℤ, Dual 5 s → s ≠ 0 → 45662836 ≤ ∑ k, s k ^ 2) ∧
      Dual 5 shortest5 ∧ ∑ k, shortest5 k ^ 2 = 45662836 := by
  refine ⟨fun s hs h0 => ?_, by decide +kernel, by decide +kernel⟩
  obtain ⟨y, rfl⟩ := dual_eq_vecMul (t := 4) hs
  exact le_of_certificate (canonical 4) unimodular5 basis5 adjugate5 (18446744073709551616)
    45662836 bounds5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) y h0

/-- A reduced basis of `Dual 6`. -/
def basis6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![801, -177, 290, 952, 345, 253; 148, -317, 1084, -91, -270, -730; -701, -207, 254, 958, 609,
    711; -75, -808, -65, -586, 705, -895; -410, 941, -1030, 518, -449, -1086; -63, -1585, -1340,
    929, -2177, -252]
/-- The matrix whose product with `basis6` is `canonical 5`. -/
def unimodular6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![12557189713614605, -3217686658582046, -11362421943500019, -192754300057388, -2094344566315074,
    -419954150593620; -4332236930636854, 1110103557519165, 3920041433453820, 66500332979942,
    722549956048809, 144884398648797; -5119675275131929, 1311878788548019, 4632558081581190,
    78587601739363, 853882464015409, 171218953485437; -540412112322393, 138476592582702,
    488994001335163, 8295387808014, 90132362162701, 18073176783719; -12326729956646409,
    3158633056442657, 11153889536218633, 189216716397436, 2055907451740200, 412246810520653;
    -5171326387454687, 1325114002701204, 4679294791422086, 79380452228208, 862497068788005,
    172946338314162]
/-- The adjugate of `basis6`. -/
def adjugate6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![12557189713614605, -3217686658582046, -11362421943500019, -192754300057388, -2094344566315074,
    -419954150593620; -610885885018039, 2759705332410, -2599583864193975, -7423569315284668,
    5273353111567974, -4316030885822148; -1426229932358699, 11928665882994866, 2927660147838933,
    -4376540974822156, -2407717568130578, -1807184328983668; 7997000255395697, 2750734375122250,
    6731145515823985, -1236463404838172, 5126257010079958, 1351464551230364; 4604113132514781,
    -5314994576501758, 3156881470314973, 8297722516368916, 723865619130270, -3663691768885652;
    -2006514948672807, -6586891782307238, 1165919176224473, -6229169164040828, -7196595727558458,
    292129133337852]
/-- The bounds of the box of coefficients for `t = 6`. -/
def bounds6 : Fin 6 → ℕ := ![1, 1, 1, 0, 0, 0]
-- The shortest vector of `Dual 6`, `shortest6` of Lattice.lean: ![801, -177, 290, 952, 345, 253]

/-- The spectral test value `ν_6² = 1846368`: every nonzero vector of `Dual 6` has
squared length at least 1846368, which `shortest6` attains. -/
theorem spectral_six :
    (∀ s : Fin 6 → ℤ, Dual 6 s → s ≠ 0 → 1846368 ≤ ∑ k, s k ^ 2) ∧
      Dual 6 shortest6 ∧ ∑ k, shortest6 k ^ 2 = 1846368 := by
  refine ⟨fun s hs h0 => ?_, by decide +kernel, by decide +kernel⟩
  obtain ⟨y, rfl⟩ := dual_eq_vecMul (t := 5) hs
  exact le_of_certificate (canonical 5) unimodular6 basis6 adjugate6 (18446744073709551616)
    1846368 bounds6 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) y h0

end Library.Random.Lcg
