import Verified.Examples.ErfcHardBase
import Verified.Examples.ErfcAccMain

/-!
The rows of the tables of hard cases of `Erfc`, checked one at a time.  `HardSerOK` states the
kernel's conditions for a row of the negative or the positive table: finite words, the rounded sum
`cw` of the row's two words, the enclosure of `erfc` at the row's input from the series of `erf`
(`SerEncl`), and the interior conditions of `ErfcHardBase.hard_within` (`Interior`).  `HardAsymOK`
states them for a row of the asymptotic table, with a model of `erfcxN` and an enclosure of
`exp (-x²)` (`AsymEncl`).  `ser_row` and `asym_row` give one step for an input that equals the
row's.
-/

namespace Verified.Examples.ErfcHardRows

open Real Set CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcRound ErfcSeries ErfcHardBase PolyBound
  PolyCalc RealErf RealErfScaled F64NearestNonnegative

set_option exponentiation.threshold 4096

/-- The words of row `k` at offset `o`: finite, with rounded sum `cw`. -/
def RowWords (o : UInt64) (k : ℕ) (cw : UInt64) : Prop :=
  Finite Erfc.excTable[(o + 3 * UInt64.ofNat k).toNat]! ∧
  Finite Erfc.excTable[(o + 3 * UInt64.ofNat k + 1).toNat]! ∧
  Finite Erfc.excTable[(o + 3 * UInt64.ofNat k + 2).toNat]! ∧
  Wasm.IEEE64.add Erfc.excTable[(o + 3 * UInt64.ofNat k + 1).toNat]!
    Erfc.excTable[(o + 3 * UInt64.ofNat k + 2).toNat]! = cw ∧ cw.toNat < limit

/-- The conditions of `hard_within` or of `half_within` for the word `cw`, the enclosure
`[Ylo, Yhi]`, and the binade `e`. -/
def Interior (cw : UInt64) (Ylo Yhi : ℚ) (e : ℕ) : Prop :=
  1 ≤ e ∧ e ≤ 2046 ∧ Yhi < 2 ^ 1023 ∧
  ((((2 : ℚ) ^ (e + 51) + 2 * 2 ^ (e - 1)) / 2 ^ 1074 ≤ Ylo ∧
      ratOfWord cw - Ylo < 2 ^ (e - 1) / 2 ^ 1074 ∧ Yhi - ratOfWord cw < 2 ^ (e - 1) / 2 ^ 1074) ∨
    ((2 : ℚ) ^ (e + 51) / 2 ^ 1074 ≤ Ylo ∧ ratOfWord cw - Ylo < 2 ^ (e - 1) / 2 ^ 1074 / 2 ∧
      Yhi - ratOfWord cw < 2 ^ (e - 1) / 2 ^ 1074 / 2))

/-- `[Ylo, Yhi]` encloses `erfc q` by the series of `n` terms, for `q ≤ 0` when `neg` and
`0 ≤ q` otherwise. -/
def SerEncl (n : ℕ) (neg : Bool) (q Ylo Yhi : ℚ) : Prop :=
  if neg then q ≤ 0 ∧ 0 ≤ evalQ (ser n) (-q) ∧
    Ylo ≤ 1 + (sLo * evalQ (ser n) (-q) - sHi * serRem n (-q)) ∧
    1 + (sHi * evalQ (ser n) (-q) + sHi * serRem n (-q)) ≤ Yhi
  else 0 ≤ q ∧ 0 ≤ evalQ (ser n) q ∧
    Ylo ≤ 1 - (sHi * evalQ (ser n) q + sHi * serRem n q) ∧
    1 - (sLo * evalQ (ser n) q - sHi * serRem n q) ≤ Yhi

def HardSerOK (o : UInt64) (k n : ℕ) (neg : Bool) (cw : UInt64) (Ylo Yhi : ℚ) (e : ℕ) : Prop :=
  RowWords o k cw ∧ SerEncl n neg (ratOfWord Erfc.excTable[(o + 3 * UInt64.ofNat k).toNat]!) Ylo Yhi ∧
    Interior cw Ylo Yhi e

instance (o : UInt64) (k n : ℕ) (neg : Bool) (cw : UInt64) (Ylo Yhi : ℚ) (e : ℕ) :
    Decidable (HardSerOK o k n neg cw Ylo Yhi e) := by
  unfold HardSerOK RowWords SerEncl Interior; infer_instance

theorem entry_bits (tab : Array UInt64) (j : UInt64) (h : Finite tab[j.toNat]!) :
    (Erfc.entry tab j).toBits = tab[j.toNat]! := by
  rw [show Erfc.entry tab j = Float.ofBits tab[j.toNat]! from rfl, F64Bits.toBits_ofBits,
    not_nan_of_finite h]
  simp

/-- The input of a matching row, and the result word. -/
theorem match_row (o : UInt64) (k : ℕ) (cw : UInt64) (hw : RowWords o k cw) (x : Float) (hx : ff x)
    (heq : (Erfc.entry Erfc.excTable (o + 3 * UInt64.ofNat k) == x) = true) :
    fv x = ratOfWord Erfc.excTable[(o + 3 * UInt64.ofNat k).toNat]! ∧
      (Erfc.entry Erfc.excTable (o + 3 * UInt64.ofNat k + 1) +
        Erfc.entry Erfc.excTable (o + 3 * UInt64.ofNat k + 2)).toBits = cw := by
  obtain ⟨h0, h1, h2, hadd, -⟩ := hw
  obtain ⟨ef, ev⟩ := ErfcAccMain.ent_of_q Erfc.excTable (o + 3 * UInt64.ofNat k) _ ⟨h0, rfl⟩
  have he := (fbeq_iff _ _ ef hx).mp heq
  refine ⟨by rw [← he, ev], ?_⟩
  rw [F64Bits.toBits_add, entry_bits _ _ h1, entry_bits _ _ h2, hadd]

theorem interior_within (y : ℝ) (cw : UInt64) (Ylo Yhi : ℚ) (e : ℕ) (hlim : cw.toNat < limit)
    (hi : Interior cw Ylo Yhi e) (hy : (Ylo : ℝ) ≤ y ∧ y ≤ Yhi) :
    F64SignedRounding.WithinSteps 1 y cw := by
  obtain ⟨he1, he2, hyt, ⟨hb, hd1, hd2⟩ | ⟨hb, hd1, hd2⟩⟩ := hi
  · exact hard_within y cw hlim Ylo Yhi hy e he1 he2 hb hyt hd1 hd2
  · exact half_within y cw hlim Ylo Yhi hy e he1 he2 hb hyt hd1 hd2

theorem ser_encl (n : ℕ) (neg : Bool) (q Ylo Yhi : ℚ) (h : SerEncl n neg q Ylo Yhi) :
    (Ylo : ℝ) ≤ erfc q ∧ erfc q ≤ Yhi := by
  unfold erfc
  unfold SerEncl at h
  cases neg
  · rw [if_neg (by decide)] at h
    obtain ⟨hq0, hS, hlo, hhi⟩ := h
    obtain ⟨k1, k2⟩ := erf_encl n q hq0 hS
    have c1 : (Ylo : ℝ) ≤ ((1 - (sHi * evalQ (ser n) q + sHi * serRem n q) : ℚ) : ℝ) := by qc hlo
    have c2 : ((1 - (sLo * evalQ (ser n) q - sHi * serRem n q) : ℚ) : ℝ) ≤ (Yhi : ℝ) := by qc hhi
    push_cast at c1 c2 k1 k2
    constructor <;> linarith
  · rw [if_pos rfl] at h
    obtain ⟨hq0, hS, hlo, hhi⟩ := h
    obtain ⟨k1, k2⟩ := erf_encl n (-q) (by linarith) hS
    have hodd : erf (q : ℝ) = -erf (((-q : ℚ) : ℝ)) := by
      push_cast; rw [erf_neg]; ring
    rw [hodd]
    have c1 : (Ylo : ℝ) ≤ ((1 + (sLo * evalQ (ser n) (-q) - sHi * serRem n (-q)) : ℚ) : ℝ) := by
      qc hlo
    have c2 : ((1 + (sHi * evalQ (ser n) (-q) + sHi * serRem n (-q)) : ℚ) : ℝ) ≤ (Yhi : ℝ) := by
      qc hhi
    push_cast at c1 c2 k1 k2 ⊢
    constructor <;> linarith

/-- One step for an input that equals the input of a row of the series tables. -/
theorem ser_row (o : UInt64) (k n : ℕ) (neg : Bool) (cw : UInt64) (Ylo Yhi : ℚ) (e : ℕ)
    (hok : HardSerOK o k n neg cw Ylo Yhi e) (x : Float) (hx : ff x)
    (heq : (Erfc.entry Erfc.excTable (o + 3 * UInt64.ofNat k) == x) = true) :
    F64SignedRounding.WithinSteps 1 (erfc (fv x))
      (Erfc.entry Erfc.excTable (o + 3 * UInt64.ofNat k + 1) +
        Erfc.entry Erfc.excTable (o + 3 * UInt64.ofNat k + 2)).toBits := by
  obtain ⟨hw, hs, hi⟩ := hok
  obtain ⟨hxv, hbits⟩ := match_row o k cw hw x hx heq
  rw [hbits, hxv]
  exact interior_within _ cw Ylo Yhi e hw.2.2.2.2 hi (ser_encl n neg _ Ylo Yhi hs)

/-- `[Ylo, Yhi]` encloses `erfc x` by the model `p` of `erfcxN` on `[a, b]` around `c` with errors
`s + eD (b - x)`, and the chain `los`, `his` of `exp (2^i (-x²/1024))` from `N` terms. -/
def AsymEncl (p : List ℚ) (a b c s eD : ℚ) (N : ℕ) (los his : List ℚ) (x Ylo Yhi : ℚ) : Prop :=
  0 < x ∧ a ≤ x ∧ x ≤ b ∧ ChainOK (-(x ^ 2) / 1024) N los his 10 ∧ 0 ≤ los.getD 10 0 ∧
    0 ≤ evalQ p (x - c) - (s + eD * (b - x)) ∧
    Ylo ≤ los.getD 10 0 * sLo * (evalQ p (x - c) - (s + eD * (b - x))) ∧
    his.getD 10 0 * sHi * (evalQ p (x - c) + (s + eD * (b - x))) ≤ Yhi

def HardAsymOK (k : ℕ) (cw : UInt64) (p : List ℚ) (a b c s eD : ℚ) (N : ℕ) (los his : List ℚ)
    (Ylo Yhi : ℚ) (e : ℕ) : Prop :=
  RowWords 0 k cw ∧
    AsymEncl p a b c s eD N los his (ratOfWord Erfc.excTable[((0 : UInt64) + 3 * UInt64.ofNat k).toNat]!)
      Ylo Yhi ∧
    Interior cw Ylo Yhi e

instance (k : ℕ) (cw : UInt64) (p : List ℚ) (a b c s eD : ℚ) (N : ℕ) (los his : List ℚ)
    (Ylo Yhi : ℚ) (e : ℕ) : Decidable (HardAsymOK k cw p a b c s eD N los his Ylo Yhi e) := by
  unfold HardAsymOK RowWords AsymEncl Interior; infer_instance

theorem asym_encl (p : List ℚ) (a b c s eD : ℚ) (N : ℕ) (los his : List ℚ) (x Ylo Yhi : ℚ)
    (hmodel : ∀ y ∈ Icc (a : ℝ) b, |erfcxN y - eval p (y - c)| ≤ (s : ℝ) + eD * ((b : ℝ) - y))
    (h : AsymEncl p a b c s eD N los his x Ylo Yhi) : (Ylo : ℝ) ≤ erfc x ∧ erfc x ≤ Yhi := by
  obtain ⟨hx0, ha, hb, hch, hlo0, hPD, hlo, hhi⟩ := h
  have hE := exp_chain (-(x ^ 2) / 1024) N los his 10 hch
  have e10 : (2 : ℝ) ^ 10 * (((-(x ^ 2) / 1024 : ℚ)) : ℝ) = -((x : ℝ) ^ 2) := by
    push_cast; ring
  rw [e10] at hE
  obtain ⟨k1, k2⟩ := erfc_model_encl x hx0 p a b c s eD hmodel ⟨ha, hb⟩ (los.getD 10 0)
    (his.getD 10 0) hE hlo0 hPD
  have q1 : (Ylo : ℝ) ≤ ((los.getD 10 0 * sLo * (evalQ p (x - c) - (s + eD * (b - x))) : ℚ) :
      ℝ) := by qc hlo
  have q2 : ((his.getD 10 0 * sHi * (evalQ p (x - c) + (s + eD * (b - x))) : ℚ) : ℝ) ≤ Yhi := by
    qc hhi
  exact ⟨q1.trans k1, k2.trans q2⟩

/-- One step for an input that equals the input of a row of the asymptotic table. -/
theorem asym_row (k : ℕ) (cw : UInt64) (p : List ℚ) (a b c s eD : ℚ) (N : ℕ) (los his : List ℚ)
    (Ylo Yhi : ℚ) (e : ℕ)
    (hmodel : ∀ y ∈ Icc (a : ℝ) b, |erfcxN y - eval p (y - c)| ≤ (s : ℝ) + eD * ((b : ℝ) - y))
    (hok : HardAsymOK k cw p a b c s eD N los his Ylo Yhi e) (x : Float) (hx : ff x)
    (heq : (Erfc.entry Erfc.excTable (0 + 3 * UInt64.ofNat k) == x) = true) :
    F64SignedRounding.WithinSteps 1 (erfc (fv x))
      (Erfc.entry Erfc.excTable (0 + 3 * UInt64.ofNat k + 1) +
        Erfc.entry Erfc.excTable (0 + 3 * UInt64.ofNat k + 2)).toBits := by
  obtain ⟨hw, hs, hi⟩ := hok
  obtain ⟨hxv, hbits⟩ := match_row 0 k cw hw x hx heq
  rw [hbits, hxv]
  exact interior_within _ cw Ylo Yhi e hw.2.2.2.2 hi (asym_encl p a b c s eD N los his _ Ylo Yhi
    hmodel hs)

#print axioms ser_row
#print axioms asym_row

end Verified.Examples.ErfcHardRows
