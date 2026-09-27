import Project.SpectralKL.Series
import Project.SpectralKL.Horner
import LeanExe.Examples.SpectralKL.Coefficients

namespace Project.SpectralKL
open CodeLib.IEEE64 Project.ProofKit.F64Horner

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

noncomputable def coefficients40 : List (UInt64 × ℝ) := [
  (0x3FE0000000000000, 1 / 2),
  (0xBFC5555555555555, -1 / 6),
  (0x3FB5555555555555, 1 / 12),
  (0xBFA999999999999A, -1 / 20),
  (0x3FA1111111111111, 1 / 30),
  (0xBF98618618618618, -1 / 42),
  (0x3F92492492492492, 1 / 56),
  (0xBF8C71C71C71C71C, -1 / 72),
  (0x3F86C16C16C16C17, 1 / 90),
  (0xBF829E4129E4129E, -1 / 110),
  (0x3F7F07C1F07C1F08, 1 / 132),
  (0xBF7A41A41A41A41A, -1 / 156),
  (0x3F76816816816817, 1 / 182),
  (0xBF73813813813814, -1 / 210),
  (0x3F71111111111111, 1 / 240),
  (0xBF6E1E1E1E1E1E1E, -1 / 272),
  (0x3F6AC5701AC5701B, 1 / 306),
  (0xBF67F405FD017F40, -1 / 342),
  (0x3F658ED2308158ED, 1 / 380),
  (0xBF63813813813814, -1 / 420),
  (0x3F61BB4A4046ED29, 1 / 462),
  (0xBF603091B51F5E1A, -1 / 506),
  (0x3F5DAE6076B981DB, 1 / 552),
  (0xBF5B4E81B4E81B4F, -1 / 600),
  (0x3F5934C67F9B2CE6, 1 / 650),
  (0xBF5756CAC201756D, -1 / 702),
  (0x3F55AC056B015AC0, 1 / 756),
  (0xBF542D6625D51F87, -1 / 812),
  (0x3F52D50A012D50A0, 1 / 870),
  (0xBF519E0119E0119E, -1 / 930),
  (0x3F50842108421084, 1 / 992),
  (0xBF4F07C1F07C1F08, -1 / 1056),
  (0x3F4D347A4BC01D34, 1 / 1122),
  (0xBF4B89401B89401C, -1 / 1190),
  (0x3F4A01A01A01A01A, 1 / 1260),
  (0xBF4899C0F601899C, -1 / 1332),
  (0x3F474E4B040174E5, 1 / 1406),
  (0xBF461C544C0161C5, -1 / 1482),
  (0x3F45015015015015, 1 / 1560),
  (0xBF43FB013FB013FB, -1 / 1640),
  (0x3F43076EE7525C2C, 1 / 1722)]

theorem coefficients40_valid :
    ∀ c ∈ coefficients40, Approximation c.1 c.2 (1/2) arithmeticEpsilon := by
  intro c hc
  simp only [coefficients40, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals first
    | (unfold CodeLib.IEEE64.Finite; decide)
    | norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
        Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction,
        UInt64.toNat_ofNat, arithmeticEpsilon]

theorem coefficients40_words :
    coefficients40.map Prod.fst = LeanExe.Examples.SpectralKL.coefficients40.toList := rfl

theorem coefficients40_real (d : ℝ) :
    hornerReal d (coefficients40.map Prod.snd) = series 41 d := by
  norm_num [coefficients40, hornerReal, series, Finset.sum_range_succ]
  ring

def kernel40Bits (d : UInt64) : UInt64 :=
  hornerBits d LeanExe.Examples.SpectralKL.coefficients40.toList

theorem kernel40_error (d : UInt64) (hd : Finite d) (bd : |value d| ≤ 1/2) :
    Finite (kernel40Bits d) ∧
      |value (kernel40Bits d) - kernel (1+value d)| ≤ 1/100000000000000 := by
  have h := horner_error coefficients40 d coefficients40_valid hd bd
  rw [coefficients40_words, coefficients40_real] at h
  refine ⟨h.finite, ?_⟩
  have ha := series41_error (value d) bd
  have hb := (abs_sub_le (value (kernel40Bits d)) (series 41 (value d))
    (kernel (1+value d))).trans (add_le_add h.accuracy ha)
  apply hb.trans
  norm_num [arithmeticEpsilon]

#print axioms kernel40_error
end Project.SpectralKL
