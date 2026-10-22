import Library.Numerics.Float64.Pow.PowLogEval

/-!
The error of `Pow.powLog`'s arithmetic after `r`.  For words `rhi` and `rlo` with `r = rhi + rlo`
exact on the grid of `2 ^ -60`, `rhi` on the grid of `2 ^ -29`, `|r| ≤ 23/4000`, and
`|rlo| ≤ 3 · 2 ^ -22`, the pair `y + tail` lies within
`12 u (|k| 2 ^ -44 + |logctail| + Q) + 3 u |r| ^ 3 + 24 u ^ 2 (|t1 + r| + rhi ^ 2) +
40 (|k| + 1) μ`
of `M = k (ln2hi + ln2lo) + logc + logctail + r - r ^ 2 / 2 + poly r`, where
`Q = |rlo| |r + rhi|`, and `|tail|` is at most `2 u |y|` plus the same bound.
-/

namespace Library.Numerics.Float64.Pow.PowLogError
open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Exp.ExpSpecialNegative

set_option exponentiation.threshold 4096

/-- The arithmetic of `PowLogEval.logWords` after `rhi` and `rlo`. -/
def afterWords (rhi rlo kd lc lt : UInt64) : UInt64 × UInt64 :=
  let r := Wasm.IEEE64.add rhi rlo
  let t1 := Wasm.IEEE64.add (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) lc
  let t2 := Wasm.IEEE64.add t1 r
  let lo1 := Wasm.IEEE64.add (Wasm.IEEE64.mul kd 0x3D2EF35793C76730) lt
  let lo2 := Wasm.IEEE64.add (Wasm.IEEE64.sub t1 t2) r
  let ar := Wasm.IEEE64.mul 0xBFE0000000000000 r
  let arhi := Wasm.IEEE64.mul 0xBFE0000000000000 rhi
  let arhi2 := Wasm.IEEE64.mul rhi arhi
  let hi := Wasm.IEEE64.add t2 arhi2
  let lo3 := Wasm.IEEE64.mul rlo (Wasm.IEEE64.add ar arhi)
  let lo4 := Wasm.IEEE64.add (Wasm.IEEE64.sub t2 hi) arhi2
  let p := PowLogPoly.pWord r ar
  let lo := Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add lo1 lo2) lo3) lo4) p
  let y := Wasm.IEEE64.add hi lo
  (y, Wasm.IEEE64.add (Wasm.IEEE64.sub hi y) lo)

theorem logWords_eq (iz kd invc lc lt : UInt64) :
    PowLogEval.logWords iz kd invc lc lt =
      afterWords (Wasm.IEEE64.sub (Wasm.IEEE64.mul (PowLogBits.zhiOf iz) invc) one)
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub iz (PowLogBits.zhiOf iz)) invc) kd lc lt := rfl

/-- The bound of the error, for `Q ≥ |rlo| |r + rhi|` and `H ≥ rhi ^ 2`. -/
noncomputable def bound (K : Int) (lt R T Q H : ℝ) : ℝ :=
  12 / 2 ^ 53 * (|(K : ℝ)| / 2 ^ 44 + |lt| + Q) + 3 / 2 ^ 53 * |R| ^ 3 +
    24 / 2 ^ 106 * (|T + R| + H) + 40 * (|(K : ℝ)| + 1) * multiplicationUnderflowEpsilon

theorem int_bound (m : Int) (x : ℝ) (s : Nat) (hm : (m : ℝ) = x * 2 ^ s) (c : ℝ) (N : Nat)
    (hx : |x| ≤ c) (hc : c * 2 ^ s ≤ N) : m.natAbs ≤ N := by
  have h : |(m : ℝ)| ≤ N := by
    rw [hm, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ s)]
    exact (mul_le_mul_of_nonneg_right hx (by positivity)).trans hc
  rw [← Int.cast_abs] at h
  have h2 : |m| ≤ N := by exact_mod_cast h
  rw [Int.abs_eq_natAbs] at h2
  exact_mod_cast h2

theorem grid_value (w : UInt64) (m : Int) (s : Nat) (hs : s ≤ 1074)
    (hv : Wasm.IEEE64.scaledValue w = m * 2 ^ s) : (m : ℝ) = value w * 2 ^ (1074 - s) := by
  rw [PowLogReduce.value_of_scaled w m s hs hv]
  field_simp

/-- The final combination of the error bounds of `after_error`, on real numbers. -/
theorem combine (Y Tl Hi Lo M L1 L2 L3 L4 L5 K LT Q R3 TR H μ : ℝ) (hK : 0 ≤ K) (hLT : 0 ≤ LT)
    (hQ : 0 ≤ Q) (hR3 : 0 ≤ R3) (hTR : 0 ≤ TR) (hH : 0 ≤ H) (hμ : 0 ≤ μ) (hKμ : 0 ≤ K * μ)
    (h1 : |L1| ≤ K / 2 ^ 44 + LT + (3 / 2 ^ 53 * (K / 2 ^ 44 + LT) + 2 * K * μ))
    (h2 : |L2| ≤ 1 / 2 ^ 53 * TR)
    (h3 : |L3| ≤ Q / 2 + (3 / 2 ^ 53 * (Q / 2) + μ))
    (h4 : |L4| ≤ 1 / 2 ^ 53 * ((1 + 1 / 2 ^ 53) * TR + H / 2))
    (h5 : |L5| ≤ 35 / 100 * R3 + 5 * μ)
    (hlo : |Lo| ≤ (1 + 5 / 2 ^ 53) * (|L1| + |L2| + |L3| + |L4| + |L5|))
    (hhi : |Hi| ≤ (1 + 1 / 2 ^ 53) * ((1 + 1 / 2 ^ 53) * TR + H / 2))
    (hfin : |Hi + Lo - M| ≤
      1 / 2 ^ 53 * (5 * |L1| + 5 * |L2| + 4 * |L3| + 3 * |L4| + |L5|) +
      (3 / 2 ^ 53 * (K / 2 ^ 44 + LT) + 2 * K * μ) + (3 / 2 ^ 53 * (Q / 2) + μ) +
      (7 / 4 / 2 ^ 53 * R3 + 5 * μ))
    (hyte : |Y + Tl - (Hi + Lo)| ≤ (1 + 1 / 2 ^ 40) / 2 ^ 53 * |Lo| + 3 / 2 ^ 106 * |Hi + Lo|)
    (htlb : |Tl| ≤ 2 / 2 ^ 53 * (|Y| + |Lo|)) :
    |Y + Tl - M| ≤ 12 / 2 ^ 53 * (K / 2 ^ 44 + LT + Q) + 3 / 2 ^ 53 * R3 +
        24 / 2 ^ 106 * (TR + H) + 40 * (K + 1) * μ ∧
      |Tl| ≤ 2 / 2 ^ 53 * |Y| + (12 / 2 ^ 53 * (K / 2 ^ 44 + LT + Q) + 3 / 2 ^ 53 * R3 +
        24 / 2 ^ 106 * (TR + H) + 40 * (K + 1) * μ) := by
  have hs := abs_sub_le (Y + Tl) (Hi + Lo) M
  have hhl := abs_add_le Hi Lo
  have hL1 := abs_nonneg L1
  have hL2 := abs_nonneg L2
  have hL3 := abs_nonneg L3
  have hL4 := abs_nonneg L4
  have hL5 := abs_nonneg L5
  constructor <;> linarith

theorem after_error (rhi rlo kd lc lt : UInt64) (K : Int) (hrhif : Finite rhi)
    (hrlof : Finite rlo) (hrf : Finite (Wasm.IEEE64.add rhi rlo))
    (hrv : value (Wasm.IEEE64.add rhi rlo) = value rhi + value rlo)
    (hrhg : ∃ m : Int, Wasm.IEEE64.scaledValue rhi = m * 2 ^ 1045)
    (hrg : ∃ m : Int, Wasm.IEEE64.scaledValue (Wasm.IEEE64.add rhi rlo) = m * 2 ^ 1014)
    (hR : |value rhi + value rlo| ≤ 23 / 4000) (hRl : |value rlo| ≤ 3 / 2 ^ 22)
    (hkf : Finite kd) (hkv : value kd = K) (hK : |K| ≤ 1100) (hlf : Finite lc)
    (hlg : Wasm.IEEE64.scaledValue lc % 2 ^ 1031 = 0) (hlb : |value lc| ≤ 3466 / 10000)
    (htf : Finite lt) (hlt : |value lt| ≤ 1 / 2 ^ 43) :
    let R := value rhi + value rlo
    let T := K * value 0x3FE62E42FEFA3800 + value lc
    let M := K * (value 0x3FE62E42FEFA3800 + value 0x3D2EF35793C76730) + value lc + value lt +
      (R - R ^ 2 / 2 + PowLogTable.poly R)
    let B := bound K (value lt) R T (|value rlo| * |R + value rhi|) (value rhi ^ 2)
    Finite (afterWords rhi rlo kd lc lt).1 ∧ Finite (afterWords rhi rlo kd lc lt).2 ∧
      |value (afterWords rhi rlo kd lc lt).1 + value (afterWords rhi rlo kd lc lt).2 - M| ≤ B ∧
      |value (afterWords rhi rlo kd lc lt).2| ≤
        2 / 2 ^ 53 * |value (afterWords rhi rlo kd lc lt).1| + B := by
  intro R T M B
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hμ0 : 0 ≤ multiplicationUnderflowEpsilon := by norm_num [multiplicationUnderflowEpsilon]
  have hμ1 : multiplicationUnderflowEpsilon ≤ 1 / 2 ^ 1000 := by
    norm_num [multiplicationUnderflowEpsilon]
  set μ := multiplicationUnderflowEpsilon
  set Rh := value rhi
  set Rl := value rlo
  set r := Wasm.IEEE64.add rhi rlo
  have hRb := abs_le.mp hR
  have hRlb := abs_le.mp hRl
  have hRh : |Rh| ≤ 23 / 4000 + 3 / 2 ^ 22 := by
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨mh, hmh⟩ := hrhg
  obtain ⟨mr, hmr⟩ := hrg
  have hmr53 : mr.natAbs ≤ 2 ^ 53 - 1 :=
    int_bound mr (value r) 60 (grid_value r mr 1014 (by norm_num) hmr) (23 / 4000) _
      (by rw [hrv]; exact hR) (by norm_num)
  have hmh22 : mh.natAbs ≤ 2 ^ 22 :=
    int_bound mh Rh 29 (grid_value rhi mh 1045 (by norm_num) hmh) _ _ hRh (by norm_num)
  -- the halving products and `arhi2`
  obtain ⟨harf, harv, -⟩ := PowLogSum.half_exact r hrf mr 1014 (by norm_num) (by norm_num) hmr
    (by omega)
  obtain ⟨harhf, harhv, harhs⟩ := PowLogSum.half_exact rhi hrhif mh 1045 (by norm_num)
    (by norm_num) hmh (by omega)
  rw [show (1045 : Nat) - 1 = 1044 from rfl] at harhs
  obtain ⟨ha2f, ha2v, ha2g⟩ := PowLogSum.square_exact rhi _ hrhif harhf mh hmh harhs hmh22
  set ar := Wasm.IEEE64.mul 0xBFE0000000000000 r
  set arhi := Wasm.IEEE64.mul 0xBFE0000000000000 rhi
  set arhi2 := Wasm.IEEE64.mul rhi arhi
  have ha2val : value arhi2 = -(Rh ^ 2 / 2) := by rw [ha2v, harhv]; ring
  have hH : 0 ≤ Rh ^ 2 := sq_nonneg _
  have hHb : Rh ^ 2 ≤ 1 / 1000 := by
    have := pow_le_pow_left₀ (abs_nonneg Rh) hRh 2
    rw [sq_abs] at this
    exact this.trans (by norm_num)
  -- `t1`, `t2`, and `lo2`
  obtain ⟨ht1f, ht1v, ht1g, ht1b⟩ := PowLogSum.t1_exact kd lc K hkf hkv hK hlf hlg hlb
  set t1 := Wasm.IEEE64.add (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) lc
  have hTR : |value t1 + value r| ≤ 2 ^ 11 := by
    have := abs_add_le (value t1) (value r)
    rw [hrv] at this ⊢
    linarith
  obtain ⟨ht2f, ht2g, ht2e, hlo2f, hlo2v⟩ := PowLogSum.grid_sum t1 r ht1f hrf ht1g
    ⟨mr, by rw [hmr]; ring⟩ hTR (by rw [hrv]; linarith)
  set t2 := Wasm.IEEE64.add t1 r
  -- `hi` and `lo4`
  have ha2b : |value arhi2| ≤ 1 / 150 := by
    rw [ha2val, abs_neg, abs_of_nonneg (by positivity)]
    linarith
  have hrb : |value r| ≤ 23 / 4000 := by
    rw [hrv]
    exact hR
  have ht2b : |value t2| ≤ 900 := by
    have h1 := abs_sub_abs_le_abs_sub (value t2) (value t1 + value r)
    have h2 : unitRoundoff64 * |value t1 + value r| ≤ 1 := by
      rw [hu]
      calc
        1 / 2 ^ 53 * |value t1 + value r| ≤ 1 / 2 ^ 53 * 2 ^ 11 :=
          mul_le_mul_of_nonneg_left hTR (by positivity)
        _ ≤ 1 := by norm_num
    have h3 := abs_add_le (value t1) (value r)
    linarith
  obtain ⟨hhif, -, hhie, hlo4f, hlo4v⟩ := PowLogSum.grid_sum t2 arhi2 ht2f ha2f ht2g ha2g
    (by have := abs_add_le (value t2) (value arhi2); linarith) ha2b
  set hi := Wasm.IEEE64.add t2 arhi2
  -- `lo1`, `lo3`, and `p`
  obtain ⟨hlo1f, hlo1e⟩ := PowLogSum.lo1_error kd lt K hkf hkv hK htf hlt
  have hAA : value ar + value arhi = -((R + Rh) / 2) := by
    rw [harv, harhv, hrv]
    ring
  obtain ⟨hlo3f, hlo3e⟩ := PowLogSums.lo3_error rlo ar arhi hrlof harf harhf
    (hRl.trans (by norm_num)) (by
      rw [hAA, abs_neg, abs_div, abs_two]
      have := abs_add_le R Rh
      linarith)
  have harv' : value ar = value 0xBFE0000000000000 * value r := by
    rw [harv, PowLogTable.a0_value]
    ring
  obtain ⟨hpf, hpe, hpb⟩ := PowLogPoly.p_error r ar |R| hrf harf harv' (by rw [hrv]) hR
  rw [hrv] at hpe
  set lo1 := Wasm.IEEE64.add (Wasm.IEEE64.mul kd 0x3D2EF35793C76730) lt
  set lo2 := Wasm.IEEE64.add (Wasm.IEEE64.sub t1 t2) r
  set lo3 := Wasm.IEEE64.mul rlo (Wasm.IEEE64.add ar arhi)
  set lo4 := Wasm.IEEE64.add (Wasm.IEEE64.sub t2 hi) arhi2
  set p := PowLogPoly.pWord r ar
  -- magnitudes of the five parts
  obtain ⟨-, -, -, -, hlo⟩ := PowLogSum.ln2_words
  have hK' : |(K : ℝ)| ≤ 1100 := by exact_mod_cast hK
  have hk44 : |(K : ℝ) * value 0x3D2EF35793C76730| ≤ |(K : ℝ)| / 2 ^ 44 := by
    rw [abs_mul]
    calc
      _ ≤ |(K : ℝ)| * (1 / 2 ^ 44) := mul_le_mul_of_nonneg_left hlo (abs_nonneg _)
      _ = _ := by ring
  have hQ : |Rl| * |value ar + value arhi| = |Rl| * |R + Rh| / 2 := by
    rw [hAA, abs_neg, abs_div, abs_two]
    ring
  rw [hQ] at hlo3e
  have hQ0 : 0 ≤ |Rl| * |R + Rh| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hQb : |Rl| * |R + Rh| ≤ 1 / 1000 := by
    have h1 := abs_add_le R Rh
    have h2 : |R + Rh| ≤ 1 / 50 := by linarith
    calc
      _ ≤ (3 / 2 ^ 22) * (1 / 50) := mul_le_mul hRl h2 (abs_nonneg _) (by norm_num)
      _ ≤ 1 / 1000 := by norm_num
  have hb1 : |value lo1| ≤ |(K : ℝ)| / 2 ^ 44 + |value lt| +
      (3 / 2 ^ 53 * (|(K : ℝ)| / 2 ^ 44 + |value lt|) + 2 * |(K : ℝ)| * μ) := by
    have := abs_sub_abs_le_abs_sub (value lo1) ((K : ℝ) * value 0x3D2EF35793C76730 + value lt)
    have := abs_add_le ((K : ℝ) * value 0x3D2EF35793C76730) (value lt)
    linarith
  have hb2 : |value lo2| ≤ 1 / 2 ^ 53 * |value t1 + value r| := by
    rw [hlo2v, show value t1 + value r - value t2 = -(value t2 - (value t1 + value r)) by ring,
      abs_neg, ← hu]
    exact ht2e
  have hb3 : |value lo3| ≤ |Rl| * |R + Rh| / 2 +
      (3 / 2 ^ 53 * (|Rl| * |R + Rh| / 2) + μ) := by
    have := abs_sub_abs_le_abs_sub (value lo3) (Rl * (value ar + value arhi))
    have h2 : |Rl * (value ar + value arhi)| = |Rl| * |R + Rh| / 2 := by
      rw [abs_mul, hQ]
    linarith
  have hta : |value t2 + value arhi2| ≤ (1 + 1 / 2 ^ 53) * |value t1 + value r| + Rh ^ 2 / 2 := by
    have h1 := abs_add_le (value t2) (value arhi2)
    have h2 := abs_sub_abs_le_abs_sub (value t2) (value t1 + value r)
    have h3 : |value arhi2| = Rh ^ 2 / 2 := by
      rw [ha2val, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ Rh ^ 2 / 2 by positivity)]
    rw [hu] at ht2e
    linarith
  have hb4 : |value lo4| ≤ 1 / 2 ^ 53 * ((1 + 1 / 2 ^ 53) * |value t1 + value r| + Rh ^ 2 / 2) := by
    rw [hlo4v, show value t2 + value arhi2 - value hi = -(value hi - (value t2 + value arhi2)) by
      ring, abs_neg]
    rw [hu] at hhie
    exact hhie.trans (mul_le_mul_of_nonneg_left hta (by positivity))
  have hR3 : 0 ≤ |R| ^ 3 := by positivity
  have hR3b : |R| ^ 3 ≤ 1 / 10 ^ 6 := by
    have := pow_le_pow_left₀ (abs_nonneg R) hR 3
    exact this.trans (by norm_num)
  have hTRb : |value t1 + value r| ≤ 800 := by
    have := abs_add_le (value t1) (value r)
    linarith
  have hlt0 := abs_nonneg (value lt)
  have hK0 := abs_nonneg (K : ℝ)
  have hKμ : 0 ≤ |(K : ℝ)| * μ := mul_nonneg hK0 hμ0
  have hKμb : |(K : ℝ)| * μ ≤ 1100 * (1 / 2 ^ 1000) := mul_le_mul hK' hμ1 hμ0 (by norm_num)
  have hS : |value lo1| + |value lo2| + |value lo3| + |value lo4| + |value p| ≤ 1 := by
    have h1 : 1 / 2 ^ 53 * |value t1 + value r| ≤ 1 / 2 ^ 53 * 800 :=
      mul_le_mul_of_nonneg_left hTRb (by positivity)
    have h2 : |(K : ℝ)| / 2 ^ 44 ≤ 1100 / 2 ^ 44 := div_le_div_of_nonneg_right hK' (by positivity)
    linarith
  obtain ⟨hlof, hloe, hlob⟩ := PowLogSums.sum5 lo1 lo2 lo3 lo4 p hlo1f hlo2f hlo3f hlo4f hpf hS
  set lo := Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add lo1 lo2) lo3)
    lo4) p
  -- `hi`
  have hhib : |value hi| ≤ (1 + 1 / 2 ^ 53) * |value t2 + value arhi2| := by
    have := abs_sub_abs_le_abs_sub (value hi) (value t2 + value arhi2)
    rw [hu] at hhie
    linarith
  have hlo2 : |value lo| ≤ 2 := by
    have h1 : (1 + 5 / 2 ^ 53) *
        (|value lo1| + |value lo2| + |value lo3| + |value lo4| + |value p|) ≤
        (1 + 5 / 2 ^ 53) * 1 := mul_le_mul_of_nonneg_left hS (by positivity)
    linarith
  obtain ⟨hyf, htlf, hyte, htlb⟩ := PowLogSums.ytail hi lo hhif hlof (by
    have h1 : (1 + 1 / 2 ^ 53) * |value t2 + value arhi2| ≤ (1 + 1 / 2 ^ 53) * 901 := by
      have := abs_add_le (value t2) (value arhi2)
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith)
  -- the decomposition of `hi + lo - M`
  have hid : value hi + value lo - M =
      (value lo - (value lo1 + value lo2 + value lo3 + value lo4 + value p)) +
      (value lo1 - ((K : ℝ) * value 0x3D2EF35793C76730 + value lt)) +
      (value lo3 - Rl * (value ar + value arhi)) + (value p - PowLogTable.poly R) := by
    simp only [M]
    rw [hlo2v, hlo4v, ha2val, hAA, ht1v]
    rw [hrv]
    simp only [R]
    ring
  have hfin : |value hi + value lo - M| ≤
      1 / 2 ^ 53 * (5 * |value lo1| + 5 * |value lo2| + 4 * |value lo3| + 3 * |value lo4| +
        |value p|) +
      (3 / 2 ^ 53 * (|(K : ℝ)| / 2 ^ 44 + |value lt|) + 2 * |(K : ℝ)| * μ) +
      (3 / 2 ^ 53 * (|Rl| * |R + Rh| / 2) + μ) +
      (7 / 4 / 2 ^ 53 * |R| ^ 3 + 5 * μ) := by
    rw [hid]
    have h1 := abs_add_le (value lo - (value lo1 + value lo2 + value lo3 + value lo4 + value p) +
      (value lo1 - ((K : ℝ) * value 0x3D2EF35793C76730 + value lt)) +
      (value lo3 - Rl * (value ar + value arhi))) (value p - PowLogTable.poly R)
    have h2 := abs_add_le (value lo - (value lo1 + value lo2 + value lo3 + value lo4 + value p) +
      (value lo1 - ((K : ℝ) * value 0x3D2EF35793C76730 + value lt)))
      (value lo3 - Rl * (value ar + value arhi))
    have h3 := abs_add_le (value lo - (value lo1 + value lo2 + value lo3 + value lo4 + value p))
      (value lo1 - ((K : ℝ) * value 0x3D2EF35793C76730 + value lt))
    linarith
  have hT : value t1 + value r = T + R := by rw [ht1v, hrv]
  rw [hT] at hb2 hb4 hta
  have hhi2 : |value hi| ≤ (1 + 1 / 2 ^ 53) * ((1 + 1 / 2 ^ 53) * |T + R| + Rh ^ 2 / 2) :=
    hhib.trans (mul_le_mul_of_nonneg_left hta (by positivity))
  have hc := combine (value (Wasm.IEEE64.add hi lo))
    (value (Wasm.IEEE64.add (Wasm.IEEE64.sub hi (Wasm.IEEE64.add hi lo)) lo)) (value hi) (value lo)
    M (value lo1) (value lo2) (value lo3) (value lo4) (value p) |(K : ℝ)| |value lt|
    (|Rl| * |R + Rh|) (|R| ^ 3) |T + R| (Rh ^ 2) μ hK0 hlt0 hQ0 hR3 (abs_nonneg _) hH hμ0 hKμ
    hb1 hb2 hb3 hb4 hpb hlob hhi2 hfin hyte htlb
  exact ⟨hyf, htlf, hc.1, hc.2⟩

#print axioms logWords_eq
#print axioms int_bound
#print axioms combine
#print axioms grid_value
#print axioms after_error

end Library.Numerics.Float64.Pow.PowLogError
