import Library.Numerics.Reductions.SumError
import LeanExe.ProofKit.F64ErrorTrack
import LeanExe.ProofKit.F64Sterbenz
import LeanExe.ProofKit.F64Convert
import LeanExe.Dialect.Loop

/-!
Binary64 sums.  `f64` is the `SumError.Adder` of Lean's `Float`, with the unit roundoff `2 ^ -53`
of round-to-nearest-even, from `F64AddBounds.add_real_relative`; `0.0 + t` is exact for a finite
`t` up to `2 ^ 1022` in magnitude.  `sum_bound` states the error of a left-to-right sum of `n`
finite floats in closed form, `γ_(n-1) Σ |x_i|` with `γ_k = k / (2 ^ 53 - k)`, and `dot_bound`
that of a left-to-right sum of `n` rounded products, `γ_n Σ |x_i y_i| + n / 2 ^ 1074`, where the
second term covers the products that fall below the normal range.  `loop_eq_foldl` reads
`LeanExe.loop` as a fold over `List.range`, and `loop_toNat` does so for a step that reads its index
as a natural number.
-/

namespace Library.Numerics.Reductions.Binary64

open CodeLib.IEEE64 LeanExe.ProofKit LeanExe.ProofKit.F64Approx SumError

set_option exponentiation.threshold 4096

theorem loop_eq_foldl {α : Type} (n : UInt64) (init : α) (f : UInt64 → α → α) :
    LeanExe.loop n init f =
      (List.range n.toNat).foldl (fun acc i => f (UInt64.ofNat i) acc) init := by
  unfold LeanExe.loop
  generalize n.toNat = m
  induction m with
  | zero => rfl
  | succ k ih => rw [Nat.fold_succ, List.range_succ, List.foldl_append, ih]; rfl

/-- `loop_eq_foldl` for a step that reads its index as a natural number. -/
theorem loop_toNat {α : Type} (n : UInt64) (init : α) (g : ℕ → α → α) :
    LeanExe.loop n init (fun i acc => g i.toNat acc) =
      (List.range n.toNat).foldl (fun acc i => g i acc) init := by
  rw [loop_eq_foldl]
  refine List.foldl_ext _ _ _ fun acc i hi => ?_
  rw [UInt64.toNat_ofNat_of_lt' (lt_trans (List.mem_range.mp hi) n.toNat_lt)]

/-- The elements of an array, read with `xs[i]!` over its indices. -/
theorem range_map_get {α : Type} [Inhabited α] (xs : Array α) :
    (List.range xs.size).map (fun i => xs[i]!) = xs.toList := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
  exact getElem!_pos xs i (by simpa using h1)

theorem zero_bits : (0.0 : Float).toBits = 0 := rfl

theorem finite_zero : CodeLib.IEEE64.Finite (0 : UInt64) := by unfold CodeLib.IEEE64.Finite; decide

theorem scaledValue_zero : Wasm.IEEE64.scaledValue 0 = 0 := by decide

theorem value_zero : value 0 = 0 := by simp [value, scaledValue_zero]

/-- Every element of an array of finite floats, read with `xs[i]!`, is finite: a missing element
is `0.0`. -/
theorem finite_get (xs : Array Float) (hf : ∀ x ∈ xs, Finite x.toBits) (i : ℕ) :
    Finite xs[i]!.toBits := by
  by_cases hi : i < xs.size
  · rw [getElem!_pos xs i hi]; exact hf _ (Array.getElem_mem hi)
  · rw [getElem!_neg xs i hi]
    show Finite (0.0 : Float).toBits
    rw [zero_bits]; exact finite_zero

/-- Adding a finite float of magnitude at most `2 ^ 1022` to `0.0` is exact. -/
theorem zero_add_exact (t : Float) (ht : Finite t.toBits) (hm : |value t.toBits| ≤ 2 ^ 1022) :
    Finite (0.0 + t).toBits ∧ value (0.0 + t).toBits = value t.toBits := by
  rw [F64Bits.toBits_add, zero_bits]
  have hb : |Wasm.IEEE64.scaledValue 0 + Wasm.IEEE64.scaledValue t.toBits| ≤
      2 ^ 53 * 2 ^ (min (Wasm.IEEE64.exponent t.toBits - 1) 2043) := by
    rw [scaledValue_zero, zero_add, Int.abs_eq_natAbs, natAbs_scaledValue]
    by_cases he : Wasm.IEEE64.exponent t.toBits - 1 ≤ 2043
    · rw [min_eq_left he]
      exact_mod_cast (F64Sterbenz.magnitude_lt t.toBits).le
    · rw [min_eq_right (by omega)]
      have hv := F64Sterbenz.value_abs_scaled t.toBits
      have hr : (Wasm.IEEE64.scaledMagnitude t.toBits : ℝ) ≤ 2 ^ 53 * 2 ^ 2043 := by
        rw [← hv]
        calc |value t.toBits| * 2 ^ 1074 ≤ 2 ^ 1022 * 2 ^ 1074 :=
              mul_le_mul_of_nonneg_right hm (by positivity)
          _ = 2 ^ 53 * 2 ^ 2043 := by norm_num
      exact_mod_cast hr
  have h := F64ErrorTrack.add_exact_grid 0 t.toBits finite_zero ht _ (min_le_right _ _)
    (by rw [scaledValue_zero]; exact dvd_zero _)
    (F64Sterbenz.scaled_dvd _ _ (min_le_left _ _)) hb
  rw [value_zero, zero_add] at h
  exact h

/-- Lean's `Float` as an `Adder`: unit roundoff `2 ^ -53`, exact sums below `2 ^ 1023`. -/
noncomputable def f64 : Adder Float where
  val x := value x.toBits
  fin x := Finite x.toBits
  add a b := a + b
  zero := 0.0
  u := 1 / 2 ^ 53
  bound0 := 2 ^ 1022
  bound := 2 ^ 1023
  u_nonneg := by positivity
  zero_fin := by rw [zero_bits]; exact finite_zero
  zero_val := by rw [zero_bits]; exact value_zero
  zero_add := zero_add_exact
  add_rel a b ha hb h := by
    rw [F64Bits.toBits_add]
    have := F64AddBounds.add_real_relative a.toBits b.toBits ha hb h
    simpa [unitRoundoff64] using this

theorem f64_u : f64.u = 1 / 2 ^ 53 := rfl

theorem f64_approx (x : Float) (v e : ℝ) : f64.Approx x v e ↔ FApprox x v e := Iff.rfl

/-- A rounded product of finite floats below `2 ^ 1022` in magnitude lies within
`2 ^ -53 |a b| + 2 ^ -1075` of the exact product. -/
theorem mul_approx (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (h : |value a.toBits * value b.toBits| < 2 ^ 1022) :
    f64.Approx (a * b) (f64.val a * f64.val b) (f64.u * |f64.val a * f64.val b| + 1 / 2 ^ 1075) := by
  show Finite (a * b).toBits ∧ |value (a * b).toBits - value a.toBits * value b.toBits| ≤
    1 / 2 ^ 53 * |value a.toBits * value b.toBits| + 1 / 2 ^ 1075
  rw [F64Bits.toBits_mul]
  have := F64MulBounds.mul_real_mixed a.toBits b.toBits ha hb h
  simpa [unitRoundoff64, multiplicationUnderflowEpsilon, f64] using this

theorem le_sum_of_mem {α : Type} (l : List α) (f : α → ℝ) (h : ∀ a ∈ l, 0 ≤ f a) (a : α)
    (ha : a ∈ l) : f a ≤ (l.map f).sum :=
  List.single_le_sum (fun x hx => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact h b hb) _ (List.mem_map_of_mem ha)

/-- A left-to-right sum of `n < 2 ^ 52` finite floats, whose magnitudes sum to at most
`2 ^ 1022`, is finite and within `((1 + 2 ^ -53) ^ (n - 1) - 1) Σ |x_i|` of the exact sum. -/
theorem sum_raw {α : Type} (l : List α) (t : α → Float) (hf : ∀ a ∈ l, Finite (t a).toBits)
    (hn : l.length < 2 ^ 52)
    (hS : (l.map fun a => |value (t a).toBits|).sum ≤ 2 ^ 1022) :
    FApprox (l.foldl (fun acc a => acc + t a) 0.0) (l.map fun a => value (t a).toBits).sum
      (((1 + 1 / 2 ^ 53 : ℝ) ^ (l.length - 1) - 1) *
        (l.map fun a => |value (t a).toBits|).sum) := by
  set V := (l.map fun a => |value (t a).toBits|).sum
  have hmap : (l.map fun a => |f64.val (t a)| + 0) = l.map fun a => |value (t a).toBits| := by
    simp [f64]
  have hk : 2 * (((l.length - 1 : ℕ)) : ℝ) < 2 ^ 53 := by
    have : ((l.length - 1 : ℕ) : ℝ) < 2 ^ 52 := by exact_mod_cast (Nat.sub_le _ _).trans_lt hn
    linarith
  have h2 := pow_le_two 53 (l.length - 1) hk
  have h := sum_approx f64 l t (fun a => f64.val (t a)) (fun _ => 0)
    (fun a ha => ⟨hf a ha, by simp⟩) (by rw [hmap]; exact hS) (by
      rw [hmap, f64_u]
      show _ < (2 : ℝ) ^ 1023
      have hp : 0 ≤ (1 + 1 / 2 ^ 53 : ℝ) ^ (l.length - 1) := by positivity
      calc (1 + 1 / 2 ^ 53 : ℝ) ^ (l.length - 1) * V ≤
            (1 + 1 / 2 ^ 53 : ℝ) ^ (l.length - 1) * 2 ^ 1022 := mul_le_mul_of_nonneg_left hS hp
        _ < 2 * 2 ^ 1022 := by gcongr
        _ = 2 ^ 1023 := by norm_num)
  rw [hmap, f64_u] at h
  refine h.mono (le_of_eq ?_)
  simp only [f64]; ring

/-- A left-to-right sum of `n < 2 ^ 52` finite floats, whose magnitudes sum to at most
`2 ^ 1022`, is finite and within `γ_(n-1) Σ |x_i|` of the exact sum. -/
theorem sum_bound {α : Type} (l : List α) (t : α → Float) (hf : ∀ a ∈ l, Finite (t a).toBits)
    (hn : l.length < 2 ^ 52)
    (hS : (l.map fun a => |value (t a).toBits|).sum ≤ 2 ^ 1022) :
    Finite (l.foldl (fun acc a => acc + t a) 0.0).toBits ∧
      |value (l.foldl (fun acc a => acc + t a) 0.0).toBits -
          (l.map fun a => value (t a).toBits).sum| ≤
        ((l.length - 1 : ℕ) : ℝ) / (2 ^ 53 - (l.length - 1 : ℕ)) *
          (l.map fun a => |value (t a).toBits|).sum := by
  have hV : 0 ≤ (l.map fun a => |value (t a).toBits|).sum :=
    sum_nonneg_of l _ fun _ _ => abs_nonneg _
  have hk : ((l.length - 1 : ℕ) : ℝ) < 2 ^ 53 := by
    have : ((l.length - 1 : ℕ) : ℝ) < 2 ^ 52 := by exact_mod_cast (Nat.sub_le _ _).trans_lt hn
    linarith
  have h := sum_raw l t hf hn hS
  exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right (gamma_pow 53 _ hk) hV)⟩

/-- A left-to-right sum of `n < 2 ^ 52` rounded products of finite floats, whose exact products'
magnitudes sum to at most `2 ^ 1021`, is finite and within `γ_n Σ |x_i y_i| + n / 2 ^ 1074` of the
exact sum of products. -/
theorem dot_bound {α : Type} (l : List α) (x y : α → Float) (hx : ∀ a ∈ l, Finite (x a).toBits)
    (hy : ∀ a ∈ l, Finite (y a).toBits) (hn : l.length < 2 ^ 52)
    (hP : (l.map fun a => |value (x a).toBits * value (y a).toBits|).sum ≤ 2 ^ 1021) :
    Finite (l.foldl (fun acc a => acc + x a * y a) 0.0).toBits ∧
      |value (l.foldl (fun acc a => acc + x a * y a) 0.0).toBits -
          (l.map fun a => value (x a).toBits * value (y a).toBits).sum| ≤
        (l.length : ℝ) / (2 ^ 53 - l.length) *
          (l.map fun a => |value (x a).toBits * value (y a).toBits|).sum + l.length / 2 ^ 1074 := by
  set P := (l.map fun a => |value (x a).toBits * value (y a).toBits|).sum
  have hP0 : 0 ≤ P := sum_nonneg_of l _ fun _ _ => abs_nonneg _
  have hnr : (l.length : ℝ) ≤ 2 ^ 52 := by exact_mod_cast hn.le
  have hk : 2 * (((l.length - 1 : ℕ)) : ℝ) < 2 ^ 53 := by
    have : ((l.length - 1 : ℕ) : ℝ) < 2 ^ 52 := by exact_mod_cast (Nat.sub_le _ _).trans_lt hn
    linarith
  have h2 := pow_le_two 53 (l.length - 1) hk
  have hg := gamma_pow 53 l.length (by linarith)
  have hmul : ∀ a ∈ l, f64.Approx (x a * y a) (f64.val (x a) * f64.val (y a))
      (f64.u * |f64.val (x a) * f64.val (y a)| + 1 / 2 ^ 1075) := fun a ha =>
    mul_approx _ _ (hx a ha) (hy a ha) (by
      have := le_sum_of_mem l (fun a => |value (x a).toBits * value (y a).toBits|)
        (fun _ _ => abs_nonneg _) a ha
      have : (2 : ℝ) ^ 1021 < 2 ^ 1022 := by norm_num
      linarith)
  have hinner : (1 + 1 / 2 ^ 53 : ℝ) * P + l.length * (1 / 2 ^ 1075) ≤ 2 ^ 1022 := by
    have h1 : (1 + 1 / 2 ^ 53 : ℝ) * P ≤ (1 + 1 / 2 ^ 53) * 2 ^ 1021 :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    have h3 : (l.length : ℝ) * (1 / 2 ^ 1075) ≤ 2 ^ 52 * (1 / 2 ^ 1075) :=
      mul_le_mul_of_nonneg_right hnr (by positivity)
    have h4 : (1 + 1 / 2 ^ 53 : ℝ) * 2 ^ 1021 + 2 ^ 52 * (1 / 2 ^ 1075) ≤ 2 ^ 1022 := by norm_num
    linarith
  have h := dot_approx f64 l x y (· * ·) (1 / 2 ^ 1075) hmul
    (by rw [f64_u]; exact hinner) (by
      rw [f64_u]
      show _ < (2 : ℝ) ^ 1023
      have hp : 0 ≤ (1 + 1 / 2 ^ 53 : ℝ) ^ (l.length - 1) := by positivity
      have hq : 0 ≤ (1 + 1 / 2 ^ 53 : ℝ) * P + l.length * (1 / 2 ^ 1075) := by positivity
      calc (1 + 1 / 2 ^ 53 : ℝ) ^ (l.length - 1) * ((1 + 1 / 2 ^ 53) * P +
              l.length * (1 / 2 ^ 1075)) ≤
            (1 + 1 / 2 ^ 53 : ℝ) ^ (l.length - 1) * 2 ^ 1022 :=
          mul_le_mul_of_nonneg_left hinner hp
        _ < 2 * 2 ^ 1022 := by gcongr
        _ = 2 ^ 1023 := by norm_num)
  rw [f64_u] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hn0 : 0 ≤ (l.length : ℝ) * (1 / 2 ^ 1075) := by positivity
  have e1 : ((1 + 1 / 2 ^ 53 : ℝ) ^ l.length - 1) * P ≤ l.length / (2 ^ 53 - l.length) * P :=
    mul_le_mul_of_nonneg_right hg hP0
  have e2 : (1 + 1 / 2 ^ 53 : ℝ) ^ (l.length - 1) * (l.length * (1 / 2 ^ 1075)) ≤
      2 * (l.length * (1 / 2 ^ 1075)) := mul_le_mul_of_nonneg_right h2.le hn0
  have e3 : 2 * ((l.length : ℝ) * (1 / 2 ^ 1075)) = l.length / 2 ^ 1074 := by
    ring
  simp only [f64] at e1 e2 ⊢
  linarith

/-- A loop that sums the products of two arrays' elements at computed indices, as a fold over
`List.range`, when the indices read as the natural numbers `fI c` and `fJ c`. -/
theorem loop_dot (K : UInt64) (I J : UInt64 → UInt64) (p q : Array Float) (fI fJ : ℕ → ℕ)
    (h : ∀ c < K.toNat, (I (UInt64.ofNat c)).toNat = fI c ∧ (J (UInt64.ofNat c)).toNat = fJ c) :
    LeanExe.loop K 0.0 (fun c acc => acc + p[(I c).toNat]! * q[(J c).toNat]!) =
      (List.range K.toNat).foldl (fun acc c => acc + p[fI c]! * q[fJ c]!) 0.0 := by
  rw [loop_eq_foldl]
  refine List.foldl_ext _ _ _ fun acc c hc => ?_
  obtain ⟨h1, h2⟩ := h c (List.mem_range.mp hc)
  rw [h1, h2]

/-- A sum over `List.range n` as a sum over `Finset.range n`. -/
theorem range_sum (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

/-- `dot_bound` over the indices `0, …, K - 1`, with sums over `Finset.range K`. -/
theorem range_dot (K : ℕ) (x y : ℕ → Float) (hx : ∀ c, Finite (x c).toBits)
    (hy : ∀ c, Finite (y c).toBits) (hK : K < 2 ^ 52)
    (hP : ∑ c ∈ Finset.range K, |value (x c).toBits * value (y c).toBits| ≤ 2 ^ 1021) :
    Finite ((List.range K).foldl (fun acc c => acc + x c * y c) 0.0).toBits ∧
      |value ((List.range K).foldl (fun acc c => acc + x c * y c) 0.0).toBits -
          ∑ c ∈ Finset.range K, value (x c).toBits * value (y c).toBits| ≤
        (K : ℝ) / (2 ^ 53 - K) * ∑ c ∈ Finset.range K, |value (x c).toBits * value (y c).toBits| +
          K / 2 ^ 1074 := by
  have h := dot_bound (List.range K) x y (fun c _ => hx c) (fun c _ => hy c)
    (by rw [List.length_range]; exact hK) (by rw [range_sum]; exact hP)
  rw [range_sum, range_sum, List.length_range] at h
  exact h

/-- `toFloat` of a word up to `2 ^ 53` is exact. -/
theorem toFloat_exact (n : UInt64) (hn : n.toNat ≤ 2 ^ 53) :
    FApprox n.toFloat (n.toNat : ℝ) 0 := by
  have h : Finite n.toFloat.toBits ∧
      Wasm.IEEE64.scaledValue n.toFloat.toBits = n.toNat * 2 ^ 1074 := by
    rw [F64Convert.toBits_toFloat]
    unfold Wasm.IEEE64.convertI64U Wasm.IEEE64.fromInt
    exact F64GridExact.signed_grid_packing_exact (n.toNat : ℤ) 1074 (by simpa using hn)
      (by norm_num)
  refine ⟨h.1, ?_⟩
  have hv : value n.toFloat.toBits = n.toNat := by
    rw [value, h.2, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]
    field_simp
  rw [hv, sub_self, abs_zero]

/-- `γ_2 = 2 / (2 ^ 53 - 2)` bounds `2 u + u ^ 2` for `u = 2 ^ -53`. -/
theorem gamma_two : (2 : ℝ) / 2 ^ 53 + 1 / 2 ^ 106 ≤ 2 / (2 ^ 53 - 2) := by
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
    (by norm_num)]
  norm_num

/-- A rounded product followed by a rounded sum with a third float, in either order, lies within
`γ_2 (|p q| + |c|) + 2 ^ -1074` of `p q + c` for finite floats with `|p q| + |c| ≤ 2 ^ 1021`. -/
theorem mul_add_bound (p q c : Float) (hp : Finite p.toBits) (hq : Finite q.toBits)
    (hc : Finite c.toBits)
    (hm : |value p.toBits * value q.toBits| + |value c.toBits| ≤ 2 ^ 1021) :
    FApprox (p * q + c) (value p.toBits * value q.toBits + value c.toBits)
        (2 / (2 ^ 53 - 2) * (|value p.toBits * value q.toBits| + |value c.toBits|) +
          1 / 2 ^ 1074) ∧
      FApprox (c + p * q) (value c.toBits + value p.toBits * value q.toBits)
        (2 / (2 ^ 53 - 2) * (|value p.toBits * value q.toBits| + |value c.toBits|) +
          1 / 2 ^ 1074) := by
  set P := |value p.toBits * value q.toBits|
  set C := |value c.toBits|
  have hP : 0 ≤ P := abs_nonneg _
  have hC : 0 ≤ C := abs_nonneg _
  have hpq : P < 2 ^ 1022 := by
    have : (2 : ℝ) ^ 1021 < 2 ^ 1022 := by norm_num
    linarith
  have hmul := mul_approx p q hp hq hpq
  rw [f64_u] at hmul
  have hmul' : FApprox (p * q) (value p.toBits * value q.toBits) (P / 2 ^ 53 + 1 / 2 ^ 1075) :=
    hmul.mono (le_of_eq (by simp only [f64, P]; ring))
  have hcc : FApprox c (value c.toBits) 0 := approx_self _ hc
  have hsum : |value p.toBits * value q.toBits + value c.toBits| ≤ P + C := abs_add_le _ _
  have hsum' : |value c.toBits + value p.toBits * value q.toBits| ≤ P + C := by
    rw [add_comm]; exact hsum
  have hB : P + C + (P / 2 ^ 53 + 1 / 2 ^ 1075) < 2 ^ 1023 := by
    have : P / 2 ^ 53 ≤ 2 ^ 1021 / 2 ^ 53 := div_le_div_of_nonneg_right (by linarith)
      (by positivity)
    have : (2 : ℝ) ^ 1021 + 2 ^ 1021 / 2 ^ 53 + 1 / 2 ^ 1075 < 2 ^ 1023 := by norm_num
    linarith
  have e : P / 2 ^ 53 + 1 / 2 ^ 1075 + 0 + (P + C + (P / 2 ^ 53 + 1 / 2 ^ 1075)) / 2 ^ 53 ≤
      2 / (2 ^ 53 - 2) * (P + C) + 1 / 2 ^ 1074 := by
    have hg := mul_le_mul_of_nonneg_right gamma_two (add_nonneg hP hC)
    have e1 : P / 2 ^ 53 + 1 / 2 ^ 1075 + 0 + (P + C + (P / 2 ^ 53 + 1 / 2 ^ 1075)) / 2 ^ 53 =
        (2 / 2 ^ 53 + 1 / 2 ^ 106) * P + C / 2 ^ 53 + (1 / 2 ^ 1075 + 1 / 2 ^ 1128) := by ring
    have e2 : (2 / 2 ^ 53 + 1 / 2 ^ 106 : ℝ) * (P + C) =
        (2 / 2 ^ 53 + 1 / 2 ^ 106) * P + C / 2 ^ 53 + C * (1 / 2 ^ 53 + 1 / 2 ^ 106) := by ring
    have e3 : 0 ≤ C * (1 / 2 ^ 53 + 1 / 2 ^ 106 : ℝ) := by positivity
    have e4 : (1 / 2 ^ 1075 + 1 / 2 ^ 1128 : ℝ) ≤ 1 / 2 ^ 1074 := by norm_num
    linarith
  refine ⟨(fapprox_add hmul' hcc (P + C + (P / 2 ^ 53 + 1 / 2 ^ 1075)) (by linarith) hB).mono e,
    ?_⟩
  exact (fapprox_add hcc hmul' (P + C + (P / 2 ^ 53 + 1 / 2 ^ 1075)) (by linarith) hB).mono
    (by linarith)

end Library.Numerics.Reductions.Binary64
