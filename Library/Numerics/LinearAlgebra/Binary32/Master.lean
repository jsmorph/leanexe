import Library.Numerics.LinearAlgebra.Binary32.Compiled
import Library.Numerics.Reductions.Binary32
import Library.Numerics.Reductions.Binary64
import LeanExe.Dialect.ArrayLemmas
import LeanExe.Dialect.Lemmas
import Verified.Master

/-!
The master theorems of the binary32 linear algebra.  Each element of `scale32` is one rounded
product and each element of `add32` one rounded sum, whose errors `Binary32.mul_mixed` and
`Binary32.add_relative` give; each element of `axpyArray32` is a rounded product and a rounded
sum (`Binary32.mul_add_bound`); each entry of `matVec32` is a left-to-right sum of rounded
products (`Binary32.dot_bound`), and each entry of `linear32` such a sum plus the bias.
-/

namespace Library.Numerics.LinearAlgebra.Binary32

open CodeLib.IEEE32 (value Finite)
open LeanExe.ProofKit LeanExe.Dialect
open Library.Numerics.Reductions.Binary32 Library.Numerics.Reductions.SumError
open Library.Numerics.Reductions.Binary64 (loop_eq_foldl)

set_option exponentiation.threshold 4096

theorem scale32_export :
    ({ name := "scale32", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem axpyArray32_export :
    ({ name := "axpyArray32", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem matVec32_export :
    ({ name := "matVec32", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem add32_export :
    ({ name := "add32", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem linear32_export :
    ({ name := "linear32", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem size_lt {xs : Array Float32}
    (h : (xs.map fun x : Float32 => x.toBits.toUInt64).size < 536870912) :
    xs.size < 536870912 := by
  simpa using h

theorem ofNat_toNat (c : ℕ) (h : c < 2 ^ 64) : (UInt64.ofNat c).toNat = c :=
  UInt64.toNat_ofNat_of_lt' h

theorem lt64 (n : UInt64) : n.toNat < 2 ^ 64 := n.toNat_lt

theorem idx_lt {i n j m : ℕ} (hi : i < n) (hj : j < m) : i * m + j < n * m :=
  calc i * m + j < i * m + m := by omega
    _ = (i + 1) * m := by ring
    _ ≤ n * m := Nat.mul_le_mul_right _ hi

theorem mod64 {a b : ℕ} (h : a + b < 2 ^ 64) : (a % 2 ^ 64 + b) % 2 ^ 64 = a + b := by
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.le_add_right _ _) h), Nat.mod_eq_of_lt h]

/-- `Binary64.loop_dot` for `Float32`. -/
theorem loop_dot (K : UInt64) (I J : UInt64 → UInt64) (p q : Array Float32) (fI fJ : ℕ → ℕ)
    (h : ∀ c < K.toNat, (I (UInt64.ofNat c)).toNat = fI c ∧ (J (UInt64.ofNat c)).toNat = fJ c) :
    LeanExe.loop K 0.0 (fun c acc => acc + p[(I c).toNat]! * q[(J c).toNat]!) =
      (List.range K.toNat).foldl (fun acc c => acc + p[fI c]! * q[fJ c]!) 0.0 := by
  rw [loop_eq_foldl]
  refine List.foldl_ext _ _ _ fun acc c hc => ?_
  obtain ⟨h1, h2⟩ := h c (List.mem_range.mp hc)
  rw [h1, h2]

/-- An element of a build over the size of an array. -/
theorem build_elem {α : Type} [Inhabited α] (xs : Array Float32) (f : UInt64 → α)
    (hs : xs.size < 2 ^ 64) :
    (LeanExe.build xs.size.toUInt64 f).size = xs.size ∧
      ∀ i < xs.size, (LeanExe.build xs.size.toUInt64 f)[i]! = f (UInt64.ofNat i) := by
  have hsz := size_toUInt64 xs hs
  refine ⟨by rw [build_size, hsz], fun i hi => ?_⟩
  have hlt : i < xs.size.toUInt64.toNat := by rw [hsz]; exact hi
  exact build_get hlt

/-! ### `scale32` -/

/-- The export `scale32`, called on a finite float `a` and an array `x` of finite binary32 floats
with `|a x_i| < 2 ^ 126`, returns an array of the size of `x` whose element `i` is finite and
within `2 ^ -24 |a x_i| + 2 ^ -150` of `a x_i`. -/
theorem scale32_master :
    Verified.Master compiled.module compiled.tables "scale32" compiled.scale32.bound
      (fun x : Float32 × Array Float32 => Finite x.1.toBits ∧ (∀ v ∈ x.2, Finite v.toBits) ∧
        ∀ i < x.2.size, |value x.1.toBits * value x.2[i]!.toBits| < 2 ^ 126)
      (fun x (y : Array Float32) => y.size = x.2.size ∧ ∀ i < x.2.size, Finite y[i]!.toBits ∧
        |value y[i]!.toBits - value x.1.toBits * value x.2[i]!.toBits| ≤
          |value x.1.toBits * value x.2[i]!.toBits| / 2 ^ 24 + 1 / 2 ^ 150) :=
  .of_trapFree (.ofA compiled.scale32.trapFree) nofun scale32_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, _, ⟨_, _, hxs⟩⟩ hD => by
      obtain ⟨ha, hf, hm⟩ := hD
      have hs := size_lt hxs.values.size_lt_memory32
      obtain ⟨hsz, hg⟩ := build_elem x.2 (fun i => x.1 * x.2[i.toNat]!) (by omega)
      refine ⟨hsz, fun i hi => ?_⟩
      rw [scale32, hg i hi, ofNat_toNat i (by omega), F32Bits.toBits_mul]
      exact mul_mixed _ _ ha (finite_get _ hf i) (hm i hi)

#print axioms scale32_master

/-! ### `axpyArray32` -/

/-- The export `axpyArray32`, called on a finite float `a` and arrays `x` and `y` of finite
binary32 floats with `|a x_i| + |y_i| ≤ 2 ^ 125`, returns an array of the size of `x` whose
element `i` is finite and within `γ_2 (|a x_i| + |y_i|) + 2 ^ -149` of `a x_i + y_i`, each missing
`y_i` counting as 0, where `γ_2 = 2 / (2 ^ 24 - 2)`. -/
theorem axpyArray32_master :
    Verified.Master compiled.module compiled.tables "axpyArray32" compiled.axpyArray32.bound
      (fun x : Float32 × Array Float32 × Array Float32 => Finite x.1.toBits ∧
        (∀ v ∈ x.2.1, Finite v.toBits) ∧ (∀ v ∈ x.2.2, Finite v.toBits) ∧
        ∀ i < x.2.1.size,
          |value x.1.toBits * value x.2.1[i]!.toBits| + |value x.2.2[i]!.toBits| ≤ 2 ^ 125)
      (fun x (y : Array Float32) => y.size = x.2.1.size ∧ ∀ i < x.2.1.size,
        Finite y[i]!.toBits ∧
        |value y[i]!.toBits -
            (value x.1.toBits * value x.2.1[i]!.toBits + value x.2.2[i]!.toBits)| ≤
          2 / (2 ^ 24 - 2) *
            (|value x.1.toBits * value x.2.1[i]!.toBits| + |value x.2.2[i]!.toBits|) +
            1 / 2 ^ 149) :=
  .of_trapFree (.ofA compiled.axpyArray32.trapFree) nofun axpyArray32_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, _, _, _, _, ⟨_, _, hxs⟩, _⟩ hD => by
      obtain ⟨ha, hfx, hfy, hm⟩ := hD
      have hs := size_lt hxs.values.size_lt_memory32
      obtain ⟨hsz, hg⟩ := build_elem x.2.1
        (fun i => x.1 * x.2.1[i.toNat]! + x.2.2[i.toNat]!) (by omega)
      refine ⟨hsz, fun i hi => ?_⟩
      rw [axpyArray32, hg i hi, ofNat_toNat i (by omega)]
      exact mul_add_bound _ _ _ ha (finite_get _ hfx i) (finite_get _ hfy i) (hm i hi)

#print axioms axpyArray32_master

/-! ### `add32` -/

/-- The export `add32`, called on arrays `a` and `b` of finite binary32 floats with
`|a_i + b_i| < 2 ^ 127`, returns an array of the size of `a` whose element `i` is finite and
within `2 ^ -24 |a_i + b_i|` of `a_i + b_i`, each missing `b_i` counting as 0. -/
theorem add32_master :
    Verified.Master compiled.module compiled.tables "add32" compiled.add32.bound
      (fun x : Array Float32 × Array Float32 => (∀ v ∈ x.1, Finite v.toBits) ∧
        (∀ v ∈ x.2, Finite v.toBits) ∧
        ∀ i < x.1.size, |value x.1[i]!.toBits + value x.2[i]!.toBits| < 2 ^ 127)
      (fun x (y : Array Float32) => y.size = x.1.size ∧ ∀ i < x.1.size, Finite y[i]!.toBits ∧
        |value y[i]!.toBits - (value x.1[i]!.toBits + value x.2[i]!.toBits)| ≤
          |value x.1[i]!.toBits + value x.2[i]!.toBits| / 2 ^ 24) :=
  .of_trapFree (.ofA compiled.add32.trapFree) nofun add32_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, ha⟩, _⟩ hD => by
      obtain ⟨hfa, hfb, hm⟩ := hD
      have hs := size_lt ha.values.size_lt_memory32
      obtain ⟨hsz, hg⟩ := build_elem x.1 (fun i => x.1[i.toNat]! + x.2[i.toNat]!) (by omega)
      refine ⟨hsz, fun i hi => ?_⟩
      rw [add32, hg i hi, ofNat_toNat i (by omega), F32Bits.toBits_add]
      exact add_relative _ _ (finite_get _ hfa i) (finite_get _ hfb i) (hm i hi)

#print axioms add32_master

/-! ### `matVec32` -/

theorem matVec32_get (m v : Array Float32) (rows cols : UInt64)
    (hrc : rows.toNat * cols.toNat < 2 ^ 64) :
    (matVec32 m v rows cols).size = rows.toNat ∧ ∀ r < rows.toNat,
      (matVec32 m v rows cols)[r]! = (List.range cols.toNat).foldl
        (fun acc c => acc + m[r * cols.toNat + c]! * v[c]!) 0.0 := by
  refine ⟨build_size _ _, fun r hr => ?_⟩
  rw [matVec32, build_get hr]
  apply loop_dot
  intro c hc
  have hr64 : r < 2 ^ 64 := lt_trans hr (lt64 _)
  have hc64 : c < 2 ^ 64 := lt_trans hc (lt64 _)
  have hle : r * cols.toNat + c < 2 ^ 64 := lt_trans (idx_lt hr hc) hrc
  refine ⟨?_, ofNat_toNat c hc64⟩
  rw [UInt64.toNat_add, UInt64.toNat_mul, ofNat_toNat r hr64, ofNat_toNat c hc64]
  exact mod64 hle

/-- The export `matVec32`, called on an array `m` of finite binary32 floats holding a
`rows × cols` matrix by rows (`rows · cols ≤ m.size`), an array `v` of finite binary32 floats,
and the counts with `cols < 2 ^ 22`, returns `rows` finite floats, the float `r` within
`γ_cols Σ_c |m_rc v_c| + cols / 2 ^ 149` of the exact `Σ_c m_rc v_c`, each missing `v_c` counting
as 0, when each row's `Σ_c |m_rc v_c|` is at most `2 ^ 125`; here `γ_k = k / (2 ^ 24 - k)`. -/
theorem matVec32_master :
    Verified.Master compiled.module compiled.tables "matVec32" compiled.matVec32.bound
      (fun x : Array Float32 × Array Float32 × UInt64 × UInt64 =>
        (∀ v ∈ x.1, Finite v.toBits) ∧ (∀ v ∈ x.2.1, Finite v.toBits) ∧
        x.2.2.1.toNat * x.2.2.2.toNat ≤ x.1.size ∧ x.2.2.2.toNat < 2 ^ 22 ∧
        ∀ r < x.2.2.1.toNat, ∑ c ∈ Finset.range x.2.2.2.toNat,
          |value x.1[r * x.2.2.2.toNat + c]!.toBits * value x.2.1[c]!.toBits| ≤ 2 ^ 125)
      (fun x (y : Array Float32) => y.size = x.2.2.1.toNat ∧ ∀ r < x.2.2.1.toNat,
        Finite y[r]!.toBits ∧
        |value y[r]!.toBits - ∑ c ∈ Finset.range x.2.2.2.toNat,
            value x.1[r * x.2.2.2.toNat + c]!.toBits * value x.2.1[c]!.toBits| ≤
          (x.2.2.2.toNat : ℝ) / (2 ^ 24 - x.2.2.2.toNat) * ∑ c ∈ Finset.range x.2.2.2.toNat,
            |value x.1[r * x.2.2.2.toNat + c]!.toBits * value x.2.1[c]!.toBits| +
            x.2.2.2.toNat / 2 ^ 149) :=
  .of_trapFree (.ofA compiled.matVec32.trapFree) nofun matVec32_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, hm⟩, _⟩ hD => by
      obtain ⟨hfm, hfv, hsz, hK, hP⟩ := hD
      have hms := size_lt hm.values.size_lt_memory32
      obtain ⟨hs, hg⟩ := matVec32_get x.1 x.2.1 x.2.2.1 x.2.2.2 (by omega)
      refine ⟨hs, fun r hr => ?_⟩
      rw [hg r hr]
      exact dot_bound _ (fun c => x.1[r * x.2.2.2.toNat + c]!) (fun c => x.2.1[c]!)
        (fun c => finite_get _ hfm _) (finite_get _ hfv) hK (hP r hr)

#print axioms matVec32_master

/-! ### `linear32` -/

theorem linear32_get (x w b : Array Float32) (k m : UInt64)
    (hkm : k.toNat * m.toNat < 2 ^ 64) :
    (linear32 x w b k m).size = m.toNat ∧ ∀ c < m.toNat,
      (linear32 x w b k m)[c]! = (List.range k.toNat).foldl
        (fun acc i => acc + x[i]! * w[i * m.toNat + c]!) 0.0 + b[c]! := by
  refine ⟨build_size _ _, fun c hc => ?_⟩
  rw [linear32, build_get hc]
  have hc64 : c < 2 ^ 64 := lt_trans hc (lt64 _)
  rw [ofNat_toNat c hc64]
  congr 1
  apply loop_dot
  intro i hi
  have hi64 : i < 2 ^ 64 := lt_trans hi (lt64 _)
  have hle : i * m.toNat + c < 2 ^ 64 := lt_trans (idx_lt hi hc) hkm
  refine ⟨ofNat_toNat i hi64, ?_⟩
  rw [UInt64.toNat_add, UInt64.toNat_mul, ofNat_toNat i hi64, ofNat_toNat c hc64]
  exact mod64 hle

/-- A left-to-right sum of `K < 2 ^ 22` rounded products plus a float `b`, rounded, lies within
`γ_(K+1) (Σ |x_i y_i| + |b|) + K / 2 ^ 149` of the exact `Σ x_i y_i + b`. -/
theorem dot_add_bound (K : ℕ) (xf yf : ℕ → Float32) (bias : Float32)
    (hx : ∀ c, Finite (xf c).toBits) (hy : ∀ c, Finite (yf c).toBits)
    (hb : Finite bias.toBits) (hK : K < 2 ^ 22)
    (hP : ∑ c ∈ Finset.range K, |value (xf c).toBits * value (yf c).toBits| +
      |value bias.toBits| ≤ 2 ^ 124) :
    Finite ((List.range K).foldl (fun acc c => acc + xf c * yf c) 0.0 + bias).toBits ∧
      |value ((List.range K).foldl (fun acc c => acc + xf c * yf c) 0.0 + bias).toBits -
          (∑ c ∈ Finset.range K, value (xf c).toBits * value (yf c).toBits +
            value bias.toBits)| ≤
        ((K + 1 : ℕ) : ℝ) / (2 ^ 24 - (K + 1 : ℕ)) *
          (∑ c ∈ Finset.range K, |value (xf c).toBits * value (yf c).toBits| +
            |value bias.toBits|) + K / 2 ^ 149 := by
  have hd := dot_raw K xf yf hx hy hK (by have := abs_nonneg (value bias.toBits); linarith)
  set P := ∑ c ∈ Finset.range K, |value (xf c).toBits * value (yf c).toBits|
  set S := ∑ c ∈ Finset.range K, value (xf c).toBits * value (yf c).toBits
  set B := |value bias.toBits|
  set D := (List.range K).foldl (fun acc c => acc + xf c * yf c) 0.0
  set u : ℝ := 1 / 2 ^ 24 with hu
  set E := ((1 + u) ^ K - 1) * P + (1 + u) ^ (K - 1) * (K * (1 / 2 ^ 150)) with hEdef
  have hd2 : |value D.toBits - S| ≤ E := hd.2
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB0 : 0 ≤ B := abs_nonneg _
  have hSP : |S| ≤ P := Finset.abs_sum_le_sum_abs _ _
  clear_value E u
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hKr : (K : ℝ) < 2 ^ 22 := by exact_mod_cast hK
  have h2 : (1 + u) ^ (K - 1) < 2 := by
    rw [hu]
    exact pow_le_two 24 (K - 1) (by
      have : ((K - 1 : ℕ) : ℝ) ≤ 2 ^ 22 := by exact_mod_cast (Nat.sub_le _ _).trans hK.le
      linarith)
  have h2' : (1 + u) ^ K < 2 := by rw [hu]; exact pow_le_two 24 K (by linarith)
  have hQ1 : 1 ≤ (1 + u) ^ K := one_le_pow₀ (by linarith)
  have hE : E ≤ P + 2 ^ 22 * (1 / 2 ^ 149) := by
    have e1 : ((1 + u) ^ K - 1) * P ≤ 1 * P := mul_le_mul_of_nonneg_right (by linarith) hP0
    have e2 : (1 + u) ^ (K - 1) * (K * (1 / 2 ^ 150)) ≤ 2 * (2 ^ 22 * (1 / 2 ^ 150)) :=
      mul_le_mul h2.le (mul_le_mul_of_nonneg_right hKr.le (by positivity)) (by positivity)
        (by norm_num)
    have e3 : (2 : ℝ) * (2 ^ 22 * (1 / 2 ^ 150)) = 2 ^ 22 * (1 / 2 ^ 149) := by norm_num
    linarith
  have hDv : |value D.toBits| ≤ P + E := by
    have := abs_sub_abs_le_abs_sub (value D.toBits) S
    linarith
  have hsum : |value D.toBits + value bias.toBits| < 2 ^ 127 := by
    have := abs_add_le (value D.toBits) (value bias.toBits)
    have : (2 : ℝ) ^ 124 + (2 ^ 124 + 2 ^ 22 * (1 / 2 ^ 149)) < 2 ^ 127 := by norm_num
    linarith
  obtain ⟨hf, he⟩ := add_relative _ _ hd.1 hb hsum
  rw [← F32Bits.toBits_add] at hf he
  refine ⟨hf, ?_⟩
  have htri : |value (D + bias).toBits - (S + value bias.toBits)| ≤
      |value D.toBits + value bias.toBits| / 2 ^ 24 + E := by
    have : value (D + bias).toBits - (S + value bias.toBits) =
        (value (D + bias).toBits - (value D.toBits + value bias.toBits)) +
          (value D.toBits - S) := by ring
    rw [this]
    exact (abs_add_le _ _).trans (add_le_add he hd2)
  have hDB : |value D.toBits + value bias.toBits| ≤ P + E + B :=
    (abs_add_le _ _).trans (by linarith)
  have hK1 : ((K + 1 : ℕ) : ℝ) < 2 ^ 24 := by push_cast; linarith
  have hg := gamma_pow 24 (K + 1) hK1
  rw [← hu] at hg
  have hbern : 1 + ((K + 1 : ℕ) : ℝ) * u ≤ (1 + u) ^ (K + 1) :=
    one_add_mul_le_pow (by linarith) _
  have hK1u : u ≤ ((K + 1 : ℕ) : ℝ) * u := by
    have : (1 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos K
    nlinarith
  set γ := ((K + 1 : ℕ) : ℝ) / (2 ^ 24 - (K + 1 : ℕ))
  have hC : ((1 + u) ^ (K + 1) - 1) * P ≤ γ * P := mul_le_mul_of_nonneg_right hg hP0
  have hD : u * B ≤ γ * B := mul_le_mul_of_nonneg_right (by linarith) hB0
  have hA : (1 + u) * (((1 + u) ^ K - 1) * P) + u * P = ((1 + u) ^ (K + 1) - 1) * P := by ring
  have hη : (1 + u) * ((1 + u) ^ (K - 1) * (K * (1 / 2 ^ 150))) ≤ K / 2 ^ 149 := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0]; simp
    · have : (1 + u) * (1 + u) ^ (K - 1) = (1 + u) ^ K := by
        rw [← pow_succ', show K - 1 + 1 = K by omega]
      have e : (1 + u) * ((1 + u) ^ (K - 1) * (K * (1 / 2 ^ 150))) =
          (1 + u) ^ K * (K * (1 / 2 ^ 150)) := by rw [← this]; ring
      rw [e]
      have : (1 + u) ^ K * (K * (1 / 2 ^ 150)) ≤ 2 * (K * (1 / 2 ^ 150)) :=
        mul_le_mul_of_nonneg_right h2'.le (by positivity)
      have e2 : (2 : ℝ) * (K * (1 / 2 ^ 150)) = K / 2 ^ 149 := by ring
      linarith
  have hEexp : (1 + u) * E = (1 + u) * (((1 + u) ^ K - 1) * P) +
      (1 + u) * ((1 + u) ^ (K - 1) * (K * (1 / 2 ^ 150))) := by rw [hEdef]; ring
  have hdiv : |value D.toBits + value bias.toBits| / 2 ^ 24 ≤ (P + E + B) * u := by
    rw [hu, ← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_right hDB (by positivity)
  have hlin : (P + E + B) * u + E = (1 + u) * E + u * P + u * B := by ring
  linarith

/-- The export `linear32`, called on a row `x` of `k < 2 ^ 22` finite binary32 floats, an array `w`
of finite binary32 floats holding a `k × m` matrix by rows (`k m ≤ w.size`), a bias `b` of finite
binary32 floats, and the counts, returns `m` finite floats, the float `c` within
`γ_(k+1) (Σ_i |x_i w_ic| + |b_c|) + k / 2 ^ 149` of the exact `Σ_i x_i w_ic + b_c`, each missing
`b_c` counting as 0, when each such `Σ_i |x_i w_ic| + |b_c|` is at most `2 ^ 124`; here
`γ_j = j / (2 ^ 24 - j)`. -/
theorem linear32_master :
    Verified.Master compiled.module compiled.tables "linear32" compiled.linear32.bound
      (fun x : Array Float32 × Array Float32 × Array Float32 × UInt64 × UInt64 =>
        (∀ v ∈ x.1, Finite v.toBits) ∧ (∀ v ∈ x.2.1, Finite v.toBits) ∧
        (∀ v ∈ x.2.2.1, Finite v.toBits) ∧ x.2.2.2.1.toNat * x.2.2.2.2.toNat ≤ x.2.1.size ∧
        x.2.2.2.1.toNat < 2 ^ 22 ∧
        ∀ c < x.2.2.2.2.toNat, ∑ i ∈ Finset.range x.2.2.2.1.toNat,
          |value x.1[i]!.toBits * value x.2.1[i * x.2.2.2.2.toNat + c]!.toBits| +
          |value x.2.2.1[c]!.toBits| ≤ 2 ^ 124)
      (fun x (y : Array Float32) => y.size = x.2.2.2.2.toNat ∧ ∀ c < x.2.2.2.2.toNat,
        Finite y[c]!.toBits ∧
        |value y[c]!.toBits - (∑ i ∈ Finset.range x.2.2.2.1.toNat,
            value x.1[i]!.toBits * value x.2.1[i * x.2.2.2.2.toNat + c]!.toBits +
            value x.2.2.1[c]!.toBits)| ≤
          ((x.2.2.2.1.toNat + 1 : ℕ) : ℝ) / (2 ^ 24 - (x.2.2.2.1.toNat + 1 : ℕ)) *
            (∑ i ∈ Finset.range x.2.2.2.1.toNat,
              |value x.1[i]!.toBits * value x.2.1[i * x.2.2.2.2.toNat + c]!.toBits| +
              |value x.2.2.1[c]!.toBits|) + x.2.2.2.1.toNat / 2 ^ 149) :=
  .of_trapFree (.ofA compiled.linear32.trapFree) nofun linear32_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, _, _, _, _, ⟨_, _, hw⟩, _⟩ hD => by
      obtain ⟨hfx, hfw, hfb, hsz, hK, hP⟩ := hD
      have hws := size_lt hw.values.size_lt_memory32
      obtain ⟨hs, hg⟩ := linear32_get x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 (by omega)
      refine ⟨hs, fun c hc => ?_⟩
      rw [hg c hc]
      exact dot_add_bound _ (fun i => x.1[i]!) (fun i => x.2.1[i * x.2.2.2.2.toNat + c]!)
        x.2.2.1[c]! (finite_get _ hfx) (fun i => finite_get _ hfw _) (finite_get _ hfb c) hK
        (hP c hc)

#print axioms linear32_master

end Library.Numerics.LinearAlgebra.Binary32
