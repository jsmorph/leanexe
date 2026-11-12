import Library.Numerics.LinearAlgebra.Float64.Compiled
import Library.Numerics.Reductions.Binary64
import LeanExe.Dialect.ArrayLemmas
import LeanExe.Dialect.Lemmas
import Verified.Master

/-!
The master theorems of the binary64 linear algebra.  Each entry of `dot`, `matVec`, `matMul`, and
`matMulT` is a left-to-right sum of rounded products, whose error `Binary64.range_dot` gives;
each element of `axpy` and `grid` is a rounded product and a rounded sum, whose error
`Binary64.mul_add_bound` gives; each element of `add` is one rounded sum.
-/

namespace Library.Numerics.LinearAlgebra.Float64

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit LeanExe.ProofKit.F64Approx LeanExe.Dialect
open LeanExe.Pipeline (Moved)
open Library.Numerics.Reductions.Binary64

set_option exponentiation.threshold 4096

theorem dot_export :
    ({ name := "dot", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem axpy_export :
    ({ name := "axpy", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem grid_export :
    ({ name := "grid", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem matVec_export :
    ({ name := "matVec", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem matMul_export :
    ({ name := "matMul", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem matMulT_export :
    ({ name := "matMulT", funcIdx := 7 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem add_export :
    ({ name := "add", funcIdx := 8 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem size_lt {xs : Array Float} (h : (xs.map Float.toBits).size < 536870912) :
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

/-! ### `dot` -/

theorem dot_spec (xs ys : Array Float) (hs : xs.size < 2 ^ 52) (hx : ∀ v ∈ xs, Finite v.toBits)
    (hy : ∀ v ∈ ys, Finite v.toBits)
    (hP : ∑ i ∈ Finset.range xs.size, |value xs[i]!.toBits * value ys[i]!.toBits| ≤ 2 ^ 1021) :
    Finite (dot xs ys).toBits ∧
      |value (dot xs ys).toBits - ∑ i ∈ Finset.range xs.size, value xs[i]!.toBits * value ys[i]!.toBits| ≤
        (xs.size : ℝ) / (2 ^ 53 - xs.size) *
          ∑ i ∈ Finset.range xs.size, |value xs[i]!.toBits * value ys[i]!.toBits| +
          xs.size / 2 ^ 1074 := by
  have h1 : dot xs ys =
      (List.range xs.size.toUInt64.toNat).foldl (fun acc i => acc + xs[i]! * ys[i]!) 0.0 :=
    loop_toNat _ _ (fun j acc => acc + xs[j]! * ys[j]!)
  rw [h1, size_toUInt64 xs (by omega)]
  exact range_dot xs.size (fun i => xs[i]!) (fun i => ys[i]!) (finite_get xs hx)
    (finite_get ys hy) hs hP

/-- The export `dot`, called on arrays `xs` of `n` finite floats and `ys` of finite floats, whose
products `x_i y_i` have magnitudes summing to at most `2 ^ 1021`, returns a finite float within
`γ_n Σ |x_i y_i| + n / 2 ^ 1074` of the exact `Σ x_i y_i`, each missing `y_i` counting as 0,
where `γ_k = k / (2 ^ 53 - k)`. -/
theorem dot_master :
    Verified.Master compiled.module compiled.tables "dot" compiled.dot.bound
      (fun x : Array Float × Array Float => (∀ v ∈ x.1, Finite v.toBits) ∧
        (∀ v ∈ x.2, Finite v.toBits) ∧
        ∑ i ∈ Finset.range x.1.size, |value x.1[i]!.toBits * value x.2[i]!.toBits| ≤ 2 ^ 1021)
      (fun x (y : Float) => Finite y.toBits ∧
        |value y.toBits - ∑ i ∈ Finset.range x.1.size, value x.1[i]!.toBits * value x.2[i]!.toBits| ≤
          (x.1.size : ℝ) / (2 ^ 53 - x.1.size) *
            ∑ i ∈ Finset.range x.1.size, |value x.1[i]!.toBits * value x.2[i]!.toBits| +
            x.1.size / 2 ^ 1074) :=
  .of_trapFree (.ofA compiled.dot.trapFree) nofun dot_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, hxs⟩, _⟩ hD =>
      dot_spec x.1 x.2 (by have := size_lt hxs.values.size_lt_memory32; omega) hD.1 hD.2.1
        hD.2.2

#print axioms dot_master

/-! ### `axpy` -/

theorem axpy_get (a : Float) (xs ys : Array Float) (h : ys.size < 2 ^ 64) :
    (axpy a xs ys).size = ys.size ∧
      ∀ j < ys.size, (axpy a xs ys)[j]! = a * xs[j]! + ys[j]! := by
  have h1 : axpy a xs ys = (List.range ys.size.toUInt64.toNat).foldl
      (fun acc i => acc.set! i (a * xs[i]! + acc[i]!)) ys :=
    loop_toNat _ _ (fun (j : ℕ) (acc : Array Float) => acc.set! j (a * xs[j]! + acc[j]!))
  rw [h1, size_toUInt64 ys h]
  suffices hk : ∀ k ≤ ys.size,
      ((List.range k).foldl (fun acc i => acc.set! i (a * xs[i]! + acc[i]!)) ys).size =
        ys.size ∧ ∀ j < ys.size,
        ((List.range k).foldl (fun acc i => acc.set! i (a * xs[i]! + acc[i]!)) ys)[j]! =
          if j < k then a * xs[j]! + ys[j]! else ys[j]! by
    obtain ⟨hs, hg⟩ := hk ys.size le_rfl
    exact ⟨hs, fun j hj => by rw [hg j hj, ite_eq_left hj]⟩
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨hs, hg⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set acc := (List.range k).foldl (fun acc i => acc.set! i (a * xs[i]! + acc[i]!)) ys
    have hk' : k < acc.size := by rw [hs]; omega
    refine ⟨by simp [hs], fun j hj => ?_⟩
    rw [get_set acc k _ j hk', hg k (by omega), ite_eq_right (lt_irrefl k)]
    by_cases hjk : j = k
    · rw [ite_eq_left hjk, ite_eq_left (show j < k + 1 by omega), hjk]
    · rw [ite_eq_right hjk, hg j hj]
      by_cases hjl : j < k
      · rw [ite_eq_left hjl, ite_eq_left (show j < k + 1 by omega)]
      · rw [ite_eq_right hjl, ite_eq_right (show ¬ j < k + 1 by omega)]

/-- The export `axpy`, called on a finite float `a`, an array `xs` of finite floats, and an array
`ys` of finite floats that the caller moves, with `|a x_i| + |y_i| ≤ 2 ^ 1021` for each index `i`
of `ys`, returns an array of the size of `ys` whose element `i` is finite and within
`γ_2 (|a x_i| + |y_i|) + 2 ^ -1074` of `a x_i + y_i`, each missing `x_i` counting as 0, where
`γ_2 = 2 / (2 ^ 53 - 2)`. -/
theorem axpy_master :
    Verified.Master compiled.module compiled.tables "axpy" compiled.axpy.bound
      (fun x : Float × Array Float × Moved (Array Float) => Finite x.1.toBits ∧
        (∀ v ∈ x.2.1, Finite v.toBits) ∧ (∀ v ∈ x.2.2.val, Finite v.toBits) ∧
        ∀ i < x.2.2.val.size,
          |value x.1.toBits * value x.2.1[i]!.toBits| + |value x.2.2.val[i]!.toBits| ≤ 2 ^ 1021)
      (fun x (y : Array Float) => y.size = x.2.2.val.size ∧ ∀ i < x.2.2.val.size,
        Finite y[i]!.toBits ∧
        |value y[i]!.toBits -
            (value x.1.toBits * value x.2.1[i]!.toBits + value x.2.2.val[i]!.toBits)| ≤
          2 / (2 ^ 53 - 2) *
            (|value x.1.toBits * value x.2.1[i]!.toBits| + |value x.2.2.val[i]!.toBits|) +
            1 / 2 ^ 1074) :=
  .of_trapFree (.ofA compiled.axpy.trapFree) nofun axpy_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, _, _, _, _, _, ⟨_, _, hys⟩⟩ hD => by
      obtain ⟨ha, hxs, hys', hm⟩ := hD
      have hs : x.2.2.val.size < 2 ^ 64 := by
        have := hys.values.size_lt_memory32; simp at this; omega
      obtain ⟨hsz, hg⟩ := axpy_get x.1 x.2.1 x.2.2.val hs
      refine ⟨hsz, fun i hi => ?_⟩
      rw [hg i hi]
      exact (mul_add_bound _ _ _ ha (finite_get _ hxs i) (finite_get _ hys' i) (hm i hi)).1

#print axioms axpy_master

/-! ### `grid` -/

/-- The export `grid`, called on a count `n ≤ 2 ^ 53` and finite floats `x0` and `dx` with
`|x0| + n |dx| ≤ 2 ^ 1021`, returns `n` finite floats, the float `i` within
`γ_2 (|x0| + i |dx|) + 2 ^ -1074` of `x0 + i dx`, where `γ_2 = 2 / (2 ^ 53 - 2)`. -/
theorem grid_master :
    Verified.Master compiled.module compiled.tables "grid" compiled.grid.bound
      (fun x : UInt64 × Float × Float => Finite x.2.1.toBits ∧ Finite x.2.2.toBits ∧
        x.1.toNat ≤ 2 ^ 53 ∧ |value x.2.1.toBits| + x.1.toNat * |value x.2.2.toBits| ≤ 2 ^ 1021)
      (fun x (y : Array Float) => y.size = x.1.toNat ∧ ∀ i < x.1.toNat,
        Finite y[i]!.toBits ∧
        |value y[i]!.toBits - (value x.2.1.toBits + i * value x.2.2.toBits)| ≤
          2 / (2 ^ 53 - 2) * (|value x.2.1.toBits| + i * |value x.2.2.toBits|) + 1 / 2 ^ 1074) :=
  .of_trapFree (.ofA compiled.grid.trapFree) nofun grid_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ hD => by
      obtain ⟨h0, hd, hn, hm⟩ := hD
      refine ⟨build_size _ _, fun i hi => ?_⟩
      rw [grid, build_get hi]
      have hi64 : i < 2 ^ 64 := lt_trans hi (lt64 _)
      have hiv := toFloat_exact (UInt64.ofNat i) (by rw [ofNat_toNat i hi64]; omega)
      rw [ofNat_toNat i hi64] at hiv
      have hval : value (UInt64.ofNat i).toFloat.toBits = i := by
        have := hiv.2; rw [abs_nonpos_iff, sub_eq_zero] at this; exact this
      have hb : |value (UInt64.ofNat i).toFloat.toBits * value x.2.2.toBits| +
          |value x.2.1.toBits| ≤ 2 ^ 1021 := by
        rw [hval, abs_mul, Nat.abs_cast]
        have : (i : ℝ) * |value x.2.2.toBits| ≤ x.1.toNat * |value x.2.2.toBits| :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le) (abs_nonneg _)
        linarith
      have h := (mul_add_bound _ _ _ hiv.1 hd h0 hb).2
      rw [hval, abs_mul, Nat.abs_cast] at h
      refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
      ring

#print axioms grid_master

/-! ### `matVec` -/

theorem matVec_get (m v : Array Float) (rows cols : UInt64)
    (hrc : rows.toNat * cols.toNat < 2 ^ 64) :
    (matVec m v rows cols).size = rows.toNat ∧ ∀ r < rows.toNat,
      (matVec m v rows cols)[r]! = (List.range cols.toNat).foldl
        (fun acc c => acc + m[r * cols.toNat + c]! * v[c]!) 0.0 := by
  refine ⟨build_size _ _, fun r hr => ?_⟩
  rw [matVec, build_get hr]
  apply loop_dot
  intro c hc
  have hr64 : r < 2 ^ 64 := lt_trans hr (lt64 _)
  have hc64 : c < 2 ^ 64 := lt_trans hc (lt64 _)
  have hle : r * cols.toNat + c < 2 ^ 64 := lt_trans (idx_lt hr hc) hrc
  refine ⟨?_, ofNat_toNat c hc64⟩
  rw [UInt64.toNat_add, UInt64.toNat_mul, ofNat_toNat r hr64, ofNat_toNat c hc64]
  exact mod64 hle

/-- The export `matVec`, called on an array `m` of finite floats holding a `rows × cols` matrix by
rows (`rows · cols ≤ m.size`), an array `v` of finite floats, and the counts, returns `rows`
finite floats, the float `r` within `γ_cols Σ_c |m_rc v_c| + cols / 2 ^ 1074` of the exact
`Σ_c m_rc v_c`, each missing `v_c` counting as 0, when each row's `Σ_c |m_rc v_c|` is at most
`2 ^ 1021`; here `γ_k = k / (2 ^ 53 - k)`. -/
theorem matVec_master :
    Verified.Master compiled.module compiled.tables "matVec" compiled.matVec.bound
      (fun x : Array Float × Array Float × UInt64 × UInt64 =>
        (∀ v ∈ x.1, Finite v.toBits) ∧ (∀ v ∈ x.2.1, Finite v.toBits) ∧
        x.2.2.1.toNat * x.2.2.2.toNat ≤ x.1.size ∧
        ∀ r < x.2.2.1.toNat, ∑ c ∈ Finset.range x.2.2.2.toNat,
          |value x.1[r * x.2.2.2.toNat + c]!.toBits * value x.2.1[c]!.toBits| ≤ 2 ^ 1021)
      (fun x (y : Array Float) => y.size = x.2.2.1.toNat ∧ ∀ r < x.2.2.1.toNat,
        Finite y[r]!.toBits ∧
        |value y[r]!.toBits - ∑ c ∈ Finset.range x.2.2.2.toNat,
            value x.1[r * x.2.2.2.toNat + c]!.toBits * value x.2.1[c]!.toBits| ≤
          (x.2.2.2.toNat : ℝ) / (2 ^ 53 - x.2.2.2.toNat) * ∑ c ∈ Finset.range x.2.2.2.toNat,
            |value x.1[r * x.2.2.2.toNat + c]!.toBits * value x.2.1[c]!.toBits| +
            x.2.2.2.toNat / 2 ^ 1074) :=
  .of_trapFree (.ofA compiled.matVec.trapFree) nofun matVec_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, hm⟩, _⟩ hD => by
      obtain ⟨hfm, hfv, hsz, hP⟩ := hD
      have hms := size_lt hm.values.size_lt_memory32
      obtain ⟨hs, hg⟩ := matVec_get x.1 x.2.1 x.2.2.1 x.2.2.2 (by omega)
      refine ⟨hs, fun r hr => ?_⟩
      rw [hg r hr]
      have hK : x.2.2.2.toNat < 2 ^ 52 := by
        have : x.2.2.2.toNat ≤ x.2.2.1.toNat * x.2.2.2.toNat :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      exact range_dot _ (fun c => x.1[r * x.2.2.2.toNat + c]!) (fun c => x.2.1[c]!)
        (fun c => finite_get _ hfm _) (finite_get _ hfv) hK (hP r hr)

#print axioms matVec_master

/-! ### `matMul` and `matMulT` -/

theorem divmod (n m : UInt64) (i j : ℕ) (hi : i < n.toNat) (hj : j < m.toNat)
    (hnm : n.toNat * m.toNat < 2 ^ 64) :
    (UInt64.ofNat (i * m.toNat + j) / m).toNat = i ∧
      (UInt64.ofNat (i * m.toNat + j) % m).toNat = j := by
  have he : i * m.toNat + j < n.toNat * m.toNat := idx_lt hi hj
  rw [UInt64.toNat_div, UInt64.toNat_mod, ofNat_toNat _ (lt_trans he hnm)]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

theorem matMul_get (a b : Array Float) (n k m : UInt64) (hnm : n.toNat * m.toNat < 2 ^ 64)
    (hnk : n.toNat * k.toNat < 2 ^ 64) (hkm : k.toNat * m.toNat < 2 ^ 64) :
    (matMul a b n k m).size = n.toNat * m.toNat ∧ ∀ i < n.toNat, ∀ j < m.toNat,
      (matMul a b n k m)[i * m.toNat + j]! = (List.range k.toNat).foldl
        (fun acc c => acc + a[i * k.toNat + c]! * b[c * m.toNat + j]!) 0.0 := by
  have hnm' : (n * m).toNat = n.toNat * m.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt hnm]
  refine ⟨by rw [matMul, build_size, hnm'], fun i hi j hj => ?_⟩
  have he : i * m.toNat + j < (n * m).toNat := by rw [hnm']; exact idx_lt hi hj
  rw [matMul, build_get he]
  obtain ⟨hdiv, hmod⟩ := divmod n m i j hi hj hnm
  apply loop_dot
  intro c hc
  have hc64 : c < 2 ^ 64 := lt_trans hc (lt64 _)
  have h1 : i * k.toNat + c < 2 ^ 64 := lt_trans (idx_lt hi hc) hnk
  have h2 : c * m.toNat + j < 2 ^ 64 := lt_trans (idx_lt hc hj) hkm
  constructor
  · rw [UInt64.toNat_add, UInt64.toNat_mul, hdiv, ofNat_toNat c hc64]
    exact mod64 h1
  · rw [UInt64.toNat_add, UInt64.toNat_mul, hmod, ofNat_toNat c hc64]
    exact mod64 h2

theorem matMulT_get (a b : Array Float) (n k m : UInt64) (hnm : n.toNat * m.toNat < 2 ^ 64)
    (hnk : n.toNat * k.toNat < 2 ^ 64) (hmk : m.toNat * k.toNat < 2 ^ 64) :
    (matMulT a b n k m).size = n.toNat * m.toNat ∧ ∀ i < n.toNat, ∀ j < m.toNat,
      (matMulT a b n k m)[i * m.toNat + j]! = (List.range k.toNat).foldl
        (fun acc c => acc + a[i * k.toNat + c]! * b[j * k.toNat + c]!) 0.0 := by
  have hnm' : (n * m).toNat = n.toNat * m.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt hnm]
  refine ⟨by rw [matMulT, build_size, hnm'], fun i hi j hj => ?_⟩
  have he : i * m.toNat + j < (n * m).toNat := by rw [hnm']; exact idx_lt hi hj
  rw [matMulT, build_get he]
  obtain ⟨hdiv, hmod⟩ := divmod n m i j hi hj hnm
  apply loop_dot
  intro c hc
  have hc64 : c < 2 ^ 64 := lt_trans hc (lt64 _)
  have h1 : i * k.toNat + c < 2 ^ 64 := lt_trans (idx_lt hi hc) hnk
  have h2 : j * k.toNat + c < 2 ^ 64 := lt_trans (idx_lt hj hc) hmk
  constructor
  · rw [UInt64.toNat_add, UInt64.toNat_mul, hdiv, ofNat_toNat c hc64]
    exact mod64 h1
  · rw [UInt64.toNat_add, UInt64.toNat_mul, hmod, ofNat_toNat c hc64]
    exact mod64 h2

/-- The export `matMul`, called on arrays `a` and `b` of finite floats holding an `n × k` and a
`k × m` matrix by rows (`n k ≤ a.size`, `k m ≤ b.size`, `n m < 2 ^ 64`) and the counts, returns
`n m` finite floats, the float `i m + j` within `γ_k Σ_c |a_ic b_cj| + k / 2 ^ 1074` of the exact
`Σ_c a_ic b_cj`, when each such `Σ_c |a_ic b_cj|` is at most `2 ^ 1021`; here
`γ_k = k / (2 ^ 53 - k)`. -/
theorem matMul_master :
    Verified.Master compiled.module compiled.tables "matMul" compiled.matMul.bound
      (fun x : Array Float × Array Float × UInt64 × UInt64 × UInt64 =>
        (∀ v ∈ x.1, Finite v.toBits) ∧ (∀ v ∈ x.2.1, Finite v.toBits) ∧
        x.2.2.1.toNat * x.2.2.2.1.toNat ≤ x.1.size ∧
        x.2.2.2.1.toNat * x.2.2.2.2.toNat ≤ x.2.1.size ∧
        x.2.2.1.toNat * x.2.2.2.2.toNat < 2 ^ 64 ∧
        ∀ i < x.2.2.1.toNat, ∀ j < x.2.2.2.2.toNat, ∑ c ∈ Finset.range x.2.2.2.1.toNat,
          |value x.1[i * x.2.2.2.1.toNat + c]!.toBits *
            value x.2.1[c * x.2.2.2.2.toNat + j]!.toBits| ≤ 2 ^ 1021)
      (fun x (y : Array Float) => y.size = x.2.2.1.toNat * x.2.2.2.2.toNat ∧
        ∀ i < x.2.2.1.toNat, ∀ j < x.2.2.2.2.toNat,
        Finite y[i * x.2.2.2.2.toNat + j]!.toBits ∧
        |value y[i * x.2.2.2.2.toNat + j]!.toBits - ∑ c ∈ Finset.range x.2.2.2.1.toNat,
            value x.1[i * x.2.2.2.1.toNat + c]!.toBits *
              value x.2.1[c * x.2.2.2.2.toNat + j]!.toBits| ≤
          (x.2.2.2.1.toNat : ℝ) / (2 ^ 53 - x.2.2.2.1.toNat) * ∑ c ∈ Finset.range x.2.2.2.1.toNat,
            |value x.1[i * x.2.2.2.1.toNat + c]!.toBits *
              value x.2.1[c * x.2.2.2.2.toNat + j]!.toBits| +
            x.2.2.2.1.toNat / 2 ^ 1074) :=
  .of_trapFree (.ofA compiled.matMul.trapFree) nofun matMul_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, ha⟩, _, _, _, ⟨_, _, hb⟩, _⟩ hD => by
      obtain ⟨hfa, hfb, hnk, hkm, hnm, hP⟩ := hD
      have has := size_lt ha.values.size_lt_memory32
      have hbs := size_lt hb.values.size_lt_memory32
      obtain ⟨hs, hg⟩ := matMul_get x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 hnm (by omega)
        (by omega)
      refine ⟨hs, fun i hi j hj => ?_⟩
      rw [hg i hi j hj]
      have hK : x.2.2.2.1.toNat < 2 ^ 52 := by
        have : x.2.2.2.1.toNat ≤ x.2.2.1.toNat * x.2.2.2.1.toNat :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      exact range_dot _ (fun c => x.1[i * x.2.2.2.1.toNat + c]!)
        (fun c => x.2.1[c * x.2.2.2.2.toNat + j]!) (fun c => finite_get _ hfa _)
        (fun c => finite_get _ hfb _) hK (hP i hi j hj)

#print axioms matMul_master

/-- The export `matMulT`, called on arrays `a` and `b` of finite floats holding an `n × k` and an
`m × k` matrix by rows (`n k ≤ a.size`, `m k ≤ b.size`, `n m < 2 ^ 64`) and the counts, returns
`n m` finite floats, the float `i m + j` within `γ_k Σ_c |a_ic b_jc| + k / 2 ^ 1074` of the exact
`Σ_c a_ic b_jc`, the entry of `a bᵀ`, when each such `Σ_c |a_ic b_jc|` is at most `2 ^ 1021`; here
`γ_k = k / (2 ^ 53 - k)`. -/
theorem matMulT_master :
    Verified.Master compiled.module compiled.tables "matMulT" compiled.matMulT.bound
      (fun x : Array Float × Array Float × UInt64 × UInt64 × UInt64 =>
        (∀ v ∈ x.1, Finite v.toBits) ∧ (∀ v ∈ x.2.1, Finite v.toBits) ∧
        x.2.2.1.toNat * x.2.2.2.1.toNat ≤ x.1.size ∧
        x.2.2.2.2.toNat * x.2.2.2.1.toNat ≤ x.2.1.size ∧
        x.2.2.1.toNat * x.2.2.2.2.toNat < 2 ^ 64 ∧
        ∀ i < x.2.2.1.toNat, ∀ j < x.2.2.2.2.toNat, ∑ c ∈ Finset.range x.2.2.2.1.toNat,
          |value x.1[i * x.2.2.2.1.toNat + c]!.toBits *
            value x.2.1[j * x.2.2.2.1.toNat + c]!.toBits| ≤ 2 ^ 1021)
      (fun x (y : Array Float) => y.size = x.2.2.1.toNat * x.2.2.2.2.toNat ∧
        ∀ i < x.2.2.1.toNat, ∀ j < x.2.2.2.2.toNat,
        Finite y[i * x.2.2.2.2.toNat + j]!.toBits ∧
        |value y[i * x.2.2.2.2.toNat + j]!.toBits - ∑ c ∈ Finset.range x.2.2.2.1.toNat,
            value x.1[i * x.2.2.2.1.toNat + c]!.toBits *
              value x.2.1[j * x.2.2.2.1.toNat + c]!.toBits| ≤
          (x.2.2.2.1.toNat : ℝ) / (2 ^ 53 - x.2.2.2.1.toNat) * ∑ c ∈ Finset.range x.2.2.2.1.toNat,
            |value x.1[i * x.2.2.2.1.toNat + c]!.toBits *
              value x.2.1[j * x.2.2.2.1.toNat + c]!.toBits| +
            x.2.2.2.1.toNat / 2 ^ 1074) :=
  .of_trapFree (.ofA compiled.matMulT.trapFree) nofun matMulT_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, ha⟩, _, _, _, ⟨_, _, hb⟩, _⟩ hD => by
      obtain ⟨hfa, hfb, hnk, hmk, hnm, hP⟩ := hD
      have has := size_lt ha.values.size_lt_memory32
      have hbs := size_lt hb.values.size_lt_memory32
      obtain ⟨hs, hg⟩ := matMulT_get x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 hnm (by omega)
        (by omega)
      refine ⟨hs, fun i hi j hj => ?_⟩
      rw [hg i hi j hj]
      have hK : x.2.2.2.1.toNat < 2 ^ 52 := by
        have : x.2.2.2.1.toNat ≤ x.2.2.1.toNat * x.2.2.2.1.toNat :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      exact range_dot _ (fun c => x.1[i * x.2.2.2.1.toNat + c]!)
        (fun c => x.2.1[j * x.2.2.2.1.toNat + c]!) (fun c => finite_get _ hfa _)
        (fun c => finite_get _ hfb _) hK (hP i hi j hj)

#print axioms matMulT_master

/-! ### `add` -/

/-- The export `add`, called on arrays `a` and `b` of finite floats with
`|a_i + b_i| < 2 ^ 1023` for each index `i` of `a`, returns an array of the size of `a` whose
element `i` is finite and within `2 ^ -53 |a_i + b_i|` of `a_i + b_i`, each missing `b_i` counting
as 0. -/
theorem add_master :
    Verified.Master compiled.module compiled.tables "add" compiled.add.bound
      (fun x : Array Float × Array Float => (∀ v ∈ x.1, Finite v.toBits) ∧
        (∀ v ∈ x.2, Finite v.toBits) ∧
        ∀ i < x.1.size, |value x.1[i]!.toBits + value x.2[i]!.toBits| < 2 ^ 1023)
      (fun x (y : Array Float) => y.size = x.1.size ∧ ∀ i < x.1.size, Finite y[i]!.toBits ∧
        |value y[i]!.toBits - (value x.1[i]!.toBits + value x.2[i]!.toBits)| ≤
          |value x.1[i]!.toBits + value x.2[i]!.toBits| / 2 ^ 53) :=
  .of_trapFree (.ofA compiled.add.trapFree) nofun add_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, ha⟩, _⟩ hD => by
      obtain ⟨hfa, hfb, hm⟩ := hD
      have has := size_lt ha.values.size_lt_memory32
      have hsz := size_toUInt64 x.1 (by omega)
      refine ⟨by rw [add, build_size, hsz], fun i hi => ?_⟩
      have hlt : i < x.1.size.toUInt64.toNat := by rw [hsz]; exact hi
      rw [add, build_get hlt, ofNat_toNat i (by omega), F64Bits.toBits_add]
      have h := F64AddBounds.add_real_relative _ _ (finite_get _ hfa i) (finite_get _ hfb i)
        (hm i hi)
      refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
      rw [CodeLib.IEEE64.unitRoundoff64]
      ring

#print axioms add_master

end Library.Numerics.LinearAlgebra.Float64
