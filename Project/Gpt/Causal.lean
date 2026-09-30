import LeanExe.Examples.Gpt
import Mathlib.Tactic

/-! Row `i` of `attention`, `block`, and `forward` depends only on rows `0` to `i` of the
input.
The theorems concern the Lean definitions; `Implements` carries them to the bytes.
The bounds on the dimensions (`t`, `nh`, and `dh` below `2 ^ 16`; `f` and `vocab` below
`2 ^ 32`) exclude overflow in the `UInt64` index arithmetic. -/

namespace Project.Gpt.Causal

open LeanExe.Examples.Gpt

/-- Rows `0` to `i` of `a` and `b`, in rows of `w` elements stored in order, are equal. -/
def RowsAgree {α : Type} [Inhabited α] (w i : Nat) (a b : Array α) : Prop :=
  ∀ m, m < (i + 1) * w → a[m]! = b[m]!

theorem loop_congr {α : Type} {n : UInt64} {init : α} {f g : UInt64 → α → α}
    (h : ∀ k, k < n.toNat → ∀ acc, f (UInt64.ofNat k) acc = g (UInt64.ofNat k) acc) :
    LeanExe.loop n init f = LeanExe.loop n init g := by
  unfold LeanExe.loop
  congr 1
  funext k hk acc
  exact h k hk acc

/-- A loop whose every step keeps rows `0` to `i` in agreement, for arrays of equal
size, keeps them in agreement. -/
theorem loop_rows {n : UInt64} {s s' : Array Float} {step : UInt64 → Array Float → Array Float}
    {w i : Nat}
    (hStep : ∀ l x x', x.size = x'.size → RowsAgree w i x x' →
      (step l x).size = (step l x').size ∧ RowsAgree w i (step l x) (step l x'))
    (hs : s.size = s'.size) (h : RowsAgree w i s s') :
    RowsAgree w i (LeanExe.loop n s step) (LeanExe.loop n s' step) := by
  suffices ∀ k, (Nat.fold k (fun j _ x => step (UInt64.ofNat j) x) s).size =
      (Nat.fold k (fun j _ x => step (UInt64.ofNat j) x) s').size ∧
      RowsAgree w i (Nat.fold k (fun j _ x => step (UInt64.ofNat j) x) s)
        (Nat.fold k (fun j _ x => step (UInt64.ofNat j) x) s') from (this n.toNat).2
  intro k
  induction k with
  | zero => exact ⟨hs, h⟩
  | succ k ih =>
      simp only [Nat.fold_succ]
      exact hStep _ _ _ ih.1 ih.2

theorem rows_of_build {n : UInt64} {f g : UInt64 → Float} {w i : Nat}
    (h : ∀ m, m < (i + 1) * w → m < n.toNat → f (UInt64.ofNat m) = g (UInt64.ofNat m)) :
    RowsAgree w i (LeanExe.build n f) (LeanExe.build n g) := by
  intro m hm
  unfold LeanExe.build
  by_cases hn : m < n.toNat
  · simp [hn, h m hm hn]
  · simp [hn]

theorem toNat_ofNat_lt {m : Nat} {n : UInt64} (h : m < n.toNat) : (UInt64.ofNat m).toNat = m :=
  UInt64.toNat_ofNat_of_lt' (Nat.lt_trans h n.toNat_lt_size)

theorem mul_toNat {a b : UInt64} (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    (a * b).toNat = a.toNat * b.toNat := by
  have : a.toNat * b.toNat < 2 ^ 64 := by nlinarith
  rw [UInt64.toNat_mul, Nat.mod_eq_of_lt this]

theorem index_toNat {R W C : UInt64} (hR : R.toNat < 2 ^ 32) (hW : W.toNat < 2 ^ 32)
    (hC : C.toNat < W.toNat) : (R * W + C).toNat = R.toNat * W.toNat + C.toNat := by
  have hlt : R.toNat * W.toNat + C.toNat < 2 ^ 64 := by nlinarith
  rw [UInt64.toNat_add, mul_toNat hR hW, Nat.mod_eq_of_lt hlt]

/-- A read at column `C` of row `R ≤ i` agrees. -/
theorem read_agree {a b : Array Float} {W : UInt64} {i : Nat} (h : RowsAgree W.toNat i a b)
    {R C : UInt64} (hRi : R.toNat ≤ i) (hR : R.toNat < 2 ^ 32) (hW : W.toNat < 2 ^ 32)
    (hC : C.toNat < W.toNat) : a[(R * W + C).toNat]! = b[(R * W + C).toNat]! := by
  rw [index_toNat hR hW hC]
  refine h _ ?_
  calc R.toNat * W.toNat + C.toNat < (R.toNat + 1) * W.toNat := by rw [Nat.succ_mul]; omega
    _ ≤ (i + 1) * W.toNat := Nat.mul_le_mul_right _ (by omega)

theorem small_mul {a b : UInt64} (ha : a.toNat < 2 ^ 16) (hb : b.toNat < 2 ^ 16) :
    (a * b).toNat < 2 ^ 32 := by
  rw [mul_toNat (by omega) (by omega)]
  nlinarith

/-- Rows of `n · w` elements are groups of `n` rows of `w`. -/
theorem RowsAgree.split {α : Type} [Inhabited α] {a b : Array α} {n w i : Nat} (hn : 0 < n)
    (h : RowsAgree (n * w) i a b) : RowsAgree w ((i + 1) * n - 1) a b := by
  intro m hm
  have hpos : 1 ≤ (i + 1) * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [Nat.sub_add_cancel hpos] at hm
  exact h m (by rw [← Nat.mul_assoc]; exact hm)

theorem RowsAgree.join {α : Type} [Inhabited α] {a b : Array α} {n w i : Nat} (hn : 0 < n)
    (h : RowsAgree w ((i + 1) * n - 1) a b) : RowsAgree (n * w) i a b := by
  intro m hm
  have hpos : 1 ≤ (i + 1) * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact h m (by rw [Nat.sub_add_cancel hpos, Nat.mul_assoc]; exact hm)

/-- Facts about element `e` of a build over `n × w` elements, in rows of `w`. -/
theorem element_facts {n w : UInt64} {i e : Nat} (hn : n.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32)
    (he : e < (i + 1) * w.toNat) (hlt : e < (n * w).toNat) :
    (UInt64.ofNat e).toNat = e ∧ (UInt64.ofNat e / w).toNat = e / w.toNat ∧
      (UInt64.ofNat e % w).toNat = e % w.toNat ∧ e / w.toNat ≤ i ∧ e / w.toNat < n.toNat ∧
      e % w.toNat < w.toNat := by
  have hE : (UInt64.ofNat e).toNat = e := toNat_ofNat_lt hlt
  rw [mul_toNat hn hw] at hlt
  have hw0 : 0 < w.toNat := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hlt
  refine ⟨hE, by rw [UInt64.toNat_div, hE], by rw [UInt64.toNat_mod, hE],
    Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])),
    Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm]), Nat.mod_lt _ hw0⟩

theorem matMul_rows {a a' b : Array Float} {n k m : UInt64} {i : Nat} (hn : n.toNat < 2 ^ 32)
    (hk : k.toNat < 2 ^ 32) (hm : m.toNat < 2 ^ 32) (h : RowsAgree k.toNat i a a') :
    RowsAgree m.toNat i (matMul a b n k m) (matMul a' b n k m) := by
  unfold matMul
  refine rows_of_build fun e he hlt => loop_congr fun c hc acc => ?_
  obtain ⟨-, hRow, -, hri, hrn, -⟩ := element_facts hn hm he hlt
  rw [read_agree h (R := UInt64.ofNat e / m) (C := UInt64.ofNat c) (by omega) (by omega) hk
    (by rwa [toNat_ofNat_lt hc])]

theorem linear_rows {x x' w b : Array Float} {n k m : UInt64} {i : Nat} (hn : n.toNat < 2 ^ 32)
    (hk : k.toNat < 2 ^ 32) (hm : m.toNat < 2 ^ 32) (h : RowsAgree k.toNat i x x') :
    RowsAgree m.toNat i (linear x w b n k m) (linear x' w b n k m) := by
  unfold linear
  refine rows_of_build fun e he hlt => ?_
  obtain ⟨-, hRow, -, hri, hrn, -⟩ := element_facts hn hm he hlt
  congr 1
  refine loop_congr fun c hc acc => ?_
  rw [read_agree h (R := UInt64.ofNat e / m) (C := UInt64.ofNat c) (by omega) (by omega) hk
    (by rwa [toNat_ofNat_lt hc])]

theorem maskedScores_rows {q q' k k' : Array Float} {t nh dh : UInt64} {scale : Float} {i : Nat}
    (ht : t.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hq : RowsAgree (nh * dh).toNat i q q') (hk : RowsAgree (nh * dh).toNat i k k') :
    RowsAgree (nh * t).toNat i (maskedScores q k t nh dh scale)
      (maskedScores q' k' t nh dh scale) := by
  unfold maskedScores
  refine rows_of_build fun e he hlt => ?_
  have hnt := small_mul hn ht
  have hnd := small_mul hn hdh
  rw [UInt64.mul_assoc] at hlt
  obtain ⟨hE, hRow, -, hri, hrt, -⟩ := element_facts (by omega) hnt he hlt
  have hJ : (UInt64.ofNat e % t).toNat = e % t.toNat := by rw [UInt64.toNat_mod, hE]
  have hH : (UInt64.ofNat e / t % nh).toNat = e / t.toNat % nh.toNat := by
    rw [UInt64.toNat_mod, UInt64.toNat_div, hE]
  rw [mul_toNat (by omega) (by omega)] at hlt
  have hn0 : 0 < nh.toNat := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hlt
  have ht0 : 0 < t.toNat := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hlt
  have hHlt : e / t.toNat % nh.toNat < nh.toNat := Nat.mod_lt _ hn0
  have hjt : e % t.toNat < t.toNat := Nat.mod_lt _ ht0
  congr 2
  refine loop_congr fun c hc acc => ?_
  split at hc
  · rename_i hle
    rw [UInt64.le_iff_toNat_le, hJ, hRow] at hle
    have hc' : (UInt64.ofNat c).toNat < dh.toNat := by rwa [toNat_ofNat_lt hc]
    have hC : (UInt64.ofNat e / t % nh * dh + UInt64.ofNat c).toNat <
        (nh * dh).toNat := by
      rw [index_toNat (by rw [hH]; omega) (by omega) hc', hH, mul_toNat (by omega) (by omega)]
      calc e / t.toNat % nh.toNat * dh.toNat + (UInt64.ofNat c).toNat
          < (e / t.toNat % nh.toNat + 1) * dh.toNat := by rw [Nat.succ_mul]; omega
        _ ≤ nh.toNat * dh.toNat := Nat.mul_le_mul_right _ hHlt
    rw [read_agree hq (R := UInt64.ofNat e / (nh * t))
        (C := UInt64.ofNat e / t % nh * dh + UInt64.ofNat c) (by omega) (by omega) hnd hC,
      read_agree hk (R := UInt64.ofNat e % t)
        (C := UInt64.ofNat e / t % nh * dh + UInt64.ofNat c) (by omega) (by omega) hnd hC]
  · simp at hc

theorem rowMax_rows {x x' : Array Float} {t w : UInt64} {i : Nat} (ht : t.toNat < 2 ^ 32)
    (hw : w.toNat < 2 ^ 32) (h : RowsAgree w.toNat i x x') :
    RowsAgree 1 i (rowMax x t w) (rowMax x' t w) := by
  unfold rowMax
  refine rows_of_build fun r hr hlt => loop_congr fun c hc acc => ?_
  have hR := toNat_ofNat_lt hlt
  rw [read_agree h (R := UInt64.ofNat r) (C := UInt64.ofNat c) (by omega) (by omega) hw
    (by rwa [toNat_ofNat_lt hc])]

theorem rowSumExp_rows {x x' mx mx' : Array Float} {t w : UInt64} {i : Nat}
    (ht : t.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32) (h : RowsAgree w.toNat i x x')
    (hm : RowsAgree 1 i mx mx') :
    RowsAgree 1 i (rowSumExp x mx t w) (rowSumExp x' mx' t w) := by
  unfold rowSumExp
  refine rows_of_build fun r hr hlt => loop_congr fun c hc acc => ?_
  have hR := toNat_ofNat_lt hlt
  rw [read_agree h (R := UInt64.ofNat r) (C := UInt64.ofNat c) (by omega) (by omega) hw
    (by rwa [toNat_ofNat_lt hc]), hR, hm r (by omega)]

theorem softmaxApply_rows {x x' mx mx' sums sums' : Array Float} {t w : UInt64} {i : Nat}
    (ht : t.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32) (h : RowsAgree w.toNat i x x')
    (hm : RowsAgree 1 i mx mx') (hs : RowsAgree 1 i sums sums') :
    RowsAgree w.toNat i (softmaxApply x mx sums t w) (softmaxApply x' mx' sums' t w) := by
  unfold softmaxApply
  refine rows_of_build fun e he hlt => ?_
  obtain ⟨hE, hRow, -, hri, -, -⟩ := element_facts ht hw he hlt
  rw [hE, hRow, h e he, hm _ (by omega), hs _ (by omega)]

theorem softmaxRows_rows {x x' : Array Float} {t w : UInt64} {i : Nat} (ht : t.toNat < 2 ^ 32)
    (hw : w.toNat < 2 ^ 32) (h : RowsAgree w.toNat i x x') :
    RowsAgree w.toNat i (softmaxRows x t w) (softmaxRows x' t w) :=
  softmaxApply_rows ht hw h (rowMax_rows ht hw h) (rowSumExp_rows ht hw h (rowMax_rows ht hw h))

theorem causalMatMul_rows {p p' v v' : Array Float} {t nh dh : UInt64} {i : Nat}
    (ht : t.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hp : RowsAgree (nh * t).toNat i p p') (hv : RowsAgree (nh * dh).toNat i v v') :
    RowsAgree (nh * dh).toNat i (causalMatMul p v t nh dh) (causalMatMul p' v' t nh dh) := by
  unfold causalMatMul
  refine rows_of_build fun e he hlt => loop_congr fun j hj acc => ?_
  have hnt := small_mul hn ht
  have hnd := small_mul hn hdh
  obtain ⟨-, hRow, hCol, hri, hrt, hcd⟩ := element_facts (by omega) hnd he hlt
  have hJ : (UInt64.ofNat j).toNat = j := toNat_ofNat_lt hj
  rw [UInt64.toNat_add, hRow, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)] at hj
  have hHd : (UInt64.ofNat e % (nh * dh) / dh).toNat = e % (nh * dh).toNat / dh.toNat := by
    rw [UInt64.toNat_div, hCol]
  have hND : (nh * dh).toNat = nh.toNat * dh.toNat := mul_toNat (by omega) (by omega)
  have hHlt : e % (nh * dh).toNat / dh.toNat < nh.toNat :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hND]; exact hcd)
  have hC : (UInt64.ofNat e % (nh * dh) / dh * t + UInt64.ofNat j).toNat < (nh * t).toNat := by
    rw [index_toNat (by rw [hHd]; omega) (by omega) (by rw [hJ]; omega), hHd, hJ,
      mul_toNat (a := nh) (b := t) (by omega) (by omega)]
    calc e % (nh * dh).toNat / dh.toNat * t.toNat + j
        < (e % (nh * dh).toNat / dh.toNat + 1) * t.toNat := by rw [Nat.succ_mul]; omega
      _ ≤ nh.toNat * t.toNat := Nat.mul_le_mul_right _ hHlt
  rw [read_agree hp (R := UInt64.ofNat e / (nh * dh))
      (C := UInt64.ofNat e % (nh * dh) / dh * t + UInt64.ofNat j) (by omega) (by omega) hnt hC,
    read_agree hv (R := UInt64.ofNat j) (C := UInt64.ofNat e % (nh * dh)) (by omega) (by omega)
      hnd (by rwa [hCol])]

theorem rowMeans_rows {x x' : Array Float} {t d : UInt64} {i : Nat} (ht : t.toNat < 2 ^ 32)
    (hd : d.toNat < 2 ^ 32) (h : RowsAgree d.toNat i x x') :
    RowsAgree 1 i (rowMeans x t d) (rowMeans x' t d) := by
  unfold rowMeans
  refine rows_of_build fun r hr hlt => ?_
  congr 1
  refine loop_congr fun c hc acc => ?_
  rw [read_agree h (R := UInt64.ofNat r) (C := UInt64.ofNat c)
    (by rw [toNat_ofNat_lt hlt]; omega) (by rw [toNat_ofNat_lt hlt]; omega) hd
    (by rwa [toNat_ofNat_lt hc])]

theorem rowInvStd_rows {x x' means means' : Array Float} {t d : UInt64} {eps : Float} {i : Nat}
    (ht : t.toNat < 2 ^ 32) (hd : d.toNat < 2 ^ 32) (h : RowsAgree d.toNat i x x')
    (hm : RowsAgree 1 i means means') :
    RowsAgree 1 i (rowInvStd x means t d eps) (rowInvStd x' means' t d eps) := by
  unfold rowInvStd
  refine rows_of_build fun r hr hlt => ?_
  have hR := toNat_ofNat_lt hlt
  congr 4
  refine loop_congr fun c hc acc => ?_
  rw [read_agree h (R := UInt64.ofNat r) (C := UInt64.ofNat c) (by omega) (by omega) hd
    (by rwa [toNat_ofNat_lt hc]), hR, hm r (by omega)]

theorem normalizeRows_rows {x x' means means' inv inv' g b : Array Float} {t d : UInt64}
    {i : Nat} (ht : t.toNat < 2 ^ 32) (hd : d.toNat < 2 ^ 32) (h : RowsAgree d.toNat i x x')
    (hm : RowsAgree 1 i means means') (hv : RowsAgree 1 i inv inv') :
    RowsAgree d.toNat i (normalizeRows x means inv g b t d)
      (normalizeRows x' means' inv' g b t d) := by
  unfold normalizeRows
  refine rows_of_build fun e he hlt => ?_
  obtain ⟨hE, hRow, -, hri, -, -⟩ := element_facts ht hd he hlt
  rw [hE, hRow, h e he, hm _ (by omega), hv _ (by omega)]

theorem layerNormRows_rows {x x' g b : Array Float} {t d : UInt64} {eps : Float} {i : Nat}
    (ht : t.toNat < 2 ^ 32) (hd : d.toNat < 2 ^ 32) (h : RowsAgree d.toNat i x x') :
    RowsAgree d.toNat i (layerNormRows x g b t d eps) (layerNormRows x' g b t d eps) :=
  normalizeRows_rows ht hd h (rowMeans_rows ht hd h)
    (rowInvStd_rows ht hd h (rowMeans_rows ht hd h))

theorem add_rows {a a' b b' : Array Float} {w i : Nat} (hs : a.size = a'.size)
    (ha : RowsAgree w i a a') (hb : RowsAgree w i b b') :
    RowsAgree w i (add a b) (add a' b') := by
  unfold add
  rw [hs]
  refine rows_of_build fun m hm hlt => ?_
  rw [toNat_ofNat_lt hlt, ha m hm, hb m hm]

theorem geluArray_rows {a a' : Array Float} {w i : Nat} (hs : a.size = a'.size)
    (h : RowsAgree w i a a') : RowsAgree w i (geluArray a) (geluArray a') := by
  unfold geluArray
  rw [hs]
  refine rows_of_build fun m hm hlt => ?_
  rw [toNat_ofNat_lt hlt, h m hm]

theorem mlp_rows {h h' wfc bfc wproj bproj : Array Float} {t d f : UInt64} {i : Nat}
    (ht : t.toNat < 2 ^ 32) (hd : d.toNat < 2 ^ 32) (hf : f.toNat < 2 ^ 32)
    (hh : RowsAgree d.toNat i h h') :
    RowsAgree d.toNat i (mlp h wfc bfc wproj bproj t d f) (mlp h' wfc bfc wproj bproj t d f) :=
  linear_rows ht hf hd (geluArray_rows (by simp [linear, LeanExe.build])
    (linear_rows (w := wfc) (b := bfc) ht hd hf hh))

theorem embed_rows {tokens tokens' : Array UInt64} {wte wpe : Array Float} {t d : UInt64}
    {i : Nat} (ht : t.toNat < 2 ^ 32) (hd : d.toNat < 2 ^ 32) (h : RowsAgree 1 i tokens tokens') :
    RowsAgree d.toNat i (embed tokens wte wpe t d) (embed tokens' wte wpe t d) := by
  unfold embed
  refine rows_of_build fun e he hlt => ?_
  obtain ⟨-, hRow, -, hri, -, -⟩ := element_facts ht hd he hlt
  rw [hRow, h _ (by omega)]

theorem matMulT_rows {a a' b : Array Float} {n k m : UInt64} {i : Nat} (hn : n.toNat < 2 ^ 32)
    (hk : k.toNat < 2 ^ 32) (hm : m.toNat < 2 ^ 32) (h : RowsAgree k.toNat i a a') :
    RowsAgree m.toNat i (matMulT a b n k m) (matMulT a' b n k m) := by
  unfold matMulT
  refine rows_of_build fun e he hlt => loop_congr fun c hc acc => ?_
  obtain ⟨-, hRow, -, hri, hrn, -⟩ := element_facts hn hm he hlt
  rw [read_agree h (R := UInt64.ofNat e / m) (C := UInt64.ofNat c) (by omega) (by omega) hk
    (by rwa [toNat_ofNat_lt hc])]

/-- Row `i` of `attention` depends only on rows `0` to `i` of `x`. -/
theorem attention_causal {x x' wq bq wk bk wv bv wo bo : Array Float} {t nh dh : UInt64} {i : Nat}
    (ht : t.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hx : RowsAgree (nh * dh).toNat i x x') :
    RowsAgree (nh * dh).toNat i (attention x wq bq wk bk wv bv wo bo t nh dh)
      (attention x' wq bq wk bk wv bv wo bo t nh dh) := by
  have ht32 : t.toNat < 2 ^ 32 := by omega
  have hnd := small_mul hn hdh
  by_cases hn0 : nh.toNat = 0
  · intro m hm
    rw [mul_toNat (by omega) (by omega), hn0] at hm
    simp at hm
  have hq := linear_rows (w := wq) (b := bq) ht32 hnd hnd hx
  have hk := linear_rows (w := wk) (b := bk) ht32 hnd hnd hx
  have hv := linear_rows (w := wv) (b := bv) ht32 hnd hnd hx
  have hs := maskedScores_rows (scale := 1.0 / dh.toFloat.sqrt) ht hn hdh hq hk
  rw [mul_toNat (by omega) ht32] at hs
  have hp := RowsAgree.join (Nat.pos_of_ne_zero hn0)
    (softmaxRows_rows (small_mul ht hn) ht32 (RowsAgree.split (Nat.pos_of_ne_zero hn0) hs))
  rw [← mul_toNat (by omega) ht32] at hp
  exact linear_rows ht32 hnd hnd (causalMatMul_rows ht hn hdh hp hv)

/-- Row `i` of `block` depends only on rows `0` to `i` of `x`, for inputs of equal
length. -/
theorem block_causal {x x' g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float}
    {t nh dh f : UInt64}
    {eps : Float} {i : Nat} (ht : t.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16)
    (hdh : dh.toNat < 2 ^ 16) (hf : f.toNat < 2 ^ 32) (hs : x.size = x'.size)
    (hx : RowsAgree (nh * dh).toNat i x x') :
    RowsAgree (nh * dh).toNat i
      (block x g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj t nh dh f eps)
      (block x' g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj t nh dh f eps) := by
  have ht32 : t.toNat < 2 ^ 32 := by omega
  have hnd := small_mul hn hdh
  have hr := add_rows hs hx (attention_causal (wq := wq) (bq := bq) (wk := wk) (bk := bk)
    (wv := wv) (bv := bv) (wo := wo) (bo := bo) ht hn hdh
    (layerNormRows_rows (g := g1) (b := b1) (eps := eps) ht32 hnd hx))
  exact add_rows (by simp [add, LeanExe.build, hs]) hr
    (mlp_rows (wfc := wfc) (bfc := bfc) (wproj := wproj) (bproj := bproj) ht32 hnd hf
      (layerNormRows_rows ht32 hnd hr))

/-- Row `i` of `blockAt` depends only on rows `0` to `i` of `x`, for inputs of equal
length. -/
theorem blockAt_causal {x x' g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float}
    {l t nh dh f : UInt64} {eps : Float} {i : Nat} (ht : t.toNat < 2 ^ 16)
    (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16) (hf : f.toNat < 2 ^ 32)
    (hs : x.size = x'.size) (hx : RowsAgree (nh * dh).toNat i x x') :
    RowsAgree (nh * dh).toNat i
      (blockAt x g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj l t nh dh f eps)
      (blockAt x' g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj l t nh dh f eps) :=
  block_causal ht hn hdh hf hs hx

/-- Row `i` of `forward`, the scores at position `i`, depends only on tokens `0` to `i`. -/
theorem forward_causal {tokens tokens' : Array UInt64}
    {wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj gf bf : Array Float}
    {layers t nh dh f vocab : UInt64} {eps : Float} {i : Nat} (ht : t.toNat < 2 ^ 16)
    (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16) (hf : f.toNat < 2 ^ 32)
    (hv : vocab.toNat < 2 ^ 32) (h : RowsAgree 1 i tokens tokens') :
    RowsAgree vocab.toNat i
      (forward tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj gf bf
        layers t nh dh f vocab eps)
      (forward tokens' wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj gf bf
        layers t nh dh f vocab eps) := by
  have ht32 : t.toNat < 2 ^ 32 := by omega
  have hnd := small_mul hn hdh
  unfold forward
  exact matMulT_rows ht32 hnd hv (layerNormRows_rows ht32 hnd
    (loop_rows (fun _ _ _ hs hx => ⟨by simp [blockAt, block, add, LeanExe.build, hs],
        blockAt_causal ht hn hdh hf hs hx⟩)
      (by simp [embed, LeanExe.build]) (embed_rows ht32 hnd h)))

end Project.Gpt.Causal
