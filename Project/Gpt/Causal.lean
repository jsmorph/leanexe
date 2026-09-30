import LeanExe.Examples.Gpt
import Mathlib.Tactic

/-! Row `i` of `attention` and of `block` depends only on rows `0` to `i` of the input.
The theorems concern the Lean definitions; `Implements` carries them to the bytes.
Dimensions below `2 ^ 32` exclude overflow in the `UInt64` index arithmetic. -/

namespace Project.Gpt.Causal

open LeanExe.Examples.Gpt

/-- Rows `0` to `i` of `a` and `b`, in rows of `w` elements stored in order, are equal. -/
def RowsAgree (w i : Nat) (a b : Array Float) : Prop :=
  ∀ m, m < (i + 1) * w → a[m]! = b[m]!

theorem loop_congr {α : Type} {n : UInt64} {init : α} {f g : UInt64 → α → α}
    (h : ∀ k, k < n.toNat → ∀ acc, f (UInt64.ofNat k) acc = g (UInt64.ofNat k) acc) :
    LeanExe.loop n init f = LeanExe.loop n init g := by
  unfold LeanExe.loop
  congr 1
  funext k hk acc
  exact h k hk acc

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

theorem maskedScores_rows {q q' k k' : Array Float} {t d : UInt64} {scale : Float} {i : Nat}
    (ht : t.toNat < 2 ^ 32) (hd : d.toNat < 2 ^ 32) (hq : RowsAgree d.toNat i q q')
    (hk : RowsAgree d.toNat i k k') :
    RowsAgree t.toNat i (maskedScores q k t d scale) (maskedScores q' k' t d scale) := by
  unfold maskedScores
  refine rows_of_build fun e he hlt => ?_
  obtain ⟨-, hRow, hCol, hri, hrt, hct⟩ := element_facts ht ht he hlt
  congr 2
  refine loop_congr fun c hc acc => ?_
  split at hc
  · rename_i hle
    rw [UInt64.le_iff_toNat_le, hRow, hCol] at hle
    have hC : (UInt64.ofNat c).toNat < d.toNat := by rwa [toNat_ofNat_lt hc]
    rw [read_agree hq (R := UInt64.ofNat e / t) (C := UInt64.ofNat c) (by omega) (by omega) hd hC,
      read_agree hk (R := UInt64.ofNat e % t) (C := UInt64.ofNat c) (by omega) (by omega) hd hC]
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

theorem causalMatMul_rows {p p' v v' : Array Float} {t d : UInt64} {i : Nat}
    (ht : t.toNat < 2 ^ 32) (hd : d.toNat < 2 ^ 32) (hp : RowsAgree t.toNat i p p')
    (hv : RowsAgree d.toNat i v v') :
    RowsAgree d.toNat i (causalMatMul p v t d) (causalMatMul p' v' t d) := by
  unfold causalMatMul
  refine rows_of_build fun e he hlt => loop_congr fun j hj acc => ?_
  obtain ⟨-, hRow, hCol, hri, hrt, hcd⟩ := element_facts ht hd he hlt
  have hJ : (UInt64.ofNat j).toNat = j := toNat_ofNat_lt hj
  rw [UInt64.toNat_add, hRow, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)] at hj
  rw [read_agree hp (R := UInt64.ofNat e / d) (C := UInt64.ofNat j) (by omega) (by omega) ht
      (by omega),
    read_agree hv (R := UInt64.ofNat j) (C := UInt64.ofNat e % d) (by omega) (by omega) hd
      (by omega)]

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

theorem mlp_rows {h h' w1 w2 : Array Float} {t d f : UInt64} {i : Nat} (ht : t.toNat < 2 ^ 32)
    (hd : d.toNat < 2 ^ 32) (hf : f.toNat < 2 ^ 32) (hh : RowsAgree d.toNat i h h') :
    RowsAgree d.toNat i (mlp h w1 w2 t d f) (mlp h' w1 w2 t d f) :=
  matMul_rows ht hf hd (geluArray_rows (by simp [matMul, LeanExe.build])
    (matMul_rows (b := w1) ht hd hf hh))

/-- Row `i` of `attention` depends only on rows `0` to `i` of `x`. -/
theorem attention_causal {x x' wq wk wv wo : Array Float} {t d : UInt64} {i : Nat}
    (ht : t.toNat < 2 ^ 32) (hd : d.toNat < 2 ^ 32) (hx : RowsAgree d.toNat i x x') :
    RowsAgree d.toNat i (attention x wq wk wv wo t d) (attention x' wq wk wv wo t d) :=
  matMul_rows ht hd hd (causalMatMul_rows ht hd
    (softmaxRows_rows ht ht (maskedScores_rows ht hd (matMul_rows ht hd hd hx)
      (matMul_rows ht hd hd hx)))
    (matMul_rows ht hd hd hx))

/-- Row `i` of `block` depends only on rows `0` to `i` of `x`, for inputs of equal
length. -/
theorem block_causal {x x' g1 b1 wq wk wv wo g2 b2 w1 w2 : Array Float} {t d f : UInt64}
    {eps : Float} {i : Nat} (ht : t.toNat < 2 ^ 32) (hd : d.toNat < 2 ^ 32)
    (hf : f.toNat < 2 ^ 32) (hs : x.size = x'.size) (hx : RowsAgree d.toNat i x x') :
    RowsAgree d.toNat i (block x g1 b1 wq wk wv wo g2 b2 w1 w2 t d f eps)
      (block x' g1 b1 wq wk wv wo g2 b2 w1 w2 t d f eps) := by
  have hr := add_rows hs hx (attention_causal (wq := wq) (wk := wk) (wv := wv) (wo := wo) ht hd
    (layerNormRows_rows (g := g1) (b := b1) (eps := eps) ht hd hx))
  exact add_rows (by simp [add, LeanExe.build, hs]) hr
    (mlp_rows (w1 := w1) (w2 := w2) ht hd hf (layerNormRows_rows ht hd hr))

end Project.Gpt.Causal
