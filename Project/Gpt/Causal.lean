import LeanExe.Examples.Gpt
import Mathlib.Tactic
import Project.IR.Combinators

/-! Row `i` of `forward`'s scores, and of each layer's input inside it, depends only on
tokens `0` to `i`, whatever the number of tokens.  The lemmas compare a run on `t` tokens
with a run on `t'` tokens, both above `i`; `forward_causal` is the case `t = t'`, for any
`i`.  The theorems concern the Lean definitions; `Implements` carries them to the bytes.
The bounds on the dimensions (`t`, `nh`, and `dh` below `2 ^ 16`; `f` and `vocab` below
`2 ^ 32`) exclude overflow in the `UInt64` index arithmetic. -/

namespace Project.Gpt.Causal

open Project.IR (loop_congr build_get build_get_out)

open LeanExe.Examples.Gpt

/-- Rows `0` to `i` of `a` and `b`, in rows of `w` elements stored in order, are equal. -/
def RowsAgree {α : Type} [Inhabited α] (w i : Nat) (a b : Array α) : Prop :=
  ∀ m, m < (i + 1) * w → a[m]! = b[m]!

/-- The attention scores of positions `0` to `i` agree on the keys each position sees:
`a` and `b` hold rows of `nh` blocks of `t` and `t'` scores, and score `j` of block `r`
is equal in both for `j` up to the block's position `r / nh`. -/
def ScoresAgree (t t' nh i : Nat) (a b : Array Float) : Prop :=
  ∀ r j, r < (i + 1) * nh → j ≤ r / nh → a[r * t + j]! = b[r * t' + j]!

/-- Two token counts above `i` and below `2 ^ 16`. -/
structure Lengths (i : Nat) (t t' : UInt64) : Prop where
  lt : i < t.toNat
  lt' : i < t'.toNat
  small : t.toNat < 2 ^ 16
  small' : t'.toNat < 2 ^ 16

/-- A loop whose steps keep the sizes `S` and `S'` and rows `0` to `i` in agreement keeps
them after any number of steps. -/
theorem fold_rows {s s' : Array Float} {step step' : UInt64 → Array Float → Array Float}
    {w i S S' : Nat}
    (hStep : ∀ l x x', x.size = S → x'.size = S' → RowsAgree w i x x' →
      (step l x).size = S ∧ (step' l x').size = S' ∧ RowsAgree w i (step l x) (step' l x'))
    (hs : s.size = S) (hs' : s'.size = S') (h : RowsAgree w i s s') (k : Nat) :
    (Nat.fold k (fun j _ x => step (UInt64.ofNat j) x) s).size = S ∧
      (Nat.fold k (fun j _ x => step' (UInt64.ofNat j) x) s').size = S' ∧
      RowsAgree w i (Nat.fold k (fun j _ x => step (UInt64.ofNat j) x) s)
        (Nat.fold k (fun j _ x => step' (UInt64.ofNat j) x) s') := by
  induction k with
  | zero => exact ⟨hs, hs', h⟩
  | succ k ih =>
      simp only [Nat.fold_succ]
      exact hStep _ _ _ ih.1 ih.2.1 ih.2.2

theorem rows_of_build {α : Type} [Inhabited α] {n n' : UInt64} {f g : UInt64 → α} {w i : Nat}
    (hn : (i + 1) * w ≤ n.toNat) (hn' : (i + 1) * w ≤ n'.toNat)
    (h : ∀ m, m < (i + 1) * w → f (UInt64.ofNat m) = g (UInt64.ofNat m)) :
    RowsAgree w i (LeanExe.build n f) (LeanExe.build n' g) := fun m hm => by
  rw [build_get (by omega), build_get (by omega), h m hm]

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

theorem rows_le {n w : UInt64} {i : Nat} (hn : n.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32)
    (hi : i < n.toNat) : (i + 1) * w.toNat ≤ (n * w).toNat := by
  rw [mul_toNat hn hw]
  exact Nat.mul_le_mul_right _ hi

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

theorem embed_rows {tokens tokens' : Array UInt64} {wte wpe : Array Float} {t t' d : UInt64}
    {i : Nat} (hT : Lengths i t t') (hd : d.toNat < 2 ^ 32) (h : RowsAgree 1 i tokens tokens') :
    RowsAgree d.toNat i (embed tokens wte wpe t d) (embed tokens' wte wpe t' d) := by
  have ht := hT.small
  have ht' := hT.small'
  have hr := rows_le (n := t) (by omega) hd hT.lt
  unfold embed
  refine rows_of_build hr (rows_le (by omega) hd hT.lt') fun e he => ?_
  obtain ⟨-, hRow, -, hri, -, -⟩ := element_facts (n := t) (by omega) hd he (by omega)
  rw [hRow, h _ (by omega)]

theorem linear_rows {x x' w b : Array Float} {l t t' k m : UInt64} {i : Nat} (hT : Lengths i t t')
    (hk : k.toNat < 2 ^ 32) (hm : m.toNat < 2 ^ 32) (h : RowsAgree k.toNat i x x') :
    RowsAgree m.toNat i (linear x w b l t k m) (linear x' w b l t' k m) := by
  have ht := hT.small
  have ht' := hT.small'
  have hi := hT.lt
  have hr := rows_le (n := t) (by omega) hm hT.lt
  unfold linear
  refine rows_of_build hr (rows_le (by omega) hm hT.lt') fun e he => ?_
  obtain ⟨-, hRow, -, hri, -, -⟩ := element_facts (n := t) (by omega) hm he (by omega)
  congr 1
  refine loop_congr fun c hc acc => ?_
  rw [read_agree h (R := UInt64.ofNat e / m) (C := UInt64.ofNat c) (by omega) (by omega) hk
    (by rwa [toNat_ofNat_lt hc])]

theorem rowMeans_rows {x x' : Array Float} {t t' d : UInt64} {i : Nat} (hT : Lengths i t t')
    (hd : d.toNat < 2 ^ 32) (h : RowsAgree d.toNat i x x') :
    RowsAgree 1 i (rowMeans x t d) (rowMeans x' t' d) := by
  have ht := hT.small
  have hi := hT.lt
  have hi' := hT.lt'
  unfold rowMeans
  refine rows_of_build (by omega) (by omega) fun r hr => ?_
  have hR : (UInt64.ofNat r).toNat = r := toNat_ofNat_lt (n := t) (by omega)
  congr 1
  refine loop_congr fun c hc acc => ?_
  rw [read_agree h (R := UInt64.ofNat r) (C := UInt64.ofNat c) (by omega) (by omega) hd
    (by rwa [toNat_ofNat_lt hc])]

theorem rowInvStd_rows {x x' means means' : Array Float} {t t' d : UInt64} {eps : Float} {i : Nat}
    (hT : Lengths i t t') (hd : d.toNat < 2 ^ 32) (h : RowsAgree d.toNat i x x')
    (hm : RowsAgree 1 i means means') :
    RowsAgree 1 i (rowInvStd x means t d eps) (rowInvStd x' means' t' d eps) := by
  have ht := hT.small
  have hi := hT.lt
  have hi' := hT.lt'
  unfold rowInvStd
  refine rows_of_build (by omega) (by omega) fun r hr => ?_
  have hR : (UInt64.ofNat r).toNat = r := toNat_ofNat_lt (n := t) (by omega)
  congr 4
  refine loop_congr fun c hc acc => ?_
  rw [read_agree h (R := UInt64.ofNat r) (C := UInt64.ofNat c) (by omega) (by omega) hd
    (by rwa [toNat_ofNat_lt hc]), hR, hm r (by omega)]

theorem normalizeRows_rows {x x' means means' inv inv' g b : Array Float} {l t t' d : UInt64}
    {i : Nat} (hT : Lengths i t t') (hd : d.toNat < 2 ^ 32) (h : RowsAgree d.toNat i x x')
    (hm : RowsAgree 1 i means means') (hv : RowsAgree 1 i inv inv') :
    RowsAgree d.toNat i (normalizeRows x means inv g b l t d)
      (normalizeRows x' means' inv' g b l t' d) := by
  have ht := hT.small
  have ht' := hT.small'
  have hr := rows_le (n := t) (by omega) hd hT.lt
  unfold normalizeRows
  refine rows_of_build hr (rows_le (by omega) hd hT.lt') fun e he => ?_
  obtain ⟨hE, hRow, -, hri, -, -⟩ := element_facts (n := t) (by omega) hd he (by omega)
  rw [hE, hRow, h e he, hm _ (by omega), hv _ (by omega)]

theorem layerNormRows_rows {x x' g b : Array Float} {l t t' d : UInt64} {eps : Float} {i : Nat}
    (hT : Lengths i t t') (hd : d.toNat < 2 ^ 32) (h : RowsAgree d.toNat i x x') :
    RowsAgree d.toNat i (layerNormRows x g b l t d eps) (layerNormRows x' g b l t' d eps) :=
  normalizeRows_rows hT hd h (rowMeans_rows hT hd h)
    (rowInvStd_rows hT hd h (rowMeans_rows hT hd h))

theorem add_size {a b : Array Float} (h : a.size < 2 ^ 64) : (add a b).size = a.size := by
  simp [add, LeanExe.build]
  omega

theorem add_rows {a a' b b' : Array Float} {w i : Nat} (ha : (i + 1) * w ≤ a.size)
    (ha' : (i + 1) * w ≤ a'.size) (hs : a.size < 2 ^ 64) (hs' : a'.size < 2 ^ 64)
    (hA : RowsAgree w i a a') (hB : RowsAgree w i b b') : RowsAgree w i (add a b) (add a' b') := by
  have hn : a.size.toUInt64.toNat = a.size := UInt64.toNat_ofNat_of_lt' hs
  have hn' : a'.size.toUInt64.toNat = a'.size := UInt64.toNat_ofNat_of_lt' hs'
  unfold add
  refine rows_of_build (by rw [hn]; exact ha) (by rw [hn']; exact ha') fun m hm => ?_
  have hM : (UInt64.ofNat m).toNat = m := toNat_ofNat_lt (n := a.size.toUInt64) (by omega)
  rw [hM, hA m hm, hB m hm]

theorem geluArray_rows {a a' : Array Float} {w i : Nat} (ha : (i + 1) * w ≤ a.size)
    (ha' : (i + 1) * w ≤ a'.size) (hs : a.size < 2 ^ 64) (hs' : a'.size < 2 ^ 64)
    (h : RowsAgree w i a a') : RowsAgree w i (geluArray a) (geluArray a') := by
  have hn : a.size.toUInt64.toNat = a.size := UInt64.toNat_ofNat_of_lt' hs
  have hn' : a'.size.toUInt64.toNat = a'.size := UInt64.toNat_ofNat_of_lt' hs'
  unfold geluArray
  refine rows_of_build (by rw [hn]; exact ha) (by rw [hn']; exact ha') fun m hm => ?_
  have hM : (UInt64.ofNat m).toNat = m := toNat_ofNat_lt (n := a.size.toUInt64) (by omega)
  rw [hM, h m hm]

theorem mlp_rows {h h' wfc bfc wproj bproj : Array Float} {l t t' d f : UInt64} {i : Nat}
    (hT : Lengths i t t') (hd : d.toNat < 2 ^ 32) (hf : f.toNat < 2 ^ 32)
    (hh : RowsAgree d.toNat i h h') :
    RowsAgree d.toNat i (mlp h wfc bfc wproj bproj l t d f)
      (mlp h' wfc bfc wproj bproj l t' d f) := by
  have ht := hT.small
  have ht' := hT.small'
  have hs : (linear h wfc bfc l t d f).size = (t * f).toNat := by simp [linear, LeanExe.build]
  have hs' : (linear h' wfc bfc l t' d f).size = (t' * f).toNat := by
    simp [linear, LeanExe.build]
  exact linear_rows hT hf hd (geluArray_rows (by rw [hs]; exact rows_le (by omega) hf hT.lt)
    (by rw [hs']; exact rows_le (by omega) hf hT.lt') (by rw [hs]; exact UInt64.toNat_lt _)
    (by rw [hs']; exact UInt64.toNat_lt _) (linear_rows (w := wfc) (b := bfc) hT hd hf hh))

/-- Score `J` of block `H` of query row `P`, as `maskedScores` computes it. -/
def scoreAt (q k : Array Float) (nh dh : UInt64) (scale : Float) (P H J : UInt64) : Float :=
  LeanExe.loop (if J ≤ P then dh else 0) 0.0
    (fun c acc => acc + q[(P * (nh * dh) + (H * dh + c)).toNat]! *
      k[(J * (nh * dh) + (H * dh + c)).toNat]!) * scale

/-- Score `j` of block `r` of `maskedScores`, at `r · t + j`, is that of query row `r / nh`
and head `r % nh`, whatever `t`. -/
theorem maskedScores_at {q k : Array Float} {t nh dh : UInt64} {scale : Float} {r j : Nat}
    (ht : t.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hr : r < t.toNat * nh.toNat)
    (hj : j < t.toNat) :
    (maskedScores q k t nh dh scale)[r * t.toNat + j]! = scoreAt q k nh dh scale
      (UInt64.ofNat (r / nh.toNat)) (UInt64.ofNat (r % nh.toNat)) (UInt64.ofNat j) := by
  have hn0 : 0 < nh.toNat := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hr
  have ht0 : 0 < t.toNat := by omega
  have hNT : (nh * t).toNat = nh.toNat * t.toNat := mul_toNat (by omega) (by omega)
  have hE : r * t.toNat + j < (t * nh * t).toNat := by
    rw [mul_toNat (small_mul ht hn) (by omega), mul_toNat (by omega) (by omega)]
    calc r * t.toNat + j < (r + 1) * t.toNat := by rw [Nat.succ_mul]; omega
      _ ≤ t.toNat * nh.toNat * t.toNat := Nat.mul_le_mul_right _ hr
  have hE64 : r * t.toNat + j < 2 ^ 64 := by have := UInt64.toNat_lt (t * nh * t); omega
  have hdiv : (r * t.toNat + j) / t.toNat = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ ht0, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (r * t.toNat + j) % t.toNat = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have hq : r / nh.toNat ≤ r := Nat.div_le_self _ _
  have hh : r % nh.toNat < nh.toNat := Nat.mod_lt _ hn0
  have hPt : r / nh.toNat < t.toNat := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  have hP : (UInt64.ofNat (r / nh.toNat)).toNat = r / nh.toNat := toNat_ofNat_lt hPt
  have hH : (UInt64.ofNat (r % nh.toNat)).toNat = r % nh.toNat := toNat_ofNat_lt (n := nh) hh
  have hJ : (UInt64.ofNat j).toNat = j := toNat_ofNat_lt hj
  have hEn : (UInt64.ofNat (r * t.toNat + j)).toNat = r * t.toNat + j := toNat_ofNat_lt hE
  unfold maskedScores
  rw [build_get hE]
  show scoreAt q k nh dh scale _ _ _ = _
  congr 1
  · apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_div, hEn, hNT, Nat.mul_comm nh.toNat t.toNat, ← Nat.div_div_eq_div_mul,
      hdiv, hP]
  · apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod, UInt64.toNat_div, hEn, hdiv, hH]
  · apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod, hEn, hmod, hJ]

theorem maskedScores_scores {q q' k k' : Array Float} {t t' nh dh : UInt64} {scale : Float}
    {i : Nat} (hT : Lengths i t t') (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hq : RowsAgree (nh * dh).toNat i q q') (hk : RowsAgree (nh * dh).toNat i k k') :
    ScoresAgree t.toNat t'.toNat nh.toNat i (maskedScores q k t nh dh scale)
      (maskedScores q' k' t' nh dh scale) := by
  intro r j hr hj
  have ht := hT.small
  have ht' := hT.small'
  have hn0 : 0 < nh.toNat := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hr
  have hpos : r / nh.toNat ≤ i := Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm]))
  have hrt : r < t.toNat * nh.toNat := lt_of_lt_of_le hr (Nat.mul_le_mul_right _ hT.lt)
  have hrt' : r < t'.toNat * nh.toNat := lt_of_lt_of_le hr (Nat.mul_le_mul_right _ hT.lt')
  have hi := hT.lt
  have hi' := hT.lt'
  rw [maskedScores_at ht hn hrt (by omega), maskedScores_at ht' hn hrt' (by omega)]
  have hnd := small_mul hn hdh
  have hP : (UInt64.ofNat (r / nh.toNat)).toNat = r / nh.toNat :=
    toNat_ofNat_lt (n := t) (by omega)
  have hHlt : r % nh.toNat < nh.toNat := Nat.mod_lt _ hn0
  have hH : (UInt64.ofNat (r % nh.toNat)).toNat = r % nh.toNat := toNat_ofNat_lt (n := nh) hHlt
  have hJ : (UInt64.ofNat j).toNat = j := toNat_ofNat_lt (n := t) (by omega)
  unfold scoreAt
  congr 1
  refine loop_congr fun c hc acc => ?_
  split at hc
  · have hc' : (UInt64.ofNat c).toNat < dh.toNat := by rwa [toNat_ofNat_lt hc]
    have hC : (UInt64.ofNat (r % nh.toNat) * dh + UInt64.ofNat c).toNat < (nh * dh).toNat := by
      rw [index_toNat (by rw [hH]; omega) (by omega) hc', hH, mul_toNat (by omega) (by omega)]
      calc r % nh.toNat * dh.toNat + (UInt64.ofNat c).toNat
          < (r % nh.toNat + 1) * dh.toNat := by rw [Nat.succ_mul]; omega
        _ ≤ nh.toNat * dh.toNat := Nat.mul_le_mul_right _ hHlt
    rw [read_agree hq (R := UInt64.ofNat (r / nh.toNat))
        (C := UInt64.ofNat (r % nh.toNat) * dh + UInt64.ofNat c) (by omega) (by omega) hnd hC,
      read_agree hk (R := UInt64.ofNat j)
        (C := UInt64.ofNat (r % nh.toNat) * dh + UInt64.ofNat c) (by omega) (by omega) hnd hC]
  · simp at hc

/-- Column `c` read for row `r` of the causal softmax over `t · nh` rows of width `t`: `c`
is at most the row's position `r / nh`. -/
theorem causal_col {t nh : UInt64} {r c : Nat} (ht : t.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16)
    (hlt : r < (t * nh).toNat) (hc : c < (UInt64.ofNat r / nh + 1).toNat) :
    (UInt64.ofNat r).toNat = r ∧ (UInt64.ofNat c).toNat = c ∧ c ≤ r / nh.toNat ∧
      r / nh.toNat < t.toNat := by
  have hR : (UInt64.ofNat r).toNat = r := toNat_ofNat_lt hlt
  rw [mul_toNat (by omega) (by omega)] at hlt
  have hq : r / nh.toNat < t.toNat := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  rw [UInt64.toNat_add, UInt64.toNat_div, hR, UInt64.toNat_one,
    Nat.mod_eq_of_lt (by omega)] at hc
  exact ⟨hR, toNat_ofNat_lt (n := t) (by omega), by omega, hq⟩

/-- The read of column `c` of row `r` in rows of width `t`. -/
theorem row_read {x : Array Float} {t : UInt64} {r c : Nat} (ht : t.toNat < 2 ^ 16)
    (hr : r < 2 ^ 32) (hR : (UInt64.ofNat r).toNat = r) (hC : (UInt64.ofNat c).toNat = c)
    (hc : c < t.toNat) :
    x[(UInt64.ofNat r * t + UInt64.ofNat c).toNat]! = x[r * t.toNat + c]! := by
  rw [index_toNat (by omega) (by omega) (by omega), hR, hC]

theorem rowMax_rows {x x' : Array Float} {t t' nh : UInt64} {i : Nat} (hT : Lengths i t t')
    (hn : nh.toNat < 2 ^ 16) (h : ScoresAgree t.toNat t'.toNat nh.toNat i x x') :
    RowsAgree nh.toNat i (rowMax x t nh) (rowMax x' t' nh) := by
  have ht := hT.small
  have ht' := hT.small'
  have hi := hT.lt
  have hi' := hT.lt'
  have hr := rows_le (n := t) (w := nh) (by omega) (by omega) hT.lt
  have hr' := rows_le (n := t') (w := nh) (by omega) (by omega) hT.lt'
  have hnt := small_mul ht hn
  unfold rowMax
  refine rows_of_build hr hr' fun r hrn => loop_congr fun c hc acc => ?_
  obtain ⟨hR, hC, hcr, -⟩ := causal_col ht hn (by omega) hc
  have hn0 : 0 < nh.toNat := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hrn
  have hpos : r / nh.toNat ≤ i := Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm]))
  rw [row_read ht (by omega) hR hC (by omega), row_read ht' (by omega) hR hC (by omega),
    h r c hrn hcr]

theorem rowSumExp_rows {x x' mx mx' : Array Float} {t t' nh : UInt64} {i : Nat}
    (hT : Lengths i t t') (hn : nh.toNat < 2 ^ 16)
    (h : ScoresAgree t.toNat t'.toNat nh.toNat i x x') (hm : RowsAgree nh.toNat i mx mx') :
    RowsAgree nh.toNat i (rowSumExp x mx t nh) (rowSumExp x' mx' t' nh) := by
  have ht := hT.small
  have ht' := hT.small'
  have hi := hT.lt
  have hi' := hT.lt'
  have hr := rows_le (n := t) (w := nh) (by omega) (by omega) hT.lt
  have hr' := rows_le (n := t') (w := nh) (by omega) (by omega) hT.lt'
  have hnt := small_mul ht hn
  unfold rowSumExp
  refine rows_of_build hr hr' fun r hrn => loop_congr fun c hc acc => ?_
  obtain ⟨hR, hC, hcr, -⟩ := causal_col ht hn (by omega) hc
  have hn0 : 0 < nh.toNat := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hrn
  have hpos : r / nh.toNat ≤ i := Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm]))
  rw [row_read ht (by omega) hR hC (by omega), row_read ht' (by omega) hR hC (by omega),
    h r c hrn hcr, hR, hm r hrn]

/-- Element `j` of row `r` of `softmaxApply` over `t · nh` rows of width `t`. -/
theorem softmaxApply_at {x mx sums : Array Float} {t nh : UInt64} {r j : Nat}
    (ht : t.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hr : r < t.toNat * nh.toNat)
    (hj : j < t.toNat) :
    (softmaxApply x mx sums (t * nh) t)[r * t.toNat + j]! =
      exp (x[r * t.toNat + j]! - mx[r]!) / sums[r]! := by
  have ht0 : 0 < t.toNat := by omega
  have hE : r * t.toNat + j < (t * nh * t).toNat := by
    rw [mul_toNat (small_mul ht hn) (by omega), mul_toNat (by omega) (by omega)]
    calc r * t.toNat + j < (r + 1) * t.toNat := by rw [Nat.succ_mul]; omega
      _ ≤ t.toNat * nh.toNat * t.toNat := Nat.mul_le_mul_right _ hr
  have hE64 : r * t.toNat + j < 2 ^ 64 := by have := UInt64.toNat_lt (t * nh * t); omega
  have hdiv : (r * t.toNat + j) / t.toNat = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ ht0, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hEn : (UInt64.ofNat (r * t.toNat + j)).toNat = r * t.toNat + j := toNat_ofNat_lt hE
  unfold softmaxApply
  rw [build_get hE, UInt64.toNat_div, hEn, hdiv]

theorem softmaxRows_scores {x x' : Array Float} {t t' nh : UInt64} {i : Nat}
    (hT : Lengths i t t') (hn : nh.toNat < 2 ^ 16)
    (h : ScoresAgree t.toNat t'.toNat nh.toNat i x x') :
    ScoresAgree t.toNat t'.toNat nh.toNat i (softmaxRows x t nh) (softmaxRows x' t' nh) := by
  intro r j hr hj
  have ht := hT.small
  have ht' := hT.small'
  have hi := hT.lt
  have hi' := hT.lt'
  have hn0 : 0 < nh.toNat := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hr
  have hpos : r / nh.toNat ≤ i := Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm]))
  have hrt : r < t.toNat * nh.toNat := lt_of_lt_of_le hr (Nat.mul_le_mul_right _ hT.lt)
  have hrt' : r < t'.toNat * nh.toNat := lt_of_lt_of_le hr (Nat.mul_le_mul_right _ hT.lt')
  have hm := rowMax_rows hT hn h
  unfold softmaxRows
  rw [softmaxApply_at ht hn hrt (by omega), softmaxApply_at ht' hn hrt' (by omega), h r j hr hj,
    hm r hr, rowSumExp_rows hT hn h hm r hr]

theorem causalMatMul_rows {p p' v v' : Array Float} {t t' nh dh : UInt64} {i : Nat}
    (hT : Lengths i t t') (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hp : ScoresAgree t.toNat t'.toNat nh.toNat i p p') (hv : RowsAgree (nh * dh).toNat i v v') :
    RowsAgree (nh * dh).toNat i (causalMatMul p v t nh dh) (causalMatMul p' v' t' nh dh) := by
  have ht := hT.small
  have ht' := hT.small'
  have hi := hT.lt
  have hi' := hT.lt'
  have hnd := small_mul hn hdh
  have hr := rows_le (n := t) (by omega) hnd hT.lt
  unfold causalMatMul
  refine rows_of_build hr (rows_le (by omega) hnd hT.lt') fun e he =>
    loop_congr fun j hj acc => ?_
  obtain ⟨-, hRow, hCol, hri, -, hcd⟩ := element_facts (n := t) (by omega) hnd he (by omega)
  have hJ : (UInt64.ofNat j).toNat = j := toNat_ofNat_lt hj
  rw [UInt64.toNat_add, hRow, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)] at hj
  have hHd : (UInt64.ofNat e % (nh * dh) / dh).toNat = e % (nh * dh).toNat / dh.toNat := by
    rw [UInt64.toNat_div, hCol]
  have hND : (nh * dh).toNat = nh.toNat * dh.toNat := mul_toNat (by omega) (by omega)
  have hHlt : e % (nh * dh).toNat / dh.toNat < nh.toNat :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hND]; exact hcd)
  -- Row `e / (nh · dh)` and head `h` read block `row · nh + h` of `p`.
  have hP : ∀ T : UInt64, T.toNat < 2 ^ 16 → j < T.toNat →
      (UInt64.ofNat e / (nh * dh) * (nh * T) +
        (UInt64.ofNat e % (nh * dh) / dh * T + UInt64.ofNat j)).toNat =
        (e / (nh * dh).toNat * nh.toNat + e % (nh * dh).toNat / dh.toNat) * T.toNat + j := by
    intro T hT16 hjT
    have hNT := small_mul hn hT16
    have hC : (UInt64.ofNat e % (nh * dh) / dh * T + UInt64.ofNat j).toNat < (nh * T).toNat := by
      rw [index_toNat (by rw [hHd]; omega) (by omega) (by rw [hJ]; omega), hHd, hJ,
        mul_toNat (a := nh) (b := T) (by omega) (by omega)]
      calc e % (nh * dh).toNat / dh.toNat * T.toNat + j
          < (e % (nh * dh).toNat / dh.toNat + 1) * T.toNat := by rw [Nat.succ_mul]; omega
        _ ≤ nh.toNat * T.toNat := Nat.mul_le_mul_right _ hHlt
    rw [index_toNat (by rw [hRow]; omega) hNT hC, hRow,
      index_toNat (by rw [hHd]; omega) (by omega) (by rw [hJ]; omega), hHd, hJ,
      mul_toNat (a := nh) (b := T) (by omega) (by omega)]
    ring
  have hrow : e / (nh * dh).toNat * nh.toNat + e % (nh * dh).toNat / dh.toNat <
      (i + 1) * nh.toNat := by
    calc e / (nh * dh).toNat * nh.toNat + e % (nh * dh).toNat / dh.toNat
        < (e / (nh * dh).toNat + 1) * nh.toNat := by rw [Nat.succ_mul]; omega
      _ ≤ (i + 1) * nh.toNat := Nat.mul_le_mul_right _ (by omega)
  have hpos : j ≤ (e / (nh * dh).toNat * nh.toNat + e % (nh * dh).toNat / dh.toNat) /
      nh.toNat := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hHlt]
    omega
  rw [hP t ht (by omega), hP t' ht' (by omega), hp _ j hrow hpos,
    read_agree hv (R := UInt64.ofNat j) (C := UInt64.ofNat e % (nh * dh)) (by omega) (by omega)
      hnd (by rwa [hCol])]

theorem matMulT_rows {a a' b : Array Float} {t t' k m : UInt64} {i : Nat} (hT : Lengths i t t')
    (hk : k.toNat < 2 ^ 32) (hm : m.toNat < 2 ^ 32) (h : RowsAgree k.toNat i a a') :
    RowsAgree m.toNat i (matMulT a b t k m) (matMulT a' b t' k m) := by
  have ht := hT.small
  have ht' := hT.small'
  have hi := hT.lt
  have hr := rows_le (n := t) (by omega) hm hT.lt
  unfold matMulT
  refine rows_of_build hr (rows_le (by omega) hm hT.lt') fun e he =>
    loop_congr fun c hc acc => ?_
  obtain ⟨-, hRow, -, hri, -, -⟩ := element_facts (n := t) (by omega) hm he (by omega)
  rw [read_agree h (R := UInt64.ofNat e / m) (C := UInt64.ofNat c) (by omega) (by omega) hk
    (by rwa [toNat_ofNat_lt hc])]

/-- Row `i` of `attention` depends only on rows `0` to `i` of `x`, whatever the number of
rows. -/
theorem attention_rows {x x' wq bq wk bk wv bv wo bo : Array Float} {l t t' nh dh : UInt64}
    {i : Nat} (hT : Lengths i t t') (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hx : RowsAgree (nh * dh).toNat i x x') :
    RowsAgree (nh * dh).toNat i (attention x wq bq wk bk wv bv wo bo l t nh dh)
      (attention x' wq bq wk bk wv bv wo bo l t' nh dh) := by
  have hnd := small_mul hn hdh
  have hq := linear_rows (w := wq) (b := bq) (l := l) hT hnd hnd hx
  have hk := linear_rows (w := wk) (b := bk) (l := l) hT hnd hnd hx
  have hv := linear_rows (w := wv) (b := bv) (l := l) hT hnd hnd hx
  have hs := maskedScores_scores (scale := 1.0 / dh.toFloat.sqrt) hT hn hdh hq hk
  exact linear_rows hT hnd hnd (causalMatMul_rows hT hn hdh (softmaxRows_scores hT hn hs) hv)

theorem block_size {x g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float}
    {l t nh dh f : UInt64} {eps : Float} (h : x.size < 2 ^ 64) :
    (block x g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj l t nh dh f eps).size =
      x.size := by
  unfold block
  rw [add_size (by rw [add_size h]; exact h), add_size h]

/-- Row `i` of `block` depends only on rows `0` to `i` of `x`, whatever the number of
rows. -/
theorem block_rows {x x' g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float}
    {l t t' nh dh f : UInt64} {eps : Float} {i : Nat} (hT : Lengths i t t')
    (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16) (hf : f.toNat < 2 ^ 32)
    (hs : x.size = (t * (nh * dh)).toNat) (hs' : x'.size = (t' * (nh * dh)).toNat)
    (hx : RowsAgree (nh * dh).toNat i x x') :
    RowsAgree (nh * dh).toNat i
      (block x g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj l t nh dh f eps)
      (block x' g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj l t' nh dh f eps) := by
  have ht := hT.small
  have ht' := hT.small'
  have hnd := small_mul hn hdh
  have hx1 : (i + 1) * (nh * dh).toNat ≤ x.size := by rw [hs]; exact rows_le (by omega) hnd hT.lt
  have hx1' : (i + 1) * (nh * dh).toNat ≤ x'.size := by
    rw [hs']; exact rows_le (by omega) hnd hT.lt'
  have hx64 : x.size < 2 ^ 64 := by rw [hs]; exact UInt64.toNat_lt _
  have hx64' : x'.size < 2 ^ 64 := by rw [hs']; exact UInt64.toNat_lt _
  have hr := add_rows hx1 hx1' hx64 hx64' hx (attention_rows (wq := wq) (bq := bq) (wk := wk)
    (bk := bk) (wv := wv) (bv := bv) (wo := wo) (bo := bo) (l := l) hT hn hdh
    (layerNormRows_rows (g := g1) (b := b1) (l := l) (eps := eps) hT hnd hx))
  unfold block
  exact add_rows (by rw [add_size hx64]; exact hx1) (by rw [add_size hx64']; exact hx1')
    (by rw [add_size hx64]; exact hx64) (by rw [add_size hx64']; exact hx64') hr
    (mlp_rows (wfc := wfc) (bfc := bfc) (wproj := wproj) (bproj := bproj) (l := l) hT hnd hf
      (layerNormRows_rows hT hnd hr))

/-- The inputs of the layers of `forward` on `t` and `t'` tokens keep `t` and `t'` rows,
and rows `0` to `i` of each depend only on tokens `0` to `i`. -/
theorem layers_rows {tokens tokens' : Array UInt64}
    {wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float}
    {t t' nh dh f : UInt64} {eps : Float} {i : Nat} (hT : Lengths i t t')
    (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16) (hf : f.toNat < 2 ^ 32)
    (h : RowsAgree 1 i tokens tokens') (k : Nat) :
    (Nat.fold k (fun j _ x => block x g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj
      (UInt64.ofNat j) t nh dh f eps) (embed tokens wte wpe t (nh * dh))).size =
        (t * (nh * dh)).toNat ∧
      (Nat.fold k (fun j _ x => block x g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj
        (UInt64.ofNat j) t' nh dh f eps) (embed tokens' wte wpe t' (nh * dh))).size =
        (t' * (nh * dh)).toNat ∧
      RowsAgree (nh * dh).toNat i
        (Nat.fold k (fun j _ x => block x g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj
          bproj (UInt64.ofNat j) t nh dh f eps) (embed tokens wte wpe t (nh * dh)))
        (Nat.fold k (fun j _ x => block x g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj
          bproj (UInt64.ofNat j) t' nh dh f eps) (embed tokens' wte wpe t' (nh * dh))) := by
  have hnd := small_mul hn hdh
  exact fold_rows
    (step := fun l x => block x g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj l t nh dh
      f eps)
    (step' := fun l x => block x g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj l t' nh
      dh f eps) (fun _ x x' hs hs' hx =>
      ⟨by rw [block_size (by rw [hs]; exact UInt64.toNat_lt _), hs],
        by rw [block_size (by rw [hs']; exact UInt64.toNat_lt _), hs'],
        block_rows hT hn hdh hf hs hs' hx⟩)
    (by simp [embed, LeanExe.build]) (by simp [embed, LeanExe.build]) (embed_rows hT hnd h) k

/-- Row `i` of `forward`, the scores at position `i`, depends only on tokens `0` to `i`,
whatever the number of tokens. -/
theorem forward_prefix {tokens tokens' : Array UInt64}
    {wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj gf bf : Array Float}
    {layers t t' nh dh f vocab : UInt64} {eps : Float} {i : Nat} (hT : Lengths i t t')
    (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16) (hf : f.toNat < 2 ^ 32)
    (hv : vocab.toNat < 2 ^ 32) (h : RowsAgree 1 i tokens tokens') :
    RowsAgree vocab.toNat i
      (forward tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj gf bf
        layers t nh dh f vocab eps)
      (forward tokens' wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj gf bf
        layers t' nh dh f vocab eps) := by
  have hnd := small_mul hn hdh
  exact matMulT_rows hT hnd hv (layerNormRows_rows hT hnd
    (layers_rows (wte := wte) (wpe := wpe) (g1 := g1) (b1 := b1) (wq := wq) (bq := bq) (wk := wk)
      (bk := bk) (wv := wv) (bv := bv) (wo := wo) (bo := bo) (g2 := g2) (b2 := b2) (wfc := wfc)
      (bfc := bfc) (wproj := wproj) (bproj := bproj) (eps := eps) hT hn hdh hf h
      layers.toNat).2.2)

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
  by_cases hi : i < t.toNat
  · exact forward_prefix ⟨hi, hi, ht, ht⟩ hn hdh hf hv h
  intro m hm
  by_cases hmt : m < (t * vocab).toNat
  · rw [mul_toNat (by omega) hv] at hmt
    have ht0 : 0 < t.toNat := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hmt
    refine forward_prefix (i := t.toNat - 1) ⟨by omega, by omega, ht, ht⟩ hn hdh hf hv
      (fun m hm => h m (by omega)) m ?_
    rwa [Nat.sub_add_cancel ht0]
  · show (matMulT _ wte t (nh * dh) vocab)[m]! = (matMulT _ wte t (nh * dh) vocab)[m]!
    unfold matMulT
    rw [build_get_out hmt, build_get_out hmt]

end Project.Gpt.Causal
