import Project.Gpt.Causal

/-! The cached step computes `forward`'s rows exactly.  `step` run on tokens `0` to `p`
from an empty cache, followed by `scores`, gives row `p` of `forward`'s scores bit for
bit, for any number of tokens above `p`.  Each kernel that `layerStep` runs on one row
performs the operations of the corresponding row of `block`, in the same order; the
cache holds, for each earlier position, the row of the last layer's output and the
rows of each layer's keys and values.  The theorems concern the Lean definitions;
`Implements` carries them to the bytes. -/

namespace Project.Gpt.Exact

open LeanExe.Examples.Gpt Project.Gpt.Causal

/-- `x` holds row `p` of `X`, in rows of `w` elements. -/
def RowIs (w p : Nat) (x X : Array Float) : Prop :=
  ∀ c, c < w → x[c]! = X[p * w + c]!

theorem row_div {n m : UInt64} {P c : Nat} (hc : c < m.toNat) (hlt : P * m.toNat + c < n.toNat) :
    UInt64.ofNat (P * m.toNat + c) / m = UInt64.ofNat P ∧
      UInt64.ofNat (P * m.toNat + c) % m = UInt64.ofNat c := by
  have hm0 : 0 < m.toNat := by omega
  have hE : (UInt64.ofNat (P * m.toNat + c)).toNat = P * m.toNat + c := toNat_ofNat_lt hlt
  have hPle : P ≤ P * m.toNat := Nat.le_mul_of_pos_right _ hm0
  have hP : (UInt64.ofNat P).toNat = P := toNat_ofNat_lt (n := n) (by omega)
  have hC : (UInt64.ofNat c).toNat = c := toNat_ofNat_lt (n := m) hc
  refine ⟨UInt64.toNat_inj.mp ?_, UInt64.toNat_inj.mp ?_⟩
  · rw [UInt64.toNat_div, hE, hP, Nat.add_comm, Nat.add_mul_div_right _ _ hm0,
      Nat.div_eq_of_lt hc, Nat.zero_add]
  · rw [UInt64.toNat_mod, hE, hC, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem col_div {m : UInt64} {c : Nat} (hc : c < m.toNat) :
    UInt64.ofNat c / m = 0 ∧ UInt64.ofNat c % m = UInt64.ofNat c := by
  have h := row_div (n := m) (P := 0) hc (by simpa using hc)
  simpa using h

/-- Element `p · m + c` of a build over `T · m` elements, with `p < T` and `c < m`. -/
theorem row_lt {T m : UInt64} {p c : Nat} (hp : p < T.toNat) (hT : T.toNat < 2 ^ 32)
    (hm : m.toNat < 2 ^ 32) (hc : c < m.toNat) : p * m.toNat + c < (T * m).toNat := by
  rw [mul_toNat hT hm]
  calc p * m.toNat + c < (p + 1) * m.toNat := by rw [Nat.succ_mul]; omega
    _ ≤ T.toNat * m.toNat := Nat.mul_le_mul_right _ hp

theorem one_toNat (m : UInt64) : (1 * m).toNat = m.toNat := by
  simp

theorem one_lt {m : UInt64} {c : Nat} (hc : c < m.toNat) : c < (1 * m).toNat := by
  rwa [one_toNat]

theorem firstRow_get {s : Array Float} {d : UInt64} {c : Nat} (hc : c < d.toNat) :
    (firstRow s d)[c]! = s[c]! := by
  unfold firstRow
  rw [build_get hc, toNat_ofNat_lt hc]

theorem linear_row {x X w b : Array Float} {l T k m : UInt64} {p : Nat} (hp : p < T.toNat)
    (hT : T.toNat < 2 ^ 16) (hk : k.toNat < 2 ^ 32) (hm : m.toNat < 2 ^ 32)
    (h : RowIs k.toNat p x X) : RowIs m.toNat p (linear x w b l 1 k m) (linear X w b l T k m) := by
  intro c hc
  have hE := row_lt (m := m) hp (by omega) hm hc
  obtain ⟨hd1, hm1⟩ := col_div hc
  obtain ⟨hdP, hmP⟩ := row_div hc hE
  have hP : (UInt64.ofNat p).toNat = p := toNat_ofNat_lt (n := T) hp
  unfold linear
  rw [build_get (one_lt hc), build_get hE, hd1, hm1, hdP, hmP]
  congr 1
  refine loop_congr fun j hj acc => ?_
  have hJ : (UInt64.ofNat j).toNat = j := toNat_ofNat_lt hj
  have h0 : ((0 : UInt64) * k + UInt64.ofNat j).toNat = j := by simp [hJ]
  rw [index_toNat (R := UInt64.ofNat p) (by omega) hk (by rw [hJ]; exact hj), hP, hJ, h0,
    h j hj]

theorem matMulT_row {x X b : Array Float} {T k m : UInt64} {p : Nat} (hp : p < T.toNat)
    (hT : T.toNat < 2 ^ 16) (hk : k.toNat < 2 ^ 32) (hm : m.toNat < 2 ^ 32)
    (h : RowIs k.toNat p x X) : RowIs m.toNat p (matMulT x b 1 k m) (matMulT X b T k m) := by
  intro c hc
  have hE := row_lt (m := m) hp (by omega) hm hc
  obtain ⟨hd1, hm1⟩ := col_div hc
  obtain ⟨hdP, hmP⟩ := row_div hc hE
  have hP : (UInt64.ofNat p).toNat = p := toNat_ofNat_lt (n := T) hp
  unfold matMulT
  rw [build_get (one_lt hc), build_get hE, hd1, hm1, hdP, hmP]
  refine loop_congr fun j hj acc => ?_
  have hJ : (UInt64.ofNat j).toNat = j := toNat_ofNat_lt hj
  have h0 : ((0 : UInt64) * k + UInt64.ofNat j).toNat = j := by simp [hJ]
  rw [index_toNat (R := UInt64.ofNat p) (by omega) hk (by rw [hJ]; exact hj), hP, hJ, h0,
    h j hj]

theorem rowMeans_row {x X : Array Float} {T d : UInt64} {p : Nat} (hp : p < T.toNat)
    (hT : T.toNat < 2 ^ 16) (hd : d.toNat < 2 ^ 32) (h : RowIs d.toNat p x X) :
    (rowMeans x 1 d)[0]! = (rowMeans X T d)[p]! := by
  have hP : (UInt64.ofNat p).toNat = p := toNat_ofNat_lt hp
  unfold rowMeans
  rw [build_get (by simp), build_get hp]
  congr 1
  refine loop_congr fun c hc acc => ?_
  have hC : (UInt64.ofNat c).toNat = c := toNat_ofNat_lt hc
  have h0 : (UInt64.ofNat 0 * d + UInt64.ofNat c).toNat = c := by simp [hC]
  rw [index_toNat (R := UInt64.ofNat p) (by omega) hd (by rw [hC]; exact hc), hP, hC, h0,
    h c hc]

theorem rowInvStd_row {x X means Means : Array Float} {T d : UInt64} {eps : Float} {p : Nat}
    (hp : p < T.toNat) (hT : T.toNat < 2 ^ 16) (hd : d.toNat < 2 ^ 32) (h : RowIs d.toNat p x X)
    (hm : means[0]! = Means[p]!) :
    (rowInvStd x means 1 d eps)[0]! = (rowInvStd X Means T d eps)[p]! := by
  have hP : (UInt64.ofNat p).toNat = p := toNat_ofNat_lt hp
  unfold rowInvStd
  rw [build_get (by simp), build_get hp]
  congr 4
  refine loop_congr fun c hc acc => ?_
  have hC : (UInt64.ofNat c).toNat = c := toNat_ofNat_lt hc
  have h0 : (UInt64.ofNat 0 * d + UInt64.ofNat c).toNat = c := by simp [hC]
  rw [index_toNat (R := UInt64.ofNat p) (by omega) hd (by rw [hC]; exact hc), hP, hC, h0,
    h c hc]
  simp [hm]

theorem normalizeRows_row {x X means Means inv Inv g b : Array Float} {l T d : UInt64} {p : Nat}
    (hp : p < T.toNat) (hT : T.toNat < 2 ^ 16) (hd : d.toNat < 2 ^ 32) (h : RowIs d.toNat p x X)
    (hm : means[0]! = Means[p]!) (hv : inv[0]! = Inv[p]!) :
    RowIs d.toNat p (normalizeRows x means inv g b l 1 d)
      (normalizeRows X Means Inv g b l T d) := by
  intro c hc
  have hE := row_lt (m := d) hp (by omega) hd hc
  obtain ⟨hd1, hm1⟩ := col_div hc
  obtain ⟨hdP, hmP⟩ := row_div hc hE
  have hP : (UInt64.ofNat p).toNat = p := toNat_ofNat_lt (n := T) hp
  have hC : (UInt64.ofNat c).toNat = c := toNat_ofNat_lt hc
  have hEn : (UInt64.ofNat (p * d.toNat + c)).toNat = p * d.toNat + c := toNat_ofNat_lt hE
  unfold normalizeRows
  rw [build_get (one_lt hc), build_get hE, hd1, hm1, hdP, hmP, hC, hEn, hP, h c hc]
  simp only [UInt64.toNat_zero, hm, hv]

theorem layerNormRows_row {x X g b : Array Float} {l T d : UInt64} {eps : Float} {p : Nat}
    (hp : p < T.toNat) (hT : T.toNat < 2 ^ 16) (hd : d.toNat < 2 ^ 32) (h : RowIs d.toNat p x X) :
    RowIs d.toNat p (layerNormRows x g b l 1 d eps) (layerNormRows X g b l T d eps) :=
  normalizeRows_row hp hT hd h (rowMeans_row hp hT hd h)
    (rowInvStd_row hp hT hd h (rowMeans_row hp hT hd h))

theorem add_row {x X a A : Array Float} {w p : Nat} (hx : x.size = w) (hX : (p + 1) * w ≤ X.size)
    (hX64 : X.size < 2 ^ 64) (h : RowIs w p x X) (ha : RowIs w p a A) :
    RowIs w p (add x a) (add X A) := by
  intro c hc
  have hcX : p * w + c < X.size := by
    calc p * w + c < (p + 1) * w := by rw [Nat.succ_mul]; omega
      _ ≤ X.size := hX
  have hn : x.size.toUInt64.toNat = x.size :=
    UInt64.toNat_ofNat_of_lt' (show x.size < 2 ^ 64 by
      have : w ≤ (p + 1) * w := Nat.le_mul_of_pos_left w (by omega)
      omega)
  have hN : X.size.toUInt64.toNat = X.size := UInt64.toNat_ofNat_of_lt' hX64
  unfold add
  rw [build_get (by rw [hn, hx]; exact hc), build_get (by rw [hN]; exact hcX),
    toNat_ofNat_lt (n := X.size.toUInt64) (by rw [hN]; omega),
    toNat_ofNat_lt (n := X.size.toUInt64) (by rw [hN]; exact hcX), h c hc, ha c hc]

theorem geluArray_row {x X : Array Float} {w p : Nat} (hx : x.size = w)
    (hX : (p + 1) * w ≤ X.size) (hX64 : X.size < 2 ^ 64) (h : RowIs w p x X) :
    RowIs w p (geluArray x) (geluArray X) := by
  intro c hc
  have hcX : p * w + c < X.size := by
    calc p * w + c < (p + 1) * w := by rw [Nat.succ_mul]; omega
      _ ≤ X.size := hX
  have hn : x.size.toUInt64.toNat = x.size :=
    UInt64.toNat_ofNat_of_lt' (show x.size < 2 ^ 64 by
      have : w ≤ (p + 1) * w := Nat.le_mul_of_pos_left w (by omega)
      omega)
  have hN : X.size.toUInt64.toNat = X.size := UInt64.toNat_ofNat_of_lt' hX64
  unfold geluArray
  rw [build_get (by rw [hn, hx]; exact hc), build_get (by rw [hN]; exact hcX),
    toNat_ofNat_lt (n := X.size.toUInt64) (by rw [hN]; omega),
    toNat_ofNat_lt (n := X.size.toUInt64) (by rw [hN]; exact hcX), h c hc]

theorem linear_size {x w b : Array Float} {l n k m : UInt64} :
    (linear x w b l n k m).size = (n * m).toNat := by
  simp [linear, LeanExe.build]

theorem mlp_row {x X wfc bfc wproj bproj : Array Float} {l T d f : UInt64} {p : Nat}
    (hp : p < T.toNat) (hT : T.toNat < 2 ^ 16) (hd : d.toNat < 2 ^ 32) (hf : f.toNat < 2 ^ 32)
    (h : RowIs d.toNat p x X) :
    RowIs d.toNat p (mlp x wfc bfc wproj bproj l 1 d f) (mlp X wfc bfc wproj bproj l T d f) := by
  have hTf := mul_toNat (a := T) (b := f) (by omega) hf
  refine linear_row hp hT hf hd (geluArray_row (by rw [linear_size, one_toNat])
    (by rw [linear_size, hTf]; exact Nat.mul_le_mul_right _ hp)
    (by rw [linear_size]; exact UInt64.toNat_lt _) (linear_row hp hT hd hf h))

/-! ## Attention over the cache -/

theorem succ_toNat {p : Nat} (hp : p < 2 ^ 16) :
    (UInt64.ofNat p + 1).toNat = p + 1 := by
  have hP : (UInt64.ofNat p).toNat = p := UInt64.toNat_ofNat_of_lt' (show p < 2 ^ 64 by omega)
  rw [UInt64.toNat_add, hP, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]

/-- Head `h`, score `j` sits at `h · (p + 1) + j` in `nh` rows of `p + 1`. -/
theorem head_lt {nh : UInt64} {p h j : Nat} (hp : p < 2 ^ 16) (hn : nh.toNat < 2 ^ 16)
    (hh : h < nh.toNat) (hj : j ≤ p) : h * (p + 1) + j < (nh * (UInt64.ofNat p + 1)).toNat := by
  rw [mul_toNat (by omega) (by rw [succ_toNat hp]; omega), succ_toNat hp]
  calc h * (p + 1) + j < (h + 1) * (p + 1) := by rw [Nat.succ_mul]; omega
    _ ≤ nh.toNat * (p + 1) := Nat.mul_le_mul_right _ hh

theorem head_div {nh : UInt64} {p h j : Nat} (hp : p < 2 ^ 16) (hn : nh.toNat < 2 ^ 16)
    (hh : h < nh.toNat) (hj : j ≤ p) :
    UInt64.ofNat (h * (p + 1) + j) / (UInt64.ofNat p + 1) = UInt64.ofNat h ∧
      UInt64.ofNat (h * (p + 1) + j) % (UInt64.ofNat p + 1) = UInt64.ofNat j := by
  have h1 := succ_toNat hp
  have hlt := head_lt hp hn hh hj
  have := row_div (n := nh * (UInt64.ofNat p + 1)) (m := UInt64.ofNat p + 1) (P := h) (c := j)
    (by rw [h1]; omega) (by rw [h1]; exact hlt)
  rwa [h1] at this

/-- Query row `p` and head `h` is row `p · nh + h` of the attention scores. -/
theorem query_row {T nh : UInt64} {p h : Nat} (hp : p < T.toNat) (hh : h < nh.toNat) :
    p * nh.toNat + h < T.toNat * nh.toNat ∧ (p * nh.toNat + h) / nh.toNat = p ∧
      (p * nh.toNat + h) % nh.toNat = h := by
  have hn0 : 0 < nh.toNat := by omega
  refine ⟨?_, ?_, ?_⟩
  · calc p * nh.toNat + h < (p + 1) * nh.toNat := by rw [Nat.succ_mul]; omega
      _ ≤ T.toNat * nh.toNat := Nat.mul_le_mul_right _ hp
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn0, Nat.div_eq_of_lt hh, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hh]

/-- Column `h · dh + c` of head `h`. -/
theorem head_col {nh dh : UInt64} {h c : Nat} (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hh : h < nh.toNat) (hc : c < dh.toNat) :
    (UInt64.ofNat h * dh + UInt64.ofNat c).toNat = h * dh.toNat + c ∧
      h * dh.toNat + c < (nh * dh).toNat := by
  have hH : (UInt64.ofNat h).toNat = h := toNat_ofNat_lt (n := nh) hh
  have hC : (UInt64.ofNat c).toNat = c := toNat_ofNat_lt (n := dh) hc
  rw [index_toNat (by rw [hH]; omega) (by omega) (by rw [hC]; exact hc), hH, hC,
    mul_toNat (by omega) (by omega)]
  refine ⟨rfl, ?_⟩
  calc h * dh.toNat + c < (h + 1) * dh.toNat := by rw [Nat.succ_mul]; omega
    _ ≤ nh.toNat * dh.toNat := Nat.mul_le_mul_right _ hh

/-- Score `j` of head `h` in `stepScores` is score `j` of query row `p` and head `h` in
`maskedScores`, for `j ≤ p`: keys before `p` come from the cache and the key at `p` from
`k`. -/
theorem stepScores_at {q k C Q K : Array Float} {l nh dh B T : UInt64} {scale : Float}
    {p h j : Nat} (hp : p < T.toNat) (hT : T.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16)
    (hdh : dh.toNat < 2 ^ 16) (hh : h < nh.toNat) (hj : j ≤ p)
    (hq : RowIs (nh * dh).toNat p q Q) (hk : RowIs (nh * dh).toNat p k K)
    (hC : ∀ i, i < p → ∀ X : UInt64, X.toNat < (nh * dh).toNat →
      C[(UInt64.ofNat i * B + (2 * l + 1) * (nh * dh) + X).toNat]! =
        K[i * (nh * dh).toNat + X.toNat]!) :
    (stepScores q k C l (UInt64.ofNat p) nh dh B scale)[h * (p + 1) + j]! =
      (maskedScores Q K T nh dh scale)[(p * nh.toNat + h) * T.toNat + j]! := by
  have hP : (UInt64.ofNat p).toNat = p := toNat_ofNat_lt hp
  have hJ : (UInt64.ofNat j).toNat = j := toNat_ofNat_lt (n := T) (by omega)
  obtain ⟨hdiv, hmod⟩ := head_div (by omega) hn hh hj
  obtain ⟨hr, hrdiv, hrmod⟩ := query_row (T := T) hp hh
  rw [maskedScores_at hT hn hr (by omega), hrdiv, hrmod]
  unfold stepScores scoreAt
  rw [build_get (head_lt (by omega) hn hh hj), hdiv, hmod,
    ite_eq_left (show UInt64.ofNat j ≤ UInt64.ofNat p by rw [UInt64.le_iff_toNat_le, hJ, hP]; exact hj)]
  congr 1
  refine loop_congr fun c hc acc => ?_
  obtain ⟨hX, hXD⟩ := head_col (c := c) hn hdh hh hc
  have hW : (nh * dh).toNat < 2 ^ 32 := small_mul hn hdh
  rw [index_toNat (R := UInt64.ofNat p) (by omega) hW (by rw [hX]; exact hXD), hP,
    index_toNat (R := UInt64.ofNat j) (by omega) hW (by rw [hX]; exact hXD), hJ,
    hX, hq _ hXD]
  by_cases hjp : j < p
  · rw [ite_eq_left (show UInt64.ofNat j < UInt64.ofNat p by
      rw [UInt64.lt_iff_toNat_lt, hJ, hP]; exact hjp),
      hC j hjp _ (by rw [hX]; exact hXD), hX]
  · have hjeq : j = p := by omega
    subst hjeq
    have hNot : ¬ (UInt64.ofNat j < UInt64.ofNat j) := by simp
    rw [ite_eq_right hNot, hk _ hXD]

/-- The maximum of head `h`'s `p + 1` scores is the maximum of query row `p` and head
`h`. -/
theorem headMax_at {sc S : Array Float} {nh T : UInt64} {p h : Nat} (hp : p < T.toNat)
    (hT : T.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hh : h < nh.toNat)
    (hs : ∀ j, j ≤ p → sc[h * (p + 1) + j]! = S[(p * nh.toNat + h) * T.toNat + j]!) :
    (headMax sc nh (UInt64.ofNat p + 1))[h]! = (rowMax S T nh)[p * nh.toNat + h]! := by
  obtain ⟨hr, hrdiv, -⟩ := query_row (T := T) hp hh
  have hrT : p * nh.toNat + h < (T * nh).toNat := by rwa [mul_toNat (by omega) (by omega)]
  obtain ⟨hdiv, -⟩ := row_div (n := T * nh) (m := nh) (P := p) (c := h) hh hrT
  have hP1 := succ_toNat (p := p) (by omega)
  have hH : (UInt64.ofNat h).toNat = h := toNat_ofNat_lt (n := nh) hh
  have hR : (UInt64.ofNat (p * nh.toNat + h)).toNat = p * nh.toNat + h := toNat_ofNat_lt hrT
  have hTN : T.toNat * nh.toNat < 2 ^ 32 := by
    rw [← mul_toNat (by omega) (by omega)]; exact small_mul hT hn
  unfold headMax rowMax
  rw [build_get hh, build_get hrT, hdiv]
  refine loop_congr fun c hc acc => ?_
  rw [hP1] at hc
  have hC : (UInt64.ofNat c).toNat = c := toNat_ofNat_lt (n := T) (by omega)
  rw [index_toNat (by rw [hH]; omega) (by rw [hP1]; omega) (by rw [hC, hP1]; exact hc), hH, hC,
    hP1, index_toNat (by rw [hR]; omega) (by omega) (by rw [hC]; omega), hR, hC,
    hs c (by omega)]

theorem headSumExp_at {sc S mx MX : Array Float} {nh T : UInt64} {p h : Nat} (hp : p < T.toNat)
    (hT : T.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hh : h < nh.toNat)
    (hs : ∀ j, j ≤ p → sc[h * (p + 1) + j]! = S[(p * nh.toNat + h) * T.toNat + j]!)
    (hm : mx[h]! = MX[p * nh.toNat + h]!) :
    (headSumExp sc mx nh (UInt64.ofNat p + 1))[h]! = (rowSumExp S MX T nh)[p * nh.toNat + h]! := by
  obtain ⟨hr, hrdiv, -⟩ := query_row (T := T) hp hh
  have hrT : p * nh.toNat + h < (T * nh).toNat := by rwa [mul_toNat (by omega) (by omega)]
  obtain ⟨hdiv, -⟩ := row_div (n := T * nh) (m := nh) (P := p) (c := h) hh hrT
  have hP1 := succ_toNat (p := p) (by omega)
  have hH : (UInt64.ofNat h).toNat = h := toNat_ofNat_lt (n := nh) hh
  have hR : (UInt64.ofNat (p * nh.toNat + h)).toNat = p * nh.toNat + h := toNat_ofNat_lt hrT
  have hTN : T.toNat * nh.toNat < 2 ^ 32 := by
    rw [← mul_toNat (by omega) (by omega)]; exact small_mul hT hn
  unfold headSumExp rowSumExp
  rw [build_get hh, build_get hrT, hdiv]
  refine loop_congr fun c hc acc => ?_
  rw [hP1] at hc
  have hC : (UInt64.ofNat c).toNat = c := toNat_ofNat_lt (n := T) (by omega)
  rw [index_toNat (by rw [hH]; omega) (by rw [hP1]; omega) (by rw [hC, hP1]; exact hc), hH, hC,
    hP1, index_toNat (by rw [hR]; omega) (by omega) (by rw [hC]; omega), hR, hC,
    hs c (by omega), hm]

/-- The softmax of head `h`'s scores is the causal softmax of query row `p` and head `h`. -/
theorem stepSoftmax_at {sc S : Array Float} {nh T : UInt64} {p h j : Nat} (hp : p < T.toNat)
    (hT : T.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hh : h < nh.toNat) (hj : j ≤ p)
    (hs : ∀ j, j ≤ p → sc[h * (p + 1) + j]! = S[(p * nh.toNat + h) * T.toNat + j]!) :
    (stepSoftmax sc nh (UInt64.ofNat p + 1))[h * (p + 1) + j]! =
      (softmaxRows S T nh)[(p * nh.toNat + h) * T.toNat + j]! := by
  obtain ⟨hr, -, -⟩ := query_row (T := T) hp hh
  obtain ⟨hdiv, -⟩ := head_div (by omega) hn hh hj
  have hE := head_lt (by omega) hn hh hj
  have hH : (UInt64.ofNat h).toNat = h := toNat_ofNat_lt (n := nh) hh
  have hEn : (UInt64.ofNat (h * (p + 1) + j)).toNat = h * (p + 1) + j := toNat_ofNat_lt hE
  have hm := headMax_at hp hT hn hh hs
  unfold softmaxRows
  rw [softmaxApply_at hT hn hr (by omega)]
  unfold stepSoftmax softmaxApply
  rw [build_get hE, hdiv, hH, hEn, hs j hj, hm, headSumExp_at hp hT hn hh hs hm]

/-- Element `c` of `stepMix` is element `c` of row `p` of `causalMatMul`: values before `p`
come from the cache and the value at `p` from `v`. -/
theorem stepMix_row {pw v C PW V : Array Float} {l nh dh B T : UInt64} {p : Nat}
    (hp : p < T.toNat) (hT : T.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hpw : ∀ h j, h < nh.toNat → j ≤ p →
      pw[h * (p + 1) + j]! = PW[(p * nh.toNat + h) * T.toNat + j]!)
    (hv : RowIs (nh * dh).toNat p v V)
    (hC : ∀ i, i < p → ∀ X : UInt64, X.toNat < (nh * dh).toNat →
      C[(UInt64.ofNat i * B + (2 * l + 2) * (nh * dh) + X).toNat]! =
        V[i * (nh * dh).toNat + X.toNat]!) :
    RowIs (nh * dh).toNat p (stepMix pw v C l (UInt64.ofNat p) nh dh B)
      (causalMatMul PW V T nh dh) := by
  intro c hc
  have hW : (nh * dh).toNat < 2 ^ 32 := small_mul hn hdh
  have hND : (nh * dh).toNat = nh.toNat * dh.toNat := mul_toNat (by omega) (by omega)
  have hP : (UInt64.ofNat p).toNat = p := toNat_ofNat_lt hp
  have hP1 := succ_toNat (p := p) (by omega)
  have hE := row_lt (m := nh * dh) hp (by omega) hW hc
  obtain ⟨hdiv, hmod⟩ := row_div hc hE
  have hC' : (UInt64.ofNat c).toNat = c := toNat_ofNat_lt hc
  have hdh0 : 0 < dh.toNat := Nat.pos_of_ne_zero fun h0 => by simp [hND, h0] at hc
  have hHlt : c / dh.toNat < nh.toNat := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hND]; exact hc)
  have hHd : (UInt64.ofNat c / dh).toNat = c / dh.toNat := by rw [UInt64.toNat_div, hC']
  unfold stepMix causalMatMul
  rw [build_get hc, build_get hE, hdiv, hmod]
  refine loop_congr fun j hj acc => ?_
  rw [hP1] at hj
  have hJ : (UInt64.ofNat j).toNat = j := toNat_ofNat_lt (n := T) (by omega)
  have hNT := small_mul hn hT
  have hpwI : (UInt64.ofNat c / dh * (UInt64.ofNat p + 1) + UInt64.ofNat j).toNat =
      c / dh.toNat * (p + 1) + j := by
    rw [index_toNat (by rw [hHd]; omega) (by rw [hP1]; omega) (by rw [hJ, hP1]; exact hj), hHd, hJ,
      hP1]
  have hPWI : (UInt64.ofNat p * (nh * T) + (UInt64.ofNat c / dh * T + UInt64.ofNat j)).toNat =
      (p * nh.toNat + c / dh.toNat) * T.toNat + j := by
    have hIn : (UInt64.ofNat c / dh * T + UInt64.ofNat j).toNat < (nh * T).toNat := by
      rw [index_toNat (by rw [hHd]; omega) (by omega) (by rw [hJ]; omega), hHd, hJ,
        mul_toNat (a := nh) (b := T) (by omega) (by omega)]
      calc c / dh.toNat * T.toNat + j < (c / dh.toNat + 1) * T.toNat := by
            rw [Nat.succ_mul]; omega
        _ ≤ nh.toNat * T.toNat := Nat.mul_le_mul_right _ hHlt
    rw [index_toNat (by rw [hP]; omega) hNT hIn, hP,
      index_toNat (by rw [hHd]; omega) (by omega) (by rw [hJ]; omega), hHd, hJ,
      mul_toNat (a := nh) (b := T) (by omega) (by omega)]
    ring
  rw [hpwI, hPWI, hpw _ _ hHlt (by omega),
    index_toNat (R := UInt64.ofNat j) (by omega) hW (by rw [hC']; exact hc), hJ, hC']
  by_cases hjp : j < p
  · rw [ite_eq_left (show UInt64.ofNat j < UInt64.ofNat p by
      rw [UInt64.lt_iff_toNat_lt, hJ, hP]; exact hjp), hC j hjp _ (by rw [hC']; exact hc), hC']
  · have hjeq : j = p := by omega
    subst hjeq
    have hNot : ¬ (UInt64.ofNat j < UInt64.ofNat j) := by simp
    rw [ite_eq_right hNot, hv c hc]

/-! ## One layer -/

/-- The keys of layer `l` of `block` on `X`, as `attention` computes them. -/
def blockKeys (X g1 b1 wk bk : Array Float) (l T nh dh : UInt64) (eps : Float) : Array Float :=
  linear (layerNormRows X g1 b1 l T (nh * dh) eps) wk bk l T (nh * dh) (nh * dh)

/-- The values of layer `l` of `block` on `X`, as `attention` computes them. -/
def blockValues (X g1 b1 wv bv : Array Float) (l T nh dh : UInt64) (eps : Float) : Array Float :=
  linear (layerNormRows X g1 b1 l T (nh * dh) eps) wv bv l T (nh * dh) (nh * dh)

theorem slot_toNat {l d : UInt64} (hl : l.toNat < 2 ^ 16)
    (hld : (2 * l.toNat + 3) * d.toNat < 2 ^ 32) :
    ((2 * l + 1) * d).toNat = (2 * l.toNat + 1) * d.toNat ∧
      ((2 * l + 2) * d).toNat = (2 * l.toNat + 2) * d.toNat ∧
      ((2 * l + 3) * d).toNat = (2 * l.toNat + 3) * d.toNat := by
  have h2 : (2 * l).toNat = 2 * l.toNat := by
    rw [UInt64.toNat_mul, show (2 : UInt64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hd0 : ∀ a : Nat, a ≤ 3 → (2 * l.toNat + a) * d.toNat < 2 ^ 32 := fun a ha =>
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hld
  refine ⟨?_, ?_, ?_⟩
  · have : (2 * l + 1).toNat = 2 * l.toNat + 1 := by
      rw [UInt64.toNat_add, h2, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
    rw [UInt64.toNat_mul, this, Nat.mod_eq_of_lt (by have := hd0 1 (by omega); omega)]
  · have : (2 * l + 2).toNat = 2 * l.toNat + 2 := by
      rw [UInt64.toNat_add, h2, show (2 : UInt64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
    rw [UInt64.toNat_mul, this, Nat.mod_eq_of_lt (by have := hd0 2 (by omega); omega)]
  · have : (2 * l + 3).toNat = 2 * l.toNat + 3 := by
      rw [UInt64.toNat_add, h2, show (3 : UInt64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
    rw [UInt64.toNat_mul, this, Nat.mod_eq_of_lt (by have := hd0 3 (by omega); omega)]

theorem writeBlock_size {s x k v : Array Float} {l d : UInt64} (hs : s.size < 2 ^ 64) :
    (writeBlock s x k v l d).size = s.size := by
  simp [writeBlock, LeanExe.build]
  omega

theorem writeBlock_get {s x k v : Array Float} {l d : UInt64} {e : Nat} (he : e < s.size)
    (hs : s.size < 2 ^ 32) (hl : l.toNat < 2 ^ 16) (hld : (2 * l.toNat + 3) * d.toNat < 2 ^ 32) :
    (writeBlock s x k v l d)[e]! =
      if e < d.toNat then x[e]!
      else if e < (2 * l.toNat + 1) * d.toNat then s[e]!
      else if e < (2 * l.toNat + 2) * d.toNat then k[e - (2 * l.toNat + 1) * d.toNat]!
      else if e < (2 * l.toNat + 3) * d.toNat then v[e - (2 * l.toNat + 2) * d.toNat]!
      else s[e]! := by
  have hN : s.size.toUInt64.toNat = s.size :=
    UInt64.toNat_ofNat_of_lt' (show s.size < 2 ^ 64 by omega)
  have hE : (UInt64.ofNat e).toNat = e := toNat_ofNat_lt (n := s.size.toUInt64) (by rw [hN]; exact he)
  obtain ⟨h1, h2, h3⟩ := slot_toNat hl hld
  unfold writeBlock
  rw [build_get (by rw [hN]; exact he)]
  simp only [UInt64.lt_iff_toNat_lt, hE, h1, h2, h3]
  split_ifs with c1 c2 c3 c4
  · rfl
  · rfl
  · rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hE, h1]; omega), hE, h1]
  · rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hE, h2]; omega), hE, h2]
  · rfl

/-- Layer `lN` of `step` at position `p` computes row `p` of `block`, and the row's key
and value, from row `p` of the layer's input and the cache's keys and values of the
earlier positions; it leaves the other slots of the block unchanged. -/
theorem layerStep_row
    {s C X g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float}
    {T nh dh f B : UInt64} {eps : Float} {lN p : Nat}
    (hp : p < T.toNat) (hT : T.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hf : f.toNat < 2 ^ 32) (hl : lN < 2 ^ 16)
    (hX : X.size = (T * (nh * dh)).toNat) (hsize : s.size = B.toNat) (hB : B.toNat < 2 ^ 32)
    (hlB : (2 * lN + 3) * (nh * dh).toNat ≤ B.toNat)
    (hs : ∀ c, c < (nh * dh).toNat → s[c]! = X[p * (nh * dh).toNat + c]!)
    (hK : ∀ i, i < p → ∀ Y : UInt64, Y.toNat < (nh * dh).toNat →
      C[(UInt64.ofNat i * B + (2 * UInt64.ofNat lN + 1) * (nh * dh) + Y).toNat]! =
        (blockKeys X g1 b1 wk bk (UInt64.ofNat lN) T nh dh eps)[i * (nh * dh).toNat + Y.toNat]!)
    (hV : ∀ i, i < p → ∀ Y : UInt64, Y.toNat < (nh * dh).toNat →
      C[(UInt64.ofNat i * B + (2 * UInt64.ofNat lN + 2) * (nh * dh) + Y).toNat]! =
        (blockValues X g1 b1 wv bv (UInt64.ofNat lN) T nh dh eps)[i * (nh * dh).toNat + Y.toNat]!) :
    let s' := layerStep s C g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj
      (UInt64.ofNat lN) (UInt64.ofNat p) nh dh f B eps
    s'.size = s.size ∧
      (∀ c, c < (nh * dh).toNat → s'[c]! =
        (block X g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj (UInt64.ofNat lN) T nh dh
          f eps)[p * (nh * dh).toNat + c]!) ∧
      (∀ c, c < (nh * dh).toNat → s'[(2 * lN + 1) * (nh * dh).toNat + c]! =
        (blockKeys X g1 b1 wk bk (UInt64.ofNat lN) T nh dh eps)[p * (nh * dh).toNat + c]!) ∧
      (∀ c, c < (nh * dh).toNat → s'[(2 * lN + 2) * (nh * dh).toNat + c]! =
        (blockValues X g1 b1 wv bv (UInt64.ofNat lN) T nh dh eps)[p * (nh * dh).toNat + c]!) ∧
      (∀ e, e < s.size → (nh * dh).toNat ≤ e →
        (e < (2 * lN + 1) * (nh * dh).toNat ∨ (2 * lN + 3) * (nh * dh).toNat ≤ e) → s'[e]! = s[e]!) := by
  intro s'
  have hW : (nh * dh).toNat < 2 ^ 32 := small_mul hn hdh
  have hL : (UInt64.ofNat lN).toNat = lN := UInt64.toNat_ofNat_of_lt' (show lN < 2 ^ 64 by omega)
  have hTD : (T * (nh * dh)).toNat = T.toNat * (nh * dh).toNat := mul_toNat (by omega) hW
  have hXrows : (p + 1) * (nh * dh).toNat ≤ X.size := by
    rw [hX, hTD]; exact Nat.mul_le_mul_right _ hp
  have hX64 : X.size < 2 ^ 64 := by rw [hX]; exact UInt64.toNat_lt _
  have hx : RowIs (nh * dh).toNat p (firstRow s (nh * dh)) X := fun c hc => by
    rw [firstRow_get hc, hs c hc]
  have hxs : (firstRow s (nh * dh)).size = (nh * dh).toNat := by simp [firstRow, LeanExe.build]
  have hh1 := layerNormRows_row (g := g1) (b := b1) (l := UInt64.ofNat lN) (eps := eps) hp hT hW hx
  have hq := linear_row (w := wq) (b := bq) (l := UInt64.ofNat lN) hp hT hW hW hh1
  have hk := linear_row (w := wk) (b := bk) (l := UInt64.ofNat lN) hp hT hW hW hh1
  have hv := linear_row (w := wv) (b := bv) (l := UInt64.ofNat lN) hp hT hW hW hh1
  have hpw := fun h j (hh : h < nh.toNat) (hj : j ≤ p) =>
    stepSoftmax_at (sc := stepScores _ _ C (UInt64.ofNat lN) (UInt64.ofNat p) nh dh B
      (1.0 / dh.toFloat.sqrt)) hp hT hn hh hj fun j hj => stepScores_at hp hT hn hdh hh hj hq hk hK
  have ho := stepMix_row hp hT hn hdh hpw hv hV
  have ha := linear_row (w := wo) (b := bo) (l := UInt64.ofNat lN) hp hT hW hW ho
  have hr := add_row hxs hXrows hX64 hx ha
  have hrs : (add (firstRow s (nh * dh)) (linear (stepMix (stepSoftmax (stepScores
      (linear (layerNormRows (firstRow s (nh * dh)) g1 b1 (UInt64.ofNat lN) 1 (nh * dh) eps) wq bq
        (UInt64.ofNat lN) 1 (nh * dh) (nh * dh))
      (linear (layerNormRows (firstRow s (nh * dh)) g1 b1 (UInt64.ofNat lN) 1 (nh * dh) eps) wk bk
        (UInt64.ofNat lN) 1 (nh * dh) (nh * dh)) C (UInt64.ofNat lN) (UInt64.ofNat p) nh dh B
      (1.0 / dh.toFloat.sqrt)) nh (UInt64.ofNat p + 1))
      (linear (layerNormRows (firstRow s (nh * dh)) g1 b1 (UInt64.ofNat lN) 1 (nh * dh) eps) wv bv
        (UInt64.ofNat lN) 1 (nh * dh) (nh * dh)) C (UInt64.ofNat lN) (UInt64.ofNat p) nh dh B)
      wo bo (UInt64.ofNat lN) 1 (nh * dh) (nh * dh))).size = (nh * dh).toNat := by
    rw [add_size (by rw [hxs]; omega), hxs]
  have hR64 : ∀ A : Array Float, (add X A).size = X.size := fun _ => add_size hX64
  have hh2 := layerNormRows_row (g := g2) (b := b2) (l := UInt64.ofNat lN) (eps := eps) hp hT hW hr
  have hm := mlp_row (wfc := wfc) (bfc := bfc) (wproj := wproj) (bproj := bproj)
    (l := UInt64.ofNat lN) hp hT hW hf hh2
  have hy := add_row hrs (by rw [hR64]; exact hXrows) (by rw [hR64]; exact hX64) hr hm
  have hss : s.size < 2 ^ 32 := by omega
  have hld : (2 * (UInt64.ofNat lN).toNat + 3) * (nh * dh).toNat < 2 ^ 32 := by rw [hL]; omega
  have hD0 : (nh * dh).toNat ≤ (2 * lN + 1) * (nh * dh).toNat :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hS1 : (2 * lN + 2) * (nh * dh).toNat = (2 * lN + 1) * (nh * dh).toNat + (nh * dh).toNat := by
    ring
  have hS2 : (2 * lN + 3) * (nh * dh).toNat = (2 * lN + 2) * (nh * dh).toNat + (nh * dh).toNat := by
    ring
  refine ⟨writeBlock_size (by omega), fun c hc => ?_, fun c hc => ?_, fun c hc => ?_,
    fun e he hDe hout => ?_⟩
  · show (writeBlock s _ _ _ _ _)[c]! = _
    rw [writeBlock_get (by omega) hss (by rw [hL]; omega) hld, ite_eq_left hc]
    exact hy c hc
  · show (writeBlock s _ _ _ _ _)[_]! = _
    rw [writeBlock_get (by omega) hss (by rw [hL]; omega) hld, hL, ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left (by omega),
      show (2 * lN + 1) * (nh * dh).toNat + c - (2 * lN + 1) * (nh * dh).toNat = c by omega]
    exact hk c hc
  · show (writeBlock s _ _ _ _ _)[_]! = _
    rw [writeBlock_get (by omega) hss (by rw [hL]; omega) hld, hL, ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      show (2 * lN + 2) * (nh * dh).toNat + c - (2 * lN + 2) * (nh * dh).toNat = c by omega]
    exact hv c hc
  · show (writeBlock s _ _ _ _ _)[e]! = _
    rw [writeBlock_get he hss (by rw [hL]; omega) hld, hL, ite_eq_right (by omega)]
    rcases hout with hlt | hge
    · rw [ite_eq_left hlt]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-! ## The step and the cache -/

/-- The input of layer `k` of `forward` on `T` tokens. -/
def layerInput (tokens : Array UInt64)
    (wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float)
    (T nh dh f : UInt64) (eps : Float) (k : Nat) : Array Float :=
  Nat.fold k (fun j _ x => block x g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj
    (UInt64.ofNat j) T nh dh f eps) (embed tokens wte wpe T (nh * dh))

/-- The cache after the first `n` tokens, from an empty cache. -/
def cacheAfter (tokens : Array UInt64)
    (wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float)
    (layers nh dh f : UInt64) (eps : Float) (n : Nat) : Array Float :=
  Nat.fold n (fun j _ c => step c wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj
    tokens[j]! layers nh dh f eps) #[]

/-- `C` holds `p` blocks of `B` values: block `j` holds row `j` of `X`, then the key and
value rows `j` of each of the `L` layers, in rows of `D` values. -/
structure CacheIs (C : Array Float) (p B D L : Nat) (X : Array Float)
    (K V : Nat → Array Float) : Prop where
  size : C.size = p * B
  hidden : ∀ j, j < p → ∀ c, c < D → C[j * B + c]! = X[j * D + c]!
  keys : ∀ l, l < L → ∀ j, j < p → ∀ c, c < D →
    C[j * B + ((2 * l + 1) * D + c)]! = (K l)[j * D + c]!
  values : ∀ l, l < L → ∀ j, j < p → ∀ c, c < D →
    C[j * B + ((2 * l + 2) * D + c)]! = (V l)[j * D + c]!

theorem layerInput_size {tokens : Array UInt64}
    {wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float}
    {T nh dh f : UInt64} {eps : Float} (k : Nat) :
    (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj T nh dh f
      eps k).size = (T * (nh * dh)).toNat := by
  induction k with
  | zero => simp [layerInput, embed, LeanExe.build]
  | succ k ih =>
    unfold layerInput at ih ⊢
    rw [Nat.fold_succ, block_size (by rw [ih]; exact UInt64.toNat_lt _), ih]

theorem layerInput_succ {tokens : Array UInt64}
    {wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float}
    {T nh dh f : UInt64} {eps : Float} (k : Nat) :
    layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj T nh dh f eps
      (k + 1) =
      block (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj T nh
        dh f eps k) g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj (UInt64.ofNat k) T nh dh
        f eps := by
  unfold layerInput
  rw [Nat.fold_succ]

/-- The index of a key or value word of layer `k` in block `i` of the cache. -/
theorem cache_index {i k Bn D : Nat} {B nd Y c : UInt64} {a : Nat} (hB : B.toNat = Bn)
    (hnd : nd.toNat = D) (hc : c.toNat = a) (ha : a ≤ 2) (hi : i < 2 ^ 32) (hk : k < 2 ^ 16)
    (hD : D < 2 ^ 32)
    (hY : Y.toNat < D) (hfit : (2 * k + 3) * D ≤ Bn) (hall : (i + 1) * Bn < 2 ^ 32) :
    (UInt64.ofNat i * B + (2 * UInt64.ofNat k + c) * nd + Y).toNat =
      i * Bn + ((2 * k + a) * D + Y.toNat) := by
  have hBn : Bn < 2 ^ 32 := lt_of_le_of_lt (Nat.le_mul_of_pos_left Bn (by omega)) hall
  have hiB : i * Bn < 2 ^ 32 := lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hall
  have hI : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
  have hK : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)
  have h2k : (2 * UInt64.ofNat k + c).toNat = 2 * k + a := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, show (2 : UInt64).toNat = 2 from rfl, hK, hc,
      Nat.mod_eq_of_lt (show 2 * k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
  have hslot : (2 * k + a) * D + Y.toNat < Bn := by
    have : (2 * k + a) * D + D ≤ (2 * k + 3) * D := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  have hmul1 : (UInt64.ofNat i * B).toNat = i * Bn := by
    rw [UInt64.toNat_mul, hI, hB, Nat.mod_eq_of_lt (by omega)]
  have hmul2 : ((2 * UInt64.ofNat k + c) * nd).toNat = (2 * k + a) * D := by
    rw [UInt64.toNat_mul, h2k, hnd, Nat.mod_eq_of_lt (by omega)]
  rw [UInt64.toNat_add, UInt64.toNat_add, hmul1, hmul2, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  ring

theorem appendBlock_size {C s : Array Float} (h : C.size + s.size < 2 ^ 64) :
    (appendBlock C s).size = C.size + s.size := by
  have hC : C.size.toUInt64.toNat = C.size :=
    UInt64.toNat_ofNat_of_lt' (show C.size < 2 ^ 64 by omega)
  have hs : s.size.toUInt64.toNat = s.size :=
    UInt64.toNat_ofNat_of_lt' (show s.size < 2 ^ 64 by omega)
  simp only [appendBlock, LeanExe.build, Array.size_ofFn]
  rw [UInt64.toNat_add, hC, hs, Nat.mod_eq_of_lt h]

theorem appendBlock_get {C s : Array Float} {e : Nat} (h : C.size + s.size < 2 ^ 64)
    (he : e < C.size + s.size) :
    (appendBlock C s)[e]! = if e < C.size then C[e]! else s[e - C.size]! := by
  have hC : C.size.toUInt64.toNat = C.size :=
    UInt64.toNat_ofNat_of_lt' (show C.size < 2 ^ 64 by omega)
  have hs : s.size.toUInt64.toNat = s.size :=
    UInt64.toNat_ofNat_of_lt' (show s.size < 2 ^ 64 by omega)
  have hN : (C.size.toUInt64 + s.size.toUInt64).toNat = C.size + s.size := by
    rw [UInt64.toNat_add, hC, hs, Nat.mod_eq_of_lt h]
  have hE : (UInt64.ofNat e).toNat = e := toNat_ofNat_lt (n := C.size.toUInt64 + s.size.toUInt64)
    (by rw [hN]; exact he)
  unfold appendBlock
  rw [build_get (by rw [hN]; exact he)]
  simp only [UInt64.lt_iff_toNat_lt, hE, hC]
  split_ifs with h1
  · rfl
  · rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hE, hC]; omega), hE, hC]

theorem embedBlock_row {tokens : Array UInt64} {wte wpe : Array Float} {T d bsize : UInt64}
    {p c : Nat} (hp : p < T.toNat) (hT : T.toNat < 2 ^ 16) (hd : d.toNat < 2 ^ 32)
    (hc : c < d.toNat) (hcb : c < bsize.toNat) :
    (embedBlock wte wpe tokens[p]! (UInt64.ofNat p) d bsize)[c]! =
      (embed tokens wte wpe T d)[p * d.toNat + c]! := by
  have hE := row_lt (m := d) hp (by omega) hd hc
  obtain ⟨hdiv, hmod⟩ := row_div hc hE
  have hP : (UInt64.ofNat p).toNat = p := toNat_ofNat_lt hp
  have hC : (UInt64.ofNat c).toNat = c := toNat_ofNat_lt hc
  have hEn : (UInt64.ofNat (p * d.toNat + c)).toNat = p * d.toNat + c := toNat_ofNat_lt hE
  unfold embedBlock embed
  rw [build_get hcb, build_get hE, ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, hC]; exact hc), hdiv,
    hmod, hP, hEn, index_toNat (R := UInt64.ofNat p) (C := UInt64.ofNat c) (by rw [hP]; omega) hd
      (by rw [hC]; exact hc), hP, hC]

/-- The layer loop of `step` at position `p`: after `k` layers the block holds row `p` of
layer `k`'s input and the key and value rows `p` of the first `k` layers. -/
theorem layerLoop {C : Array Float} {tokens : Array UInt64}
    {wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float}
    {T nh dh f B : UInt64} {eps : Float} {p L : Nat}
    (hp : p < T.toNat) (hT : T.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hf : f.toNat < 2 ^ 32) (hL : L < 2 ^ 16)
    (hBn : B.toNat = (2 * L + 1) * (nh * dh).toNat) (hall : (p + 1) * B.toNat < 2 ^ 32)
    (hC : CacheIs C p B.toNat (nh * dh).toNat L
      (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj T nh dh f
        eps L)
      (fun l => blockKeys (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc
        wproj bproj T nh dh f eps l) g1 b1 wk bk (UInt64.ofNat l) T nh dh eps)
      (fun l => blockValues (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc
        wproj bproj T nh dh f eps l) g1 b1 wv bv (UInt64.ofNat l) T nh dh eps))
    (k : Nat) (hk : k ≤ L) :
    let s := Nat.fold k (fun i _ s => layerStep s C g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc
      wproj bproj (UInt64.ofNat i) (UInt64.ofNat p) nh dh f B eps)
      (embedBlock wte wpe tokens[p]! (UInt64.ofNat p) (nh * dh) B)
    s.size = B.toNat ∧
      (∀ c, c < (nh * dh).toNat → s[c]! = (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo
        g2 b2 wfc bfc wproj bproj T nh dh f eps k)[p * (nh * dh).toNat + c]!) ∧
      (∀ l, l < k → ∀ c, c < (nh * dh).toNat →
        s[(2 * l + 1) * (nh * dh).toNat + c]! = (blockKeys (layerInput tokens wte wpe g1 b1 wq bq
          wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj T nh dh f eps l) g1 b1 wk bk (UInt64.ofNat l)
          T nh dh eps)[p * (nh * dh).toNat + c]! ∧
        s[(2 * l + 2) * (nh * dh).toNat + c]! = (blockValues (layerInput tokens wte wpe g1 b1 wq bq
          wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj T nh dh f eps l) g1 b1 wv bv (UInt64.ofNat l)
          T nh dh eps)[p * (nh * dh).toNat + c]!) := by
  have hW : (nh * dh).toNat < 2 ^ 32 := small_mul hn hdh
  have hB32 : B.toNat < 2 ^ 32 := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by omega)) hall
  induction k with
  | zero =>
    refine ⟨by simp [embedBlock, LeanExe.build], fun c hc => ?_, fun l hl => absurd hl (by omega)⟩
    have hcB : c < B.toNat := by
      rw [hBn]; exact lt_of_lt_of_le hc (Nat.le_mul_of_pos_left _ (by omega))
    exact embedBlock_row hp hT hW hc hcB
  | succ k ih =>
    obtain ⟨hsize, hs, hslots⟩ := ih (by omega)
    have hfit : (2 * k + 3) * (nh * dh).toNat ≤ B.toNat := by
      rw [hBn]; exact Nat.mul_le_mul_right _ (by omega)
    have hK : ∀ i, i < p → ∀ Y : UInt64, Y.toNat < (nh * dh).toNat →
        C[(UInt64.ofNat i * B + (2 * UInt64.ofNat k + 1) * (nh * dh) + Y).toNat]! =
          (blockKeys (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj
            bproj T nh dh f eps k) g1 b1 wk bk (UInt64.ofNat k) T nh dh eps)[i * (nh * dh).toNat +
            Y.toNat]! := fun i hi Y hY => by
      rw [cache_index rfl rfl (show (1 : UInt64).toNat = 1 from rfl) (by omega) (by omega)
        (by omega) hW hY
        hfit (lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hall)]
      exact hC.keys k (by omega) i hi _ hY
    have hV : ∀ i, i < p → ∀ Y : UInt64, Y.toNat < (nh * dh).toNat →
        C[(UInt64.ofNat i * B + (2 * UInt64.ofNat k + 2) * (nh * dh) + Y).toNat]! =
          (blockValues (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj
            bproj T nh dh f eps k) g1 b1 wv bv (UInt64.ofNat k) T nh dh eps)[i * (nh * dh).toNat +
            Y.toNat]! := fun i hi Y hY => by
      rw [cache_index rfl rfl (show (2 : UInt64).toNat = 2 from rfl) (by omega) (by omega)
        (by omega) hW hY
        hfit (lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hall)]
      exact hC.values k (by omega) i hi _ hY
    obtain ⟨hsize', hhid, hkey, hval, hkeep⟩ := layerStep_row (lN := k) (C := C) hp hT hn hdh hf
      (by omega) (layerInput_size k) hsize hB32 hfit hs hK hV
    rw [Nat.fold_succ]
    refine ⟨by rw [hsize', hsize], fun c hc => ?_, fun l hl c hc => ?_⟩
    · rw [hhid c hc, layerInput_succ]
    · have hS1 : (2 * l + 2) * (nh * dh).toNat = (2 * l + 1) * (nh * dh).toNat + (nh * dh).toNat := by
        ring
      have hS0 : (nh * dh).toNat ≤ (2 * l + 1) * (nh * dh).toNat :=
        Nat.le_mul_of_pos_left _ (by omega)
      by_cases hlk : l < k
      · have hlt : (2 * l + 3) * (nh * dh).toNat ≤ (2 * k + 1) * (nh * dh).toNat :=
          Nat.mul_le_mul_right _ (by omega)
        have hS2 : (2 * l + 3) * (nh * dh).toNat = (2 * l + 2) * (nh * dh).toNat + (nh * dh).toNat := by
          ring
        have hK3 : (2 * k + 3) * (nh * dh).toNat =
            (2 * k + 1) * (nh * dh).toNat + (nh * dh).toNat + (nh * dh).toNat := by
          ring
        obtain ⟨hk1, hk2⟩ := hslots l hlk c hc
        rw [hkeep _ (by omega) (by omega) (Or.inl (by omega)),
          hkeep _ (by omega) (by omega) (Or.inl (by omega))]
        exact ⟨hk1, hk2⟩
      · have hlk' : l = k := by omega
        subst hlk'
        exact ⟨hkey c hc, hval c hc⟩

/-- The size of a block, `(2 · layers + 1) · nh · dh`, in natural numbers. -/
theorem bsize_toNat {layers nh dh : UInt64} (hL : layers.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16)
    (hdh : dh.toNat < 2 ^ 16) :
    ((2 * layers + 1) * (nh * dh)).toNat = (2 * layers.toNat + 1) * (nh * dh).toNat := by
  have hW : (nh * dh).toNat < 2 ^ 32 := small_mul hn hdh
  have h2 : (2 * layers + 1).toNat = 2 * layers.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, show (2 : UInt64).toNat = 2 from rfl, UInt64.toNat_one,
      Nat.mod_eq_of_lt (show 2 * layers.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
  rw [UInt64.toNat_mul, h2, Nat.mod_eq_of_lt]
  calc (2 * layers.toNat + 1) * (nh * dh).toNat < 2 ^ 17 * 2 ^ 32 :=
        Nat.mul_lt_mul_of_lt_of_lt (by omega) hW
    _ < 2 ^ 64 := by norm_num

/-- `step` at position `p` extends a cache of `p` blocks with the block of position `p`. -/
theorem step_cache {C : Array Float} {tokens : Array UInt64}
    {wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float}
    {layers T nh dh f : UInt64} {eps : Float} {p : Nat}
    (hp : p < T.toNat) (hT : T.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hn0 : 0 < nh.toNat) (hdh0 : 0 < dh.toNat) (hf : f.toNat < 2 ^ 32)
    (hL : layers.toNat < 2 ^ 16)
    (hall : T.toNat * ((2 * layers.toNat + 1) * (nh * dh).toNat) < 2 ^ 32)
    (hC : CacheIs C p ((2 * layers.toNat + 1) * (nh * dh).toNat) (nh * dh).toNat layers.toNat
      (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj T nh dh f
        eps layers.toNat)
      (fun l => blockKeys (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc
        wproj bproj T nh dh f eps l) g1 b1 wk bk (UInt64.ofNat l) T nh dh eps)
      (fun l => blockValues (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc
        wproj bproj T nh dh f eps l) g1 b1 wv bv (UInt64.ofNat l) T nh dh eps)) :
    CacheIs (step C wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj tokens[p]!
        layers nh dh f eps) (p + 1) ((2 * layers.toNat + 1) * (nh * dh).toNat) (nh * dh).toNat
      layers.toNat
      (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj T nh dh f
        eps layers.toNat)
      (fun l => blockKeys (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc
        wproj bproj T nh dh f eps l) g1 b1 wk bk (UInt64.ofNat l) T nh dh eps)
      (fun l => blockValues (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc
        wproj bproj T nh dh f eps l) g1 b1 wv bv (UInt64.ofNat l) T nh dh eps) := by
  have hW : (nh * dh).toNat < 2 ^ 32 := small_mul hn hdh
  have hND : (nh * dh).toNat = nh.toNat * dh.toNat := mul_toNat (by omega) (by omega)
  have hD0 : 0 < (nh * dh).toNat := by rw [hND]; exact Nat.mul_pos hn0 hdh0
  have hBsz := bsize_toNat hL hn hdh
  set Bn := (2 * layers.toNat + 1) * (nh * dh).toNat with hBn
  have hB0 : 0 < Bn := Nat.mul_pos (by omega) hD0
  have hall' : (p + 1) * Bn < 2 ^ 32 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hall
  have hpB : p * Bn + Bn = (p + 1) * Bn := by ring
  have hCsize := hC.size
  have hCnat : C.size.toUInt64.toNat = C.size :=
    UInt64.toNat_ofNat_of_lt' (show C.size < 2 ^ 64 by omega)
  have hBne : (2 * layers + 1) * (nh * dh) ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [hBsz] at this
    simp at this
    omega
  have hPos : C.size.toUInt64 / (if (2 * layers + 1) * (nh * dh) = 0 then 1
      else (2 * layers + 1) * (nh * dh)) = UInt64.ofNat p := by
    rw [ite_eq_right hBne]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_div, hCnat, hCsize, hBsz, Nat.mul_div_cancel _ hB0,
      toNat_ofNat_lt (n := T) hp]
  have hstep : step C wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj tokens[p]!
      layers nh dh f eps = appendBlock C (Nat.fold layers.toNat (fun i _ s => layerStep s C g1 b1 wq
        bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj (UInt64.ofNat i) (UInt64.ofNat p) nh dh f
        ((2 * layers + 1) * (nh * dh)) eps)
        (embedBlock wte wpe tokens[p]! (UInt64.ofNat p) (nh * dh) ((2 * layers + 1) * (nh * dh)))) := by
    unfold step LeanExe.loop
    simp only [hPos]
  obtain ⟨hsize, hhid, hslots⟩ := layerLoop (C := C) (tokens := tokens) (wte := wte) (wpe := wpe)
    (B := (2 * layers + 1) * (nh * dh)) (L := layers.toNat) (eps := eps) hp hT hn hdh hf hL hBsz
    (by rw [hBsz]; exact hall') (by rw [hBsz]; exact hC) layers.toNat le_rfl
  rw [hBsz] at hsize
  rw [hstep]
  set sL := Nat.fold layers.toNat (fun i _ s => layerStep s C g1 b1 wq bq wk bk wv bv wo bo g2 b2
    wfc bfc wproj bproj (UInt64.ofNat i) (UInt64.ofNat p) nh dh f ((2 * layers + 1) * (nh * dh))
    eps) (embedBlock wte wpe tokens[p]! (UInt64.ofNat p) (nh * dh) ((2 * layers + 1) * (nh * dh)))
  have hsum : C.size + sL.size < 2 ^ 64 := by omega
  have hread : ∀ j, j < p + 1 → ∀ x, x < Bn →
      (appendBlock C sL)[j * Bn + x]! = if j < p then C[j * Bn + x]! else sL[x]! := by
    intro j hj x hx
    have hjB : j * Bn + x < (j + 1) * Bn := by rw [Nat.succ_mul]; omega
    have hjle : (j + 1) * Bn ≤ (p + 1) * Bn := Nat.mul_le_mul_right _ hj
    rw [appendBlock_get hsum (by omega)]
    by_cases hjp : j < p
    · have : (j + 1) * Bn ≤ p * Bn := Nat.mul_le_mul_right _ hjp
      rw [ite_eq_left (by omega), ite_eq_left hjp]
    · have hjeq : j = p := by omega
      subst hjeq
      rw [ite_eq_right (by omega), ite_eq_right (lt_irrefl _), show j * Bn + x - C.size = x by omega]
  have hslot : ∀ l, l < layers.toNat → ∀ a, a ≤ 2 → ∀ c, c < (nh * dh).toNat →
      (2 * l + a) * (nh * dh).toNat + c < Bn := fun l hl a ha c hc => by
    have h1 : (2 * l + a) * (nh * dh).toNat + (nh * dh).toNat ≤ Bn := by
      rw [hBn, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  have hDB : (nh * dh).toNat ≤ Bn := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨by rw [appendBlock_size hsum, hsize, hCsize, hpB], fun j hj c hc => ?_,
    fun l hl j hj c hc => ?_, fun l hl j hj c hc => ?_⟩
  · rw [hread j hj c (by omega)]
    split_ifs with hjp
    · exact hC.hidden j hjp c hc
    · have hjeq : j = p := by omega
      subst hjeq
      exact hhid c hc
  · rw [hread j hj _ (hslot l hl 1 (by omega) c hc)]
    split_ifs with hjp
    · exact hC.keys l hl j hjp c hc
    · have hjeq : j = p := by omega
      subst hjeq
      exact (hslots l hl c hc).1
  · rw [hread j hj _ (hslot l hl 2 (by omega) c hc)]
    split_ifs with hjp
    · exact hC.values l hl j hjp c hc
    · have hjeq : j = p := by omega
      subst hjeq
      exact (hslots l hl c hc).2

/-- The cache after the first `n` tokens holds their blocks. -/
theorem cacheAfter_cache {tokens : Array UInt64}
    {wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float}
    {layers T nh dh f : UInt64} {eps : Float}
    (hT : T.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hn0 : 0 < nh.toNat) (hdh0 : 0 < dh.toNat) (hf : f.toNat < 2 ^ 32)
    (hL : layers.toNat < 2 ^ 16)
    (hall : T.toNat * ((2 * layers.toNat + 1) * (nh * dh).toNat) < 2 ^ 32) (n : Nat)
    (hnT : n ≤ T.toNat) :
    CacheIs (cacheAfter tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj
        layers nh dh f eps n) n ((2 * layers.toNat + 1) * (nh * dh).toNat) (nh * dh).toNat
      layers.toNat
      (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj T nh dh f
        eps layers.toNat)
      (fun l => blockKeys (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc
        wproj bproj T nh dh f eps l) g1 b1 wk bk (UInt64.ofNat l) T nh dh eps)
      (fun l => blockValues (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc
        wproj bproj T nh dh f eps l) g1 b1 wv bv (UInt64.ofNat l) T nh dh eps) := by
  induction n with
  | zero =>
    exact ⟨by simp [cacheAfter], fun j hj => absurd hj (by omega),
      fun l _ j hj => absurd hj (by omega), fun l _ j hj => absurd hj (by omega)⟩
  | succ n ih =>
    unfold cacheAfter
    rw [Nat.fold_succ]
    exact step_cache (by omega) hT hn hdh hn0 hdh0 hf hL hall (ih (by omega))

/-- The scores of a cache of `p + 1` blocks are row `p` of `forward`'s scores. -/
theorem scores_row {C : Array Float} {tokens : Array UInt64}
    {wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj gf bf : Array Float}
    {layers T nh dh f vocab : UInt64} {eps : Float} {p : Nat}
    (hp : p < T.toNat) (hT : T.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hv : vocab.toNat < 2 ^ 32) (hL : layers.toNat < 2 ^ 16)
    (hall : T.toNat * ((2 * layers.toNat + 1) * (nh * dh).toNat) < 2 ^ 32)
    (hC : CacheIs C (p + 1) ((2 * layers.toNat + 1) * (nh * dh).toNat) (nh * dh).toNat layers.toNat
      (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj T nh dh f
        eps layers.toNat) K V) :
    RowIs vocab.toNat p (scores C wte gf bf layers nh dh vocab eps)
      (forward tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj gf bf layers T
        nh dh f vocab eps) := by
  have hW : (nh * dh).toNat < 2 ^ 32 := small_mul hn hdh
  have hBsz := bsize_toNat hL hn hdh
  set Bn := (2 * layers.toNat + 1) * (nh * dh).toNat with hBn
  have hall' : (p + 1) * Bn < 2 ^ 32 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hall
  have hDB : (nh * dh).toNat ≤ Bn := Nat.le_mul_of_pos_left _ (by omega)
  have hCsize := hC.size
  have hCnat : C.size.toUInt64.toNat = C.size :=
    UInt64.toNat_ofNat_of_lt' (show C.size < 2 ^ 64 by omega)
  have hpB : (p + 1) * Bn = p * Bn + Bn := by ring
  have hlast : RowIs (nh * dh).toNat p (lastHidden C (nh * dh) ((2 * layers + 1) * (nh * dh)))
      (layerInput tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj T nh dh f
        eps layers.toNat) := by
    intro c hc
    have hC' : (UInt64.ofNat c).toNat = c := toNat_ofNat_lt hc
    have hsub : (C.size.toUInt64 - (2 * layers + 1) * (nh * dh)).toNat = p * Bn := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hCnat, hBsz]; omega), hCnat,
        hBsz]
      omega
    unfold lastHidden
    rw [build_get hc, UInt64.toNat_add, hsub, hC', Nat.mod_eq_of_lt (by omega)]
    exact hC.hidden p (by omega) c hc
  exact matMulT_row hp hT hW hv (layerNormRows_row hp hT hW hlast)

/-- The cached steps give `forward`'s scores bit for bit: `step` run on tokens `0` to `p`
from an empty cache, followed by `scores`, gives row `p` of `forward` on `T > p` tokens. -/
theorem steps_exact {tokens : Array UInt64}
    {wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj gf bf : Array Float}
    {layers T nh dh f vocab : UInt64} {eps : Float} {p : Nat}
    (hp : p < T.toNat) (hT : T.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hn0 : 0 < nh.toNat) (hdh0 : 0 < dh.toNat) (hf : f.toNat < 2 ^ 32)
    (hv : vocab.toNat < 2 ^ 32) (hL : layers.toNat < 2 ^ 16)
    (hall : T.toNat * ((2 * layers.toNat + 1) * (nh.toNat * dh.toNat)) < 2 ^ 32) :
    scores (cacheAfter tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj
        layers nh dh f eps (p + 1)) wte gf bf layers nh dh vocab eps =
      (forward tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj gf bf layers T
        nh dh f vocab eps).extract (p * vocab.toNat) ((p + 1) * vocab.toNat) := by
  have hND : (nh * dh).toNat = nh.toNat * dh.toNat := mul_toNat (by omega) (by omega)
  rw [← hND] at hall
  have hrow : RowIs vocab.toNat p (scores (cacheAfter tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo
      g2 b2 wfc bfc wproj bproj layers nh dh f eps (p + 1)) wte gf bf layers nh dh vocab eps)
      (forward tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj gf bf layers T
        nh dh f vocab eps) :=
    scores_row hp hT hn hdh hv hL hall
      (cacheAfter_cache hT hn hdh hn0 hdh0 hf hL hall (p + 1) hp)
  have hVF : (forward tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj gf bf
      layers T nh dh f vocab eps).size = T.toNat * vocab.toNat := by
    simp only [forward, matMulT, LeanExe.build, Array.size_ofFn]
    exact mul_toNat (by omega) hv
  have hS : (scores (cacheAfter tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj
      bproj layers nh dh f eps (p + 1)) wte gf bf layers nh dh vocab eps).size = vocab.toNat := by
    simp only [scores, matMulT, LeanExe.build, Array.size_ofFn, one_toNat]
  have hle : (p + 1) * vocab.toNat ≤ T.toNat * vocab.toNat := Nat.mul_le_mul_right _ hp
  have hpv : (p + 1) * vocab.toNat = p * vocab.toNat + vocab.toNat := by ring
  apply Array.ext
  · rw [hS, Array.size_extract, hVF]
    omega
  · intro c hc1 hc2
    have hcv : c < vocab.toNat := by rwa [hS] at hc1
    have hidx : p * vocab.toNat + c < (forward tokens wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc
        bfc wproj bproj gf bf layers T nh dh f vocab eps).size := by
      rw [hVF]; omega
    have h := hrow c hcv
    simp only [getElem!_pos, hc1, hidx] at h
    rw [h, Array.getElem_extract]

end Project.Gpt.Exact
