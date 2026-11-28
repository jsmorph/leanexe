module

public import Library.Numerics.Bignum.Third.DivNat
public import Library.Numerics.Bignum.ToText

@[expose] public section

/-!
The leaves of the printer and the powers of `10^9`.

`sigSeg_spec` states the scan for the top nonzero limb of a segment, the loop of the second
iteration's `trimSeg`.  `leafChunks_spec` states the first iteration's quadratic printer in place:
`K` divisions by `10^9` of a segment, each over the limbs below the top zero limbs, write the `K`
chunks of nine digits `X / 10^(9 j) mod 10^9`.  `powInit_spec` states the table of the powers
`P_i = 10^(9·2^i)` that `powInit` computes by Karatsuba's squares.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-- The scan for the top nonzero limb of the `len` limbs at `p`. -/
theorem sigSeg_spec (W : Array UInt64) (p len : UInt64) (hp : p.toNat + len.toNat < 2 ^ 64) :
    (LeanExe.loop len (0 : UInt64) fun i k => if W[(p + i).toNat]! = 0 then k else i + 1).toNat
        ≤ len.toNat ∧
      (∀ i, (LeanExe.loop len (0 : UInt64) fun i k =>
          if W[(p + i).toNat]! = 0 then k else i + 1).toNat ≤ i → i < len.toNat →
        W[p.toNat + i]! = 0) ∧
      (0 < (LeanExe.loop len (0 : UInt64) fun i k =>
          if W[(p + i).toNat]! = 0 then k else i + 1).toNat →
        W[p.toNat + (LeanExe.loop len (0 : UInt64) fun i k =>
          if W[(p + i).toNat]! = 0 then k else i + 1).toNat - 1]! ≠ 0) := by
  have h := loop_induction (n := len) (init := (0 : UInt64))
    (f := fun i k => if W[(p + i).toNat]! = 0 then k else i + 1)
    (fun j (k : UInt64) => k.toNat ≤ j ∧ (∀ i, k.toNat ≤ i → i < j → W[p.toNat + i]! = 0) ∧
      (0 < k.toNat → W[p.toNat + k.toNat - 1]! ≠ 0))
    ⟨by simp, fun i _ h => absurd h (Nat.not_lt_zero _), fun h => absurd h (by simp)⟩
    (by
      intro j k hj ⟨h1, h2, h3⟩
      have hjj : (UInt64.ofNat j).toNat = j := toNat_ofNat_lt (by omega)
      have hpj : (p + UInt64.ofNat j).toNat = p.toNat + j := by rw [toNat_add_lt] <;> omega
      show _ ∧ _ ∧ _
      rw [hpj]
      by_cases hz : W[p.toNat + j]! = 0
      · rw [if_pos hz]
        refine ⟨by omega, fun i hi1 hi2 => ?_, h3⟩
        rcases Nat.lt_or_ge i j with h | h
        · exact h2 i hi1 h
        · rw [show i = j by omega]; exact hz
      · rw [if_neg hz]
        have hj1 : (UInt64.ofNat j + 1).toNat = j + 1 := by
          rw [toNat_add_lt] <;> simp [hjj] <;> omega
        rw [hj1]
        refine ⟨le_rfl, fun i hi1 hi2 => by omega, fun _ => ?_⟩
        rwa [show p.toNat + (j + 1) - 1 = p.toNat + j by omega])
  exact h

/-- The state of `leafChunks` after `j` chunks: the low `l` limbs hold `X / 10^(9 j)`, the limbs
from `l` to `len` are zeros, and the chunks below `j` are written. -/
def LeafInv (W : Array UInt64) (p len cp X : ℕ) (j : ℕ) (st : UInt64 × Array UInt64) : Prop :=
  st.2.size = W.size ∧
  (∀ q, (q < p ∨ p + len ≤ q) → (q < cp ∨ cp + j ≤ q) → st.2[q]! = W[q]!) ∧
  st.1.toNat ≤ len ∧ SegDigits st.2 p len ∧ (∀ i, st.1.toNat ≤ i → i < len → st.2[p + i]! = 0) ∧
  segVal st.2 p st.1.toNat = X / 10 ^ (9 * j) ∧
  (∀ i, i < j → st.2[cp + i]!.toNat = X / 10 ^ (9 * i) % 10 ^ 9)

/-- The first iteration's quadratic printer in place: `leafChunks` writes the `K` chunks of nine
digits of the `len` limbs at `p` to the `K` words at `cp`. -/
theorem leafChunks_spec (W : Array UInt64) (p len cp K : UInt64) (hW : W.size < 2 ^ 62)
    (hp : p.toNat + len.toNat ≤ W.size) (hc : cp.toNat + K.toNat ≤ W.size)
    (hsep : cp.toNat + K.toNat ≤ p.toNat ∨ p.toNat + len.toNat ≤ cp.toNat)
    (hdig : SegDigits W p.toNat len.toNat) :
    (leafChunks W p len cp K).size = W.size ∧
    (∀ q, (q < p.toNat ∨ p.toNat + len.toNat ≤ q) → (q < cp.toNat ∨ cp.toNat + K.toNat ≤ q) →
      (leafChunks W p len cp K)[q]! = W[q]!) ∧
    ∀ j, j < K.toNat → (leafChunks W p len cp K)[cp.toNat + j]!.toNat =
      segVal W p.toNat len.toNat / 10 ^ (9 * j) % 10 ^ 9 := by
  have key := loop_induction (n := K) (init := (len, W))
    (f := fun j st =>
      ((if st.1 != 0 ∧ ((divSmallSeg st.2 p st.1 1000000000).2.set! (cp + j).toNat
          (divSmallSeg st.2 p st.1 1000000000).1)[(p + st.1 - 1).toNat]! = 0 then st.1 - 1
        else st.1),
        (divSmallSeg st.2 p st.1 1000000000).2.set! (cp + j).toNat
          (divSmallSeg st.2 p st.1 1000000000).1))
    (LeafInv W p.toNat len.toNat cp.toNat (segVal W p.toNat len.toNat))
    ⟨rfl, fun _ _ _ => rfl, le_rfl, hdig, fun i h1 h2 => absurd h1 (by simp; omega), by simp,
      fun i hi => by omega⟩
    (by
      intro j st hj ⟨s1, s2, s3, s4, s5, s6, s7⟩
      have hjj : (UInt64.ofNat j).toNat = j := toNat_ofNat_lt (by omega)
      have hcj : (cp + UInt64.ofNat j).toNat = cp.toNat + j := by rw [toNat_add_lt] <;> omega
      obtain ⟨d1, d2, d3, d4, d5⟩ := divSmallSeg_spec st.2 p st.1 1000000000 (by rw [s1]; omega)
        (by decide) (by rw [base_eq]; decide) (by rw [s1]; omega) (s4.mono s3)
      simp only [UInt64.reduceToNat] at d4 d5
      generalize hD : divSmallSeg st.2 p st.1 1000000000 = D at d1 d2 d3 d4 d5
      rw [hcj]
      have hin : cp.toNat + j < D.2.size := by omega
      have hget := fun q => get_set D.2 (cp.toNat + j) D.1 q hin
      generalize hV : D.2.set! (cp.toNat + j) D.1 = V at hget
      have hVs : V.size = W.size := by rw [← hV]; simp [d1, s1]
      have hVr : ∀ i, i < len.toNat → V[p.toNat + i]! = D.2[p.toNat + i]! := fun i hi => by
        rw [hget, if_neg (by omega)]
      rw [s6] at d4 d5
      have hdiv : segVal W p.toNat len.toNat / 10 ^ (9 * j) / 1000000000 =
          segVal W p.toNat len.toNat / 10 ^ (9 * (j + 1)) := by
        rw [Nat.div_div_eq_div_mul, show 9 * (j + 1) = 9 * j + 9 by ring, pow_add]; rfl
      have hV1 : segVal V p.toNat st.1.toNat = segVal W p.toNat len.toNat / 10 ^ (9 * (j + 1)) := by
        rw [← hdiv, ← d4]; exact segVal_congr fun i hi => hVr i (by omega)
      have hzero : ∀ i, st.1.toNat ≤ i → i < len.toNat → V[p.toNat + i]! = 0 := fun i h1 h2 => by
        rw [hVr i h2, d2 _ (by omega)]; exact s5 i h1 h2
      -- the new length
      obtain ⟨l', hl', hl'1, hl'2, hl'3⟩ : ∃ l' : UInt64,
          (if (st.1 != 0) = true ∧ V[(p + st.1 - 1).toNat]! = 0 then st.1 - 1 else st.1) = l' ∧
          l'.toNat ≤ st.1.toNat ∧ (∀ i, l'.toNat ≤ i → i < len.toNat → V[p.toNat + i]! = 0) ∧
          segVal V p.toNat l'.toNat = segVal W p.toNat len.toNat / 10 ^ (9 * (j + 1)) := by
        by_cases hc : (st.1 != 0) = true ∧ V[(p + st.1 - 1).toNat]! = 0
        · refine ⟨_, by rw [if_pos hc], ?_⟩
          have hne : st.1 ≠ 0 := by simpa using hc.1
          have hne' : st.1.toNat ≠ 0 := fun h => hne (UInt64.toNat_inj.mp (by rw [h]; rfl))
          have hl1 : (st.1 - 1).toNat = st.1.toNat - 1 := by rw [toNat_sub_le' (by simp; omega)]; simp
          have htop := hc.2
          rw [show (p + st.1 - 1).toNat = p.toNat + (st.1.toNat - 1) by
            rw [toNat_sub_le' (by rw [toNat_add_lt (by omega)]; simp; omega),
              toNat_add_lt (by omega)]; simp; omega] at htop
          rw [hl1]
          refine ⟨by omega, fun i h1 h2 => ?_, ?_⟩
          · by_cases hi : i = st.1.toNat - 1
            · rw [hi]; exact htop
            · exact hzero i (by omega) h2
          · rw [← hV1, show st.1.toNat = st.1.toNat - 1 + 1 by omega, segVal_succ, htop]
            simp
        · exact ⟨_, by rw [if_neg hc], le_rfl, hzero, hV1⟩
      rw [hl']
      refine ⟨hVs, fun q h1 h2 => ?_, by show l'.toNat ≤ len.toNat; omega, fun i hi => ?_, hl'2,
        hl'3, fun i hi => ?_⟩
      · rw [hget, if_neg (by omega), d2 q (by omega)]; exact s2 q h1 (by omega)
      · rw [hVr i hi]
        by_cases hil : i < st.1.toNat
        · exact d3 i hil
        · rw [d2 _ (by omega), s5 i (by omega) hi]; exact base_pos
      · rw [hget]
        split
        · rename_i h; rw [show i = j by omega, d5]; norm_num
        · rw [d2 _ (by omega)]; exact s7 i (by omega))
  obtain ⟨k1, k2, -, -, -, -, k7⟩ := key
  exact ⟨k1, k2, k7⟩

end Library.Numerics.Bignum

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-- A segment whose top limb is not 0 is at least `β^(n-1)`. -/
theorem segVal_ge_top {W : Array UInt64} {p n : ℕ} (hn : 1 ≤ n) (htop : W[p + n - 1]! ≠ 0) :
    base ^ (n - 1) ≤ segVal W p n := by
  have hpos : 0 < W[p + n - 1]!.toNat := by
    rcases Nat.eq_zero_or_pos W[p + n - 1]!.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by rw [h0]; rfl)) htop
    · exact h0
  have := segVal_succ W p (n - 1)
  rw [show n - 1 + 1 = n by omega, show p + (n - 1) = p + n - 1 by omega] at this
  rw [this]
  calc base ^ (n - 1) = 1 * base ^ (n - 1) := by ring
    _ ≤ W[p + n - 1]!.toNat * base ^ (n - 1) := Nat.mul_le_mul_right _ hpos
    _ ≤ _ := Nat.le_add_left _ _

/-- Entry `j` of the table of powers at `tb`: the position and the number of limbs of
`P_j = 10^(9·2^j)` within `2^(j+1)` words from `pb`, with at most `2^j` limbs and a top limb that
is not 0. -/
def PowOK (W : Array UInt64) (tb pb j : ℕ) : Prop :=
  pb ≤ W[tb + 2 * j]!.toNat ∧ W[tb + 2 * j]!.toNat + W[tb + 2 * j + 1]!.toNat ≤ pb + 2 ^ (j + 1) ∧
  1 ≤ W[tb + 2 * j + 1]!.toNat ∧ W[tb + 2 * j + 1]!.toNat ≤ 2 ^ j ∧
  SegDigits W W[tb + 2 * j]!.toNat W[tb + 2 * j + 1]!.toNat ∧
  segVal W W[tb + 2 * j]!.toNat W[tb + 2 * j + 1]!.toNat = 10 ^ (9 * 2 ^ j) ∧
  W[W[tb + 2 * j]!.toNat + W[tb + 2 * j + 1]!.toNat - 1]! ≠ 0

/-- An entry of the table is kept by every array that keeps its two words and its power. -/
theorem PowOK.congr {W V : Array UInt64} {tb pb j : ℕ} (h : PowOK W tb pb j)
    (h1 : V[tb + 2 * j]! = W[tb + 2 * j]!) (h2 : V[tb + 2 * j + 1]! = W[tb + 2 * j + 1]!)
    (h3 : ∀ q, W[tb + 2 * j]!.toNat ≤ q → q < W[tb + 2 * j]!.toNat + W[tb + 2 * j + 1]!.toNat →
      V[q]! = W[q]!) : PowOK V tb pb j := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  unfold PowOK
  rw [h1, h2]
  refine ⟨a1, a2, a3, a4, a5.congr fun i hi => h3 _ (by omega) (by omega), ?_, ?_⟩
  · rw [← a6]; exact segVal_congr fun i hi => h3 _ (by omega) (by omega)
  · rw [h3 _ (by omega) (by omega)]; exact a7

end Library.Numerics.Bignum

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-- The state of `powInit` after `i` squares. -/
def PowInv (W : Array UInt64) (tb pb A : ℕ) (i : ℕ) (V : Array UInt64) : Prop :=
  V.size = W.size ∧
  (∀ q, ¬ (tb ≤ q ∧ q < tb + 2 * i + 2) → ¬ (pb ≤ q ∧ q < pb + A) → V[q]! = W[q]!) ∧
  (∀ j, j ≤ i → PowOK V tb pb j) ∧
  (∀ j, j ≤ i → V[tb + 2 * j]!.toNat + V[tb + 2 * j + 1]!.toNat ≤
    V[tb + 2 * i]!.toNat + V[tb + 2 * i + 1]!.toNat)

set_option maxHeartbeats 4000000 in
/-- `powInit` writes the table of the powers `P_j = 10^(9·2^j)` for `j ≤ K` at `tb`, the powers
from `pb`, and changes no word outside the table and the `7·2^K` words from `pb`. -/
theorem powInit_spec (t : UInt64) (W : Array UInt64) (tb pb K : UInt64) (hW : W.size < 2 ^ 62)
    (hK : K.toNat < 40) (htb : tb.toNat + 2 * K.toNat + 2 ≤ pb.toNat)
    (hsz : pb.toNat + 7 * 2 ^ K.toNat ≤ W.size) :
    (powInit t W tb pb K).size = W.size ∧
    (∀ q, ¬ (tb.toNat ≤ q ∧ q < tb.toNat + 2 * K.toNat + 2) →
      ¬ (pb.toNat ≤ q ∧ q < pb.toNat + 7 * 2 ^ K.toNat) → (powInit t W tb pb K)[q]! = W[q]!) ∧
    ∀ j, j ≤ K.toNat → PowOK (powInit t W tb pb K) tb.toNat pb.toNat j := by
  have hb := base_eq
  have hb0 := base_pos
  have hpK : 2 ^ K.toNat < 2 ^ 40 := Nat.pow_lt_pow_right (by norm_num) hK
  have htb1 : (tb + 1).toNat = tb.toNat + 1 := by rw [toNat_add_lt] <;> simp <;> omega
  -- the first entry
  have h2K : 0 < 2 ^ K.toNat := pow_pos (by norm_num) _
  have hin0 : pb.toNat < W.size := by omega
  generalize hV0 : ((W.set! pb.toNat 1000000000).set! tb.toNat pb).set! (tb + 1).toNat 1 = V0
  have g0 : ∀ q, V0[q]! = if q = tb.toNat + 1 then 1 else if q = tb.toNat then pb else
      if q = pb.toNat then 1000000000 else W[q]! := fun q => by
    have s1 : (W.set! pb.toNat 1000000000).size = W.size := by simp
    have s2 : ((W.set! pb.toNat 1000000000).set! tb.toNat pb).size = W.size := by simp
    rw [← hV0, htb1, get_set _ _ _ _ (by rw [s2]; omega), get_set _ _ _ _ (by rw [s1]; omega),
      get_set _ _ _ _ (by omega)]
  have key := loop_induction (n := K) (init := V0)
    (f := fun i W =>
      (((kara t W W[(tb + 2 * i).toNat]! W[(tb + 2 * i).toNat]!
        (W[(tb + 2 * i).toNat]! + W[(tb + 2 * i + 1).toNat]!)
        (W[(tb + 2 * i).toNat]! + 3 * W[(tb + 2 * i + 1).toNat]!) W[(tb + 2 * i + 1).toNat]!).set!
          (tb + 2 * i + 2).toNat (W[(tb + 2 * i).toNat]! + W[(tb + 2 * i + 1).toNat]!)).set!
          (tb + 2 * i + 3).toNat
          (if (kara t W W[(tb + 2 * i).toNat]! W[(tb + 2 * i).toNat]!
            (W[(tb + 2 * i).toNat]! + W[(tb + 2 * i + 1).toNat]!)
            (W[(tb + 2 * i).toNat]! + 3 * W[(tb + 2 * i + 1).toNat]!)
            W[(tb + 2 * i + 1).toNat]!)[(W[(tb + 2 * i).toNat]! + 3 * W[(tb + 2 * i + 1).toNat]! -
              1).toNat]! = 0 then 2 * W[(tb + 2 * i + 1).toNat]! - 1
          else 2 * W[(tb + 2 * i + 1).toNat]!)))
    (PowInv W tb.toNat pb.toNat (7 * 2 ^ K.toNat))
    ⟨by rw [← hV0]; simp, fun q h1 h2 => by
      rw [g0, if_neg (by omega), if_neg (by omega), if_neg (by omega)], fun j hj => by
      rw [show j = 0 by omega]
      have e1 : V0[tb.toNat + 2 * 0]! = pb := by rw [g0]; simp
      have e2 : V0[tb.toNat + 2 * 0 + 1]! = 1 := by rw [g0]; simp
      have e3 : V0[pb.toNat]! = 1000000000 := by
        rw [g0, if_neg (by omega), if_neg (by omega), if_pos rfl]
      unfold PowOK
      rw [e1, e2, show (1 : UInt64).toNat = 1 from rfl]
      refine ⟨le_rfl, by simp, le_rfl, by simp, ?_, ?_, ?_⟩
      · intro i hi
        rw [show i = 0 by omega, Nat.add_zero, e3, hb]; decide
      · rw [segVal_succ, segVal_zero, Nat.add_zero, e3]; norm_num
      · rw [show pb.toNat + 1 - 1 = pb.toNat by omega, e3]; decide, fun j hj => by
      rw [show j = 0 by omega]⟩ (by
      intro i V hi ⟨v1, v2, v3, v4⟩
      have hii : (UInt64.ofNat i).toNat = i := toNat_ofNat_lt (by omega)
      have h2i : (tb + 2 * UInt64.ofNat i).toNat = tb.toNat + 2 * i := by
        simp only [UInt64.toNat_add, UInt64.toNat_mul, hii, UInt64.reduceToNat]; omega
      have h2i1 : (tb + 2 * UInt64.ofNat i + 1).toNat = tb.toNat + 2 * i + 1 := by
        simp only [UInt64.toNat_add, UInt64.toNat_mul, hii, UInt64.reduceToNat]; omega
      have h2i2 : (tb + 2 * UInt64.ofNat i + 2).toNat = tb.toNat + 2 * i + 2 := by
        simp only [UInt64.toNat_add, UInt64.toNat_mul, hii, UInt64.reduceToNat]; omega
      have h2i3 : (tb + 2 * UInt64.ofNat i + 3).toNat = tb.toNat + 2 * i + 3 := by
        simp only [UInt64.toNat_add, UInt64.toNat_mul, hii, UInt64.reduceToNat]; omega
      have hpow : 2 ^ (i + 1) ≤ 2 ^ K.toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpow' : 2 ^ (i + 1) = 2 * 2 ^ i := by ring
      rw [h2i, h2i1, h2i2, h2i3]
      have hVi := v3 i le_rfl
      have hend := v4
      generalize hpw : V[tb.toNat + 2 * i]! = pw at hVi hend
      generalize hnw : V[tb.toNat + 2 * i + 1]! = nw at hVi hend
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hVi
      simp only [hpw, hnw] at a1 a2 a3 a4 a5 a6 a7
      obtain ⟨P, n, hP, hn⟩ : ∃ P n, pw.toNat = P ∧ nw.toNat = n := ⟨_, _, rfl, rfl⟩
      simp only [hP, hn] at a1 a2 a3 a4 a5 a6 a7 hend
      have hpn : (pw + nw).toNat = P + n := by rw [toNat_add_lt (by omega), hP, hn]
      have h3n : (3 * nw).toNat = 3 * n := by
        simp only [UInt64.toNat_mul, hn, UInt64.reduceToNat]; omega
      have hp3 : (pw + 3 * nw).toNat = P + 3 * n := by rw [toNat_add_lt (by omega), hP, h3n]
      have hp31 : (pw + 3 * nw - 1).toNat = P + 3 * n - 1 := by
        rw [toNat_sub_le' (by rw [hp3]; simp; omega), hp3]; simp
      have h2n : (2 * nw).toNat = 2 * n := by
        simp only [UInt64.toNat_mul, hn, UInt64.reduceToNat]; omega
      have h2n1 : (2 * nw - 1).toNat = 2 * n - 1 := by
        rw [toNat_sub_le' (by rw [h2n]; simp; omega), h2n]; simp
      -- the square
      have hk := kara_spec t n V pw pw (pw + nw) (pw + 3 * nw) nw hn (by omega)
        (by rw [hP, hpn]) (by rw [hP, hpn]) (by rw [hpn, hp3]; omega) (by rw [hp3]; omega)
        (by rw [hP]; exact a5) (by rw [hP]; exact a5)
      unfold KaraPost at hk
      rw [hP, hpn, hp3, a6] at hk
      obtain ⟨k1, k2, k3, k4⟩ := hk
      rw [hp31]
      generalize hR : kara t V pw pw (pw + nw) (pw + 3 * nw) nw = R at k1 k2 k3 k4
      have hPP : 10 ^ (9 * 2 ^ i) * 10 ^ (9 * 2 ^ i) = 10 ^ (9 * 2 ^ (i + 1)) := by
        rw [← pow_add, hpow']; ring_nf
      rw [hPP] at k4
      have hPge : base ^ (n - 1) ≤ 10 ^ (9 * 2 ^ i) := by rw [← a6]; exact segVal_ge_top a3 a7
      have hsq : base ^ (2 * n - 2) ≤ 10 ^ (9 * 2 ^ (i + 1)) := by
        rw [← hPP, show 2 * n - 2 = (n - 1) + (n - 1) by omega, pow_add]
        exact Nat.mul_le_mul hPge hPge
      -- the new entry
      obtain ⟨nn, hnn, hnn1, hnn2, hdnn, hvnn, htnn⟩ : ∃ nn : UInt64,
          (if R[P + 3 * n - 1]! = 0 then 2 * nw - 1 else 2 * nw) = nn ∧
          2 * n - 1 ≤ nn.toNat ∧ nn.toNat ≤ 2 * n ∧ SegDigits R (P + n) nn.toNat ∧
          segVal R (P + n) nn.toNat = 10 ^ (9 * 2 ^ (i + 1)) ∧
          R[P + n + nn.toNat - 1]! ≠ 0 := by
        by_cases htop : R[P + 3 * n - 1]! = 0
        · refine ⟨_, by rw [if_pos htop], by rw [h2n1], by rw [h2n1]; omega,
            by rw [h2n1]; exact k3.mono (by omega), ?_, ?_⟩
          · rw [h2n1, ← k4, show 2 * n = 2 * n - 1 + 1 by omega, segVal_succ,
              show P + n + (2 * n - 1) = P + 3 * n - 1 by omega, htop]
            simp
          · rw [h2n1]
            have hlt : 10 ^ (9 * 2 ^ (i + 1)) < base ^ (2 * n - 1) := by
              have := segVal_lt (k3.mono (k' := 2 * n - 1) (by omega))
              rw [show segVal R (P + n) (2 * n - 1) = 10 ^ (9 * 2 ^ (i + 1)) by
                rw [← k4, show 2 * n = 2 * n - 1 + 1 by omega, segVal_succ,
                  show P + n + (2 * n - 1) = P + 3 * n - 1 by omega, htop]; simp] at this
              exact this
            have hdig := segVal_digit (k3.mono (k' := 2 * n - 1) (by omega))
              (show 2 * n - 2 < 2 * n - 1 by omega)
            rw [show segVal R (P + n) (2 * n - 1) = 10 ^ (9 * 2 ^ (i + 1)) by
              rw [← k4, show 2 * n = 2 * n - 1 + 1 by omega, segVal_succ,
                show P + n + (2 * n - 1) = P + 3 * n - 1 by omega, htop]; simp] at hdig
            rw [Nat.mod_eq_of_lt (by
              rw [Nat.div_lt_iff_lt_mul (pow_pos base_pos _), ← pow_succ']
              rw [show 2 * n - 2 + 1 = 2 * n - 1 by omega]; exact hlt)] at hdig
            have hge : 1 ≤ 10 ^ (9 * 2 ^ (i + 1)) / base ^ (2 * n - 2) :=
              (Nat.le_div_iff_mul_le (pow_pos base_pos _)).mpr (by rw [Nat.one_mul]; exact hsq)
            rw [show P + n + (2 * n - 1) - 1 = P + n + (2 * n - 2) by omega]
            intro h0
            rw [h0] at hdig
            have h00 : (0 : UInt64).toNat = 0 := rfl
            omega
        · refine ⟨_, by rw [if_neg htop], by rw [h2n]; omega, by rw [h2n], by rw [h2n]; exact k3,
            by rw [h2n]; exact k4, by rw [h2n, show P + n + 2 * n - 1 = P + 3 * n - 1 by omega]
                                      exact htop⟩
      rw [hnn]
      have hin2 : tb.toNat + 2 * i + 2 < R.size := by omega
      have hin3 : tb.toNat + 2 * i + 3 < (R.set! (tb.toNat + 2 * i + 2) (pw + nw)).size := by
        simp; omega
      have g : ∀ q, ((R.set! (tb.toNat + 2 * i + 2) (pw + nw)).set! (tb.toNat + 2 * i + 3) nn)[q]! =
          if q = tb.toNat + 2 * i + 3 then nn else if q = tb.toNat + 2 * i + 2 then pw + nw
          else R[q]! := fun q => by rw [get_set _ _ _ _ hin3, get_set _ _ _ _ hin2]
      generalize hV' : (R.set! (tb.toNat + 2 * i + 2) (pw + nw)).set! (tb.toNat + 2 * i + 3) nn = V'
        at g
      have hV's : V'.size = W.size := by rw [← hV']; simp [k1, v1]
      have hRV : ∀ q, q < P + n → R[q]! = V[q]! := fun q hq => k2 q (by omega) (by omega)
      have hV'R : ∀ q, pb.toNat ≤ q → V'[q]! = R[q]! := fun q hq => by
        rw [g, if_neg (by omega), if_neg (by omega)]
      refine ⟨hV's, fun q h1 h2 => ?_, fun j hj => ?_, fun j hj => ?_⟩
      · rw [g, if_neg (by omega), if_neg (by omega), k2 q (by omega) (by omega)]
        exact v2 q (by omega) h2
      · rcases Nat.lt_or_ge j (i + 1) with hj' | hj'
        · have hVj := v3 j (by omega)
          have e1 : V'[tb.toNat + 2 * j]! = V[tb.toNat + 2 * j]! := by
            rw [g, if_neg (by omega), if_neg (by omega), k2 _ (by omega) (by omega)]
          have e2 : V'[tb.toNat + 2 * j + 1]! = V[tb.toNat + 2 * j + 1]! := by
            rw [g, if_neg (by omega), if_neg (by omega), k2 _ (by omega) (by omega)]
          have hej := hend j (by omega)
          exact hVj.congr e1 e2 fun q hq1 hq2 => by
            rw [hV'R q (by have := hVj.1; omega), hRV q (by omega)]
        · rw [show j = i + 1 by omega]
          unfold PowOK
          have e1 : V'[tb.toNat + 2 * (i + 1)]! = pw + nw := by
            rw [g, if_neg (by omega), if_pos (by omega)]
          have e2 : V'[tb.toNat + 2 * (i + 1) + 1]! = nn := by rw [g, if_pos (by omega)]
          rw [e1, e2, hpn]
          refine ⟨by omega, by omega, by omega, by omega,
            hdnn.congr fun i' hi' => hV'R _ (by omega), ?_, ?_⟩
          · rw [← hvnn]; exact segVal_congr fun i' hi' => hV'R _ (by omega)
          · rw [hV'R _ (by omega)]; exact htnn
      · have e1 : V'[tb.toNat + 2 * (i + 1)]! = pw + nw := by
          rw [g, if_neg (by omega), if_pos (by omega)]
        have e2 : V'[tb.toNat + 2 * (i + 1) + 1]! = nn := by rw [g, if_pos (by omega)]
        rw [e1, e2, hpn]
        rcases Nat.lt_or_ge j (i + 1) with hj' | hj'
        · have e3 : V'[tb.toNat + 2 * j]! = V[tb.toNat + 2 * j]! := by
            rw [g, if_neg (by omega), if_neg (by omega), k2 _ (by omega) (by omega)]
          have e4 : V'[tb.toNat + 2 * j + 1]! = V[tb.toNat + 2 * j + 1]! := by
            rw [g, if_neg (by omega), if_neg (by omega), k2 _ (by omega) (by omega)]
          have hej := hend j (by omega)
          rw [e3, e4]; omega
        · rw [show j = i + 1 by omega, e1, e2, hpn])
  obtain ⟨k1, k2, k3, -⟩ := key
  unfold powInit
  rw [hV0]
  exact ⟨k1, k2, k3⟩

end Library.Numerics.Bignum
