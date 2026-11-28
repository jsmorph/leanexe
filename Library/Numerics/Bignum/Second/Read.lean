module

public import Library.Numerics.Bignum.Second.Mul
public import Library.Numerics.Bignum.OfText
public import Library.Numerics.Bignum.Second.Spec

@[expose] public section

/-!
The reader of the second iteration equals the first iteration's.  `decimalValueDC` reads the
digits in chunks of nine, `ch i` for the chunk of index `i` from the least significant end, and
`chunkSum ch p e = Σ_{i<e} ch (p + i) · 10^(9 i)` is the value of the `e` chunks from `p`.
`readInit_spec` states that each base element of `e0` limbs holds the `chunkSum` of its chunks, by
Horner's rule in place (`mulAddSeg_spec`), and that `10^(9 e0)` follows the elements.
`readPass_spec` states that a pass turns the elements of `e` limbs into elements of `2 e` limbs,
`l0 + 10^(9 e) l1` by `kara_spec` and `addGen_spec`, and squares the power, and `passes_spec`
iterates it until one element of `N` limbs remains.  `chunkSum_top` relates the chunks to the first
iteration's `dv` of the padded digits, so that `decimalValueDC_eq` meets `decimalValue_eq`.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open Library.Numerics.Decimal.Int64Text (digitsValue isDigitWord isDigitWord_iff isDigitW
  magnitude magnitude_cons digitsValue_pos denote denote_minus denote_plain denote_zero
  getElem!_of_toList toList_cons_of_size isDigitWord_ne48)
open LeanExe.Dialect

/-! ## Multiply and add in place -/

/-- `mulAddSeg` replaces the `len` words from `p` by their value times `m` plus `a`, with the
final carry dropped: the words hold `segVal · m + a` when it is below `base ^ len`. -/
theorem mulAddSeg_spec (W : Array UInt64) (p len m a : UInt64) (hW : W.size < 2 ^ 64)
    (hp : p.toNat + len.toNat ≤ W.size) (hd : SegDigits W p.toNat len.toNat)
    (hm : m.toNat < base) (ha : a.toNat < base)
    (hlt : segVal W p.toNat len.toNat * m.toNat + a.toNat < base ^ len.toNat) :
    (mulAddSeg W p len m a).size = W.size ∧
    (∀ q, (q < p.toNat ∨ p.toNat + len.toNat ≤ q) → (mulAddSeg W p len m a)[q]! = W[q]!) ∧
    SegDigits (mulAddSeg W p len m a) p.toNat len.toNat ∧
    segVal (mulAddSeg W p len m a) p.toNat len.toNat =
      segVal W p.toNat len.toNat * m.toNat + a.toNat := by
  unfold mulAddSeg
  have key : ∀ (s : UInt64 × Array UInt64), s.2.size = W.size ∧
      (∀ q, (q < p.toNat ∨ p.toNat + len.toNat ≤ q) → s.2[q]! = W[q]!) ∧
      SegDigits s.2 p.toNat len.toNat ∧ s.1.toNat < base ∧
      segVal s.2 p.toNat len.toNat + s.1.toNat * base ^ len.toNat =
        segVal W p.toNat len.toNat * m.toNat + a.toNat →
      s.2.size = W.size ∧ (∀ q, (q < p.toNat ∨ p.toNat + len.toNat ≤ q) → s.2[q]! = W[q]!) ∧
      SegDigits s.2 p.toNat len.toNat ∧
      segVal s.2 p.toNat len.toNat = segVal W p.toNat len.toNat * m.toNat + a.toNat := by
    rintro s ⟨h1, h2, h3, -, h5⟩
    refine ⟨h1, h2, h3, ?_⟩
    have hs := segVal_lt h3
    have hz : s.1.toNat = 0 := by
      by_contra hne
      have : 1 * base ^ len.toNat ≤ s.1.toNat * base ^ len.toNat :=
        Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.mpr hne)
      omega
    rw [hz] at h5; simpa using h5
  apply key
  refine loop_induction (P := fun i (s : UInt64 × Array UInt64) => s.2.size = W.size ∧
      (∀ q, (q < p.toNat ∨ p.toNat + i ≤ q) → s.2[q]! = W[q]!) ∧
      SegDigits s.2 p.toNat i ∧ s.1.toNat < base ∧
      segVal s.2 p.toNat i + s.1.toNat * base ^ i = segVal W p.toNat i * m.toNat + a.toNat)
    ⟨rfl, fun _ _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero _), ha, by simp [segVal]⟩ ?_
  intro i s hi ⟨hs, hfr, hdg, hc, hv⟩
  have hii : (UInt64.ofNat i).toNat = i := toNat_ofNat_lt (by omega)
  have hpi : (p + UInt64.ofNat i).toNat = p.toNat + i := by rw [toNat_add_lt] <;> omega
  have hX := read_kept (x := p.toNat) hfr fun i' hi' => by omega
  have hXd := hd i hi
  dsimp only
  rw [hpi, hX]
  have ht : (W[p.toNat + i]! * m + s.1).toNat = W[p.toNat + i]!.toNat * m.toNat + s.1.toNat := by
    rw [base_eq] at hXd hm hc
    have : W[p.toNat + i]!.toNat * m.toNat ≤ 4294967295 * 4294967295 :=
      Nat.mul_le_mul (by omega) (by omega)
    rw [UInt64.toNat_add, UInt64.toNat_mul]
    rw [Nat.mod_eq_of_lt (by omega : W[p.toNat + i]!.toNat * m.toNat < 2 ^ 64)]
    omega
  generalize W[p.toNat + i]! * m + s.1 = t at ht
  have hdin : p.toNat + i < s.2.size := by omega
  have hget := fun q => get_set s.2 (p.toNat + i) (t &&& 0xFFFFFFFF) q hdin
  refine ⟨by simp [hs], fun q hq => ?_, fun i' hi' => ?_, ?_, ?_⟩
  · rw [hget, if_neg (by omega)]; exact hfr q (by omega)
  · rw [hget]
    split
    · rw [and_mask]; exact Nat.mod_lt _ base_pos
    · exact hdg i' (by omega)
  · rw [shr32, ht]
    rw [base_eq] at hXd hm hc ⊢
    have : W[p.toNat + i]!.toNat * m.toNat ≤ 4294967295 * 4294967295 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  · have hcongr : segVal (s.2.set! (p.toNat + i) (t &&& 0xFFFFFFFF)) p.toNat i =
        segVal s.2 p.toNat i :=
      segVal_congr fun i' hi' => by rw [hget, if_neg (by omega)]
    rw [segVal_succ, hcongr, hget, if_pos rfl, and_mask, shr32, segVal_succ, ht, pow_succ]
    have hdm := Nat.mod_add_div (W[p.toNat + i]!.toNat * m.toNat + s.1.toNat) base
    zify at hv hdm ⊢
    linear_combination hv + (base : ℤ) ^ i * hdm


/-! ## Sums of chunks -/

/-- The value of the `e` chunks from position `p` in base `10^9`. -/
def chunkSum (ch : ℕ → ℕ) (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => chunkSum ch p e + ch (p + e) * 10 ^ (9 * e)

theorem chunkSum_succ (ch : ℕ → ℕ) (p e : ℕ) :
    chunkSum ch p (e + 1) = chunkSum ch p e + ch (p + e) * 10 ^ (9 * e) := rfl

theorem chunkSum_congr {ch ch' : ℕ → ℕ} {p p' e : ℕ} (h : ∀ i, i < e → ch (p + i) = ch' (p' + i)) :
    chunkSum ch p e = chunkSum ch' p' e := by
  induction e with
  | zero => rfl
  | succ e ih => rw [chunkSum_succ, chunkSum_succ, ih fun i hi => h i (by omega), h e (by omega)]

theorem chunkSum_add (ch : ℕ → ℕ) (p a b : ℕ) :
    chunkSum ch p (a + b) = chunkSum ch p a + 10 ^ (9 * a) * chunkSum ch (p + a) b := by
  induction b with
  | zero => simp [chunkSum]
  | succ b ih =>
    rw [← Nat.add_assoc, chunkSum_succ, ih, chunkSum_succ, Nat.add_assoc p a b,
      show 9 * (a + b) = 9 * a + 9 * b by ring, pow_add]
    ring

theorem chunkSum_lt {ch : ℕ → ℕ} (h : ∀ i, ch i < 10 ^ 9) (p e : ℕ) :
    chunkSum ch p e < 10 ^ (9 * e) := by
  induction e with
  | zero => simp [chunkSum]
  | succ e ih =>
    rw [chunkSum_succ, show 9 * (e + 1) = 9 * e + 9 by ring, pow_add]
    have h2 := h (p + e)
    have : ch (p + e) * 10 ^ (9 * e) + 10 ^ (9 * e) ≤ 10 ^ (9 * e) * 10 ^ 9 := by
      calc ch (p + e) * 10 ^ (9 * e) + 10 ^ (9 * e) = (ch (p + e) + 1) * 10 ^ (9 * e) := by ring
        _ ≤ 10 ^ 9 * 10 ^ (9 * e) := Nat.mul_le_mul_right _ h2
        _ = _ := by ring
    omega

/-- Horner's rule: the first chunk plus `10^9` times the rest. -/
theorem chunkSum_horner (ch : ℕ → ℕ) (p j : ℕ) :
    chunkSum ch p (j + 1) = ch p + 10 ^ 9 * chunkSum ch (p + 1) j := by
  rw [Nat.add_comm j 1, chunkSum_add]
  simp [chunkSum]

theorem chunkSum_zeros {ch : ℕ → ℕ} {p e : ℕ} (h : ∀ i, i < e → ch (p + i) = 0) :
    chunkSum ch p e = 0 := by
  induction e with
  | zero => rfl
  | succ e ih => rw [chunkSum_succ, ih fun i hi => h i (by omega), h e (by omega)]; simp

theorem pow_chunk_le (e : ℕ) : 10 ^ (9 * e) ≤ base ^ e := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (by rw [base_eq]; norm_num) e

/-- The chunks counted from the least significant end, of the digits that `dv g (9 K)` reads
from the most significant end. -/
theorem chunkSum_top (g : ℕ → ℕ) : ∀ K : ℕ,
    chunkSum (fun i => dv (fun e => g (9 * (K - 1 - i) + e)) 9) 0 K = dv g (9 * K)
  | 0 => rfl
  | K + 1 => by
    rw [chunkSum_horner, Nat.zero_add,
      chunkSum_congr (ch' := fun i => dv (fun e => g (9 * (K - 1 - i) + e)) 9) (p' := 0)
        (fun i hi => by
          show dv (fun e => g (9 * (K + 1 - 1 - (0 + 1 + i)) + e)) 9 =
            dv (fun e => g (9 * (K - 1 - (0 + i)) + e)) 9
          rw [show K + 1 - 1 - (0 + 1 + i) = K - 1 - (0 + i) by omega]),
      chunkSum_top g K, show 9 * (K + 1) = 9 * K + 9 by ring, dv_add, show K + 1 - 1 - 0 = K by omega]
    ring

/-! ## The base elements -/

/-- One step of Horner's rule over the first `j + 1` limbs of an element whose limbs from `j` on
are 0. -/
theorem horner_step {U : Array UInt64} {p j : ℕ} {S a : ℕ} (hU : U.size < 2 ^ 64)
    (hp : p + (j + 1) ≤ U.size) (hd : SegDigits U p j) (hz : U[p + j]! = 0)
    (hv : segVal U p j = S) (hS : S < 10 ^ (9 * j)) (ha : a < 10 ^ 9)
    (pp lp aa : UInt64) (hpp : pp.toNat = p) (hlp : lp.toNat = j + 1) (haa : aa.toNat = a) :
    (mulAddSeg U pp lp 1000000000 aa).size = U.size ∧
    (∀ q, (q < p ∨ p + (j + 1) ≤ q) → (mulAddSeg U pp lp 1000000000 aa)[q]! = U[q]!) ∧
    SegDigits (mulAddSeg U pp lp 1000000000 aa) p (j + 1) ∧
    segVal (mulAddSeg U pp lp 1000000000 aa) p (j + 1) = S * 10 ^ 9 + a := by
  have hb9 : (10 : ℕ) ^ 9 < base := by rw [base_eq]; norm_num
  have hd' : SegDigits U p (j + 1) := fun i hi => by
    by_cases hij : i < j
    · exact hd i hij
    · rw [show i = j by omega, hz]; exact base_pos
  have hv' : segVal U p (j + 1) = S := by rw [segVal_succ, hz, hv]; simp
  have hlt : S * 10 ^ 9 + a < base ^ (j + 1) := by
    have h1 : S * 10 ^ 9 + a < 10 ^ (9 * (j + 1)) := by
      rw [show 9 * (j + 1) = 9 * j + 9 by ring, pow_add]
      have : S * 10 ^ 9 + 10 ^ 9 ≤ 10 ^ (9 * j) * 10 ^ 9 := by
        calc S * 10 ^ 9 + 10 ^ 9 = (S + 1) * 10 ^ 9 := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ hS
      omega
    exact lt_of_lt_of_le h1 (pow_chunk_le _)
  have k := mulAddSeg_spec U pp lp 1000000000 aa hU (by omega) (by rw [hpp, hlp]; exact hd')
    (by rw [base_eq]; decide) (by rw [haa]; omega) (by rw [hpp, hlp, hv', haa]; exact hlt)
  rw [hpp, hlp, hv', haa] at k
  exact k

/-- `readInit` writes the base elements, each the `chunkSum` of its `e0` chunks, and, when
passes follow, `10^(9 e0)` from position `N`. -/
theorem readInit_spec (s : Array UInt64) (start count C e0 N : UInt64) (ch : ℕ → ℕ) (P : ℕ)
    (hch : ∀ i : UInt64, i.toNat < N.toNat →
      (if i < C then chunkValue s start (9 * C - count) (C - 1 - i) else 0).toNat = ch i.toNat)
    (hlt : ∀ i, ch i < 10 ^ 9) (he0 : 1 ≤ e0.toNat) (hP : (N / e0).toNat = P)
    (hN : N.toNat = P * e0.toNat) (hNlt : N.toNat < 2 ^ 60) :
    (readInit s start count C e0 N).size = (if e0 < N then 6 * N.toNat else N.toNat) ∧
    (∀ k, k < P → segVal (readInit s start count C e0 N) (k * e0.toNat) e0.toNat =
      chunkSum ch (k * e0.toNat) e0.toNat) ∧
    SegDigits (readInit s start count C e0 N) 0 N.toNat ∧
    (e0 < N → segVal (readInit s start count C e0 N) N.toNat e0.toNat = 10 ^ (9 * e0.toNat) ∧
      SegDigits (readInit s start count C e0 N) N.toNat e0.toNat) := by
  obtain ⟨E0, hE0⟩ : ∃ E0, E0 = e0.toNat := ⟨_, rfl⟩
  obtain ⟨NN, hNN⟩ : ∃ NN, NN = N.toNat := ⟨_, rfl⟩
  rw [← hE0] at he0 hN ⊢
  rw [← hNN] at hN hNlt hch ⊢
  obtain ⟨sz, hsz⟩ : ∃ sz, sz = (if e0 < N then 6 * NN else NN) := ⟨_, rfl⟩
  rw [← hsz]
  have hszNN : NN ≤ sz := by rw [hsz]; split <;> omega
  have hPN : P ≤ NN := by rw [hN]; exact Nat.le_mul_of_pos_right _ he0
  have hsz6 : sz ≤ 6 * NN := by rw [hsz]; split <;> omega
  unfold readInit
  lift_lets
  intro pad W1
  have hZs : (LeanExe.build (if e0 < N then 6 * N else N) fun _ => (0 : UInt64)).size = sz := by
    rw [build_size, hsz]
    split
    · rw [UInt64.toNat_mul, ← hNN]; simp only [UInt64.reduceToNat]; omega
    · rw [hNN]
  have hZz : ∀ q, (LeanExe.build (if e0 < N then 6 * N else N) fun _ => (0 : UInt64))[q]! =
      (0 : UInt64) :=
    fun q => by
      by_cases hq : q < (if e0 < N then 6 * N else N).toNat
      · rw [build_get hq]
      · rw [build_get_out hq]; rfl
  -- the base elements
  have outer : W1.size = sz ∧
      (∀ k, k < P → segVal W1 (k * E0) E0 = chunkSum ch (k * E0) E0) ∧
      SegDigits W1 0 (P * E0) ∧ (∀ q, P * E0 ≤ q → q < sz → W1[q]! = 0) := by
    rw [← hP]
    refine loop_induction (P := fun k (V : Array UInt64) => V.size = sz ∧
      (∀ k', k' < k → segVal V (k' * E0) E0 = chunkSum ch (k' * E0) E0) ∧
      SegDigits V 0 (k * E0) ∧ (∀ q, k * E0 ≤ q → q < sz → V[q]! = 0))
      ⟨hZs, fun _ h => absurd h (Nat.not_lt_zero _), fun i hi => by simp at hi,
        fun q _ _ => hZz q⟩ ?_
    intro k V hk ⟨vs, vel, vd, vz⟩
    rw [hP] at hk
    have hkk : (UInt64.ofNat k).toNat = k := toNat_ofNat_lt (by omega)
    have hkE : (k + 1) * E0 ≤ NN := by rw [hN]; exact Nat.mul_le_mul_right _ hk
    have hkE' : (k + 1) * E0 = k * E0 + E0 := by ring
    have hke : (UInt64.ofNat k * e0).toNat = k * E0 := by
      rw [UInt64.toNat_mul, hkk, ← hE0]; exact Nat.mod_eq_of_lt (by omega)
    have hk1e : ((UInt64.ofNat k + 1) * e0).toNat = (k + 1) * E0 := by
      rw [UInt64.toNat_mul, toNat_add_lt (by simp only [UInt64.reduceToNat]; omega), hkk, ← hE0]
      simp only [UInt64.reduceToNat]; exact Nat.mod_eq_of_lt (by omega)
    refine (fun inner => ?_) (loop_induction (n := e0) (init := V)
      (P := fun j (U : Array UInt64) => U.size = sz ∧
        (∀ q, (q < k * E0 ∨ k * E0 + j ≤ q) → U[q]! = V[q]!) ∧
        SegDigits U (k * E0) j ∧ segVal U (k * E0) j = chunkSum ch ((k + 1) * E0 - j) j)
      (f := fun j W =>
        mulAddSeg W (UInt64.ofNat k * e0) (j + 1) 1000000000
          (if (UInt64.ofNat k + 1) * e0 - 1 - j < C then
            chunkValue s start pad (C - 1 - ((UInt64.ofNat k + 1) * e0 - 1 - j)) else 0))
      ⟨vs, fun _ _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero _), rfl⟩ ?_)
    · rw [← hE0] at inner
      obtain ⟨us, ufr, ud, uv⟩ := inner
      rw [show (k + 1) * E0 - E0 = k * E0 by omega] at uv
      refine ⟨us, fun k' hk' => ?_, fun i hi => ?_, fun q hq1 hq2 => ?_⟩
      · by_cases hkk' : k' < k
        · rw [← vel k' hkk']
          exact segVal_congr fun i hi => ufr _ (by
            have : k' * E0 + E0 ≤ k * E0 := by nlinarith
            omega)
        · rw [show k' = k by omega, uv]
      · by_cases hik : i < k * E0
        · rw [Nat.zero_add, ufr _ (by omega)]; have := vd i hik; rwa [Nat.zero_add] at this
        · have := ud (i - k * E0) (by omega)
          rwa [show k * E0 + (i - k * E0) = 0 + i by omega] at this
      · rw [ufr q (by omega)]; exact vz q (by omega) hq2
    · intro j U hj ⟨us, ufr, ud, uv⟩
      rw [← hE0] at hj
      have hjj : (UInt64.ofNat j).toNat = j := toNat_ofNat_lt (by omega)
      have hidx : ((UInt64.ofNat k + 1) * e0 - 1 - UInt64.ofNat j).toNat = (k + 1) * E0 - 1 - j := by
        rw [UInt64.toNat_sub_of_le, UInt64.toNat_sub_of_le, hk1e, hjj]
        · simp only [UInt64.reduceToNat]
        · rw [UInt64.le_iff_toNat_le, hk1e]; simp only [UInt64.reduceToNat]; omega
        · rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le, hk1e, hjj]
          · simp only [UInt64.reduceToNat]; omega
          · rw [UInt64.le_iff_toNat_le, hk1e]; simp only [UInt64.reduceToNat]; omega
      have hadd := hch ((UInt64.ofNat k + 1) * e0 - 1 - UInt64.ofNat j) (by rw [hidx]; omega)
      rw [hidx] at hadd
      have hj1 : (UInt64.ofNat j + 1).toNat = j + 1 := by
        rw [toNat_add_lt] <;> simp only [hjj, UInt64.reduceToNat] <;> omega
      have hS := chunkSum_lt hlt ((k + 1) * E0 - j) j
      obtain ⟨m1, m2, m3, m4⟩ := horner_step (U := U) (p := k * E0) (j := j) (by omega) (by omega)
        ud (by rw [ufr _ (by omega)]; exact vz _ (by omega) (by omega)) uv hS (hlt _)
        (UInt64.ofNat k * e0) (UInt64.ofNat j + 1) _ hke hj1 hadd
      refine ⟨by rw [m1, us], fun q hq => by rw [m2 q (by omega)]; exact ufr q (by omega), m3, ?_⟩
      rw [m4, chunkSum_horner, show (k + 1) * E0 - (j + 1) + 1 = (k + 1) * E0 - j by omega,
        show (k + 1) * E0 - (j + 1) = (k + 1) * E0 - 1 - j by omega]
      ring
  obtain ⟨o1, o2, o3, o4⟩ := outer
  rw [← hN] at o3 o4
  by_cases hb : e0 < N
  · rw [if_pos hb]
    have hNE : E0 < NN := by rw [hE0, hNN]; exact UInt64.lt_iff_toNat_lt.mp hb
    have hsz6' : sz = 6 * NN := by rw [hsz, if_pos hb]
    -- the power `10^(9 e0)` by `e0` multiplications by `10^9` from 1
    have hW1s : (W1.set! NN 1).size = sz := by simp [o1]
    have hg1 := fun q => get_set W1 NN 1 q (by omega)
    have bl := loop_induction (n := e0) (init := W1.set! N.toNat 1)
      (f := fun j W => mulAddSeg W N (j + 1) 1000000000 0)
      (P := fun j (U : Array UInt64) => U.size = sz ∧ (∀ q, q < NN → U[q]! = W1[q]!) ∧
        (∀ i, j < i → i < E0 → U[NN + i]! = 0) ∧ SegDigits U NN E0 ∧
        segVal U NN E0 = 10 ^ (9 * j))
      ⟨by rw [← hNN]; exact hW1s, fun q hq => by rw [← hNN, hg1, if_neg (by omega)],
        fun i hi1 hi2 => by rw [← hNN, hg1, if_neg (by omega)]; exact o4 _ (by omega) (by omega),
        fun i hi => by
          rw [← hNN, hg1]
          split
          · rw [base_eq]; decide
          · exact (by rw [o4 _ (by omega) (by omega)]; exact base_pos),
        by
          rw [← hNN]
          have h1 := segVal_add (W1.set! NN 1) NN 1 (E0 - 1)
          rw [show 1 + (E0 - 1) = E0 by omega,
            segVal_zeros (W := W1.set! NN 1) (p := NN + 1) (k := E0 - 1) (fun i hi => by
              rw [hg1, if_neg (by omega)]; exact o4 _ (by omega) (by omega))] at h1
          rw [h1, show (1 : ℕ) = 0 + 1 from rfl, segVal_succ, segVal_zero, Nat.add_zero, hg1,
            if_pos rfl]
          simp⟩
      (by
        intro j U hj ⟨us, ulow, uz, ud, uv⟩
        rw [← hE0] at hj
        have hjj : (UInt64.ofNat j).toNat = j := toNat_ofNat_lt (by omega)
        have hj1 : (UInt64.ofNat j + 1).toNat = j + 1 := by
          rw [toNat_add_lt] <;> simp only [hjj, UInt64.reduceToNat] <;> omega
        have hz0 : ∀ i, i < E0 - (j + 1) → U[NN + (j + 1) + i]! = 0 := fun i hi => by
          rw [Nat.add_assoc]; exact uz _ (by omega) (by omega)
        have hsplit := segVal_add U NN (j + 1) (E0 - (j + 1))
        rw [show j + 1 + (E0 - (j + 1)) = E0 by omega, segVal_zeros hz0, Nat.mul_zero,
          Nat.add_zero, uv] at hsplit
        have hUs : U.size < 2 ^ 64 := by omega
        have hUp : NN + (j + 1) ≤ U.size := by omega
        have hpow : 10 ^ (9 * j) * 1000000000 = 10 ^ (9 * (j + 1)) := by
          rw [show (1000000000 : ℕ) = 10 ^ 9 by norm_num, ← pow_add]; ring_nf
        have hlt' : 10 ^ (9 * (j + 1)) < base ^ (j + 1) := by
          rw [pow_mul]
          exact Nat.pow_lt_pow_left (by rw [base_eq]; norm_num) (by omega)
        obtain ⟨m1, m2, m3, m4⟩ := mulAddSeg_spec U N (UInt64.ofNat j + 1) 1000000000 0 hUs
          (by rw [← hNN, hj1]; exact hUp) (by rw [← hNN, hj1]; exact ud.mono (by omega))
          (by rw [base_eq]; decide) (by rw [base_eq]; decide)
          (by rw [← hNN, hj1, ← hsplit]; simp only [UInt64.reduceToNat, Nat.add_zero]
              rw [hpow]; exact hlt')
        rw [← hNN, hj1, ← hsplit] at m4
        rw [← hNN, hj1] at m2 m3
        simp only [UInt64.reduceToNat, Nat.add_zero, hpow] at m4
        have hz1 : ∀ i, i < E0 - (j + 1) →
            (mulAddSeg U N (UInt64.ofNat j + 1) 1000000000 0)[NN + (j + 1) + i]! = 0 :=
          fun i hi => by rw [m2 _ (by omega)]; exact hz0 i hi
        refine ⟨by rw [m1, us], fun q hq => by rw [m2 q (by omega)]; exact ulow q hq,
          fun i hi1 hi2 => by rw [m2 _ (by omega)]; exact uz i (by omega) hi2,
          fun i hi => ?_, ?_⟩
        · by_cases hij : i < j + 1
          · exact m3 i hij
          · rw [m2 _ (by omega)]; exact ud i hi
        · have h2 := segVal_add (mulAddSeg U N (UInt64.ofNat j + 1) 1000000000 0) NN (j + 1)
            (E0 - (j + 1))
          rw [show j + 1 + (E0 - (j + 1)) = E0 by omega, segVal_zeros hz1, Nat.mul_zero,
            Nat.add_zero, m4] at h2
          exact h2)
    rw [← hE0] at bl
    obtain ⟨b1, b2, -, b4, b5⟩ := bl
    refine ⟨b1, fun k hk => ?_, fun i hi => ?_, fun _ => ⟨b5, b4⟩⟩
    · rw [← o2 k hk]
      have : k * E0 + E0 ≤ NN := by rw [hN]; nlinarith
      exact segVal_congr fun i hi => b2 (k * E0 + i) (by omega)
    · rw [b2 _ (by omega)]; exact o3 i hi
  · rw [if_neg hb]
    exact ⟨o1, o2, o3, fun h => absurd h hb⟩

/-! ## The passes -/

/-- The facts of the passes at element size `e`: the size, the elements of `e` limbs that hold the
sums of their chunks, the limbs, and, while a pass follows, `10^(9 e)` from `N + e - e0`. -/
def PassInv (ch : ℕ → ℕ) (N e0 e sz : ℕ) (W : Array UInt64) : Prop :=
  W.size = sz ∧ (∀ k, k < N / e → segVal W (k * e) e = chunkSum ch (k * e) e) ∧
  SegDigits W 0 N ∧
  (e < N → segVal W (N + e - e0) e = 10 ^ (9 * e) ∧ SegDigits W (N + e - e0) e)

theorem chunk_pow_lt (e : ℕ) : 10 ^ (9 * e) ≤ base ^ e := pow_chunk_le e

theorem toNat_mul_lt {a b : UInt64} (h : a.toNat * b.toNat < 2 ^ 64) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [UInt64.toNat_mul]; exact Nat.mod_eq_of_lt h

/-- The step of the loop over the pairs of a pass. -/
theorem pair_step (t : UInt64) (W V : Array UInt64) (N e0 e kk : UInt64) (ch : ℕ → ℕ)
    (hlt : ∀ i, ch i < 10 ^ 9) (NN E0 Ee Pc k : ℕ) (hNN : N.toNat = NN) (hE0 : e0.toNat = E0)
    (hEe : e.toNat = Ee) (hkk : kk.toNat = k) (he0 : 1 ≤ E0) (hle : E0 ≤ Ee)
    (hPc : NN = 2 * Ee * Pc) (hk : k < Pc) (hNlt : NN < 2 ^ 60)
    (hNE : NN / Ee = 2 * Pc) (bv : segVal W (NN + Ee - E0) Ee = 10 ^ (9 * Ee))
    (bd : SegDigits W (NN + Ee - E0) Ee)
    (vs : V.size = 6 * NN)
    (vpairs : ∀ k', k' < k → segVal V (k' * (2 * Ee)) (2 * Ee) = chunkSum ch (k' * (2 * Ee)) (2 * Ee))
    (vsingle : ∀ k', 2 * k ≤ k' → k' < NN / Ee → segVal V (k' * Ee) Ee = chunkSum ch (k' * Ee) Ee)
    (vd : SegDigits V 0 NN) (vb : ∀ q, NN ≤ q → q < 2 * NN → V[q]! = W[q]!) :
    let V' := (addGen (kara t V ((2 * kk + 1) * e) (N + e - e0) (2 * N) (3 * N) e) (2 * N)
      (2 * kk * e) e (2 * kk * e) (2 * e)).2
    V'.size = 6 * NN ∧
    (∀ k', k' < k + 1 → segVal V' (k' * (2 * Ee)) (2 * Ee) = chunkSum ch (k' * (2 * Ee)) (2 * Ee)) ∧
    (∀ k', 2 * (k + 1) ≤ k' → k' < NN / Ee → segVal V' (k' * Ee) Ee = chunkSum ch (k' * Ee) Ee) ∧
    SegDigits V' 0 NN ∧ (∀ q, NN ≤ q → q < 2 * NN → V'[q]! = W[q]!) := by
  dsimp only
  have hPcN : Pc ≤ NN := by rw [hPc]; exact Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨a, ha⟩ : ∃ a, a = 2 * k * Ee := ⟨_, rfl⟩
  have ha1 : (2 * k + 1) * Ee = a + Ee := by rw [ha]; ring
  have ha2 : (2 * k + 2) * Ee = a + 2 * Ee := by rw [ha]; ring
  have hak : k * (2 * Ee) = a := by rw [ha]; ring
  have hkE : a + 2 * Ee ≤ NN := by
    rw [← ha2, hPc]
    calc (2 * k + 2) * Ee = 2 * Ee * (k + 1) := by ring
      _ ≤ 2 * Ee * Pc := Nat.mul_le_mul_left _ hk
  have h2k : (2 * kk).toNat = 2 * k := by
    rw [toNat_mul_lt] <;> simp only [UInt64.reduceToNat, hkk] <;> omega
  have hk2 : 2 * k ≤ a := by rw [ha]; exact Nat.le_mul_of_pos_right _ (by omega)
  have pl1 : ((2 * kk + 1) * e).toNat = a + Ee := by
    rw [toNat_mul_lt, toNat_add_lt, h2k, hEe] <;> simp only [UInt64.reduceToNat, h2k, hEe]
    · rw [ha1]
    · omega
    · rw [toNat_add_lt] <;> simp only [UInt64.reduceToNat, h2k] <;> [rw [ha1]; omega]
      omega
  have pl0 : (2 * kk * e).toNat = a := by
    rw [toNat_mul_lt, h2k, hEe, ha] <;> rw [h2k, hEe] <;> omega
  have p2N : (2 * N).toNat = 2 * NN := by
    rw [toNat_mul_lt] <;> simp only [UInt64.reduceToNat, hNN] <;> omega
  have p3N : (3 * N).toNat = 3 * NN := by
    rw [toNat_mul_lt] <;> simp only [UInt64.reduceToNat, hNN] <;> omega
  have p2e : (2 * e).toNat = 2 * Ee := by
    rw [toNat_mul_lt] <;> simp only [UInt64.reduceToNat, hEe] <;> omega
  have pb : (N + e - e0).toNat = NN + Ee - E0 := by
    rw [UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, toNat_add_lt (by omega)]; omega), toNat_add_lt (by omega)]
    omega
  -- the product `l1 · 10^(9 e)` into the buffer
  have kK := kara_spec t Ee V ((2 * kk + 1) * e) (N + e - e0) (2 * N) (3 * N) e
    hEe (by omega) (by rw [pl1, p2N]; omega) (by rw [pb, p2N]; omega)
    (by rw [p2N, p3N]; omega) (by rw [p3N]; omega)
    (by rw [pl1]; exact fun i hi => by have := vd (a + Ee + i) (by omega); rwa [Nat.zero_add] at this)
    (by rw [pb]; exact fun i hi => by rw [vb _ (by omega) (by omega)]; exact bd i hi)
  rw [pl1, pb, p2N, p3N] at kK
  obtain ⟨ks, kfr, kd, kv⟩ := kK
  have hl1 : segVal V (a + Ee) Ee = chunkSum ch (a + Ee) Ee := by
    rw [← ha1]; exact vsingle (2 * k + 1) (by omega) (by omega)
  have hbV : segVal V (NN + Ee - E0) Ee = 10 ^ (9 * Ee) := by
    rw [← bv]; exact segVal_congr fun i hi => vb _ (by omega) (by omega)
  rw [hl1, hbV] at kv
  generalize kara t V ((2 * kk + 1) * e) (N + e - e0) (2 * N) (3 * N) e = V1 at ks kfr kd kv ⊢
  have rV1 : ∀ q, q < 2 * NN → V1[q]! = V[q]! := fun q hq => kfr q (by omega) (by omega)
  -- the sum `l0 + l1 · 10^(9 e)` over the pair
  have kA := addGen_spec V1 (2 * N) (2 * kk * e) e (2 * kk * e) (2 * e)
    (by omega) (by rw [p2N, p2e]; omega) (by rw [pl0, p2e, hEe]; omega)
    (by rw [pl0, p2e]; omega) (by rw [p2N, p2e]; exact kd)
    (by
      rw [pl0, p2e, hEe, show min Ee (2 * Ee) = Ee by omega]
      exact fun i hi => by
        rw [rV1 _ (by omega)]; have := vd (a + i) (by omega); rwa [Nat.zero_add] at this)
    (fun i j _ hj => by rw [pl0, p2N]; rw [p2e] at hj; omega)
    (fun i j h1 hj => by rw [pl0]; omega)
  rw [p2N, pl0, p2e, hEe, show min Ee (2 * Ee) = Ee by omega] at kA
  obtain ⟨as, afr, ad, ac, av⟩ := kA
  have hl0 : segVal V1 a Ee = chunkSum ch a Ee := by
    have h1 := vsingle (2 * k) le_rfl (by omega)
    rw [show 2 * k * Ee = a by rw [ha]] at h1
    rw [← h1]; exact segVal_congr fun i hi => rV1 _ (by omega)
  rw [kv, hl0] at av
  have hsum : chunkSum ch (a + Ee) Ee * 10 ^ (9 * Ee) + chunkSum ch a Ee =
      chunkSum ch a (2 * Ee) := by
    rw [show 2 * Ee = Ee + Ee by ring, chunkSum_add]; ring
  rw [hsum] at av
  have hlt2 := lt_of_lt_of_le (chunkSum_lt hlt a (2 * Ee)) (pow_chunk_le (2 * Ee))
  generalize (addGen V1 (2 * N) (2 * kk * e) e (2 * kk * e) (2 * e)) = A at as afr ad av ac ⊢
  have hc0 : A.1.toNat = 0 := by
    by_contra hne
    have : 1 * base ^ (2 * Ee) ≤ A.1.toNat * base ^ (2 * Ee) :=
      Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.mpr hne)
    omega
  rw [hc0, Nat.zero_mul, Nat.add_zero] at av
  refine ⟨by rw [as, ks, vs], fun k' hk' => ?_, fun k' hk1 hk2 => ?_, fun i hi => ?_,
    fun q hq1 hq2 => ?_⟩
  · by_cases hkk' : k' < k
    · rw [← vpairs k' hkk']
      have : k' * (2 * Ee) + 2 * Ee ≤ a := by
        rw [← hak]
        calc k' * (2 * Ee) + 2 * Ee = (k' + 1) * (2 * Ee) := by ring
          _ ≤ k * (2 * Ee) := Nat.mul_le_mul_right _ hkk'
      exact segVal_congr fun i hi => by rw [afr _ (by omega), rV1 _ (by omega)]
    · rw [show k' = k by omega, hak, av]
  · rw [← vsingle k' (by omega) hk2]
    have h3 : a + 2 * Ee ≤ k' * Ee := by
      rw [← ha2]; exact Nat.mul_le_mul_right _ (by omega)
    have h4 : k' * Ee + Ee ≤ NN := by
      rw [hNE] at hk2
      rw [hPc]
      calc k' * Ee + Ee = (k' + 1) * Ee := by ring
        _ ≤ (2 * Pc) * Ee := Nat.mul_le_mul_right _ hk2
        _ = 2 * Ee * Pc := by ring
    exact segVal_congr fun i hi => by rw [afr _ (by omega), rV1 _ (by omega)]
  · by_cases hin : a ≤ i ∧ i < a + 2 * Ee
    · have := ad (i - a) (by omega)
      rwa [show a + (i - a) = 0 + i by omega] at this
    · rw [Nat.zero_add, afr _ (by omega), rV1 _ (by omega)]
      have := vd i hi; rwa [Nat.zero_add] at this
  · rw [afr _ (by omega), rV1 _ hq2]; exact vb q hq1 hq2

/-- A pass turns the elements of `e` limbs into elements of `2 e` limbs and squares the power
when a later pass needs it. -/
theorem readPass_spec (t : UInt64) (W : Array UInt64) (N e0 e : UInt64) (ch : ℕ → ℕ)
    (hlt : ∀ i, ch i < 10 ^ 9) (NN E0 Ee : ℕ) (hNN : N.toNat = NN) (hE0 : e0.toNat = E0)
    (hEe : e.toNat = Ee) (he0 : 1 ≤ E0) (hle : E0 ≤ Ee) (hen : Ee < NN)
    (hdvd : 2 * Ee ∣ NN) (hNlt : NN < 2 ^ 60)
    (hinv : PassInv ch NN E0 Ee (6 * NN) W) :
    PassInv ch NN E0 (2 * Ee) (6 * NN) (readPass t W N e0 e) := by
  obtain ⟨Pc, hPc⟩ := hdvd
  have hPc1 : 1 ≤ Pc := by
    rcases Nat.eq_zero_or_pos Pc with h | h
    · rw [h] at hPc; omega
    · exact h
  have hNE : NN / Ee = 2 * Pc := by
    rw [hPc, show 2 * Ee * Pc = Ee * (2 * Pc) by ring, Nat.mul_div_cancel_left _ (by omega)]
  have hNE2 : NN / (2 * Ee) = Pc := by
    rw [hPc, Nat.mul_div_cancel_left _ (by omega)]
  obtain ⟨ws, wel, wd, wb⟩ := hinv
  obtain ⟨bv, bd⟩ := wb hen
  have pPc : (N / e / 2).toNat = Pc := by
    rw [UInt64.toNat_div, UInt64.toNat_div, hNN, hEe, hNE]; simp only [UInt64.reduceToNat]; omega
  unfold readPass
  lift_lets
  intro W1
  have pairs : W1.size = 6 * NN ∧
      (∀ k', k' < Pc → segVal W1 (k' * (2 * Ee)) (2 * Ee) = chunkSum ch (k' * (2 * Ee)) (2 * Ee)) ∧
      SegDigits W1 0 NN ∧ (∀ q, NN ≤ q → q < 2 * NN → W1[q]! = W[q]!) := by
    rw [← pPc]
    refine (fun h => ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩) (loop_induction (P := fun k (V : Array UInt64) =>
      V.size = 6 * NN ∧
      (∀ k', k' < k → segVal V (k' * (2 * Ee)) (2 * Ee) = chunkSum ch (k' * (2 * Ee)) (2 * Ee)) ∧
      (∀ k', 2 * k ≤ k' → k' < NN / Ee → segVal V (k' * Ee) Ee = chunkSum ch (k' * Ee) Ee) ∧
      SegDigits V 0 NN ∧ (∀ q, NN ≤ q → q < 2 * NN → V[q]! = W[q]!))
      ⟨ws, fun _ h => absurd h (Nat.not_lt_zero _), fun k' _ h => wel k' h, wd, fun _ _ _ => rfl⟩
      ?_)
    intro k V hk ⟨vs, vpairs, vsingle, vd, vb⟩
    rw [pPc] at hk
    have hPcN : Pc ≤ NN := by rw [hPc]; exact Nat.le_mul_of_pos_left _ (by omega)
    exact pair_step t W V N e0 e (UInt64.ofNat k) ch hlt NN E0 Ee Pc k hNN hE0 hEe
      (toNat_ofNat_lt (by omega)) he0 hle hPc hk hNlt hNE bv bd vs vpairs vsingle vd vb
  obtain ⟨ps, pel, pd, pb⟩ := pairs
  have p2e : (2 * e).toNat = 2 * Ee := by
    rw [toNat_mul_lt] <;> simp only [UInt64.reduceToNat, hEe] <;> omega
  by_cases h2 : 2 * Ee < NN
  · have h4 : 4 * Ee ≤ NN := by
      rw [hPc]
      have : 2 ≤ Pc := by
        by_contra hc
        have : Pc = 1 := by omega
        rw [this] at hPc; omega
      calc 4 * Ee = 2 * Ee * 2 := by ring
        _ ≤ 2 * Ee * Pc := Nat.mul_le_mul_left _ this
    rw [if_pos (by rw [UInt64.lt_iff_toNat_lt, p2e, hNN]; exact h2)]
    have pb1 : (N + e - e0).toNat = NN + Ee - E0 := by
      rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, toNat_add_lt (by omega)]; omega), toNat_add_lt (by omega)]
      omega
    have pb2 : (N + 2 * e - e0).toNat = NN + 2 * Ee - E0 := by
      rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, toNat_add_lt (by rw [p2e]; omega), p2e]; omega),
        toNat_add_lt (by rw [p2e]; omega), p2e]
      omega
    have p3N : (3 * N).toNat = 3 * NN := by
      rw [toNat_mul_lt] <;> simp only [UInt64.reduceToNat, hNN] <;> omega
    have hbW1 : SegDigits W1 (NN + Ee - E0) Ee :=
      fun i hi => by rw [pb _ (by omega) (by omega)]; exact bd i hi
    have kK := kara_spec t Ee W1 (N + e - e0) (N + e - e0) (N + 2 * e - e0) (3 * N) e hEe
      (by omega) (by rw [pb1, pb2]; omega) (by rw [pb1, pb2]; omega) (by rw [pb2, p3N]; omega)
      (by rw [p3N]; omega) (by rw [pb1]; exact hbW1) (by rw [pb1]; exact hbW1)
    rw [pb1, pb2, p3N] at kK
    obtain ⟨ks, kfr, kd, kv⟩ := kK
    have hbv1 : segVal W1 (NN + Ee - E0) Ee = 10 ^ (9 * Ee) := by
      rw [← bv]; exact segVal_congr fun i hi => pb _ (by omega) (by omega)
    rw [hbv1] at kv
    have hW1 : ∀ q, q < NN → (kara t W1 (N + e - e0) (N + e - e0) (N + 2 * e - e0) (3 * N) e)[q]! =
        W1[q]! := fun q hq => kfr q (by omega) (by omega)
    refine ⟨by rw [ks, ps], fun k hk => ?_, fun i hi => ?_, fun _ => ⟨?_, kd⟩⟩
    · rw [hNE2] at hk
      have : k * (2 * Ee) + 2 * Ee ≤ NN := by
        rw [hPc]
        calc k * (2 * Ee) + 2 * Ee = (k + 1) * (2 * Ee) := by ring
          _ ≤ Pc * (2 * Ee) := Nat.mul_le_mul_right _ hk
          _ = 2 * Ee * Pc := by ring
      rw [← pel k hk]; exact segVal_congr fun i hi => hW1 _ (by omega)
    · rw [Nat.zero_add, hW1 _ hi]; have := pd i hi; rwa [Nat.zero_add] at this
    · rw [kv, ← pow_add]; congr 1; ring
  · rw [if_neg (by rw [UInt64.lt_iff_toNat_lt, p2e, hNN]; exact h2)]
    refine ⟨ps, fun k hk => pel k (by rw [hNE2] at hk; exact hk), pd, fun h => absurd h h2⟩

/-- The passes double the element size from `e0 2^j` until it reaches `N = e0 2^K`. -/
theorem passes_spec (t : UInt64) (N e0 : UInt64) (ch : ℕ → ℕ) (hlt : ∀ i, ch i < 10 ^ 9)
    (NN E0 K sz : ℕ) (hNN : N.toNat = NN) (hE0 : e0.toNat = E0) (he0 : 1 ≤ E0)
    (hK : NN = E0 * 2 ^ K) (hNlt : NN < 2 ^ 60) (hsz : 0 < K → sz = 6 * NN) :
    ∀ (f j : ℕ) (st : UInt64 × Array UInt64), st.1.toNat = E0 * 2 ^ j → j ≤ K → K - j ≤ f →
      PassInv ch NN E0 st.1.toNat sz st.2 →
      PassInv ch NN E0 NN sz (LeanExe.repeatWhile.go (fun st => decide (st.1 < N))
        (fun st => (2 * st.1, readPass t st.2 N e0 st.1)) f st).2
  | 0, j, st, h1, h2, h3, h4 => by
    rw [show j = K by omega, ← hK] at h1
    simpa [LeanExe.repeatWhile.go, h1] using h4
  | f + 1, j, st, h1, h2, h3, h4 => by
    simp only [LeanExe.repeatWhile.go]
    by_cases hj : j < K
    · have h2j : 2 ^ j < 2 ^ K := Nat.pow_lt_pow_right (by norm_num) hj
      have hjK : E0 * 2 ^ j < E0 * 2 ^ K := (Nat.mul_lt_mul_left (by omega)).mpr h2j
      have hlt' : st.1 < N := by
        rw [UInt64.lt_iff_toNat_lt, h1, hNN, hK]; exact hjK
      rw [if_pos (by simpa using hlt')]
      have hpow : E0 * 2 ^ (j + 1) ≤ NN := by
        rw [hK]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hj)
      have h2e : E0 * 2 ^ (j + 1) = 2 * (E0 * 2 ^ j) := by ring
      have h2s : (2 * st.1).toNat = E0 * 2 ^ (j + 1) := by
        rw [toNat_mul_lt (by rw [h1]; simp only [UInt64.reduceToNat]; omega), h1, h2e]
        simp only [UInt64.reduceToNat]
      apply passes_spec t N e0 ch hlt NN E0 K sz hNN hE0 he0 hK hNlt hsz f (j + 1) _ h2s
        (by omega) (by omega)
      rw [h2s, h2e, ← h1]
      have hsz' := hsz (by omega)
      rw [hsz'] at h4 ⊢
      have hle' : E0 ≤ st.1.toNat := by rw [h1]; exact Nat.le_mul_of_pos_right _ (by positivity)
      have hen' : st.1.toNat < NN := by rw [h1, hK]; exact hjK
      have hdvd' : 2 * st.1.toNat ∣ NN := by
        rw [h1, hK, ← h2e]
        exact Nat.mul_dvd_mul_left _ (Nat.pow_dvd_pow 2 (by omega))
      exact readPass_spec t st.2 N e0 st.1 ch hlt NN E0 _ hNN hE0 rfl he0 hle' hen' hdvd' hNlt h4
    · have hjK : j = K := by omega
      have hge : ¬ st.1 < N := by
        rw [UInt64.lt_iff_toNat_lt, h1, hNN, hK, hjK]; omega
      rw [if_neg (by simpa using hge)]
      rw [hjK, ← hK] at h1
      rw [h1] at h4
      exact h4

/-- The count of base elements is a power of two. -/
theorem count_pow (E C : UInt64) : ∀ (f j : ℕ) (p : UInt64), p.toNat = 2 ^ j → j + f ≤ 32 →
    ∃ K, (LeanExe.repeatWhile.go (fun p => decide (E * p < C)) (fun p => 2 * p) f p).toNat =
      2 ^ K ∧ K ≤ 32
  | 0, j, p, h1, h2 => ⟨j, by simpa [LeanExe.repeatWhile.go] using h1, by omega⟩
  | f + 1, j, p, h1, h2 => by
    simp only [LeanExe.repeatWhile.go]
    split
    · apply count_pow E C f (j + 1) (2 * p) _ (by omega)
      have : 2 ^ (j + 1) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
      rw [toNat_mul_lt (by rw [h1]; simp only [UInt64.reduceToNat]; omega), h1, h2]
      simp only [UInt64.reduceToNat]
    · exact ⟨j, h1, by omega⟩

/-! ## The reader of digits -/

set_option maxHeartbeats 1000000 in
/-- The second iteration's reader of digits returns the canonical limbs of the digits' value, as
the first iteration's `decimalValue` does. -/
theorem decimalValueDC_eq (t E : UInt64) (s : Array UInt64) (start count : UInt64)
    (hs : s.size < 2 ^ 32) (hsz : start.toNat + count.toNat = s.size) (hc : 1 ≤ count.toNat)
    (hdig : ∀ w ∈ s.toList.drop start.toNat, isDigitWord w = true) :
    decimalValueDC t E s start count = limbsOf (digitsValue (s.toList.drop start.toNat)) := by
  unfold decimalValueDC
  lift_lets
  intro C P2 e0 N W
  obtain ⟨Cn, hCnd⟩ : ∃ x, x = (count.toNat + 8) / 9 := ⟨_, rfl⟩
  have hCn : C.toNat = Cn := by
    show ((count + 8) / 9).toNat = Cn
    rw [UInt64.toNat_div, toNat_add_lt (by simp only [UInt64.reduceToNat]; omega), hCnd]
    simp only [UInt64.reduceToNat]
  have hC1 : 1 ≤ Cn := by omega
  have hCs : Cn < 2 ^ 29 := by omega
  have hpad : (9 * C - count).toNat = 9 * Cn - count.toNat := by
    have h9 : (9 * C).toNat = 9 * Cn := by
      rw [toNat_mul_lt] <;> simp only [UInt64.reduceToNat, hCn] <;> omega
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, h9]; omega), h9]
  obtain ⟨K, hK, hK32⟩ := count_pow E C 32 0 1 rfl (by omega)
  have hP2 : P2.toNat = 2 ^ K := hK
  have hpow : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hpow32 : 2 ^ K ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hK32
  obtain ⟨E0, hE0d⟩ : ∃ x, x = (Cn + 2 ^ K - 1) / 2 ^ K := ⟨_, rfl⟩
  have he0 : e0.toNat = E0 := by
    show ((C + P2 - 1) / P2).toNat = E0
    rw [UInt64.toNat_div, UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, toNat_add_lt (by rw [hCn, hP2]; omega), hCn, hP2]
      simp only [UInt64.reduceToNat]; omega), toNat_add_lt (by rw [hCn, hP2]; omega), hCn, hP2,
      hE0d]
    simp only [UInt64.reduceToNat]
  have hE1 : 1 ≤ E0 := by
    rw [hE0d]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hEN1 : Cn ≤ E0 * 2 ^ K := by
    have := Nat.lt_div_mul_add (a := Cn + 2 ^ K - 1) (b := 2 ^ K) (by omega)
    rw [← hE0d] at this; omega
  have hEN2 : E0 * 2 ^ K ≤ Cn + 2 ^ K - 1 := by
    have := Nat.div_mul_le_self (Cn + 2 ^ K - 1) (2 ^ K)
    rw [← hE0d] at this; omega
  obtain ⟨NN, hNNd⟩ : ∃ x, x = E0 * 2 ^ K := ⟨_, rfl⟩
  have hNN : N.toNat = NN := by
    show (e0 * P2).toNat = NN
    rw [toNat_mul_lt (by rw [he0, hP2]; omega), he0, hP2, hNNd]
  have hNlt : NN < 2 ^ 60 := by omega
  have hNe : (N / e0).toNat = 2 ^ K := by
    rw [UInt64.toNat_div, hNN, he0, hNNd, Nat.mul_div_cancel_left _ (by omega)]
  -- the chunks
  have hst : start.toNat ≤ s.size := by omega
  have hgl := fun q => padDigit_lt (pad := (9 * Cn - count.toNat)) hst hdig q
  obtain ⟨ch, hchd⟩ : ∃ ch : ℕ → ℕ, ch = fun i => if i < Cn then
      dv (fun e => padDigit s start.toNat (9 * Cn - count.toNat) (9 * (Cn - 1 - i) + e)) 9 else 0 :=
    ⟨_, rfl⟩
  have hlt : ∀ i, ch i < 10 ^ 9 := fun i => by
    rw [hchd]; dsimp only; split
    · exact dv_lt (fun q => hgl _) 9
    · positivity
  have hch : ∀ i : UInt64, i.toNat < N.toNat →
      (if i < C then chunkValue s start (9 * C - count) (C - 1 - i) else 0).toNat = ch i.toNat := by
    intro i hi
    rw [hchd]
    dsimp only
    by_cases hiC : i.toNat < Cn
    · rw [if_pos (by rw [UInt64.lt_iff_toNat_lt, hCn]; exact hiC), if_pos hiC]
      have hk : (C - 1 - i).toNat = Cn - 1 - i.toNat := by
        rw [UInt64.toNat_sub_of_le, UInt64.toNat_sub_of_le, hCn]
        · simp only [UInt64.reduceToNat]
        · rw [UInt64.le_iff_toNat_le, hCn]; simp only [UInt64.reduceToNat]; omega
        · rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le, hCn]
          · simp only [UInt64.reduceToNat]; omega
          · rw [UInt64.le_iff_toNat_le, hCn]; simp only [UInt64.reduceToNat]; omega
      unfold chunkValue
      rw [chunk_spec s start (9 * C - count) (C - 1 - i) hs hst (by rw [hk]; omega)
        (by rw [hpad]; omega) (by rw [hk, hpad]; omega) hdig, hk, hpad]
    · rw [if_neg (by rw [UInt64.lt_iff_toNat_lt, hCn]; exact hiC), if_neg hiC]; rfl
  -- the base elements and the passes
  obtain ⟨r1, r2, r3, r4⟩ := readInit_spec s start count C e0 N ch (2 ^ K) hch hlt
    (by rw [he0]; exact hE1) hNe (by rw [hNN, he0, hNNd, Nat.mul_comm]) (by rw [hNN]; exact hNlt)
  rw [hNN] at r1 r3
  rw [he0] at r2
  rw [he0, hNN] at r4
  obtain ⟨sz, hszd⟩ : ∃ x, x = (if e0 < N then 6 * NN else NN) := ⟨_, rfl⟩
  rw [← hszd] at r1
  have hsz6 : 0 < K → sz = 6 * NN := fun hK0 => by
    rw [hszd, if_pos (by
      rw [UInt64.lt_iff_toNat_lt, he0, hNN, hNNd]
      have : 2 ≤ 2 ^ K := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK0
      nlinarith)]
  have hszN : NN ≤ sz := by rw [hszd]; split <;> omega
  have hsz6' : sz ≤ 6 * NN := by rw [hszd]; split <;> omega
  have hinv0 : PassInv ch NN E0 E0 sz (readInit s start count C e0 N) := by
    refine ⟨r1, fun k hk => ?_, r3, fun h => ?_⟩
    · rw [hNNd, Nat.mul_div_cancel_left _ (by omega)] at hk
      exact r2 k hk
    · rw [show NN + E0 - E0 = NN by omega]
      exact r4 (by rw [UInt64.lt_iff_toNat_lt, he0, hNN]; exact h)
  have hfin := passes_spec t N e0 ch hlt NN E0 K sz hNN he0 hE1 hNNd hNlt hsz6 32 0
    (e0, readInit s start count C e0 N) (by rw [he0, pow_zero, Nat.mul_one]) (Nat.zero_le _)
    (by omega) (by rw [he0]; exact hinv0)
  obtain ⟨f1, f2, f3, -⟩ := hfin
  have hW : W = (LeanExe.repeatWhile.go (fun st => decide (st.1 < N))
      (fun st => (2 * st.1, readPass t st.2 N e0 st.1)) 32 (e0, readInit s start count C e0 N)).2 :=
    rfl
  rw [← hW] at f1 f2 f3
  have hv := f2 0 (by rw [Nat.div_self (by omega)]; omega)
  rw [Nat.zero_mul] at hv
  rw [trimSeg_eq W 0 N (by omega) (by rw [hNN, f1]; simp only [UInt64.reduceToNat]; omega)
    (by rw [hNN]; exact f3), hNN, show (0 : UInt64).toNat = 0 from rfl, hv]
  congr 1
  -- the value of the chunks is the value of the digits
  have hz := chunkSum_add ch 0 Cn (NN - Cn)
  rw [show Cn + (NN - Cn) = NN by omega,
    chunkSum_zeros (ch := ch) (p := 0 + Cn) (e := NN - Cn) (fun i hi => by
      rw [hchd]; dsimp only; rw [if_neg (by omega)]), Nat.mul_zero, Nat.add_zero] at hz
  rw [hz, chunkSum_congr (ch' := fun i =>
      dv (fun e => padDigit s start.toNat (9 * Cn - count.toNat) (9 * (Cn - 1 - i) + e)) 9)
      (p' := 0) (fun i hi => by rw [hchd]; dsimp only; rw [if_pos (by omega)]),
    chunkSum_top (padDigit s start.toNat (9 * Cn - count.toNat)) Cn]
  generalize hpd : 9 * Cn - count.toNat = pd
  have h9 : 9 * Cn = pd + count.toNat := by omega
  rw [h9, dv_add, dv_zeros (fun q hq => by unfold padDigit; rw [ite_eq_left hq]), Nat.mul_zero,
    Nat.zero_add, digitsValue_eq_dv, show (s.toList.drop start.toNat).length = count.toNat by
      simp; omega]
  apply dv_congr
  intro e he
  unfold padDigit
  rw [ite_eq_right (by omega), show pd + e - pd = e by omega, drop_getElem! s (by omega)]

/-- The second iteration's reader of digits returns what the first iteration's returns. -/
theorem decimalValueDC_eq_decimalValue (t E : UInt64) (s : Array UInt64) (start count : UInt64)
    (hs : s.size < 2 ^ 32) (hsz : start.toNat + count.toNat = s.size) (hc : 1 ≤ count.toNat)
    (hdig : ∀ w ∈ s.toList.drop start.toNat, isDigitWord w = true) :
    decimalValueDC t E s start count = decimalValue s start count := by
  rw [decimalValueDC_eq t E s start count hs hsz hc hdig, decimalValue_eq s start count hs hsz hdig]

end Library.Numerics.Bignum
