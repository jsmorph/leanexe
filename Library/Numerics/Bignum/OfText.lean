module

public import Library.Numerics.Bignum.ToText

@[expose] public section

/-!
The reader equals the specification: `intOfText_eq`, and with `readSpec_print` the round trip
`read_print`.  `dv g n` is the value of the decimal digits `g 0, …, g (n - 1)`, most significant
first, which the program's loops follow: the loop of a chunk computes `dv` of nine digits, and
`dv_add` splits `dv g (9 (k + 1))` into `10^9 · dv g (9 k)` and the chunk.  `mulAdd_spec` proves the
multiply-and-add in place over all `C` limbs, whose final carry is 0 when the result is below
`2^(32 C)`, which holds since each chunk is below `10^9 < 2^32`.  The leading zeros that pad the
digits to `9 C` add nothing (`dv_zeros`), and `digitsValue_eq_dv` reads Int64Text's `digitsValue`
as `dv`.  `allDigits_spec` reads the digit test as `List.all`, and the cases of `intOfText_eq`
follow those of Int64Text's `readInt64_eq` without its range test.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open Library.Numerics.Decimal.Int64Text (digitsValue isDigitWord isDigitWord_iff isDigitW
  magnitude magnitude_cons digitsValue_snoc digitsValue_pos denote denote_minus denote_plain
  denote_zero getElem!_of_toList toList_cons_of_size isDigitWord_ne48)
open LeanExe.Dialect

/-! ## Values of decimal digits -/

/-- The value of the decimal digits `g 0, …, g (n - 1)`, most significant first. -/
def dv (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 10 * dv g n + g n

theorem dv_add (g : ℕ → ℕ) (a b : ℕ) :
    dv g (a + b) = 10 ^ b * dv g a + dv (fun e => g (a + e)) b := by
  induction b with
  | zero => simp [dv]
  | succ b ih =>
    rw [← Nat.add_assoc, dv, ih, dv]
    ring

theorem dv_congr {g g' : ℕ → ℕ} {n : ℕ} (h : ∀ e, e < n → g e = g' e) : dv g n = dv g' n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dv, dv, ih fun e he => h e (by omega), h n (by omega)]

theorem dv_lt {g : ℕ → ℕ} (h : ∀ q, g q < 10) (n : ℕ) : dv g n < 10 ^ n := by
  induction n with
  | zero => simp [dv]
  | succ n ih => rw [dv, pow_succ]; have := h n; omega

theorem dv_zeros {g : ℕ → ℕ} {a : ℕ} (h : ∀ q, q < a → g q = 0) : dv g a = 0 := by
  induction a with
  | zero => rfl
  | succ a ih => rw [dv, ih fun q hq => h q (by omega), h a (by omega)]

theorem digitsValue_eq_dv (l : List UInt64) :
    digitsValue l = dv (fun e => l[e]!.toNat - 48) l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l w ih =>
    rw [digitsValue_snoc, List.length_append, List.length_singleton, dv, ih]
    congr 1
    · congr 1
      apply dv_congr
      intro e he
      rw [getElem!_pos (l ++ [w]) e (by simp; omega), getElem!_pos l e he,
        List.getElem_append_left he]
    · rw [getElem!_pos (l ++ [w]) l.length (by simp), List.getElem_append_right (by omega)]
      simp

/-! ## The digit test -/

theorem allDigits_spec (s : Array UInt64) (start count : UInt64) (hs : s.size < 2 ^ 64)
    (hsz : start.toNat + count.toNat = s.size) :
    allDigits s start count = (s.toList.drop start.toNat).all isDigitWord := by
  have hlen : (s.toList.drop start.toNat).length = count.toNat := by simp; omega
  have key := loop_induction (n := count) (init := true)
    (f := fun i ok => ok && isDigitW s[(start + i).toNat]!)
    (fun k ok => ok = ((s.toList.drop start.toNat).take k).all isDigitWord) (by simp)
    (by
      intro k ok hk h1
      have hkl : k < (s.toList.drop start.toNat).length := by omega
      have hidx : (start + UInt64.ofNat k).toNat = start.toNat + k := by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
        omega
      have hw : s[(start + UInt64.ofNat k).toNat]! = (s.toList.drop start.toNat)[k] := by
        rw [hidx, List.getElem_drop, Array.getElem_toList, getElem!_pos s _ (by omega)]
      rw [hw, List.take_succ_eq_append_getElem hkl, List.all_append, ← h1]
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      rfl)
  rw [List.take_of_length_le (by omega)] at key
  exact key

/-! ## Multiply and add in place -/

theorem and_mask (t : UInt64) : (t &&& 0xFFFFFFFF).toNat = t.toNat % base := by
  rw [Library.Numerics.Arithmetic.Uscale.UscaleTheorem.and_mask, base]

theorem shr32 (t : UInt64) : (t >>> 32).toNat = t.toNat / base := by
  rw [Library.Numerics.Arithmetic.Uscale.UscaleTheorem.shr32, base]

theorem prefixValue_set_last (w : Array UInt64) {i : ℕ} (hi : i < w.size) (y : UInt64) :
    prefixValue (w.set! i y) (i + 1) = prefixValue w i + y.toNat * base ^ i := by
  rw [prefixValue_succ, get_set w i y i hi, ite_eq_left rfl]
  congr 1
  exact prefixValue_congr fun p hp => by rw [get_set w i y p hi, ite_eq_right (by omega)]

/-- The word `x · 10^9 + c` of two limbs, without wrapping.  `omega` reaches the recursion limit
when a hypothesis `x * 1000000000 < 2 ^ 64` is in its context, so the larger bound comes first. -/
theorem toNat_mulAdd (x c : UInt64) (hx : x.toNat < base) (hc : c.toNat < base) :
    (x * 1000000000 + c).toNat = x.toNat * 10 ^ 9 + c.toNat := by
  have hx' : x.toNat < 4294967296 := base_eq ▸ hx
  have hc' : c.toNat < 4294967296 := base_eq ▸ hc
  have hm2 : x.toNat * 1000000000 + c.toNat < 2 ^ 64 := by omega
  have hm1 : x.toNat * 1000000000 < 2 ^ 64 := lt_of_le_of_lt (Nat.le_add_right _ _) hm2
  rw [UInt64.toNat_add, UInt64.toNat_mul]
  simp only [UInt64.reduceToNat]
  rw [Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hm2]
  norm_num

theorem carry_lt {x c : ℕ} (hx : x < base) (hc : c < base) : (x * 10 ^ 9 + c) / base < base := by
  rw [base_eq] at *
  omega

/-- The step of the multiply-and-add: the digit and the carry keep the invariant. -/
theorem carry_step {Pst PW x c d i : ℕ} (h5 : Pst + c * base ^ i = PW * 10 ^ 9 + d) :
    Pst + (x * 10 ^ 9 + c) % base * base ^ i + (x * 10 ^ 9 + c) / base * (base ^ i * base) =
      (PW + x * base ^ i) * 10 ^ 9 + d := by
  have hdm := Nat.div_add_mod (x * 10 ^ 9 + c) base
  have e1 : (x * 10 ^ 9 + c) % base * base ^ i + (x * 10 ^ 9 + c) / base * (base ^ i * base) =
      (x * 10 ^ 9 + c) * base ^ i := by
    conv_rhs => rw [← hdm]
    ring
  calc Pst + (x * 10 ^ 9 + c) % base * base ^ i + (x * 10 ^ 9 + c) / base * (base ^ i * base)
      = Pst + (x * 10 ^ 9 + c) * base ^ i := by rw [Nat.add_assoc, e1]
    _ = (Pst + c * base ^ i) + x * 10 ^ 9 * base ^ i := by ring
    _ = _ := by rw [h5]; ring

/-- The inner loop of `decimalValue`: `W · 10^9 + d` in place over the `C` limbs of `W`, when the
result is below `2^(32 C)`. -/
theorem mulAdd_spec (W : Array UInt64) (C d : UInt64) (hC : C.toNat = W.size)
    (hW : Digits W) (hs : W.size < 2 ^ 32) (hd : d.toNat < base)
    (hlt : value W * 10 ^ 9 + d.toNat < base ^ W.size) :
    (LeanExe.loop C (d, W) fun i st =>
      ((st.2[i.toNat]! * 1000000000 + st.1) >>> 32,
        st.2.set! i.toNat ((st.2[i.toNat]! * 1000000000 + st.1) &&& 0xFFFFFFFF))).2.size =
        W.size ∧
      Digits (LeanExe.loop C (d, W) fun i st =>
      ((st.2[i.toNat]! * 1000000000 + st.1) >>> 32,
        st.2.set! i.toNat ((st.2[i.toNat]! * 1000000000 + st.1) &&& 0xFFFFFFFF))).2 ∧
      value (LeanExe.loop C (d, W) fun i st =>
      ((st.2[i.toNat]! * 1000000000 + st.1) >>> 32,
        st.2.set! i.toNat ((st.2[i.toNat]! * 1000000000 + st.1) &&& 0xFFFFFFFF))).2 =
        value W * 10 ^ 9 + d.toNat := by
  have key := loop_induction (n := C) (init := (d, W))
    (f := fun i st =>
      ((st.2[i.toNat]! * 1000000000 + st.1) >>> 32,
        st.2.set! i.toNat ((st.2[i.toNat]! * 1000000000 + st.1) &&& 0xFFFFFFFF)))
    (fun i (st : UInt64 × Array UInt64) => st.2.size = W.size ∧
      (∀ p : ℕ, i ≤ p → st.2[p]! = W[p]!) ∧ (∀ p : ℕ, st.2[p]!.toNat < base) ∧
      st.1.toNat < base ∧
      prefixValue st.2 i + st.1.toNat * base ^ i = prefixValue W i * 10 ^ 9 + d.toNat)
    ⟨rfl, fun _ _ => rfl, digit_all hW, hd, by simp [prefixValue_zero]⟩
    (by
      intro i st hi ⟨h1, h2, h3, h4, h5⟩
      rw [hC] at hi
      have hii : (UInt64.ofNat i).toNat = i :=
        UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      simp only [hii]
      have hx : st.2[i]! = W[i]! := h2 i le_rfl
      have hxb : W[i]!.toNat < base := digit_all hW i
      have ht : (st.2[i]! * 1000000000 + st.1).toNat = W[i]!.toNat * 10 ^ 9 + st.1.toNat := by
        rw [hx]; exact toNat_mulAdd _ _ hxb h4
      refine ⟨by rw [Array.size_set!, h1], fun p hp => ?_, fun p => ?_, ?_, ?_⟩
      · rw [get_set _ _ _ _ (by omega), ite_eq_right (by omega)]
        exact h2 p (by omega)
      · rw [get_set _ _ _ _ (by omega)]
        split
        · rw [and_mask]; exact Nat.mod_lt _ base_pos
        · exact h3 p
      · rw [shr32, ht]
        exact carry_lt hxb h4
      · rw [prefixValue_set_last _ (by omega), and_mask, shr32, ht, pow_succ, prefixValue_succ]
        exact carry_step h5)
  rw [hC] at key
  obtain ⟨h1, -, h3, -, h5⟩ := key
  generalize (LeanExe.loop C (d, W) fun i st =>
      ((st.2[i.toNat]! * 1000000000 + st.1) >>> 32,
        st.2.set! i.toNat ((st.2[i.toNat]! * 1000000000 + st.1) &&& 0xFFFFFFFF))) = R at h1 h3 h5 ⊢
  have hvR : value R.2 = prefixValue R.2 W.size := by unfold value; rw [h1]
  have hvW : value W = prefixValue W W.size := rfl
  rw [← hvR, ← hvW] at h5
  have hc0 : R.1.toNat = 0 := by
    by_contra hc
    have : base ^ W.size ≤ R.1.toNat * base ^ W.size := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [hc0, Nat.zero_mul, Nat.add_zero] at h5
  exact ⟨h1, fun i _ => h3 i, h5⟩

/-! ## The value of the digits -/

/-- The digit at position `q` of the text padded with `pad` leading zeros. -/
def padDigit (s : Array UInt64) (start pad : ℕ) (q : ℕ) : ℕ :=
  if q < pad then 0 else s[start + (q - pad)]!.toNat - 48

theorem padDigit_lt {s : Array UInt64} {start pad : ℕ} (hs : start ≤ s.size)
    (hdig : ∀ w ∈ s.toList.drop start, isDigitWord w = true) (q : ℕ) :
    padDigit s start pad q < 10 := by
  unfold padDigit
  split
  · omega
  · by_cases hq : start + (q - pad) < s.size
    · have hmem : s[start + (q - pad)]! ∈ s.toList.drop start := by
        rw [getElem!_pos s _ hq]
        apply List.mem_iff_getElem.mpr
        refine ⟨q - pad, by simp; omega, ?_⟩
        rw [List.getElem_drop, Array.getElem_toList]
      have := (isDigitWord_iff _).mp (hdig _ hmem)
      omega
    · rw [getElem!_neg s _ hq]
      decide

/-- The loop of one chunk computes the value of its nine digits. -/
theorem chunk_spec (s : Array UInt64) (start pad k : UInt64) (hs : s.size < 2 ^ 32)
    (hst : start.toNat ≤ s.size) (hk : k.toNat < 2 ^ 32) (hpad : pad.toNat ≤ 8)
    (hrange : 9 * k.toNat + 9 ≤ pad.toNat + (s.size - start.toNat))
    (hdig : ∀ w ∈ s.toList.drop start.toNat, isDigitWord w = true) :
    (LeanExe.loop 9 (0 : UInt64) fun e v =>
      10 * v + (if 9 * k + e < pad then 0 else s[(start + (9 * k + e - pad)).toNat]! - 48)).toNat =
      dv (fun e => padDigit s start.toNat pad.toNat (9 * k.toNat + e)) 9 := by
  have key := loop_induction (n := 9) (init := (0 : UInt64))
    (f := fun e v =>
      10 * v + (if 9 * k + e < pad then 0 else s[(start + (9 * k + e - pad)).toNat]! - 48))
    (fun e v => v.toNat = dv (fun e => padDigit s start.toNat pad.toNat (9 * k.toNat + e)) e)
    rfl
    (by
      intro e v he hv
      have he9 : e < 9 := by simpa using he
      have hee : (UInt64.ofNat e).toNat = e :=
        UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      have hq : (9 * k + UInt64.ofNat e).toNat = 9 * k.toNat + e := by
        rw [UInt64.toNat_add, UInt64.toNat_mul, hee]
        simp only [UInt64.reduceToNat]
        omega
      have hlt := padDigit_lt (pad := pad.toNat) hst hdig (9 * k.toNat + e)
      have hdv := dv_lt (g := fun e => padDigit s start.toNat pad.toNat (9 * k.toNat + e))
        (fun q => padDigit_lt hst hdig _) e
      have h10 : 10 ^ e ≤ 10 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpd : (if 9 * k + UInt64.ofNat e < pad then (0 : UInt64)
          else s[(start + (9 * k + UInt64.ofNat e - pad)).toNat]! - 48).toNat =
          padDigit s start.toNat pad.toNat (9 * k.toNat + e) := by
        unfold padDigit
        by_cases hlt' : 9 * k.toNat + e < pad.toNat
        · rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, hq]; exact hlt'), ite_eq_left hlt']
          rfl
        · rw [ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, hq]; exact hlt'), ite_eq_right hlt']
          have hidx : (start + (9 * k + UInt64.ofNat e - pad)).toNat =
              start.toNat + (9 * k.toNat + e - pad.toNat) := by
            rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (by
              rw [UInt64.le_iff_toNat_le, hq]; omega), hq]
            omega
          rw [hidx]
          by_cases hin : start.toNat + (9 * k.toNat + e - pad.toNat) < s.size
          · have hmem : s[start.toNat + (9 * k.toNat + e - pad.toNat)]! ∈
                s.toList.drop start.toNat := by
              rw [getElem!_pos s _ hin]
              apply List.mem_iff_getElem.mpr
              refine ⟨9 * k.toNat + e - pad.toNat, by simp; omega, ?_⟩
              rw [List.getElem_drop, Array.getElem_toList]
            have hd := (isDigitWord_iff _).mp (hdig _ hmem)
            rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using hd.1)]
            rfl
          · omega
      show (10 * v + _).toNat = _
      have hv8 : v.toNat < 10 ^ 8 := hv ▸ lt_of_lt_of_le hdv h10
      rw [UInt64.toNat_add, UInt64.toNat_mul, hpd]
      simp only [UInt64.reduceToNat]
      have h2 : 10 * v.toNat + padDigit s start.toNat pad.toNat (9 * k.toNat + e) < 2 ^ 64 := by
        have : 10 * v.toNat + padDigit s start.toNat pad.toNat (9 * k.toNat + e) < 10 ^ 9 := by
          omega
        exact lt_of_lt_of_le this (by norm_num)
      have h1 : 10 * v.toNat < 2 ^ 64 := lt_of_le_of_lt (Nat.le_add_right _ _) h2
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, dv, hv])
  simpa using key

theorem drop_getElem! (s : Array UInt64) {start e : ℕ} (h : start + e < s.size) :
    (s.toList.drop start)[e]! = s[start + e]! := by
  rw [getElem!_pos (s.toList.drop start) e (by simp; omega), getElem!_pos s _ h,
    List.getElem_drop, Array.getElem_toList]

/-- The limbs of `decimalValue` are the canonical limbs of the digits' value. -/
theorem decimalValue_eq (s : Array UInt64) (start count : UInt64) (hs : s.size < 2 ^ 32)
    (hsz : start.toNat + count.toNat = s.size)
    (hdig : ∀ w ∈ s.toList.drop start.toNat, isDigitWord w = true) :
    decimalValue s start count = limbsOf (digitsValue (s.toList.drop start.toNat)) := by
  unfold decimalValue
  dsimp only
  have hCn : ((count + 8) / 9).toNat = (count.toNat + 8) / 9 := by
    rw [UInt64.toNat_div, UInt64.toNat_add]
    simp only [UInt64.reduceToNat]
    rw [Nat.mod_eq_of_lt (by omega)]
  generalize hC : (count + 8) / 9 = C at hCn ⊢
  have hpn : (9 * C - count).toNat = 9 * ((count.toNat + 8) / 9) - count.toNat := by
    have h9 : (9 * C).toNat = 9 * ((count.toNat + 8) / 9) := by
      rw [UInt64.toNat_mul, hCn]; simp only [UInt64.reduceToNat]; omega
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, h9]; omega), h9]
  generalize hP : 9 * C - count = pad at hpn ⊢
  generalize hCN : (count.toNat + 8) / 9 = CN at hCn hpn
  have hgl := fun q => padDigit_lt (pad := pad.toNat) (by omega) hdig q
  have key := loop_induction (n := C) (init := LeanExe.build C fun _ => (0 : UInt64))
    (f := fun k w =>
      (LeanExe.loop C ((LeanExe.loop 9 (0 : UInt64) fun e v =>
        10 * v + (if 9 * k + e < pad then 0 else s[(start + (9 * k + e - pad)).toNat]! - 48)),
          w) fun i st =>
        ((st.2[i.toNat]! * 1000000000 + st.1) >>> 32,
          st.2.set! i.toNat ((st.2[i.toNat]! * 1000000000 + st.1) &&& 0xFFFFFFFF))).2)
    (fun kk (w : Array UInt64) => w.size = CN ∧ Digits w ∧
      value w = dv (padDigit s start.toNat pad.toNat) (9 * kk))
    ⟨by rw [build_size, hCn], fun i hi => by
      rw [build_size] at hi; rw [build_get hi]; exact base_pos, by
      rw [Nat.mul_zero, dv]
      unfold value prefixValue
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      rw [List.mem_range, build_size] at hi
      rw [build_get hi, show (0 : UInt64).toNat = 0 from rfl, Nat.zero_mul]⟩
    (by
      intro kk w hkk ⟨h1, h2, h3⟩
      rw [hCn] at hkk
      have hkk' : (UInt64.ofNat kk).toNat = kk :=
        UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      have hch := chunk_spec s start pad (UInt64.ofNat kk) hs (by omega) (by rw [hkk']; omega)
        (by omega) (by rw [hkk']; omega) hdig
      rw [hkk'] at hch
      have hdl := dv_lt (g := fun e => padDigit s start.toNat pad.toNat (9 * kk + e))
        (fun q => hgl _) 9
      have hb9 : (10 : ℕ) ^ 9 < base := by rw [base_eq]; norm_num
      have hsum := dv_add (padDigit s start.toNat pad.toNat) (9 * kk) 9
      have hglt := dv_lt hgl (9 * kk + 9)
      have hpow : 10 ^ (9 * kk + 9) ≤ base ^ w.size := by
        rw [h1, show 9 * kk + 9 = 9 * (kk + 1) by ring, pow_mul]
        exact le_trans (Nat.pow_le_pow_left hb9.le _) (Nat.pow_le_pow_right base_pos (by omega))
      obtain ⟨m1, m2, m3⟩ := mulAdd_spec w C _ (by rw [hCn, h1]) h2 (by omega)
        (by rw [hch]; omega) (by rw [hch, h3]; rw [hsum] at hglt; nlinarith)
      refine ⟨by rw [m1, h1], m2, ?_⟩
      rw [m3, hch, h3, show 9 * (kk + 1) = 9 * kk + 9 by ring, hsum]
      ring)
  rw [hCn] at key
  obtain ⟨k1, k2, k3⟩ := key
  rw [natTrim_eq k2 (by omega), k3]
  congr 1
  have h9 : 9 * CN = pad.toNat + count.toNat := by omega
  rw [h9, dv_add, dv_zeros (fun q hq => by unfold padDigit; rw [ite_eq_left hq]), Nat.mul_zero,
    Nat.zero_add, digitsValue_eq_dv, show (s.toList.drop start.toNat).length = count.toNat by
      simp; omega]
  apply dv_congr
  intro e he
  unfold padDigit
  rw [ite_eq_right (by omega), show pad.toNat + e - pad.toNat = e by omega,
    drop_getElem! s (by omega)]

/-! ## The reader -/

theorem readSpec_eq_of_denote {s : Array UInt64} {z : ℤ} (h : denote s.toList = some z) :
    readSpec s = (true, .ofInt z) := by
  unfold readSpec; rw [h]

theorem readSpec_eq_of_none {s : Array UInt64} (h : denote s.toList = none) :
    readSpec s = (false, ⟨false, #[]⟩) := by
  unfold readSpec; rw [h]; simp [BigInt.ofInt, limbsOf_zero]

/-- The reader returns the specification's result on every array of fewer than `2^32` words. -/
theorem intOfText_eq (s : Array UInt64) (hs : s.size < 2 ^ 32) : intOfText s = readSpec s := by
  have hn : s.size.toUInt64.toNat = s.size :=
    UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  have hlen : s.toList.length = s.size := by simp
  simp only [intOfText]
  by_cases h0 : s.size = 0
  · have he : s.toList = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [ite_eq_left (by rw [beq_iff_eq, ← UInt64.toNat_inj, hn, h0]; rfl),
      readSpec_eq_of_none (by rw [he]; simp [denote, magnitude])]
  rw [ite_eq_right (by rw [beq_iff_eq, ← UInt64.toNat_inj, hn]; simpa using h0)]
  obtain ⟨a, t, hl⟩ := toList_cons_of_size s h0
  have hsz : s.size = t.length + 1 := by rw [← hlen, hl]; rfl
  have h0a : s[(0 : UInt64).toNat]! = a := by
    rw [getElem!_of_toList s _ (by simp; omega)]
    simp [hl]
  rw [h0a]
  by_cases ha : a = 45
  · subst ha
    have hb : ((45 : UInt64) == 45) = true := rfl
    simp only [hb, ↓reduceIte, Bool.not_true, Bool.and_false, Bool.or_false]
    generalize hCd : s.size.toUInt64 - 1 = C
    have hCn : C.toNat = t.length := by
      rw [← hCd, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hn]; simp; omega), hn]
      simp only [UInt64.reduceToNat]
      omega
    have hden : denote s.toList = (magnitude t).map fun n : ℕ => -(n : ℤ) := by
      rw [hl, denote_minus _ (by simp) (by simp), List.tail_cons]
    by_cases ht0 : t = []
    · subst ht0
      rw [ite_eq_left (by rw [beq_iff_eq, ← UInt64.toNat_inj, hCn]; rfl),
        readSpec_eq_of_none (by rw [hden]; simp [magnitude])]
    rw [ite_eq_right (by rw [beq_iff_eq, ← UInt64.toNat_inj, hCn]; simpa using ht0)]
    obtain ⟨d, rest, htd⟩ : ∃ d rest, t = d :: rest := by
      cases t with
      | nil => exact absurd rfl ht0
      | cons d rest => exact ⟨d, rest, rfl⟩
    have htl : 1 ≤ t.length := by rw [htd]; simp
    have hdrop : s.toList.drop (1 : UInt64).toNat = t := by rw [hl]; rfl
    have hall := allDigits_spec s 1 C (by omega) (by simp only [UInt64.reduceToNat]; omega)
    rw [hdrop] at hall
    have h1d : s[(1 : UInt64).toNat]! = d := by
      rw [getElem!_of_toList s _ (by simp; omega)]
      simp [hl, htd]
    rw [h1d, hall]
    rw [htd, magnitude_cons d rest] at hden
    by_cases hc : ((d :: rest).all isDigitWord && d != 48) = true
    · rw [htd, ite_eq_left hc]
      rw [ite_eq_left hc, Option.map_some] at hden
      rw [readSpec_eq_of_denote hden]
      have hdig : ∀ w ∈ s.toList.drop (1 : UInt64).toNat, isDigitWord w = true := by
        rw [hdrop, htd]
        simp only [Bool.and_eq_true] at hc
        exact List.all_eq_true.mp hc.1
      rw [decimalValue_eq s 1 C hs (by simp only [UInt64.reduceToNat]; omega) hdig, hdrop, htd]
      have hd49 := isDigitWord_ne48 (d := d) (by
        simp only [List.all_cons, Bool.and_eq_true] at hc ⊢; exact ⟨hc.1.1, hc.2⟩)
      have hpos := digitsValue_pos (rest := rest) hd49
      unfold BigInt.ofInt
      congr 2
      · simp; omega
      · rw [Int.natAbs_neg, Int.natAbs_natCast]
    · rw [htd, ite_eq_right hc]
      rw [ite_eq_right hc] at hden
      rw [readSpec_eq_of_none (by rw [hden]; rfl)]
  · have hb : (a == 45) = false := by simpa using ha
    simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true]
    have hdrop : s.toList.drop (0 : UInt64).toNat = s.toList := rfl
    have hall := allDigits_spec s 0 (s.size.toUInt64 - 0) (by omega) (by
      simp only [UInt64.reduceToNat, Nat.zero_add]
      rw [UInt64.sub_zero, hn])
    rw [hdrop] at hall
    rw [show s.size.toUInt64 - 0 = s.size.toUInt64 from UInt64.sub_zero _]
    rw [show s.size.toUInt64 - 0 = s.size.toUInt64 from UInt64.sub_zero _] at hall
    rw [ite_eq_right (by rw [beq_iff_eq, ← UInt64.toNat_inj, hn]; simpa using h0), h0a, hall]
    by_cases h48 : s.toList = [48]
    · have hsz1 : s.size = 1 := by rw [← hlen, h48]; rfl
      have ha48 : a = 48 := by rw [hl] at h48; simp at h48; exact h48.1
      have hc : (s.toList.all isDigitWord && (a != 48 || s.size.toUInt64 == 1)) = true := by
        rw [h48, ha48]
        simp only [List.all_cons, List.all_nil, Bool.and_true, bne_self_eq_false,
          Bool.false_or, Bool.and_eq_true, beq_iff_eq]
        refine ⟨rfl, ?_⟩
        rw [← UInt64.toNat_inj, hn, hsz1]; rfl
      rw [ite_eq_left hc, readSpec_eq_of_denote (by rw [h48]; exact denote_zero),
        decimalValue_eq s 0 s.size.toUInt64 hs (by simp only [UInt64.reduceToNat]; omega)
          (by rw [hdrop, h48]; simp; rfl), hdrop, h48]
      rfl
    · have h45 : ¬ s.toList.head? = some 45 := by rw [hl]; simpa using ha
      have hden := denote_plain _ h48 h45
      rw [show magnitude s.toList = magnitude (a :: t) by rw [hl], magnitude_cons a t] at hden
      by_cases ha48 : a = 48
      · subst ha48
        have ht0 : t ≠ [] := by rintro rfl; exact h48 hl
        have hc : ¬ (s.toList.all isDigitWord && ((48 : UInt64) != 48 || s.size.toUInt64 == 1))
            = true := by
          simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq, not_and]
          intro _ h1
          rw [← UInt64.toNat_inj, hn] at h1
          have : t.length = 0 := by simp at h1; omega
          exact ht0 (List.eq_nil_of_length_eq_zero this)
        rw [ite_eq_right hc, readSpec_eq_of_none (by rw [hden]; simp)]
      · have hane : (a != 48) = true := by simpa using ha48
        by_cases hc : s.toList.all isDigitWord = true
        · have hc' : ((a :: t).all isDigitWord && a != 48) = true := by
            rw [← hl, hc, hane]; rfl
          rw [ite_eq_left (by rw [hc, hane]; rfl)]
          rw [ite_eq_left hc', Option.map_some] at hden
          rw [readSpec_eq_of_denote hden,
            decimalValue_eq s 0 s.size.toUInt64 hs (by simp only [UInt64.reduceToNat]; omega)
              (by rw [hdrop]; exact List.all_eq_true.mp hc), hdrop, hl]
          unfold BigInt.ofInt
          congr 2
        · have hc' : ¬ ((a :: t).all isDigitWord && a != 48) = true := by
            rw [← hl]; simp [hc]
          rw [ite_eq_right (by simp [hc])]
          rw [ite_eq_right hc'] at hden
          rw [readSpec_eq_of_none (by rw [hden]; rfl)]

/-- The reader reads the printer's text of `z` as `z`. -/
theorem read_print (z : ℤ) (h : (printSpec z).size < 2 ^ 32) :
    intOfText (printSpec z) = (true, .ofInt z) := by
  rw [intOfText_eq _ h, readSpec_print]

end Library.Numerics.Bignum
