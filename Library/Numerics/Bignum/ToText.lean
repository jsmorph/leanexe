module

public import Library.Numerics.Bignum.IntProof
public import Library.Numerics.Bignum.Inverse
public import Library.Numerics.Decimal.Int64Text.Proof

@[expose] public section

/-!
The printer equals the specification: `intToText_eq`.  `divLoop_spec` proves the inner loop of
`chunks`, a short division by `10^9` from the top limb down that writes each quotient limb over
the limb it reads.  After `e` steps the limbs below `N - e` are those of the dividend and the array
holds `prefixValue W (N - e) + base^(N - e) · ⌊W / base^(N - e) / 10^9⌋`, with the remainder of
`⌊W / base^(N - e)⌋` by `10^9` in the state, which at `e = N` gives the quotient and the
remainder; the step is MultiPrecision's `div_step`, as in `shortDiv_spec`.  `chunks_spec` gives
chunk `j` as `⌊A / 10^(9 j)⌋ mod 10^9`, `pow_chunks` shows that `K = n + n / 14 + 2` chunks hold
every digit of a value below `2^(32 n)`, from `2^448 < 10^135`, and `text_length` counts the digits
from the top nonzero chunk.  Digit `p` from the least significant is digit `p mod 9` of chunk
`⌊p / 9⌋`, and Int64Text's `digitWords_getElem?` reads the specification's digit at the same place.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open Library.Numerics.Decimal.Int64Text (digitWords digitWords_getElem? digitCount_toNat
  digitByte_eq digitWords_length_le_iff digitWords_length_pos build_getElem? digitCount digitByte)
open LeanExe.Dialect

/-! ## Values after an update -/

theorem prefixValue_set_add (w : Array UInt64) {p : ℕ} (hp : p < w.size) (y : UInt64) (L : ℕ) :
    prefixValue (w.set! p y) L + (if p < L then w[p]!.toNat * base ^ p else 0) =
      prefixValue w L + (if p < L then y.toNat * base ^ p else 0) := by
  induction L with
  | zero => simp [prefixValue_zero]
  | succ L ih =>
    rw [prefixValue_succ, prefixValue_succ, get_set w p y L hp]
    by_cases hL : p < L
    · rw [ite_eq_left hL, ite_eq_left hL] at ih
      rw [ite_eq_left (show p < L + 1 by omega), ite_eq_left (show p < L + 1 by omega),
        ite_eq_right (show ¬ L = p by omega)]
      omega
    · rw [ite_eq_right hL, ite_eq_right hL] at ih
      by_cases hpL : p = L
      · subst hpL
        rw [ite_eq_left (rfl : p = p), ite_eq_left (show p < p + 1 by omega),
          ite_eq_left (show p < p + 1 by omega)]
        omega
      · rw [ite_eq_right (show ¬ p < L + 1 by omega), ite_eq_right (show ¬ p < L + 1 by omega),
          ite_eq_right (show ¬ L = p by omega)]
        omega

/-- Writing `y` at position `p` changes the value by the difference of the limbs there. -/
theorem value_set_add (w : Array UInt64) {p : ℕ} (hp : p < w.size) (y : UInt64) :
    value (w.set! p y) + w[p]!.toNat * base ^ p = value w + y.toNat * base ^ p := by
  have h := prefixValue_set_add w hp y w.size
  rw [ite_eq_left hp, ite_eq_left hp] at h
  unfold value
  rw [Array.size_set!]
  exact h

/-! ## Short division in place -/

theorem base_mul_eq : (4294967296 : UInt64).toNat = base := by rw [base_eq]; rfl

/-- The inner loop of `chunks`: a short division by `10^9` over the `n` limbs of `W`. -/
def divLoop (n : UInt64) (W : Array UInt64) : UInt64 × Array UInt64 :=
  LeanExe.loop n ((0 : UInt64), W) fun e s =>
    ((s.1 * 4294967296 + s.2[(n - 1 - e).toNat]!) % 1000000000,
      s.2.set! (n - 1 - e).toNat ((s.1 * 4294967296 + s.2[(n - 1 - e).toNat]!) / 1000000000))

/-- The short division of `chunks` by `10^9`: the quotient in place of the dividend and the
remainder. -/
theorem divLoop_spec (W : Array UInt64) (n : UInt64) (hn : n.toNat = W.size) (hW : Digits W)
    (hs : W.size < 2 ^ 32) :
    (divLoop n W).2.size = W.size ∧ Digits (divLoop n W).2 ∧
      value (divLoop n W).2 = value W / 10 ^ 9 ∧ (divLoop n W).1.toNat = value W % 10 ^ 9 := by
  generalize hN : W.size = N at hn hs
  have hb := base_eq
  have hvlt : value W < base ^ N := by rw [← hN]; exact value_lt hW
  have key := loop_induction (n := n) (init := ((0 : UInt64), W))
    (f := fun e s =>
      ((s.1 * 4294967296 + s.2[(n - 1 - e).toNat]!) % 1000000000,
        s.2.set! (n - 1 - e).toNat ((s.1 * 4294967296 + s.2[(n - 1 - e).toNat]!) / 1000000000)))
    (fun e (s : UInt64 × Array UInt64) => s.2.size = N ∧ (∀ p : ℕ, p < N - e → s.2[p]! = W[p]!) ∧
      (∀ p : ℕ, s.2[p]!.toNat < base) ∧
      value s.2 = prefixValue W (N - e) + base ^ (N - e) * (value W / base ^ (N - e) / 10 ^ 9) ∧
      s.1.toNat = value W / base ^ (N - e) % 10 ^ 9)
    ⟨hN, fun _ _ => rfl, digit_all hW, by
      rw [Nat.sub_zero, Nat.div_eq_of_lt hvlt, Nat.zero_div, Nat.mul_zero, Nat.add_zero]
      unfold value; rw [hN], by
      rw [Nat.sub_zero, Nat.div_eq_of_lt hvlt]; rfl⟩
    (by
      intro e s he ⟨h1, h2, h3, h4, h5⟩
      rw [hn] at he
      have hp : (n - 1 - UInt64.ofNat e).toNat = N - 1 - e := by
        have he' : (UInt64.ofNat e).toNat = e :=
          UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
        have h1n : (n - 1).toNat = N - 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hn]; simp; omega), hn]
          simp
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, h1n, he']; omega), h1n, he']
      simp only [hp]
      generalize hP : N - 1 - e = P
      have hPN : P < N := by omega
      have hNe : N - e = P + 1 := by omega
      have hNe' : N - (e + 1) = P := by omega
      rw [hNe] at h4 h5
      rw [hNe']
      have hx : s.2[P]! = W[P]! := h2 P (by omega)
      have hxb : W[P]!.toNat < base := digit_all hW P
      have hr : s.1.toNat < 10 ^ 9 := by rw [h5]; exact Nat.mod_lt _ (by positivity)
      have ht : (s.1 * 4294967296 + s.2[P]!).toNat = s.1.toNat * base + W[P]!.toNat := by
        have hprod : s.1.toNat * base < 2 ^ 64 := by rw [hb]; omega
        have hsum : s.1.toNat * base + W[P]!.toNat < 2 ^ 64 := by rw [hb] at hxb ⊢; omega
        rw [UInt64.toNat_add, UInt64.toNat_mul, hx, base_mul_eq, Nat.mod_eq_of_lt hprod,
          Nat.mod_eq_of_lt hsum]
      generalize hT : value W / base ^ (P + 1) = T at h4 h5
      have hT' : value W / base ^ P = T * base + W[P]!.toNat := by
        rw [← value_digit hW P, ← hT, pow_succ, ← Nat.div_div_eq_div_mul]
        exact (Nat.div_add_mod' _ _).symm
      obtain ⟨hdq, hdr⟩ := div_step (H := T) (b := base) (x := W[P]!.toNat)
        (show 0 < 10 ^ 9 by positivity)
      have hq : ((s.1 * 4294967296 + s.2[P]!) / 1000000000).toNat =
          (T % 10 ^ 9 * base + W[P]!.toNat) / 10 ^ 9 := by
        rw [UInt64.toNat_div, ht, h5]; rfl
      have hqb : (T % 10 ^ 9 * base + W[P]!.toNat) / 10 ^ 9 < base := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]
        have := Nat.mod_lt T (show 0 < 10 ^ 9 by positivity)
        rw [hb] at hxb ⊢
        nlinarith
      refine ⟨by rw [Array.size_set!, h1], fun p hp' => ?_, fun p => ?_, ?_, ?_⟩
      · rw [get_set _ _ _ _ (by omega), ite_eq_right (by omega)]
        exact h2 p (by omega)
      · rw [get_set _ _ _ _ (by omega)]
        split
        · rw [hq]; exact hqb
        · exact h3 p
      · have hv := value_set_add s.2 (p := P) (by omega)
          ((s.1 * 4294967296 + s.2[P]!) / 1000000000)
        rw [hq, h4, hx, prefixValue_succ W P, pow_succ] at hv
        rw [hT', hdq, hx]
        linarith
      · rw [UInt64.toNat_mod, ht, h5, hT', hdr]
        rfl)
  rw [hn, Nat.sub_self] at key
  obtain ⟨h1, -, h3, h4, h5⟩ := key
  refine ⟨h1, fun i _ => h3 i, ?_, ?_⟩
  · rw [divLoop, h4, pow_zero, Nat.div_one, prefixValue_zero, Nat.one_mul, Nat.zero_add]
  · rw [divLoop, h5, pow_zero, Nat.div_one]

/-! ## The chunks -/

/-- Chunk `j` of the chunks of `m` is `⌊A / 10^(9 j)⌋ mod 10^9` for the value `A` of `m`. -/
theorem chunks_spec (m : Array UInt64) (K : UInt64) (hm : Digits m) (hs : m.size < 2 ^ 32) :
    (chunks m K).size = K.toNat ∧
      ∀ j, j < K.toNat → (chunks m K)[j]!.toNat = value m / 10 ^ (9 * j) % 10 ^ 9 := by
  have hn := size_toNat (u := m) (by omega)
  have hcopy : LeanExe.build m.size.toUInt64 (fun i => m[i.toNat]!) = m := by
    apply array_ext (by rw [build_size, hn])
    intro i hi
    rw [build_size, hn] at hi
    rw [build_get (by rw [hn]; exact hi), UInt64.toNat_ofNat_of_lt' (by
      simp only [UInt64.size]; omega)]
  have key := loop_induction (n := K)
    (init := (LeanExe.build m.size.toUInt64 (fun i => m[i.toNat]!),
      LeanExe.build K fun _ => (0 : UInt64)))
    (f := fun k st => ((divLoop m.size.toUInt64 st.1).2,
      st.2.set! k.toNat (divLoop m.size.toUInt64 st.1).1))
    (fun k (st : Array UInt64 × Array UInt64) => st.1.size = m.size ∧ Digits st.1 ∧ value st.1 = value m / 10 ^ (9 * k) ∧
      st.2.size = K.toNat ∧ ∀ j, j < k → st.2[j]!.toNat = value m / 10 ^ (9 * j) % 10 ^ 9)
    ⟨by rw [hcopy], by rw [hcopy]; exact hm, by rw [hcopy]; simp, build_size _ _,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
    (by
      intro k st hk ⟨h1, h2, h3, h4, h5⟩
      obtain ⟨d1, d2, d3, d4⟩ := divLoop_spec st.1 m.size.toUInt64 (by rw [hn, h1]) h2 (by omega)
      have hkk : (UInt64.ofNat k).toNat = k :=
        UInt64.toNat_ofNat_of_lt' (by have := K.toNat_lt; simp only [UInt64.size] at this ⊢; omega)
      refine ⟨by rw [d1, h1], d2, ?_, by rw [Array.size_set!, h4], fun j hj => ?_⟩
      · rw [d3, h3, Nat.div_div_eq_div_mul, ← pow_add]
        congr 2
      · rw [hkk, get_set _ _ _ _ (by omega)]
        split
        · rename_i hjk
          rw [d4, h3, hjk]
        · exact h5 j (by omega))
  obtain ⟨-, -, -, h4, h5⟩ := key
  unfold chunks
  exact ⟨h4, h5⟩

/-! ## Enough chunks -/

/-- `2^(32 n) ≤ 10^(9 (n + n / 14 + 2))`, from `2^448 < 10^135`, so `n + n / 14 + 2` chunks of nine
decimal digits hold every value of `n` limbs. -/
theorem pow_chunks (n : ℕ) : base ^ n ≤ 10 ^ (9 * (n + n / 14 + 2)) := by
  have hb := base_eq
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 14 ∧ n = 14 * q + r :=
    ⟨n / 14, n % 14, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 14).symm⟩
  rw [show (14 * q + r) / 14 = q by omega]
  have h1 : base ^ (14 * q + r) = (base ^ 14) ^ q * base ^ r := by rw [pow_add, pow_mul]
  have h2 : 10 ^ (9 * (14 * q + r + q + 2)) = (10 ^ 135) ^ q * 10 ^ (9 * (r + 2)) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  rw [h1, h2]
  apply Nat.mul_le_mul
  · apply Nat.pow_le_pow_left; rw [hb]; norm_num
  · interval_cases r <;> rw [hb] <;> norm_num

/-- A value below `B^K` whose digits in base `B` vanish from position `s` on is below `B^s`. -/
theorem lt_of_digits_zero {A B K s : ℕ} (hB : 0 < B) (hA : A < B ^ K)
    (hz : ∀ j, s ≤ j → j < K → A / B ^ j % B = 0) (hs : s ≤ K) : A < B ^ s := by
  have key : ∀ i, i ≤ K - s → A < B ^ (K - i) := by
    intro i hi
    induction i with
    | zero => simpa using hA
    | succ i ih =>
      have h := ih (by omega)
      have hj := hz (K - i - 1) (by omega) (by omega)
      rw [show K - i = K - i - 1 + 1 by omega, pow_succ] at h
      have hlt : A / B ^ (K - i - 1) < B :=
        (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by rw [Nat.mul_comm]; exact h)
      rw [Nat.mod_eq_of_lt hlt] at hj
      rw [show K - (i + 1) = K - i - 1 by omega]
      rcases Nat.div_eq_zero_iff.mp hj with h0 | h0
      · exact absurd h0 (by positivity)
      · exact h0
  have := key (K - s) le_rfl
  rwa [show K - (K - s) = s by omega] at this

/-- The digits of `A` are those of its top chunk `c = ⌊A / 10^(9 t)⌋` and `9 t` more. -/
theorem digits_length_split {A t c : ℕ} (hc : c = A / 10 ^ (9 * t))
    (hA : A < 10 ^ (9 * (t + 1))) (ht : 0 < t → 0 < c) :
    (digitWords c).length + 9 * t = (digitWords A).length := by
  rcases Nat.eq_zero_or_pos t with h0 | htp
  · subst h0
    simp [hc]
  have hcp := ht htp
  have hD := digitWords_length_pos c
  generalize hDd : (digitWords c).length = D at hD
  have hcD : c < 10 ^ D := (digitWords_length_le_iff c D hD).mp (by omega)
  have hAc : c * 10 ^ (9 * t) ≤ A := by rw [hc]; exact Nat.div_mul_le_self _ _
  have hAu : A < 10 ^ (9 * t) * (c + 1) := by rw [hc]; exact Nat.lt_mul_div_succ A (by positivity)
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have hle : (digitWords A).length ≤ 9 * t + D - 1 := by omega
    have hA' := (digitWords_length_le_iff A (9 * t + D - 1) (by omega)).mp hle
    have hcl : 10 ^ (D - 1) ≤ c := by
      rcases Nat.eq_zero_or_pos (D - 1) with hd | hd
      · rw [hd]; simpa using Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hcp)
      · by_contra hc'
        push Not at hc'
        have := (digitWords_length_le_iff c (D - 1) hd).mpr hc'
        omega
    have : 10 ^ (9 * t + D - 1) ≤ A := by
      calc 10 ^ (9 * t + D - 1) = 10 ^ (D - 1) * 10 ^ (9 * t) := by
            rw [← pow_add]; congr 1; omega
        _ ≤ c * 10 ^ (9 * t) := Nat.mul_le_mul_right _ hcl
        _ ≤ A := hAc
    omega
  · apply (digitWords_length_le_iff A _ (by omega)).mpr
    calc A < 10 ^ (9 * t) * (c + 1) := hAu
      _ ≤ 10 ^ (9 * t) * 10 ^ D := Nat.mul_le_mul_left _ hcD
      _ = 10 ^ (D + 9 * t) := by rw [← pow_add, Nat.add_comm]

/-- Digit `e < 9` of chunk `q` is digit `9 q + e` of `A`. -/
theorem chunk_digit (A q e : ℕ) (he : e < 9) :
    A / 10 ^ (9 * q) % 10 ^ 9 / 10 ^ e % 10 = A / 10 ^ (9 * q + e) % 10 := by
  rw [show (10 : ℕ) ^ 9 = 10 ^ e * 10 ^ (9 - e) by rw [← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 10 (by omega)),
    Nat.div_div_eq_div_mul, ← pow_add]

/-! ## The printer -/

/-- The printer writes Lean's decimal text of the integer. -/
theorem intToText_eq {z : ℤ} (h : (BigInt.ofInt z).mag.size < 2 ^ 32) :
    intToText (.ofInt z) = printSpec z := by
  have hx : BigInt.ofInt z = ⟨decide (z < 0), limbsOf z.natAbs⟩ := rfl
  simp only [BigInt.ofInt] at h
  rw [hx]
  simp only [intToText]
  have hmD := (canonical_limbsOf z.natAbs).1
  have hA := value_limbsOf z.natAbs
  generalize hm : limbsOf z.natAbs = m at h hmD hA ⊢
  have hn := size_toNat (u := m) (by omega)
  have hK : (m.size.toUInt64 + m.size.toUInt64 / 14 + 2).toNat = m.size + m.size / 14 + 2 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_div, hn]
    simp only [UInt64.reduceToNat]
    omega
  generalize hKd : m.size.toUInt64 + m.size.toUInt64 / 14 + 2 = K at hK ⊢
  obtain ⟨hcs, hcj⟩ := chunks_spec m K hmD h
  rw [hK] at hcs hcj
  rw [hA] at hcj
  generalize hc : chunks m K = c at hcs hcj ⊢
  obtain ⟨hts, hz, htop⟩ := significant_spec c (by omega)
  generalize hsc : significant c = sc at hts hz htop ⊢
  have hAK : z.natAbs < (10 ^ 9) ^ (m.size + m.size / 14 + 2) := by
    rw [← pow_mul, ← hA]
    exact lt_of_lt_of_le (value_lt hmD) (pow_chunks _)
  have hAs : z.natAbs < (10 ^ 9) ^ sc.toNat := by
    refine lt_of_digits_zero (by positivity) hAK (fun j h1 h2 => ?_) (by omega)
    have := hcj j (by omega)
    rw [hz j h1] at this
    rw [← pow_mul]
    exact this.symm
  have hTn : (if (sc == 0) = true then (0 : UInt64) else sc - 1).toNat = sc.toNat - 1 := by
    by_cases h0 : sc = 0
    · rw [ite_eq_left (by simp [h0]), h0]; rfl
    · rw [ite_eq_right (by simpa using h0), UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le]
        have : sc.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
        simp; omega)]
      rfl
  generalize hTd : (if (sc == 0) = true then (0 : UInt64) else sc - 1) = T at hTn ⊢
  have hTK : T.toNat < m.size + m.size / 14 + 2 := by omega
  have hAT : z.natAbs < 10 ^ (9 * (T.toNat + 1)) := by
    rw [pow_mul]
    exact lt_of_lt_of_le hAs (Nat.pow_le_pow_right (by positivity) (by omega))
  have hcT : c[T.toNat]!.toNat = z.natAbs / 10 ^ (9 * T.toNat) := by
    rw [hcj _ hTK, Nat.mod_eq_of_lt]
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact lt_of_lt_of_le hAT (by rw [show 9 * (T.toNat + 1) = 9 + 9 * T.toNat by ring])
  have htpos : 0 < T.toNat → 0 < c[T.toNat]!.toNat := by
    intro hT0
    have hne := htop (by omega)
    rw [show sc.toNat - 1 = T.toNat by omega] at hne
    rcases Nat.eq_zero_or_pos c[T.toNat]!.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by rw [h0]; rfl)) hne
    · exact h0
  have hsplit := digits_length_split hcT hAT htpos
  have hcTlt : c[T.toNat]!.toNat < 10 ^ 9 := by
    rw [hcj _ hTK]; exact Nat.mod_lt _ (by positivity)
  have hDc : (digitWords c[T.toNat]!.toNat).length ≤ 9 :=
    (digitWords_length_le_iff _ 9 (by norm_num)).mpr hcTlt
  have hDc1 := digitWords_length_pos c[T.toNat]!.toNat
  have hdc := digitCount_toNat c[T.toNat]!
  generalize hLd : (digitWords z.natAbs).length = L at hsplit
  have hsign : (if decide (z < 0) = true then (1 : UInt64) else 0).toNat =
      if z < 0 then 1 else 0 := by
    by_cases hz0 : z < 0
    · rw [ite_eq_left (by simpa using hz0), ite_eq_left hz0]; rfl
    · rw [ite_eq_right (by simpa using hz0), ite_eq_right hz0]; rfl
  generalize hSd : (if decide (z < 0) = true then (1 : UInt64) else 0) = S at hsign ⊢
  have hlen : (S + digitCount c[T.toNat]! + 9 * T).toNat = (if z < 0 then 1 else 0) + L := by
    have hT9 : (9 * T).toNat = 9 * T.toNat := by
      rw [UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
    rw [UInt64.toNat_add, UInt64.toNat_add, hsign, hdc, hT9]
    split <;> omega
  apply Array.ext_getElem?
  intro i
  rw [← Array.getElem?_toList (xs := printSpec z), printSpec_toList, build_getElem?, hlen]
  have hget := digitWords_getElem? z.natAbs
  rw [hLd] at hget
  have hdigit : ∀ j, j < L → digitByte c[((S + digitCount c[T.toNat]! + 9 * T - 1 -
      UInt64.ofNat (j + (if z < 0 then 1 else 0))) / 9).toNat]!
      ((S + digitCount c[T.toNat]! + 9 * T - 1 -
        UInt64.ofNat (j + (if z < 0 then 1 else 0))) % 9) =
      UInt64.ofNat (z.natAbs / 10 ^ (L - 1 - j) % 10 + 48) := by
    intro j hj
    have hk : (S + digitCount c[T.toNat]! + 9 * T - 1 -
        UInt64.ofNat (j + (if z < 0 then 1 else 0))).toNat = L - 1 - j := by
      have hj' : (UInt64.ofNat (j + (if z < 0 then 1 else 0))).toNat =
          j + (if z < 0 then 1 else 0) :=
        UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; split <;> omega)
      rw [UInt64.toNat_sub, UInt64.toNat_sub, hlen, hj']
      simp only [UInt64.reduceToNat]
      split <;> omega
    rw [digitByte_eq, UInt64.toNat_div, UInt64.toNat_mod, hk]
    simp only [UInt64.reduceToNat]
    rw [hcj _ (by omega), chunk_digit _ _ _ (Nat.mod_lt _ (by norm_num)), Nat.div_add_mod]
  by_cases hneg : z < 0
  · simp only [hneg, ↓reduceIte] at hsign hdigit ⊢
    rcases i with _ | i
    · have hs : UInt64.ofNat 0 < S := by
        rw [UInt64.lt_iff_toNat_lt, hsign]; decide
      rw [ite_eq_left (by omega), ite_eq_left hs]
      rfl
    · rw [List.singleton_append, List.getElem?_cons_succ, hget]
      by_cases hi : i < L
      · rw [ite_eq_left (by omega), ite_eq_left hi]
        have hnot : ¬ UInt64.ofNat (i + 1) < S := by
          rw [UInt64.lt_iff_toNat_lt, hsign, UInt64.toNat_ofNat_of_lt' (by
            simp only [UInt64.size]; omega)]
          omega
        rw [ite_eq_right hnot, hdigit i hi]
      · rw [ite_eq_right (by omega), ite_eq_right hi]
  · simp only [hneg, ↓reduceIte, List.nil_append] at hsign hdigit ⊢
    rw [hget]
    by_cases hi : i < L
    · rw [ite_eq_left (by omega), ite_eq_left hi]
      have hnot : ¬ UInt64.ofNat i < S := by
        rw [UInt64.lt_iff_toNat_lt, hsign]; omega
      rw [ite_eq_right hnot, ← hdigit i hi, Nat.add_zero]
    · rw [ite_eq_right (by omega), ite_eq_right hi]

end Library.Numerics.Bignum
