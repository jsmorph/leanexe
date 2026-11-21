import Demos.RandomChoice.Spec
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.FinEnum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.UInt
import Mathlib.Tactic

/-! Counting theorems of `pickSpec`, which state that the choice is unbiased.  They count words
and sequences of words and assume no probability.

- `pick_count`: for every `n` and every `v` in [1, n], exactly `⌊2^64 / n⌋` words are accepted
  and give `v`, the same number for every `v`.
- `picks_count`: for every `K` and every sequence `o` of `K` values in [1, n], exactly
  `⌊2^64 / n⌋^K` sequences of `K` accepted words give `o`.
- `accepted_count`, `accepted_half`: `n ≥ 1` accepts `2^64 - (2^64 mod n)` words, a multiple of
  `n`, and at least `2^63`.
- `short_count`: for `n ≥ 1` and `M ≥ 4 K + 1024`, at most a `2^-512` part of the sequences of `M`
  words hold fewer than `K` accepted words.

When the words are independent and uniform on [0, 2^64), the first two with `accepted_count` give
the probability of each value and of each sequence of values given that the words are accepted, and
the last bounds the probability that `M` words hold fewer than `K` accepted ones.  The probability
of the command's output also needs the fact that the first `K` accepted words of such a stream are
uniform on the accepted `K`-tuples, which no theorem here states.  `short_count` follows the
exponential moment bound: the sum of `3^r` over the sequences, with `r` the number of rejected words
of a sequence, is the `M`-th power of the sum over one word, at most `2^65`. -/

namespace Demos.RandomChoice

open Finset

/-- A count of words by a condition on their values equals the count of the naturals below
`2^64`. -/
theorem card_words (P : Nat → Prop) [DecidablePred P] :
    (univ.filter fun w : UInt64 => P w.toNat).card = ((range (2 ^ 64)).filter P).card := by
  apply card_bij (fun w _ => w.toNat)
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    simp only [mem_filter, mem_range]
    exact ⟨w.toNat_lt, hw⟩
  · intro a _ b _ h
    exact UInt64.toNat_inj.mp h
  · intro m hm
    simp only [mem_filter, mem_range] at hm
    refine ⟨UInt64.ofNat m, ?_, UInt64.toNat_ofNat_of_lt' hm.1⟩
    simp only [mem_filter, mem_univ, true_and]
    rw [UInt64.toNat_ofNat_of_lt' hm.1]
    exact hm.2

/-- Exactly `⌊b / n⌋` naturals below `b` and at least `b mod n` have the residue `c < n`. -/
theorem residue_count (b n c : Nat) (hn : 0 < n) (hc : c < n) :
    ((range b).filter fun m => b % n ≤ m ∧ m % n = c).card = b / n := by
  have hS := Nat.count_modEq_card b hn c
  have hT := Nat.count_modEq_card (b % n) hn c
  rw [Nat.mod_eq_of_lt hc] at hS hT
  rw [Nat.mod_mod, Nat.div_eq_of_lt (Nat.mod_lt _ hn)] at hT
  rw [Nat.count_eq_card_filter_range] at hS hT
  have hfilter : ∀ k, (range k).filter (fun m => m ≡ c [MOD n]) =
      (range k).filter (fun m => m % n = c) := by
    intro k
    ext m
    simp [Nat.ModEq, Nat.mod_eq_of_lt hc]
  rw [hfilter] at hS hT
  have hsplit : (range b).filter (fun m => b % n ≤ m ∧ m % n = c) =
      (range b).filter (fun m => m % n = c) \ (range (b % n)).filter (fun m => m % n = c) := by
    ext m
    simp only [mem_filter, mem_range, mem_sdiff, not_and]
    constructor
    · rintro ⟨hb, hle, hm⟩
      exact ⟨⟨hb, hm⟩, fun hlt => absurd hle (by omega)⟩
    · rintro ⟨⟨hb, hm⟩, hnot⟩
      exact ⟨hb, by by_contra h; exact hnot (by omega) hm, hm⟩
  have hsub : (range (b % n)).filter (fun m => m % n = c) ⊆
      (range b).filter (fun m => m % n = c) := by
    intro m
    simp only [mem_filter, mem_range]
    rintro ⟨hm, hc'⟩
    exact ⟨lt_of_lt_of_le hm (Nat.mod_le _ _), hc'⟩
  rw [hsplit, card_sdiff_of_subset hsub, hS, hT]
  by_cases hcb : c < b % n <;> simp [hcb]

/-- For every `n` and every `v` in [1, n], exactly `⌊2^64 / n⌋` words are accepted and give `v`. -/
theorem pick_count (n v : UInt64) (hv : 1 ≤ v.toNat) (hvn : v.toNat ≤ n.toNat) :
    (univ.filter fun w : UInt64 => accepts n w = true ∧ pickSpec (n, w) = v).card =
      2 ^ 64 / n.toNat := by
  have hpos : 0 < n.toNat := by omega
  have hn : n ≠ 0 := fun e => by rw [e] at hvn; simp at hvn; omega
  have hn' : (n != 0) = true := by simpa using hn
  have hsize : UInt64.size = 2 ^ 64 := rfl
  have hcond : ∀ w : UInt64, (accepts n w = true ∧ pickSpec (n, w) = v) ↔
      (2 ^ 64 % n.toNat ≤ w.toNat ∧ w.toNat % n.toNat = v.toNat - 1) := by
    intro w
    have hacc : accepts n w = true ↔ 2 ^ 64 % n.toNat ≤ w.toNat := by
      simp [accepts, hn]
    rw [hacc]
    constructor
    · rintro ⟨ha, hp⟩
      refine ⟨ha, ?_⟩
      have hmod : w.toNat % n.toNat < n.toNat := Nat.mod_lt _ hpos
      have hvalue := congrArg UInt64.toNat hp
      simp only [pickSpec, accepts, hn', ha, decide_true, Bool.and_self, ↓reduceIte] at hvalue
      rw [UInt64.toNat_ofNat_of_lt' (by have : n.toNat < 2 ^ 64 := n.toNat_lt; omega)] at hvalue
      omega
    · rintro ⟨ha, hm⟩
      refine ⟨ha, ?_⟩
      have hmod : w.toNat % n.toNat < n.toNat := Nat.mod_lt _ hpos
      simp only [pickSpec, accepts, hn', ha, decide_true, Bool.and_self, ↓reduceIte]
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat_of_lt' (by have : n.toNat < 2 ^ 64 := n.toNat_lt; omega)]
      omega
  rw [filter_congr (fun w _ => hcond w)]
  rw [card_words (fun m => 2 ^ 64 % n.toNat ≤ m ∧ m % n.toNat = v.toNat - 1)]
  exact residue_count (2 ^ 64) n.toNat (v.toNat - 1) hpos (by omega)

/-- For every `K` and every sequence `o` of `K` values in [1, n], exactly `⌊2^64 / n⌋^K` sequences
of `K` accepted words give `o`. -/
theorem picks_count (n : UInt64) (K : Nat) (o : Fin K → UInt64)
    (ho : ∀ i, 1 ≤ (o i).toNat ∧ (o i).toNat ≤ n.toNat) :
    (univ.filter fun ws : Fin K → UInt64 =>
      ∀ i, accepts n (ws i) = true ∧ pickSpec (n, ws i) = o i).card = (2 ^ 64 / n.toNat) ^ K := by
  have hpi : (univ.filter fun ws : Fin K → UInt64 =>
      ∀ i, accepts n (ws i) = true ∧ pickSpec (n, ws i) = o i) =
      Fintype.piFinset fun i => univ.filter fun w : UInt64 =>
        accepts n w = true ∧ pickSpec (n, w) = o i := by
    ext ws
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  rw [hpi, Fintype.card_piFinset]
  rw [prod_congr rfl (fun i _ => pick_count n (o i) (ho i).1 (ho i).2)]
  simp

/-- `n ≥ 1` accepts `2^64 - (2^64 mod n)` words, `n · ⌊2^64 / n⌋`. -/
theorem accepted_count (n : UInt64) (hn : n ≠ 0) :
    (univ.filter fun w : UInt64 => accepts n w = true).card = 2 ^ 64 - 2 ^ 64 % n.toNat ∧
      2 ^ 64 - 2 ^ 64 % n.toNat = n.toNat * (2 ^ 64 / n.toNat) := by
  have hacc : ∀ w : UInt64, accepts n w = true ↔ 2 ^ 64 % n.toNat ≤ w.toNat := by
    intro w
    simp [accepts, hn]
  rw [filter_congr (fun w _ => hacc w), card_words (fun m => 2 ^ 64 % n.toNat ≤ m)]
  constructor
  · have : (range (2 ^ 64)).filter (fun m => 2 ^ 64 % n.toNat ≤ m) =
        Ico (2 ^ 64 % n.toNat) (2 ^ 64) := by
      ext m
      simp only [mem_filter, mem_range, mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1⟩
    rw [this, Nat.card_Ico]
  · have := Nat.div_add_mod (2 ^ 64) n.toNat
    omega

/-- Every `n ≥ 1` accepts at least `2^63` words. -/
theorem accepted_half (n : UInt64) (hn : n ≠ 0) :
    2 ^ 63 ≤ (univ.filter fun w : UInt64 => accepts n w = true).card := by
  rw [(accepted_count n hn).1]
  have hpos : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with e | e
    · exact absurd (UInt64.toNat_inj.mp (by simpa using e)) hn
    · exact e
  have hlt := n.toNat_lt
  have hmod : 2 ^ 64 % n.toNat < n.toNat := Nat.mod_lt _ hpos
  by_cases hsmall : n.toNat ≤ 2 ^ 63
  · omega
  · have hq : 2 ^ 64 / n.toNat = 1 := by
      apply Nat.div_eq_of_lt_le <;> omega
    have := Nat.div_add_mod (2 ^ 64) n.toNat
    rw [hq] at this
    omega

/-- The sum over the sequences of `M` words of `3^r`, with `r` the number of rejected words, is the
`M`-th power of the sum over one word. -/
theorem moment_eq (n : UInt64) (M : Nat) :
    ∑ ws : Fin M → UInt64, 3 ^ (univ.filter fun i => accepts n (ws i) = false).card =
      (∑ w : UInt64, if accepts n w = true then 1 else 3) ^ M := by
  rw [← Fin.prod_const, Fintype.prod_sum]
  refine sum_congr rfl fun ws _ => ?_
  rw [prod_ite, prod_const_one, prod_const, one_mul]
  congr 2
  ext i
  simp

/-- The sum over one word is at most `2^65`, since at most `2^63` words are rejected. -/
theorem moment_word (n : UInt64) (hn : n ≠ 0) :
    (∑ w : UInt64, if accepts n w = true then 1 else 3) ≤ 2 ^ 65 := by
  rw [sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul, mul_one]
  have hall := card_filter_add_card_filter_not (s := (univ : Finset UInt64))
    (fun w => accepts n w = true)
  have huniv : (univ : Finset UInt64).card = 2 ^ 64 := by
    rw [card_univ, ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt64]
  have hhalf := accepted_half n hn
  rw [huniv] at hall
  omega

/-- `2^(4 K + 3 a + e) ≤ 3^(3 K + 2 a + 1 + e)`, since `2^4 ≤ 3^3` and `2^3 ≤ 3^2`. -/
theorem pow_margin_gen (K a e : Nat) : 2 ^ (4 * K + 3 * a + e) ≤ 3 ^ (3 * K + 2 * a + 1 + e) := by
  have h1 : 2 ^ (4 * K + 3 * a + e) = (2 ^ 4) ^ K * (2 ^ 3) ^ a * 2 ^ e := by
    rw [pow_add, pow_add, pow_mul, pow_mul]
  have h2 : 3 ^ (3 * K + 2 * a + 1 + e) = (3 ^ 3) ^ K * ((3 ^ 2) ^ a * 3) * 3 ^ e := by
    rw [pow_add, pow_add, pow_add, pow_mul, pow_mul, pow_one, Nat.mul_assoc ((3 ^ 3) ^ K)]
  rw [h1, h2]
  refine Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) K) ?_)
    (Nat.pow_le_pow_left (by norm_num) e)
  exact le_trans (Nat.pow_le_pow_left (by norm_num) a) (Nat.le_mul_of_pos_right _ (by norm_num))

/-- `2^(M + 512) ≤ 3^(M - K + 1)` for `M ≥ 4 K + 1024`. -/
theorem pow_margin (K M : Nat) (hM : 4 * K + 1024 ≤ M) : 2 ^ (M + 512) ≤ 3 ^ (M - K + 1) := by
  have h := pow_margin_gen K 512 (M - (4 * K + 1024))
  have e1 : M + 512 = 4 * K + 3 * 512 + (M - (4 * K + 1024)) := by omega
  have e2 : M - K + 1 = 3 * K + 2 * 512 + 1 + (M - (4 * K + 1024)) := by omega
  rw [e1, e2]
  exact h

/-- For `M ≥ 4 K + 1024`, at most `2^(64 M - 512)` of the `2^(64 M)` sequences of `M` words hold
fewer than `K` words that `n ≥ 1` accepts. -/
theorem short_count (n : UInt64) (hn : n ≠ 0) (K M : Nat) (hM : 4 * K + 1024 ≤ M) :
    2 ^ 512 * (univ.filter fun ws : Fin M → UInt64 =>
      (univ.filter fun i => accepts n (ws i) = true).card < K).card ≤ 2 ^ (64 * M) := by
  set short := univ.filter fun ws : Fin M → UInt64 =>
    (univ.filter fun i => accepts n (ws i) = true).card < K
  have hrej : ∀ ws : Fin M → UInt64, ws ∈ short →
      3 ^ (M - K + 1) ≤ 3 ^ (univ.filter fun i => accepts n (ws i) = false).card := by
    intro ws hws
    simp only [short, mem_filter, mem_univ, true_and] at hws
    have hall := card_filter_add_card_filter_not (s := (univ : Finset (Fin M)))
      (fun i => accepts n (ws i) = true)
    rw [card_univ, Fintype.card_fin] at hall
    have hfalse : (univ.filter fun i => ¬accepts n (ws i) = true) =
        univ.filter fun i => accepts n (ws i) = false := by
      ext i
      simp
    rw [hfalse] at hall
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsum : short.card * 3 ^ (M - K + 1) ≤ 2 ^ (65 * M) := by
    calc short.card * 3 ^ (M - K + 1) = ∑ _ws ∈ short, 3 ^ (M - K + 1) := by
          rw [sum_const, smul_eq_mul]
      _ ≤ ∑ ws ∈ short, 3 ^ (univ.filter fun i => accepts n (ws i) = false).card :=
          sum_le_sum hrej
      _ ≤ ∑ ws : Fin M → UInt64, 3 ^ (univ.filter fun i => accepts n (ws i) = false).card :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
      _ = (∑ w : UInt64, if accepts n w = true then 1 else 3) ^ M := moment_eq n M
      _ ≤ (2 ^ 65) ^ M := Nat.pow_le_pow_left (moment_word n hn) M
      _ = 2 ^ (65 * M) := by rw [← pow_mul]
  have hmargin := pow_margin K M hM
  have key : short.card * 2 ^ (M + 512) ≤ 2 ^ (65 * M) :=
    le_trans (Nat.mul_le_mul_left _ hmargin) hsum
  have scaled : 2 ^ 512 * short.card * 2 ^ M ≤ 2 ^ (64 * M) * 2 ^ M := by
    calc 2 ^ 512 * short.card * 2 ^ M = short.card * 2 ^ (M + 512) := by
          rw [pow_add, Nat.mul_comm (2 ^ 512) short.card, Nat.mul_assoc,
            Nat.mul_comm (2 ^ 512) (2 ^ M)]
      _ ≤ 2 ^ (65 * M) := key
      _ = 2 ^ (64 * M) * 2 ^ M := by
          rw [← pow_add]
          congr 1
          omega
  exact Nat.le_of_mul_le_mul_right scaled (by positivity)

end Demos.RandomChoice
