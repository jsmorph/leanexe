import Library.Random.Xorshift.Program
import Library.Random.Orbit.Basic
import Library.Random.Xorshift.Columns
import Mathlib.Data.Fintype.Card
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Tactic.NormNum.Prime

/-! The period of Marsaglia's xorshift64 generator of `Library/Random/Xorshift/Program.lean`.  Each of
the three operations of a step distributes over xor and is injective, so the step is a bijection
on words that maps 0 to 0, and a nonzero state never becomes 0.  The kernel checks, with the
jump-ahead tables of `Library/Random/Xorshift/Columns.lean`, that the state 1 returns after `2^64 - 1`
steps and after no `(2^64 - 1) / q` steps for the seven prime factors `q` of `2^64 - 1`.  Its orbit
therefore holds all `2^64 - 1` nonzero words, and every nonzero state has the period `2^64 - 1`. -/

namespace Library.Random.Xorshift

open Function

theorem advance_eq_iterate (n x : UInt64) : advance n x = step^[n.toNat] x :=
  Orbit.loop_eq_iterate step n x

/-- `v ^^^ (v <<< a)`. -/
def shl (a : ℕ) (v : BitVec 64) : BitVec 64 := v ^^^ (v <<< a)

/-- `v ^^^ (v >>> a)`. -/
def shr (a : ℕ) (v : BitVec 64) : BitVec 64 := v ^^^ (v >>> a)

theorem toBitVec_step (x : UInt64) : (step x).toBitVec = shl 17 (shr 7 (shl 13 x.toBitVec)) :=
  rfl

theorem shl_xor (a : ℕ) (v w : BitVec 64) : shl a (v ^^^ w) = shl a v ^^^ shl a w := by
  simp only [shl, BitVec.shiftLeft_xor_distrib]
  ac_rfl

theorem shr_xor (a : ℕ) (v w : BitVec 64) : shr a (v ^^^ w) = shr a v ^^^ shr a w := by
  simp only [shr, BitVec.ushiftRight_xor_distrib]
  ac_rfl

theorem eq_zero_of_shl_eq_zero {a : ℕ} (ha : 0 < a) {v : BitVec 64} (h : shl a v = 0) : v = 0 := by
  have hv : v = v <<< a := BitVec.xor_eq_zero_iff.mp h
  have key : ∀ m i, i ≤ m → v.getLsbD i = false := by
    intro m
    induction m with
    | zero =>
      intro i hi
      rw [hv, BitVec.getLsbD_shiftLeft]
      simp [show i < a by omega]
    | succ m ih =>
      intro i hi
      rw [hv, BitVec.getLsbD_shiftLeft]
      by_cases hia : i < a
      · simp [hia]
      · simp [ih (i - a) (by omega)]
  exact BitVec.eq_of_getLsbD_eq fun i _ => by simp [key i i le_rfl]

theorem eq_zero_of_shr_eq_zero {a : ℕ} (ha : 0 < a) {v : BitVec 64} (h : shr a v = 0) : v = 0 := by
  have hv : v = v >>> a := BitVec.xor_eq_zero_iff.mp h
  have key : ∀ m i, 64 - i ≤ m → v.getLsbD i = false := by
    intro m
    induction m with
    | zero =>
      intro i hi
      exact BitVec.getLsbD_of_ge v i (by omega)
    | succ m ih =>
      intro i hi
      rw [hv, BitVec.getLsbD_ushiftRight]
      exact ih (a + i) (by omega)
  exact BitVec.eq_of_getLsbD_eq fun i _ => by simp [key 64 i (by omega)]

theorem shl_injective {a : ℕ} (ha : 0 < a) : Injective (shl a) := fun v w h =>
  BitVec.xor_eq_zero_iff.mp (eq_zero_of_shl_eq_zero ha (by rw [shl_xor, h, BitVec.xor_self]; rfl))

theorem shr_injective {a : ℕ} (ha : 0 < a) : Injective (shr a) := fun v w h =>
  BitVec.xor_eq_zero_iff.mp (eq_zero_of_shr_eq_zero ha (by rw [shr_xor, h, BitVec.xor_self]; rfl))

/-- The step distributes over xor. -/
theorem step_xor (x y : UInt64) : step (x ^^^ y) = step x ^^^ step y := by
  apply UInt64.toBitVec_inj.mp
  simp only [toBitVec_step, UInt64.toBitVec_xor, shl_xor, shr_xor]

theorem step_zero : step 0 = 0 := rfl

theorem step_injective : Injective step := fun x y h => by
  have h' := congrArg UInt64.toBitVec h
  rw [toBitVec_step, toBitVec_step] at h'
  exact UInt64.toBitVec_inj.mp
    (shl_injective (a := 13) (by omega)
      (shr_injective (a := 7) (by omega) (shl_injective (a := 17) (by omega) h')))

/-- The step is a bijection on words. -/
theorem step_bijective : Bijective step := Finite.injective_iff_bijective.mp step_injective

/-- A nonzero state never becomes 0. -/
theorem iterate_ne_zero {x : UInt64} (hx : x ≠ 0) (n : ℕ) : step^[n] x ≠ 0 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [iterate_succ_apply']
    exact fun h => ih (step_injective (h.trans step_zero.symm))

theorem advance_ne_zero {x : UInt64} (hx : x ≠ 0) (n : UInt64) : advance n x ≠ 0 := by
  rw [advance_eq_iterate]
  exact iterate_ne_zero hx _

/-! ### The period -/

/-- The step on the word that the low 64 bits of a number form. -/
def stepNat (y : Nat) : Nat := (step y.toUInt64).toNat

theorem stepNat_linear : Linear stepNat := fun a b => by
  rw [stepNat, Nat.toUInt64_eq, UInt64.ofNat_xor, step_xor, UInt64.toNat_xor]; rfl

theorem stepNat_wordValued : WordValued stepNat := fun _ => UInt64.toNat_lt _

theorem stepNat_iterate (m : Nat) (x : UInt64) : stepNat^[m] x.toNat = (step^[m] x).toNat := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply', stepNat, Nat.toUInt64_eq, UInt64.ofNat_toNat]

/-- The primes that divide `2^64 - 1`. -/
def primes : List Nat := [3, 5, 17, 257, 641, 65537, 6700417]

theorem mem_primes_of_dvd {q : Nat} (hq : q.Prime) (h : q ∣ 2 ^ 64 - 1) : q ∈ primes := by
  rw [show 2 ^ 64 - 1 = 3 * 5 * 17 * 257 * 641 * 65537 * 6700417 by norm_num] at h
  simp only [hq.dvd_mul, or_assoc] at h
  have e : ∀ r, r.Prime → q ∣ r → q = r := fun r hr h => (Nat.prime_dvd_prime_iff_eq hq hr).mp h
  simp only [primes, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl (e 3 (by norm_num) h)
  · exact Or.inr (Or.inl (e 5 (by norm_num) h))
  · exact Or.inr (Or.inr (Or.inl (e 17 (by norm_num) h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (e 257 (by norm_num) h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e 641 (by norm_num) h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e 65537 (by norm_num) h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (e 6700417 (by norm_num) h))))))

/-- The columns of the step and of its 63 repeated squares. -/
def tables : List (List Nat) := pows 64 (cols stepNat 64)

/-- Whether the state 1 returns after `2^64 - 1` steps and after no `(2^64 - 1) / q` steps. -/
def orbitCheck : Bool :=
  jumpList tables (2 ^ 64 - 1) 1 == 1 &&
    primes.all fun q => jumpList tables ((2 ^ 64 - 1) / q) 1 != 1

/-- `orbitCheck` holds.  The kernel evaluates the tables and the eight jumps in about 20 seconds. -/
theorem orbitCheck_eq : orbitCheck = true := by decide +kernel

theorem jumpList_tables {m : Nat} (hm : m < 2 ^ 64) (x : UInt64) :
    jumpList tables m x.toNat = (step^[m] x).toNat := by
  have := jumpList_pows stepNat_linear stepNat_wordValued 64 0 m x.toNat hm x.toNat_lt
  rw [pow_zero, iterate_one, Nat.one_mul] at this
  rw [tables, this, stepNat_iterate]

/-- The state 1 returns after `2^64 - 1` steps and not before. -/
theorem minimalPeriod_one : minimalPeriod step 1 = 2 ^ 64 - 1 := by
  have hcheck := orbitCheck_eq
  simp only [orbitCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq]
    at hcheck
  refine Orbit.minimalPeriod_eq_of_primes ?_ fun q hq hd h =>
    hcheck.2 q (mem_primes_of_dvd hq hd) ?_
  · rw [← UInt64.toNat_inj, ← jumpList_tables (by norm_num)]
    exact hcheck.1
  · have := jumpList_tables (lt_of_le_of_lt (Nat.div_le_self (2 ^ 64 - 1) q) (by norm_num)) 1
    rw [h] at this
    exact this

/-- The nonzero words. -/
def Nonzero : Set UInt64 := {y | y ≠ 0}

theorem natCard_nonzero : Nat.card Nonzero = 2 ^ 64 - 1 := by
  rw [Nonzero, Nat.card_eq_fintype_card, Set.card_ne_eq, ← Nat.card_eq_fintype_card,
    Orbit.natCard_uint64]

/-- From every nonzero state, `step` returns after `2^64 - 1` steps and not before. -/
theorem step_minimalPeriod {x : UInt64} (hx : x ≠ 0) : minimalPeriod step x = 2 ^ 64 - 1 := by
  obtain ⟨n, ⟨_, hn⟩, _⟩ := Orbit.existsUnique_iterate (S := Nonzero)
    (by rw [natCard_nonzero, minimalPeriod_one])
    (fun n => iterate_ne_zero (by decide : (1 : UInt64) ≠ 0) n)
    (show x ∈ Nonzero from hx)
  rw [← hn, minimalPeriod_apply_iterate (minimalPeriod_pos_iff_mem_periodicPts.mp
    (by rw [minimalPeriod_one]; norm_num)), minimalPeriod_one]

/-- From every nonzero state `x`, `step` reaches each nonzero state `y` at exactly one count of
steps below `2^64 - 1`. -/
theorem existsUnique_iterate {x y : UInt64} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃! n, n < 2 ^ 64 - 1 ∧ step^[n] x = y := by
  rw [← step_minimalPeriod hx]
  exact Orbit.existsUnique_iterate (S := Nonzero) (by rw [natCard_nonzero, step_minimalPeriod hx])
    (iterate_ne_zero hx) (show y ∈ Nonzero from hy)

/-- From every nonzero state `x`, `advance` reaches each nonzero state `y` at exactly one count `n`
below `2^64 - 1`. -/
theorem advance_existsUnique {x y : UInt64} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃! n : UInt64, n < 18446744073709551615 ∧ advance n x = y := by
  obtain ⟨n, ⟨hn, hny⟩, huniq⟩ := existsUnique_iterate hx hy
  have hsize : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  refine ⟨UInt64.ofNat n, ⟨?_, ?_⟩, fun m ⟨hm, hmy⟩ => ?_⟩
  · rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', hsize]
    exact hn
  · rw [advance_eq_iterate, UInt64.toNat_ofNat', hsize, hny]
  · rw [advance_eq_iterate] at hmy
    rw [UInt64.lt_iff_toNat_lt] at hm
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat', hsize]
    exact huniq _ ⟨hm, hmy⟩

/-- Over a period from a nonzero state, the top `j` bits of the state take each nonzero value
`2^(64 - j)` times and the value 0 `2^(64 - j) - 1` times, since the word 0 never occurs. -/
theorem advance_topBits {x : UInt64} (hx : x ≠ 0) {j v : Nat} (hj : j ≤ 64) (hv : v < 2 ^ j) :
    ((Finset.univ : Finset UInt64).filter fun n => n < 18446744073709551615 ∧
      (advance n x).toNat / 2 ^ (64 - j) = v).card =
      if v = 0 then 2 ^ (64 - j) - 1 else 2 ^ (64 - j) := by
  have hnz : ((Finset.univ : Finset UInt64).filter fun y => y ≠ 0 ∧ y.toNat / 2 ^ (64 - j) = v) =
      ((Finset.univ : Finset UInt64).filter fun y => y.toNat / 2 ^ (64 - j) = v).erase 0 := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  have hcount : ((Finset.univ : Finset UInt64).filter
      fun y => y ≠ 0 ∧ y.toNat / 2 ^ (64 - j) = v).card =
      if v = 0 then 2 ^ (64 - j) - 1 else 2 ^ (64 - j) := by
    rw [hnz]
    by_cases hv0 : v = 0
    · subst hv0
      rw [Finset.card_erase_of_mem (by simp), Orbit.card_topBits hj hv]
      simp
    · rw [Finset.erase_eq_of_notMem (by simp [Ne.symm hv0]), Orbit.card_topBits hj hv]
      simp [hv0]
  refine Eq.trans ?_ hcount
  apply Finset.card_bij (fun n _ => advance n x)
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨Finset.mem_univ _, advance_ne_zero hx n, hn.2.2⟩
  · intro a ha b hb h
    rw [Finset.mem_filter] at ha hb
    obtain ⟨k, _, hk⟩ := advance_existsUnique hx (advance_ne_zero hx b)
    exact (hk a ⟨ha.2.1, h⟩).trans (hk b ⟨hb.2.1, rfl⟩).symm
  · intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨n, ⟨hn, hny⟩, _⟩ := advance_existsUnique hx hy.2.1
    exact ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn, by rw [hny]; exact hy.2.2⟩, hny⟩

end Library.Random.Xorshift
