import Library.Numerics.Filters.Cic.Spec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! This module defines the block form of the CIC decimation filter of `Spec.lean` and proves that
it computes `outputs`.  Each stage of the block form maps a whole list to a list.  `integrate xs` is
the list of running sums of `xs`, whose element `t` is `0 + x₀ + ⋯ + xₜ`, added from the left, so an
integrator's value at index `t` includes the input at `t`, as in Hogenauer's equation (1).
`decimate R v` keeps the elements of a list `v` of length `n` at the indices `m·R + R − 1` for
`m < ⌊n / R⌋`, the last index of each complete block of `R`.  `comb M v` has the element
`v(m) − v(m − M)` at each index `m` of `v`, with `v` read as 0 before index 0, which `List.zipWith`
computes from `v` and from `v` delayed by `M` zeros.  `cascade N R M xs` applies `N` integrators,
the decimation, and `N` combs.

The definitions require of the element type only a zero, an addition, and a subtraction, so one
definition serves ℤ and `UInt64`.  At `UInt64` the operations are the wrapping operations of Lean's
core library, which a program in the verified compiler's dialect uses, so a proof that such a
program computes `cascade` involves no cast and no integer.  The lemmas `length_cascade`,
`getElem_integrate`, `getElem_integrate_succ`, `getElem_decimate`, and `getElem_comb` give the
length of each stage's result and its element at each index, the form of the dialect's `build_get`
and of the invariant of a loop that writes one array element per step.  `cascade_map` states that a
map that preserves zero, addition, and subtraction commutes with the cascade, and `Exact.lean`
applies it to the reduction from ℤ to `UInt64`.  The cascade over ℤ also evaluates the filter where
`outputs` is too slow: it makes `N·n` additions and `N·⌊n / R⌋` subtractions, plus the list reads
of the decimation, while `outputs` reads the input `(R·M)^N` times for each output.

`cascade_eq_outputs` states that the cascade over ℤ equals `outputs N R M xs` for every `N`, `R`,
`M`, and list, including the degenerate values of the parameters.  The proof reads a list as a
signal on ℤ, as the specification does: element `t` at each time `t` below the list's length, and
0 at every other time.  On signals, the comb of delay `L` maps `y` to `t ↦ y t − y (t − L)`, and
the backward difference is the comb of delay 1.  The difference of a moving sum of length `L` is
the comb of delay `L` of its input (`movingSum_step`), and the difference of the signal of a list's
running sums agrees with the list's signal at every time below the list's length.  Combs commute,
so `N` differences of `N` combs of the integrators' output agree there with `N` combs of the input,
which are the `N` differences of the `N`-fold moving sum.  A signal that is 0 at negative times is
determined, at the times below any bound, by its difference at those times, so the `N` combs of the
integrators' output agree with the `N`-fold moving sum below the input's length.  Sampling at
`m·R + R − 1` turns a comb of delay `R·M` into a comb of delay `M` at the output rate.  Each
stage's value at a time depends only on its input at that time and earlier, so agreement below a
time passes through the decimation and the combs to every output. -/

namespace Library.Numerics.Filters.Cic

section Stages

variable {α : Type*}

/-- The running sums of a list after the value `s`: element `t` is `s + x₀ + ⋯ + xₜ`, added from
the left. -/
def integrateFrom [Add α] (s : α) : List α → List α
  | [] => []
  | x :: xs => (s + x) :: integrateFrom (s + x) xs

/-- An integrator over a block: the running sums of `xs` from 0. -/
def integrate [Zero α] [Add α] (xs : List α) : List α :=
  integrateFrom 0 xs

/-- Decimation by `R`: the elements at the indices `m·R + R − 1` for `m < ⌊n / R⌋`. -/
def decimate [Zero α] (R : ℕ) (v : List α) : List α :=
  (List.range (v.length / R)).map fun m => v.getD (m * R + R - 1) 0

/-- A comb of differential delay `M` over a block: `v(m) − v(m − M)` at each index `m`, with `v`
read as 0 before index 0. -/
def comb [Zero α] [Sub α] (M : ℕ) (v : List α) : List α :=
  List.zipWith (· - ·) v (List.replicate M 0 ++ v)

/-- The block cascade: `N` integrators, decimation by `R`, and `N` combs of differential delay
`M`. -/
def cascade [Zero α] [Add α] [Sub α] (N R M : ℕ) (xs : List α) : List α :=
  (comb M)^[N] (decimate R (integrate^[N] xs))

@[simp] theorem length_integrateFrom [Add α] (s : α) (xs : List α) :
    (integrateFrom s xs).length = xs.length := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp [integrateFrom, ih]

@[simp] theorem length_integrate [Zero α] [Add α] (xs : List α) :
    (integrate xs).length = xs.length :=
  length_integrateFrom 0 xs

@[simp] theorem length_decimate [Zero α] (R : ℕ) (v : List α) :
    (decimate R v).length = v.length / R := by
  simp [decimate]

@[simp] theorem length_comb [Zero α] [Sub α] (M : ℕ) (v : List α) :
    (comb M v).length = v.length := by
  simp only [comb, List.length_zipWith, List.length_append, List.length_replicate]
  omega

@[simp] theorem length_iterate_integrate [Zero α] [Add α] (N : ℕ) (xs : List α) :
    (integrate^[N] xs).length = xs.length := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', length_integrate, ih]

@[simp] theorem length_iterate_comb [Zero α] [Sub α] (M N : ℕ) (v : List α) :
    ((comb M)^[N] v).length = v.length := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', length_comb, ih]

@[simp] theorem length_cascade [Zero α] [Add α] [Sub α] (N R M : ℕ) (xs : List α) :
    (cascade N R M xs).length = xs.length / R := by
  simp [cascade]

theorem getElem_integrateFrom [Add α] (s : α) (xs : List α) (t : ℕ) (h : t < xs.length) :
    (integrateFrom s xs)[t]'(by simpa using h) = (xs.take (t + 1)).foldl (· + ·) s := by
  induction xs generalizing s t with
  | nil => simp at h
  | cons x xs ih =>
    cases t with
    | zero => simp [integrateFrom]
    | succ t =>
      simp only [integrateFrom, List.getElem_cons_succ, List.take_succ_cons, List.foldl_cons]
      exact ih (s + x) t (by simpa using h)

theorem getElem_integrate [Zero α] [Add α] (xs : List α) (t : ℕ) (h : t < xs.length) :
    (integrate xs)[t]'(by simpa using h) = (xs.take (t + 1)).foldl (· + ·) 0 :=
  getElem_integrateFrom 0 xs t h

theorem getElem_integrate_zero [Zero α] [Add α] (xs : List α) (h : 0 < xs.length) :
    (integrate xs)[0]'(by simpa using h) = (0 : α) + xs[0] := by
  rw [getElem_integrate xs 0 h]
  cases xs with
  | nil => simp at h
  | cons x xs => simp

theorem getElem_integrate_succ [Zero α] [Add α] (xs : List α) (t : ℕ) (h : t + 1 < xs.length) :
    (integrate xs)[t + 1]'(by simpa using h) =
      (integrate xs)[t]'(by rw [length_integrate]; omega) + xs[t + 1] := by
  rw [getElem_integrate xs (t + 1) h, getElem_integrate xs t (by omega),
    List.take_add_one (l := xs) (i := t + 1), List.foldl_append, List.getElem?_eq_getElem h]
  rfl

theorem getElem_decimate [Zero α] (R : ℕ) (v : List α) (m : ℕ) (h : m < v.length / R) :
    (decimate R v)[m]'(by simpa using h) = v.getD (m * R + R - 1) 0 := by
  simp [decimate]

theorem getElem_comb [Zero α] [Sub α] (M : ℕ) (v : List α) (m : ℕ) (h : m < v.length) :
    (comb M v)[m]'(by simpa using h) = v[m] - if m < M then 0 else v.getD (m - M) 0 := by
  have e : (List.replicate M (0 : α) ++ v)[m]'(by simp; omega) =
      if m < M then 0 else v.getD (m - M) 0 := by
    by_cases hm : m < M
    · rw [List.getElem_append_left (as := List.replicate M (0 : α)) (bs := v) (i := m)
        (by simpa using hm), List.getElem_replicate, ite_eq_left hm]
    · rw [List.getElem_append_right (as := List.replicate M (0 : α)) (bs := v) (i := m)
        (by simpa using hm), ite_eq_right hm, List.getElem_eq_getD 0]
      simp
  simp only [comb, List.getElem_zipWith]
  rw [e]

end Stages

section Map

variable {α β : Type*} [Zero α] [Add α] [Sub α] [Zero β] [Add β] [Sub β]

/-- A map that preserves zero, addition, and subtraction commutes with the cascade. -/
theorem cascade_map (f : α → β) (h0 : f 0 = 0) (hadd : ∀ a b, f (a + b) = f a + f b)
    (hsub : ∀ a b, f (a - b) = f a - f b) (N R M : ℕ) (xs : List α) :
    cascade N R M (xs.map f) = (cascade N R M xs).map f := by
  have hF : ∀ s v, (integrateFrom s v).map f = integrateFrom (f s) (v.map f) := by
    intro s v
    induction v generalizing s with
    | nil => rfl
    | cons x v ih => simp [integrateFrom, ih, hadd]
  have hI : Function.Semiconj (List.map f) integrate integrate := fun v => by
    simp only [integrate, hF, h0]
  have hD : ∀ v : List α, decimate R (v.map f) = (decimate R v).map f := by
    intro v
    simp only [decimate, List.length_map, List.map_map]
    refine List.map_congr_left fun m _ => ?_
    simp only [Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases v[m * R + R - 1]? <;> simp [h0]
  have hC : Function.Semiconj (List.map f) (comb M) (comb M) := fun v => by
    have e : List.replicate M (0 : β) ++ v.map f = (List.replicate M 0 ++ v).map f := by
      simp [List.map_replicate, h0]
    simp only [comb]
    rw [e, List.map_zipWith, List.zipWith_map]
    simp only [hsub]
  simp only [cascade]
  rw [← hI.iterate_right N xs, hD]
  exact (hC.iterate_right N _).symm

end Map

/-- The moving sum at `t` is the moving sum at `t − 1`, plus the sample that enters the window,
minus the sample that leaves it. -/
theorem movingSum_step (L : ℕ) (y : ℤ → ℤ) (t : ℤ) :
    movingSum L y t = movingSum L y (t - 1) + y t - y (t - L) := by
  have h1 : movingSum (L + 1) y t = movingSum L y t + y (t - L) :=
    Finset.sum_range_succ (fun i : ℕ => y (t - i)) L
  have h2 : movingSum (L + 1) y t = movingSum L y (t - 1) + y t := by
    unfold movingSum
    rw [Finset.sum_range_succ']
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by congr 1; push_cast; ring
    · simp
  linarith

section Signals

/-- The signal of a list. -/
private def signal (v : List ℤ) : ℤ → ℤ :=
  extend fun t => v.getD t 0

/-- The comb of delay `L` on signals. -/
private def diff (L : ℕ) (y : ℤ → ℤ) (t : ℤ) : ℤ :=
  y t - y (t - L)

/-- The values of a signal at the times `m·R + R − 1`. -/
private def sample (R : ℕ) (z : ℤ → ℤ) (m : ℤ) : ℤ :=
  z (m * R + R - 1)

private def Causal (y : ℤ → ℤ) : Prop :=
  ∀ t < 0, y t = 0

private def Agree (n : ℤ) (y z : ℤ → ℤ) : Prop :=
  ∀ t < n, y t = z t

private theorem getD_of_lt (v : List ℤ) (i : ℕ) (h : i < v.length) : v.getD i 0 = v[i] :=
  (List.getElem_eq_getD 0).symm

private theorem signal_neg (v : List ℤ) {t : ℤ} (ht : t < 0) : signal v t = 0 := by
  simp [signal, extend, not_le.mpr ht]

private theorem signal_of_nonneg (v : List ℤ) {t : ℤ} (ht : 0 ≤ t) :
    signal v t = v.getD t.toNat 0 := by
  simp only [signal, extend, ite_eq_left ht]

private theorem signal_nat (v : List ℤ) (k : ℕ) : signal v k = v.getD k 0 := by
  rw [signal_of_nonneg v (Int.natCast_nonneg k), Int.toNat_natCast]

private theorem causal_signal (v : List ℤ) : Causal (signal v) :=
  fun _ ht => signal_neg v ht

private theorem causal_diff {L : ℕ} {y : ℤ → ℤ} (hy : Causal y) : Causal (diff L y) := by
  intro t ht
  simp only [diff, hy t ht, hy (t - L) (by omega), sub_zero]

private theorem causal_movingSum {L : ℕ} {y : ℤ → ℤ} (hy : Causal y) :
    Causal (movingSum L y) :=
  fun t ht => Finset.sum_eq_zero fun i _ => hy _ (by omega)

private theorem causal_iterate {f : (ℤ → ℤ) → ℤ → ℤ} (hf : ∀ y, Causal y → Causal (f y))
    (N : ℕ) {y : ℤ → ℤ} (hy : Causal y) : Causal (f^[N] y) := by
  induction N with
  | zero => exact hy
  | succ N ih => rw [Function.iterate_succ_apply']; exact hf _ ih

private theorem agree_diff {L : ℕ} {n : ℤ} {y z : ℤ → ℤ} (h : Agree n y z) :
    Agree n (diff L y) (diff L z) := by
  intro t ht
  simp only [diff, h t ht, h (t - L) (by omega)]

private theorem agree_iterate_diff (L N : ℕ) {n : ℤ} {y z : ℤ → ℤ} (h : Agree n y z) :
    Agree n ((diff L)^[N] y) ((diff L)^[N] z) := by
  induction N with
  | zero => exact h
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact agree_diff ih

private theorem diff_comm (a b : ℕ) : Function.Commute (diff a) (diff b) := by
  intro y
  funext t
  simp only [diff]
  rw [show t - (b : ℤ) - a = t - a - b by ring]
  ring

private theorem diff_one_movingSum (L : ℕ) (y : ℤ → ℤ) : diff 1 (movingSum L y) = diff L y := by
  funext t
  simp only [diff, Nat.cast_one]
  linarith [movingSum_step L y t]

private theorem diff_one_iterate_movingSum (L N : ℕ) (y : ℤ → ℤ) :
    (diff 1)^[N] ((movingSum L)^[N] y) = (diff L)^[N] y := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply' (movingSum L) N y, Function.iterate_succ_apply (diff 1) N,
      diff_one_movingSum, ((diff_comm 1 L).iterate_left N) ((movingSum L)^[N] y), ih,
      Function.iterate_succ_apply' (diff L) N y]

/-- A signal that is 0 at negative times is determined, below `n`, by its difference below `n`. -/
private theorem agree_of_diff_one {n : ℤ} {y z : ℤ → ℤ} (hy : Causal y) (hz : Causal z)
    (h : Agree n (diff 1 y) (diff 1 z)) : Agree n y z := by
  have key : ∀ k : ℕ, (k : ℤ) < n → y k = z k := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 := h 0 (by exact_mod_cast hk)
      simp only [diff, Nat.cast_one, zero_sub, hy (-1) (by norm_num), hz (-1) (by norm_num),
        sub_zero] at h0
      simpa using h0
    | succ k ih =>
      intro hk
      have h1 := h ((k : ℤ) + 1) (by push_cast at hk; exact hk)
      have h2 := ih (by push_cast at hk; omega)
      simp only [diff, Nat.cast_one, add_sub_cancel_right] at h1
      push_cast
      linarith
  intro t ht
  rcases lt_or_ge t 0 with h0 | h0
  · rw [hy t h0, hz t h0]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    exact key k ht

private theorem agree_of_iterate_diff_one (N : ℕ) {n : ℤ} {y z : ℤ → ℤ} (hy : Causal y)
    (hz : Causal z) (h : Agree n ((diff 1)^[N] y) ((diff 1)^[N] z)) : Agree n y z := by
  induction N generalizing y z with
  | zero => exact h
  | succ N ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
    exact agree_of_diff_one hy hz (ih (causal_diff hy) (causal_diff hz) h)

private theorem getD_integrate_zero (v : List ℤ) : (integrate v).getD 0 0 = v.getD 0 0 := by
  cases v with
  | nil => rfl
  | cons x v => simp [integrate, integrateFrom]

private theorem getD_integrate_succ (v : List ℤ) (k : ℕ) (hk : k + 1 < v.length) :
    (integrate v).getD (k + 1) 0 = (integrate v).getD k 0 + v.getD (k + 1) 0 := by
  rw [getD_of_lt (integrate v) (k + 1) (by simpa using hk),
    getD_of_lt (integrate v) k (by rw [length_integrate]; omega), getD_of_lt v (k + 1) hk,
    getElem_integrate_succ v k hk]

/-- The difference of the signal of a list's running sums is the list's signal below its
length. -/
private theorem agree_diff_one_integrate (v : List ℤ) :
    Agree v.length (diff 1 (signal (integrate v))) (signal v) := by
  intro t ht
  simp only [diff, Nat.cast_one]
  rcases lt_or_ge t 0 with h0 | h0
  · rw [signal_neg (integrate v) h0, signal_neg (integrate v) (by omega : t - 1 < 0),
      signal_neg v h0, sub_zero]
  · rw [signal_of_nonneg (integrate v) h0, signal_of_nonneg v h0]
    rcases (show t = 0 ∨ 1 ≤ t by omega) with rfl | h1
    · rw [signal_neg (integrate v) (by norm_num : (0 : ℤ) - 1 < 0), sub_zero]
      exact getD_integrate_zero v
    · rw [signal_of_nonneg (integrate v) (by omega : 0 ≤ t - 1),
        show t.toNat = (t - 1).toNat + 1 by omega,
        getD_integrate_succ v (t - 1).toNat (by omega)]
      ring

private theorem agree_integrate_iterate (N : ℕ) (xs : List ℤ) :
    Agree xs.length ((diff 1)^[N] (signal (integrate^[N] xs))) (signal xs) := by
  induction N with
  | zero => intro t _; rfl
  | succ N ih =>
    intro t ht
    rw [Function.iterate_succ_apply (diff 1), Function.iterate_succ_apply' (integrate (α := ℤ))]
    have h1 := agree_diff_one_integrate (integrate^[N] xs)
    rw [length_iterate_integrate] at h1
    exact (agree_iterate_diff 1 N h1 t ht).trans (ih t ht)

/-- `N` combs of delay `L` of the integrators' output agree with the `N`-fold moving sum of
length `L` below the input's length. -/
private theorem agree_combs_movingSum (L N : ℕ) (xs : List ℤ) :
    Agree xs.length ((diff L)^[N] (signal (integrate^[N] xs)))
      ((movingSum L)^[N] (signal xs)) := by
  apply agree_of_iterate_diff_one N
  · exact causal_iterate (fun _ h => causal_diff h) N (causal_signal _)
  · exact causal_iterate (fun _ h => causal_movingSum h) N (causal_signal _)
  · intro t ht
    rw [((diff_comm 1 L).iterate_iterate N N) (signal (integrate^[N] xs)),
      diff_one_iterate_movingSum]
    exact agree_iterate_diff L N (agree_integrate_iterate N xs) t ht

private theorem sample_diff (R M : ℕ) :
    Function.Semiconj (sample R) (diff (R * M)) (diff M) := by
  intro z
  funext m
  simp only [sample, diff]
  rw [show m * R + R - 1 - ((R * M : ℕ) : ℤ) = (m - M) * R + R - 1 by push_cast; ring]

private theorem agree_sample (R : ℕ) {n : ℕ} {y z : ℤ → ℤ} (h : Agree n y z) :
    Agree ((n / R : ℕ) : ℤ) (sample R y) (sample R z) := by
  intro m hm
  simp only [sample]
  apply h
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp only [Nat.div_zero, Nat.cast_zero, mul_zero, zero_add] at hm ⊢
    omega
  · have h1 : (m + 1) * (R : ℤ) ≤ ((n / R : ℕ) : ℤ) * R :=
      mul_le_mul_of_nonneg_right (Int.add_one_le_iff.mpr hm) (by positivity)
    have h2 : ((n / R : ℕ) : ℤ) * R ≤ n := by exact_mod_cast Nat.div_mul_le_self n R
    linarith

private theorem agree_signal_decimate (R : ℕ) (v : List ℤ) :
    Agree ((v.length / R : ℕ) : ℤ) (signal (decimate R v)) (sample R (signal v)) := by
  intro m hm
  simp only [sample]
  rcases lt_or_ge m 0 with h0 | h0
  · rw [signal_neg (decimate R v) h0, signal_neg v]
    linarith [mul_le_mul_of_nonneg_right (show m + 1 ≤ 0 by omega)
      (show (0 : ℤ) ≤ R by positivity)]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have hk : k < v.length / R := by exact_mod_cast hm
    have hR : 0 < R := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
    have h1 : 1 ≤ k * R + R := by omega
    have e : (k : ℤ) * R + R - 1 = ((k * R + R - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [e, signal_nat, signal_nat, getD_of_lt (decimate R v) k (by simpa using hk),
      getElem_decimate R v k hk]

private theorem agree_signal_comb (M : ℕ) (v : List ℤ) :
    Agree v.length (signal (comb M v)) (diff M (signal v)) := by
  intro t ht
  simp only [diff]
  rcases lt_or_ge t 0 with h0 | h0
  · rw [signal_neg (comb M v) h0, signal_neg v h0, signal_neg v (by omega : t - (M : ℤ) < 0),
      sub_zero]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have hk : k < v.length := by exact_mod_cast ht
    rw [signal_nat, signal_nat, getD_of_lt (comb M v) k (by simpa using hk),
      getElem_comb M v k hk, getD_of_lt v k hk]
    congr 1
    split_ifs with hkM
    · rw [signal_neg v (by omega : (k : ℤ) - M < 0)]
    · rw [show (k : ℤ) - M = ((k - M : ℕ) : ℤ) by omega, signal_nat]

private theorem agree_iterate_comb (M N : ℕ) (d : List ℤ) :
    Agree d.length (signal ((comb M)^[N] d)) ((diff M)^[N] (signal d)) := by
  induction N with
  | zero => intro t _; rfl
  | succ N ih =>
    intro t ht
    rw [Function.iterate_succ_apply' (comb (α := ℤ) M), Function.iterate_succ_apply' (diff M)]
    have h1 := agree_signal_comb M ((comb M)^[N] d)
    rw [length_iterate_comb] at h1
    exact (h1 t ht).trans (agree_diff ih t ht)

end Signals

/-- The block cascade over ℤ computes the filter's outputs, for every order, decimation, and
differential delay. -/
theorem cascade_eq_outputs (N R M : ℕ) (xs : List ℤ) : cascade N R M xs = outputs N R M xs := by
  apply List.ext_getElem
  · simp [outputs]
  · intro m h1 h2
    have hm : (m : ℤ) < ((xs.length / R : ℕ) : ℤ) := by
      rw [length_cascade] at h1
      exact_mod_cast h1
    have c1 := agree_iterate_comb M N (decimate R (integrate^[N] xs))
    rw [length_decimate, length_iterate_integrate] at c1
    have c2 := agree_signal_decimate R (integrate^[N] xs)
    rw [length_iterate_integrate] at c2
    have c3 := agree_iterate_diff M N c2
    have c4 := (sample_diff R M).iterate_right N (signal (integrate^[N] xs))
    have c5 := agree_sample R (agree_combs_movingSum (R * M) N xs)
    have e : (cascade N R M xs)[m] = signal (cascade N R M xs) m := by
      rw [signal_nat, getD_of_lt _ _ h1]
    rw [e, cascade, c1 m hm, c3 m hm, ← c4, c5 m hm]
    simp only [outputs, List.getElem_map, List.getElem_range]
    rfl

-- The cascade agrees with `outputs` on the specification's examples of lists.
example : cascade 1 2 1 [1, 2, 3, 4, 5] = outputs 1 2 1 [1, 2, 3, 4, 5] := by decide
example : cascade 1 2 1 [3, -1, -4, 1, -5, -9] = outputs 1 2 1 [3, -1, -4, 1, -5, -9] := by
  decide
example : cascade 2 2 1 [1, 2, 3, 4, 5, 6] = outputs 2 2 1 [1, 2, 3, 4, 5, 6] := by decide
example : cascade 2 2 1 [1, -1, 1, -1, 1, -1] = outputs 2 2 1 [1, -1, 1, -1, 1, -1] := by decide
example : cascade 2 3 1 [2, -3, 5, -7, 11, -13, 17] = outputs 2 3 1 [2, -3, 5, -7, 11, -13, 17] :=
  by decide
example : cascade 1 2 2 [1, 2, 3, 4, 5, 6] = outputs 1 2 2 [1, 2, 3, 4, 5, 6] := by decide
example : cascade 0 3 1 [7, 8, 9, 10, 11, 12, 13] = outputs 0 3 1 [7, 8, 9, 10, 11, 12, 13] := by
  decide
example :
    cascade 1 2 1 [9223372036854775807, 9223372036854775807, -9223372036854775808,
      -9223372036854775808] =
    outputs 1 2 1 [9223372036854775807, 9223372036854775807, -9223372036854775808,
      -9223372036854775808] := by decide
example : cascade 3 2 1 ([] : List ℤ) = outputs 3 2 1 [] := by decide
example : cascade 1 0 1 [1, 2] = outputs 1 0 1 [1, 2] := by decide
example : cascade 2 2 0 [1, 2, 3, 4] = outputs 2 2 0 [1, 2, 3, 4] := by decide
example : cascade 3 2 1 [1, 1, 1, 1] = outputs 3 2 1 [1, 1, 1, 1] := by decide
example : cascade 2 1 2 [1, 2, 3] = outputs 2 1 2 [1, 2, 3] := by decide
example : cascade 1 3 1 [1, 2] = outputs 1 3 1 [1, 2] := by decide
example : cascade 2 2 2 [1, 2, 3, 4, 5, 6, 7, 8] = outputs 2 2 2 [1, 2, 3, 4, 5, 6, 7, 8] := by
  decide
example : cascade 0 1 1 [5, 6] = outputs 0 1 1 [5, 6] := by decide
example : cascade 0 2 0 [1, 2, 3, 4] = outputs 0 2 0 [1, 2, 3, 4] := by decide

end Library.Numerics.Filters.Cic
