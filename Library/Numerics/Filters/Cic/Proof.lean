import Library.Numerics.Filters.Cic.Program
import Library.Numerics.Filters.Cic.Cascade

/-! `cic_toList` proves that the dialect's filter `cic` of `Program.lean` computes the block cascade
`cascade 3 8 1` at `UInt64` on every input array.  Each pass equals its stage of `Cascade.lean` as a
list.  The integrator's and the comb's folds append one element per step, so induction on the list
from the left, with the state generalized, gives `integrateFrom` and the comb's `zipWith`.  The
decimation's fold appends an element only at the end of a block, so induction from the right
carries the invariant that its counter is the length of the list read so far modulo 8 and its result
is `decimate 8` of that list. -/

namespace Library.Numerics.Filters.Cic

/-- The integrator pass's fold over a list, from the sum `s` and the result `out`, appends to `out`
the running sums of the list after `s`. -/
theorem foldl_integratePass (l : List UInt64) (s : UInt64) (out : Array UInt64) :
    (l.foldl (fun (state : UInt64 × Array UInt64) x =>
      let sum := state.1 + x
      (sum, state.2.push sum)) (s, out)).2.toList = out.toList ++ integrateFrom s l := by
  induction l generalizing s out with
  | nil => simp [integrateFrom]
  | cons x l ih =>
    rw [List.foldl_cons]
    dsimp only
    rw [ih]
    simp [integrateFrom]

theorem integratePass_toList (xs : Array UInt64) :
    (integratePass xs).toList = integrate xs.toList := by
  rw [integratePass, ← Array.foldl_toList, foldl_integratePass]
  rfl

/-- The comb pass's fold over a list, from the previous element `p` and the result `out`, appends
to `out` the differences of the list's elements and their predecessors, with `p` before the
first. -/
theorem foldl_combPass (l : List UInt64) (p : UInt64) (out : Array UInt64) :
    (l.foldl (fun (state : UInt64 × Array UInt64) x =>
      (x, state.2.push (x - state.1))) (p, out)).2.toList =
      out.toList ++ List.zipWith (· - ·) l (p :: l) := by
  induction l generalizing p out with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons]
    dsimp only
    rw [ih]
    simp

theorem combPass_toList (xs : Array UInt64) : (combPass xs).toList = comb 1 xs.toList := by
  rw [combPass, ← Array.foldl_toList, foldl_combPass]
  rfl

/-- The step of the decimation pass's fold. -/
private def decimateStep (state : UInt64 × Array UInt64) (x : UInt64) : UInt64 × Array UInt64 :=
  if state.1 == 7 then ((0 : UInt64), state.2.push x) else (state.1 + 1, state.2)

/-- `decimate 8` of a list with one more element: the element is kept when it ends a block. -/
theorem decimate_concat (l : List UInt64) (x : UInt64) :
    decimate 8 (l ++ [x]) = if l.length % 8 = 7 then decimate 8 l ++ [x] else decimate 8 l := by
  have hget : ∀ (d : UInt64), ∀ m ∈ List.range (l.length / 8),
      (l ++ [x]).getD (m * 8 + 8 - 1) d = l.getD (m * 8 + 8 - 1) d := by
    intro d m hm
    rw [List.mem_range] at hm
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (l₂ := [x]) (show m * 8 + 8 - 1 < l.length by omega)]
  have hlast : ∀ (i : Nat) (d : UInt64), i = l.length → (l ++ [x]).getD i d = x := by
    rintro i d rfl
    rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length]
    rfl
  unfold decimate
  rw [List.length_append, List.length_singleton]
  split_ifs with h
  · rw [show (l.length + 1) / 8 = l.length / 8 + 1 by omega, List.range_succ, List.map_append,
      List.map_congr_left (hget _)]
    congr 1
    simp only [List.map_cons, List.map_nil]
    rw [hlast]
    omega
  · rw [show (l.length + 1) / 8 = l.length / 8 by omega]
    exact List.map_congr_left (hget _)

private theorem foldl_decimateStep (l : List UInt64) :
    (l.foldl decimateStep (0, #[])).1.toNat = l.length % 8 ∧
      (l.foldl decimateStep (0, #[])).2.toList = decimate 8 l := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨rfl, by simp [decimate]⟩
  | append_singleton l x ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, decimate_concat, List.length_append,
      List.length_singleton]
    generalize l.foldl decimateStep (0, #[]) = st at ih ⊢
    obtain ⟨c, out⟩ := st
    obtain ⟨h1, h2⟩ := ih
    dsimp only at h1 h2
    unfold decimateStep
    dsimp only
    by_cases h : l.length % 8 = 7
    · have hc : c = 7 := UInt64.toNat_inj.mp (by rw [h1, h]; rfl)
      subst hc
      simp [h, h2]
      omega
    · have hc : (c == 7) = false := by
        rw [beq_eq_false_iff_ne]
        intro hc
        rw [hc] at h1
        exact h (by rw [← h1]; rfl)
      simp [hc, h, h1, h2]
      omega

theorem decimatePass_toList (xs : Array UInt64) :
    (decimatePass xs).toList = decimate 8 xs.toList := by
  rw [show decimatePass xs = (xs.foldl decimateStep (0, #[])).2 from rfl, ← Array.foldl_toList]
  exact (foldl_decimateStep xs.toList).2

/-- The dialect's filter computes the block cascade of order 3, decimation 8, and differential
delay 1 in 64-bit words on every input array. -/
theorem cic_toList (xs : Array UInt64) : (cic xs).toList = cascade 3 8 1 xs.toList := by
  simp only [cic, combPass_toList, decimatePass_toList, integratePass_toList]
  rfl

end Library.Numerics.Filters.Cic
