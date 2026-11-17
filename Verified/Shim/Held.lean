import Verified.Shim.Descriptors

/-!
How a layer event changes the descriptor numbers that the shim holds, `openNumbers`, and whether
descriptor 3 is still the preopened directory, `preopened`.  An event whose call opens no
descriptor below `2^31` and is no `close` keeps both (`openNumbers_append_quiet`): `read`,
`write`, `clock_gettime`, `getrandom`, and an `openat2` that failed.  An `openat2` whose result
lies below `descriptorLimit` adds the result (`openNumbers_append_open`), and a `close` of a
number below `2^32` removes the number whatever the call returned, and ends the preopened
directory when the number is 3 (`openNumbers_append_close`).  Before any event the shim holds 3
exactly when the launcher granted it (`openNumbers_nil`).  A binding that keeps the shim's state
in memory restores its relation to these functions after each call with these lemmas.
`Carried.shift` moves the replies of a run that starts after `n` calls to the start of the
sequence.
-/

namespace Verified.Shim

open LeanExe

theorem closeCall_opens : Linux.closeCall.opens = false := rfl

theorem openAfter_single (opened : List UInt64) (e : Linux.Event) :
    Linux.openAfter opened [e] =
      if e.call.opens = true ∧ e.ret.toNat < 2 ^ 31 then e.ret :: opened
      else if e.call = Linux.closeCall then
        opened.filter (· ≠ Linux.descriptor (Linux.arg e.args 0))
      else opened := by
  simp only [Linux.openAfter]

theorem preopened_append (I : Launch) (events : List Linux.Event) (e : Linux.Event) :
    preopened I (events ++ [e]) = (preopened I events &&
      !(decide (e.call = Linux.closeCall) && Linux.descriptor (Linux.arg e.args 0) == 3)) := by
  simp only [preopened, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_assoc]

/-- An event whose call opens no descriptor below `2^31` and is no `close` keeps the numbers that
the shim holds and the preopened directory. -/
theorem openNumbers_append_quiet (I : Launch) (events : List Linux.Event) {e : Linux.Event}
    (hopen : ¬(e.call.opens = true ∧ e.ret.toNat < 2 ^ 31)) (hclose : e.call ≠ Linux.closeCall) :
    openNumbers I (events ++ [e]) = openNumbers I events ∧
      preopened I (events ++ [e]) = preopened I events := by
  refine ⟨?_, ?_⟩
  · unfold openNumbers
    rw [openAfter_append, openAfter_single, if_neg hopen, if_neg hclose]
  · rw [preopened_append]
    simp [hclose]

/-- An `openat2`, or any call that opens a descriptor, whose result lies below `descriptorLimit`
adds the result to the numbers that the shim holds and keeps the preopened directory. -/
theorem openNumbers_append_open (I : Launch) (events : List Linux.Event) {e : Linux.Event}
    (hopen : e.call.opens = true) (hsmall : e.ret.toNat < descriptorLimit) :
    (∀ x, x ∈ openNumbers I (events ++ [e]) ↔ x = e.ret ∨ x ∈ openNumbers I events) ∧
      preopened I (events ++ [e]) = preopened I events := by
  have hclose : e.call ≠ Linux.closeCall := fun h => by
    rw [h, closeCall_opens] at hopen
    cases hopen
  refine ⟨fun x => ?_, ?_⟩
  · unfold openNumbers
    rw [openAfter_append, openAfter_single,
      if_pos ⟨hopen, by unfold descriptorLimit at hsmall; omega⟩]
    simp only [List.filter_cons, decide_eq_true_eq, hsmall, ↓reduceIte, List.mem_cons]
  · rw [preopened_append]
    simp [hclose]

/-- A `close` of the number `d` below `2^32` removes `d` from the numbers that the shim holds,
whatever the call returned, and ends the preopened directory when `d` is 3. -/
theorem openNumbers_append_close (I : Launch) (events : List Linux.Event) {e : Linux.Event}
    {d : UInt64} (hclose : e.call = Linux.closeCall) (harg : Linux.arg e.args 0 = d)
    (hd : d.toNat < 2 ^ 32) :
    (∀ x, x ∈ openNumbers I (events ++ [e]) ↔ x ≠ d ∧ x ∈ openNumbers I events) ∧
      preopened I (events ++ [e]) = (preopened I events && d != 3) := by
  have hdesc : Linux.descriptor d = d := by
    apply UInt64.toNat_inj.mp
    rw [Linux.descriptor, UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 32) hd
  have hopen : ¬(e.call.opens = true ∧ e.ret.toNat < 2 ^ 31) := by
    rw [hclose, closeCall_opens]
    simp
  refine ⟨fun x => ?_, ?_⟩
  · unfold openNumbers
    rw [openAfter_append, openAfter_single, if_neg hopen, if_pos hclose, harg, hdesc]
    simp only [List.mem_filter, decide_eq_true_eq, ne_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h2, h1, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h2, h1⟩, h3⟩
  · rw [preopened_append, harg, hdesc]
    simp [hclose, bne]

/-- Before any event the shim holds 3 exactly when the launcher granted it, and descriptor 3 is
the preopened directory exactly then. -/
theorem openNumbers_nil (I : Launch) :
    openNumbers I [] = (if I.preopen then [3] else []) ∧ preopened I [] = I.preopen := by
  refine ⟨?_, ?_⟩
  · unfold openNumbers
    cases I.preopen <;> decide
  · simp [preopened]

/-- The replies from call `n` on, counted from 0, hold the events that the replies hold from call
`n` on. -/
theorem Carried.shift (R : Linux.Replies) (n : Nat) :
    ∀ (k : Nat) (ls : List Linux.Event),
      Carried (fun j => R (n + j)) k ls ↔ Carried R (n + k) ls
  | _, [] => Iff.rfl
  | k, _ :: ls => and_congr Iff.rfl (Carried.shift R n (k + 1) ls)

end Verified.Shim
