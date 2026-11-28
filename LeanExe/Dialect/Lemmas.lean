module

public import LeanExe.Dialect.Loop
public import LeanExe.Dialect.Build
public import LeanExe.Dialect.RepeatWhile
public import Mathlib.Tactic

@[expose] public section

/-! Lemmas about the combinators `LeanExe.loop`, `LeanExe.repeatWhile`, and `LeanExe.build`. -/

namespace LeanExe.Dialect

/-- A property of the state after `k` steps of `LeanExe.loop` that each step preserves holds at
the end. -/
theorem loop_induction {α : Type} {n : UInt64} {init : α} {f : UInt64 → α → α}
    (P : Nat → α → Prop) (h0 : P 0 init)
    (hStep : ∀ k s, k < n.toNat → P k s → P (k + 1) (f (UInt64.ofNat k) s)) :
    P n.toNat (LeanExe.loop n init f) := by
  unfold LeanExe.loop
  suffices h : ∀ m, m ≤ n.toNat →
      P m (Nat.fold m (fun i _ s => f (UInt64.ofNat i) s) init) from h _ le_rfl
  intro m
  induction m with
  | zero => intro _; simpa using h0
  | succ m ih =>
    intro hm
    rw [Nat.fold_succ]
    exact hStep m _ (by omega) (ih (by omega))

/-- A property that holds at the start of `LeanExe.repeatWhile` and that each step under the
condition keeps holds at the end. -/
theorem repeatWhile_induction {α : Type} {fuel : UInt64} {init : α} {cond : α → Bool}
    {step : α → α} (P : α → Prop) (h0 : P init) (hs : ∀ s, P s → cond s = true → P (step s)) :
    P (LeanExe.repeatWhile fuel init cond step) := by
  unfold LeanExe.repeatWhile
  generalize fuel.toNat = k
  induction k generalizing init with
  | zero => exact h0
  | succ k ih =>
    rw [LeanExe.repeatWhile.go]
    by_cases hc : cond init = true
    · rw [ite_eq_left hc]
      exact ih (hs _ h0 hc)
    · rw [ite_eq_right hc]
      exact h0

/-- `repeatWhile_induction` with a measure `μ`, at most the fuel at the start, that each step under
the condition lowers: the property holds at the end, and the condition fails there. -/
theorem repeatWhile_induction_stop {α : Type} {fuel : UInt64} {init : α} {cond : α → Bool}
    {step : α → α} (P : α → Prop) (μ : α → Nat) (h0 : P init) (hμ : μ init ≤ fuel.toNat)
    (hs : ∀ s, P s → cond s = true → P (step s) ∧ μ (step s) < μ s) :
    P (LeanExe.repeatWhile fuel init cond step) ∧
      cond (LeanExe.repeatWhile fuel init cond step) = false := by
  unfold LeanExe.repeatWhile
  generalize fuel.toNat = k at hμ
  induction k generalizing init with
  | zero =>
    refine ⟨h0, Bool.eq_false_iff.mpr fun hc => ?_⟩
    have := (hs _ h0 hc).2
    omega
  | succ k ih =>
    rw [LeanExe.repeatWhile.go]
    by_cases hc : cond init = true
    · rw [ite_eq_left hc]
      obtain ⟨h1, h2⟩ := hs _ h0 hc
      exact ih h1 (by omega)
    · rw [ite_eq_right hc]
      exact ⟨h0, by simpa using hc⟩

/-- An invariant indexed by the number of steps taken holds at the result of `LeanExe.repeatWhile`
at a count no larger than the fuel, and the condition fails there when that count is below the
fuel. -/
theorem repeatWhile_steps {α : Type} {fuel : UInt64} {init : α} {cond : α → Bool}
    {step : α → α} (I : Nat → α → Prop) (h0 : I 0 init)
    (hs : ∀ j s, j < fuel.toNat → I j s → cond s = true → I (j + 1) (step s)) :
    ∃ j, j ≤ fuel.toNat ∧ I j (LeanExe.repeatWhile fuel init cond step) ∧
      (j < fuel.toNat → cond (LeanExe.repeatWhile fuel init cond step) = false) := by
  unfold LeanExe.repeatWhile
  suffices h : ∀ f j s, j + f = fuel.toNat → I j s →
      ∃ j', j' ≤ fuel.toNat ∧ I j' (LeanExe.repeatWhile.go cond step f s) ∧
        (j' < fuel.toNat → cond (LeanExe.repeatWhile.go cond step f s) = false) from
    h _ 0 init (by omega) h0
  intro f
  induction f with
  | zero => exact fun j s hj hI => ⟨j, by omega, hI, fun h => absurd h (by omega)⟩
  | succ f ih =>
    intro j s hj hI
    rw [LeanExe.repeatWhile.go]
    by_cases hc : cond s = true
    · rw [ite_eq_left hc]
      exact ih (j + 1) (step s) (by omega) (hs j s (by omega) hI hc)
    · rw [ite_eq_right hc]
      exact ⟨j, by omega, hI, fun _ => by simpa using hc⟩

/-- `repeatWhile_steps` with an invariant whose count at the fuel excludes the condition: the
loop ends by its condition. -/
theorem repeatWhile_steps_stop {α : Type} {fuel : UInt64} {init : α} {cond : α → Bool}
    {step : α → α} (I : Nat → α → Prop) (h0 : I 0 init)
    (hs : ∀ j s, j < fuel.toNat → I j s → cond s = true → I (j + 1) (step s))
    (hstop : ∀ s, I fuel.toNat s → cond s = false) :
    ∃ j, j ≤ fuel.toNat ∧ I j (LeanExe.repeatWhile fuel init cond step) ∧
      cond (LeanExe.repeatWhile fuel init cond step) = false := by
  obtain ⟨j, hj, hI, hc⟩ := repeatWhile_steps I h0 hs
  refine ⟨j, hj, hI, ?_⟩
  rcases Nat.lt_or_ge j fuel.toNat with h | h
  · exact hc h
  · exact hstop _ (by rw [← Nat.le_antisymm hj h]; exact hI)

/-- Two loops whose steps agree at every index give the same state. -/
theorem loop_congr {α : Type} {n : UInt64} {init : α} {f g : UInt64 → α → α}
    (h : ∀ k, k < n.toNat → ∀ s, f (UInt64.ofNat k) s = g (UInt64.ofNat k) s) :
    LeanExe.loop n init f = LeanExe.loop n init g := by
  unfold LeanExe.loop
  congr 1
  funext k hk s
  exact h k hk s

/-- A loop from `true` whose step conjoins its state with a test of the index returns `true`
exactly when the test holds at every index below the count. -/
theorem loop_and_iff {n : UInt64} {P : UInt64 → Bool} :
    LeanExe.loop n true (fun i ok => ok && P i) = true ↔
      ∀ k, k < n.toNat → P (UInt64.ofNat k) = true :=
  loop_induction (n := n) (init := true) (f := fun i ok => ok && P i)
    (fun m s => (s = true ↔ ∀ k, k < m → P (UInt64.ofNat k) = true))
    (by simp)
    (fun m s _ ih => by
      rw [Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h1, h2⟩ k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact h1 k hk
        · exact h2
      · intro h
        exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h m (Nat.lt_succ_self m)⟩)

theorem build_size {α : Type} (n : UInt64) (f : UInt64 → α) :
    (LeanExe.build n f).size = n.toNat := by
  simp [LeanExe.build]

theorem build_get {α : Type} [Inhabited α] {n : UInt64} {f : UInt64 → α} {m : Nat}
    (h : m < n.toNat) : (LeanExe.build n f)[m]! = f (UInt64.ofNat m) := by
  simp [LeanExe.build, h]

theorem build_get_out {α : Type} [Inhabited α] {n : UInt64} {f : UInt64 → α} {m : Nat}
    (h : ¬ m < n.toNat) : (LeanExe.build n f)[m]! = default := by
  simp [LeanExe.build, h]

/-- Two builds agree when their functions agree below the count. -/
theorem build_congr {α : Type} {f g : UInt64 → α} {n : UInt64}
    (h : ∀ i : UInt64, i.toNat < n.toNat → f i = g i) :
    LeanExe.build n f = LeanExe.build n g := by
  unfold LeanExe.build
  congr 1
  funext j
  apply h
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (lt_of_lt_of_le j.isLt (UInt64.toNat_lt n).le)]
  exact j.isLt

end LeanExe.Dialect
