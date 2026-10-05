import LeanExe.Loop
import LeanExe.Build
import Mathlib.Tactic

/-! Lemmas about the combinators `LeanExe.loop` and `LeanExe.build`. -/

namespace Project.IR

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

/-- Two loops whose steps agree at every index give the same state. -/
theorem loop_congr {α : Type} {n : UInt64} {init : α} {f g : UInt64 → α → α}
    (h : ∀ k, k < n.toNat → ∀ s, f (UInt64.ofNat k) s = g (UInt64.ofNat k) s) :
    LeanExe.loop n init f = LeanExe.loop n init g := by
  unfold LeanExe.loop
  congr 1
  funext k hk s
  exact h k hk s

theorem build_size {α : Type} (n : UInt64) (f : UInt64 → α) :
    (LeanExe.build n f).size = n.toNat := by
  simp [LeanExe.build]

theorem build_get {α : Type} [Inhabited α] {n : UInt64} {f : UInt64 → α} {m : Nat}
    (h : m < n.toNat) : (LeanExe.build n f)[m]! = f (UInt64.ofNat m) := by
  simp [LeanExe.build, h]

theorem build_get_out {α : Type} [Inhabited α] {n : UInt64} {f : UInt64 → α} {m : Nat}
    (h : ¬ m < n.toNat) : (LeanExe.build n f)[m]! = default := by
  simp [LeanExe.build, h]

end Project.IR
