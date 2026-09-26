import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-! Reusable shortest-path certificate theorem for a layered graph.
A certificate is a lower-bound potential at every node. Its local inequalities
and an attaining route establish global optimality, including the secondary
altitude objective. Establishing these conditions for Drone.compute is a
separate implementation theorem. -/
namespace Project.Drone.Optimality

structure Cost where
  time : Nat
  excess : Nat
  deriving DecidableEq, Repr

def Cost.zero : Cost := ⟨0, 0⟩
def Cost.add (a b : Cost) : Cost := ⟨a.time+b.time, a.excess+b.excess⟩
def Cost.LE (a b : Cost) : Prop :=
  a.time < b.time ∨ (a.time = b.time ∧ a.excess ≤ b.excess)

instance (a b : Cost) : Decidable (Cost.LE a b) := inferInstanceAs
  (Decidable (a.time < b.time ∨ (a.time = b.time ∧ a.excess ≤ b.excess)))

theorem Cost.le_refl (a : Cost) : a.LE a := by
  simp [Cost.LE]

theorem Cost.le_trans {a b c : Cost} (hab : a.LE b) (hbc : b.LE c) : a.LE c := by
  unfold Cost.LE at *
  omega

theorem Cost.le_total (a b : Cost) : a.LE b ∨ b.LE a := by
  unfold Cost.LE
  omega

theorem Cost.le_antisymm {a b : Cost} (hab : a.LE b) (hba : b.LE a) : a = b := by
  cases a; cases b
  simp only [Cost.LE] at *
  congr <;> omega

theorem Cost.add_mono_right {a b : Cost} (h : a.LE b) (w : Cost) :
    (a.add w).LE (b.add w) := by
  unfold Cost.LE Cost.add at *
  dsimp at *
  omega

theorem Cost.time_le {a b : Cost} (h : a.LE b) : a.time ≤ b.time := by
  unfold Cost.LE at h
  omega

/-- All paths begin at node zero in layer zero. Edges advance one layer. -/
inductive Prefix (edge : Nat → Nat → Nat → Option Cost) : Nat → Nat → Cost → Prop
  | start : Prefix edge 0 0 Cost.zero
  | step {i u v : Nat} {c w : Cost} :
      Prefix edge i u c → edge i u v = some w →
      Prefix edge (i+1) v (c.add w)

/-- A finite potential denotes a reachable lower-bound label. `none` represents
an unreachable node. The edge condition also requires finite labels to propagate. -/
def Certificate (edge : Nat → Nat → Nat → Option Cost)
    (potential : Nat → Nat → Option Cost) : Prop :=
  potential 0 0 = some Cost.zero ∧
  ∀ i u v a w, potential i u = some a → edge i u v = some w →
    ∃ b, potential (i+1) v = some b ∧ b.LE (a.add w)

theorem prefix_lower_bound {edge : Nat → Nat → Nat → Option Cost}
    {potential : Nat → Nat → Option Cost} (cert : Certificate edge potential)
    {i v : Nat} {c : Cost} (path : Prefix edge i v c) :
    ∃ lower, potential i v = some lower ∧ lower.LE c := by
  induction path with
  | start => exact ⟨Cost.zero, cert.1, Cost.le_refl _⟩
  | @step i u v c w previous hedge ih =>
    obtain ⟨a, ha, hle⟩ := ih
    obtain ⟨b, hb, hb_le⟩ := cert.2 i u v a w ha hedge
    exact ⟨b, hb, Cost.le_trans hb_le (Cost.add_mono_right hle w)⟩

/-- If the output route attains its certified lower bound, it is globally
lexicographically optimal among all paths in the same graph. -/
theorem attaining_route_optimal {edge : Nat → Nat → Nat → Option Cost}
    {potential : Nat → Nat → Option Cost} (cert : Certificate edge potential)
    {n goal : Nat} {chosen : Cost}
    (attains : potential n goal = some chosen)
    (route : Prefix edge n goal chosen) :
    Prefix edge n goal chosen ∧
    ∀ alternative, Prefix edge n goal alternative → chosen.LE alternative := by
  refine ⟨route, ?_⟩
  intro alternative path
  obtain ⟨lower, hlabel, hbound⟩ := prefix_lower_bound cert path
  rw [attains] at hlabel
  cases hlabel
  exact hbound

/-- The primary minimum-time result follows independently of whether the
caller needs the secondary altitude objective. -/
theorem attaining_route_minimum_time {edge : Nat → Nat → Nat → Option Cost}
    {potential : Nat → Nat → Option Cost} (cert : Certificate edge potential)
    {n goal : Nat} {chosen : Cost}
    (attains : potential n goal = some chosen)
    (route : Prefix edge n goal chosen) :
    ∀ alternative, Prefix edge n goal alternative → chosen.time ≤ alternative.time := by
  intro alternative path
  exact Cost.time_le ((attaining_route_optimal cert attains route).2 alternative path)

#print axioms attaining_route_optimal
end Project.Drone.Optimality
