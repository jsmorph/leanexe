import Project.Smalltalk.SweepList

namespace Project.Smalltalk.Graph
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory

def Root (s : Array UInt64) (h : UInt64) : Prop :=
  h ≠ 0 ∧ h ∈ [1, 2, 3, read s 2, read s 7, read s 16]

/-- Pointer fields only. Class and method identifiers, PCs, integer values,
and the mark word are scalar data. -/
def PointerField (tag k : UInt64) : Prop :=
  ((tag = 4 ∨ tag = 6) ∧ k = 3) ∨
  (tag = 5 ∧ (k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7)) ∨
  (tag = 7 ∧ (k = 2 ∨ k = 3))

def Edge (s : Array UInt64) (parent child : UInt64) : Prop :=
  child ≠ 0 ∧ ∃ k, k.toNat < 8 ∧ PointerField (field s parent 0) k ∧ field s parent k = child

def ValidTag (tag : UInt64) : Prop :=
  tag = 1 ∨ tag = 2 ∨ tag = 4 ∨ tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8

inductive Reachable (s : Array UInt64) : UInt64 → Prop
  | root {h} : Root s h → Reachable s h
  | next {parent child} : Reachable s parent → Edge s parent child → Reachable s child

def Valid (s : Array UInt64) (cap : Nat) : Prop :=
  Shape s cap ∧
  (∀ h, Root s h → Handle cap h ∧ field s h 0 ≠ 0) ∧
  (∀ parent child, Handle cap parent → field s parent 0 ≠ 0 → Edge s parent child →
    Handle cap child ∧ field s child 0 ≠ 0) ∧
  (∀ h, Handle cap h → field s h 0 ≠ 0 → ValidTag (field s h 0))

theorem reachable_allocated {s : Array UInt64} {cap : Nat} (valid : Valid s cap)
    {h : UInt64} (reachable : Reachable s h) : Handle cap h ∧ field s h 0 ≠ 0 := by
  induction reachable with
  | root root => exact valid.2.1 _ root
  | next _ edge ih => exact valid.2.2.1 _ _ ih.1 ih.2 edge

def SamePayload (original t : Array UInt64) (cap : Nat) : Prop :=
  ∀ h, Handle cap h → ∀ k : UInt64, k.toNat < 8 → k ≠ 1 → field t h k = field original h k

def MarkedExactly (original marked : Array UInt64) (cap : Nat) : Prop :=
  Shape marked cap ∧ SamePayload original marked cap ∧
    ∀ h, Handle cap h → (field marked h 1 ≠ 0 ↔ Reachable original h)

/-- A marking result satisfying graph reachability is sufficient for the
concrete sweep to preserve every reachable value and free exactly the rest. -/
theorem sweep_correct {original marked : Array UInt64} {cap : Nat}
    (valid : Valid original cap) (marks : MarkedExactly original marked cap) (count : UInt64) :
    (∀ h, Reachable original h → ∀ k : UInt64, k.toNat < 8 → k ≠ 1 →
      field (finishCollection marked (read marked 14) count) h k = field original h k) ∧
    ∃ nodes, Project.Smalltalk.FreeList.Valid (finishCollection marked (read marked 14) count) cap nodes ∧
      (∀ h, Handle cap h → (h ∈ nodes ↔ ¬ Reachable original h)) ∧ nodes.Nodup := by
  rcases marks with ⟨shape, payload, exactMarks⟩
  have live : ∀ h, Handle cap h → field marked h 1 ≠ 0 → field marked h 0 ≠ 0 := by
    intro h hh hm
    rw [payload h hh 0 (by decide) (by decide)]
    exact (reachable_allocated valid ((exactMarks h hh).mp hm)).2
  constructor
  · intro h reached k hk nonmark
    have hh := (reachable_allocated valid reached).1
    rw [Project.Smalltalk.Sweep.finishCollection_preserves_marked shape hh hk
      ((exactMarks h hh).mpr reached), payload h hh k hk nonmark]
  · rcases Project.Smalltalk.SweepList.finishCollection_freeList shape live count with
      ⟨nodes, free, members, nodup⟩
    refine ⟨nodes, free, ?_, nodup⟩
    intro h hh
    rw [members h hh]
    have eq := exactMarks h hh
    constructor
    · intro zero reached
      exact (eq.mpr reached) zero
    · intro unreachable
      by_cases zero : field marked h 1 = 0
      · exact zero
      · exact False.elim (unreachable (eq.mp zero))

end Project.Smalltalk.Graph
