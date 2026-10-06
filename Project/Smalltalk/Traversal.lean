import Project.Smalltalk.Memory
import Init.Data.Nat.Fold

namespace Project.Smalltalk.Traversal
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory

def hop (s : Array UInt64) (tag next head : UInt64) : UInt64 :=
  if kind s head = tag then field s head next else 0

def follow (s : Array UInt64) (tag next : UInt64) : Nat → UInt64 → UInt64
  | 0, head => head
  | n + 1, head => hop s tag next (follow s tag next n head)

theorem loop_follow (s : Array UInt64) (tag next count head : UInt64) :
    LeanExe.loop count head (fun _ h => hop s tag next h) = follow s tag next count.toNat head := by
  have fold : ∀ n, Nat.fold n (fun _ _ h => hop s tag next h) head = follow s tag next n head := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [Nat.fold_succ, follow, ih]
  exact fold count.toNat

theorem walk_eq_follow (s : Array UInt64) (head count : UInt64) :
    walk s head count = follow s 7 3 (min count (read s 14)).toNat head := by
  simpa only [walk, hop, beq_iff_eq] using loop_follow s 7 3 (min count (read s 14)) head

theorem lexical_eq_follow (s : Array UInt64) (head count : UInt64) :
    lexical s head count = follow s 5 5 (min count (read s 14)).toNat head := by
  simpa only [lexical, hop, beq_iff_eq] using loop_follow s 5 5 (min count (read s 14)) head

inductive Path (s : Array UInt64) (tag next : UInt64) : UInt64 → List UInt64 → Prop
  | nil : Path s tag next 0 []
  | cons {head tail rest} : kind s head = tag → field s head next = tail →
      Path s tag next tail rest → Path s tag next head (head :: rest)

theorem follow_commute (s : Array UInt64) (tag next head : UInt64) (n : Nat) :
    follow s tag next n (hop s tag next head) = hop s tag next (follow s tag next n head) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [follow, ih]

theorem follow_succ (s : Array UInt64) (tag next head : UInt64) (n : Nat) :
    follow s tag next (n + 1) head = follow s tag next n (hop s tag next head) :=
  (follow_commute s tag next head n).symm

/-- Following a represented path returns the handle at the selected index,
or zero after the path ends. The nil case requires a nonzero cell tag. -/
theorem follow_path {s : Array UInt64} {tag next head : UInt64} {nodes : List UInt64}
    (path : Path s tag next head nodes) (nonzero : tag ≠ 0) (n : Nat) :
    follow s tag next n head = (nodes[n]?).getD 0 := by
  induction n generalizing head nodes with
  | zero =>
    cases path <;> rfl
  | succ n ih =>
    rw [follow_succ]
    cases path with
    | nil =>
      have zero : hop s tag next 0 = 0 := by
        simp only [hop, kind, BEq.rfl, Bool.true_or, ite_true, Ne.symm nonzero, ite_false]
      rw [zero]
      exact ih Path.nil
    | cons cell link tail =>
      simp only [hop, cell, ite_true, link]
      exact ih tail

theorem walk_path {s : Array UInt64} {head : UInt64} {nodes : List UInt64}
    (path : Path s 7 3 head nodes) (count : UInt64) :
    walk s head count = (nodes[(min count (read s 14)).toNat]?).getD 0 := by
  rw [walk_eq_follow]
  exact follow_path path (by decide) _

theorem lexical_path {s : Array UInt64} {head : UInt64} {nodes : List UInt64}
    (path : Path s 5 5 head nodes) (count : UInt64) :
    lexical s head count = (nodes[(min count (read s 14)).toNat]?).getD 0 := by
  rw [lexical_eq_follow]
  exact follow_path path (by decide) _

end Project.Smalltalk.Traversal
