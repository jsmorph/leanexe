import Project.Pipeline.RuntimeSpec
import Project.Pipeline.Records

/-!
`release` on a tree of records.  The runtime's loop takes the head of the pending list,
links the non-null children of its masked slots onto the front of the list through their
count words, and frees the record.
-/

namespace Project.Pipeline

open Wasm Project.Runtime Project.ProofKit

/-- A loop rule whose measure is a ghost index in the invariant: each iteration that
branches back re-enters the invariant at a smaller index. -/
theorem wp_loop_ghost {α : Type} {m : Module} {env : HostEnv α} {ps rs : Nat}
    {body rest : Program} {Q : Assertion α} {st : Store α} {s : Locals}
    (Inv : Nat → AssertionF α) (n : Nat) (hInit : Inv n st s)
    (hStep : ∀ n st s, Inv n st s →
        wp m body
          (fun c => match c with
            | .Fallthrough st' s' =>
              wp m rest Q st' { s' with values := s'.values.take rs ++ s.values.drop ps } env
            | .Break 0 st' s' =>
              ∃ n' < n, Inv n' st' { s' with values := s'.values.take ps ++ s.values.drop ps }
            | .Break (k+1) st' s' => Q (.Break k st' s')
            | other => Q other)
          st s env) :
    wp m (.loop ps rs body :: rest) Q st s env := by
  classical
  refine wp_loop_cons (fun st s => ∃ n, Inv n st s)
    (fun st s => if h : ∃ n, Inv n st s then Nat.find h else 0) ⟨n, hInit⟩ ?_
  intro st s hEx
  refine wp.conseq ?_ (hStep _ st s (Nat.find_spec hEx))
  intro c hc
  rcases c with ⟨st', s'⟩ | ⟨_ | k, st', s'⟩ | _ | _ | _ | _ | _ | _
  · exact hc
  · obtain ⟨n', hlt, hInv⟩ := hc
    refine ⟨⟨n', hInv⟩, ?_⟩
    rw [dite_eq_left_of_eq_true (eq_true ⟨n', hInv⟩), dite_eq_left_of_eq_true (eq_true hEx)]
    exact lt_of_le_of_lt (Nat.find_min' _ hInv) hlt
  all_goals exact hc

end Project.Pipeline
