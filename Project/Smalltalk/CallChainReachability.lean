import Project.Smalltalk.CallChain
import Project.Smalltalk.Reachability

namespace Project.Smalltalk.CallChainReachability
open LeanExe.Smalltalk.Arena Project.Smalltalk.Graph Project.Smalltalk.Reachability

def Holds (s : Array UInt64) (target : UInt64) (st : UInt64 × Bool) : Prop :=
  Live s st.1 ∧ (st.2 = true → Reachable s target)

theorem next_holds {s : Array UInt64} {cap : Nat} {target : UInt64} {st : UInt64 × Bool}
    (valid : Graph.Valid s cap) (holds : Holds s target st) : Holds s target (CallChain.next s target st) := by
  constructor
  · exact guarded_field_live valid holds.1 (show (5 : UInt64) ≠ 0 by decide)
      (show (4 : UInt64).toNat < 8 by decide) (by simp [PointerField])
  · intro found
    change (st.2 || (st.1 != 0 && st.1 == target)) = true at found
    simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at found
    rcases found with previous | ⟨nonzero, same⟩
    · exact holds.2 previous
    · exact same ▸ (holds.1.resolve_left nonzero)

theorem onChain_reachable {s : Array UInt64} {cap : Nat} {target : UInt64}
    (valid : Graph.Valid s cap) (found : LeanExe.Smalltalk.Runtime.onChain s target = true) : Reachable s target := by
  have initial : Holds s target (read s 2, false) :=
    ⟨root_live s 2 (Or.inl rfl), by intro impossible; cases impossible⟩
  have checked := Loops.applyN_invariant (Holds s target) (CallChain.next s target)
    (fun _ holds => next_holds valid holds) (read s 14).toNat (read s 2, false) initial
  rw [CallChain.onChain_eq] at found
  exact checked.2 found

end Project.Smalltalk.CallChainReachability
