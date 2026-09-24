import Project.Compiler.ScalarLowering

namespace Project.Compiler.ScalarLowering

open Project.ProofKit.ScalarTransition

def capacity (state : State) : Nat := state.params.length + state.locals.length

def Agrees (source : LeanExe.IR.ScalarStore) (state : State) : Prop :=
  ∀ index value, source[index]? = some value → state.get index = some (.i64 value)

theorem set_exists {state : State} {index : Nat} (value : Wasm.Value)
    (bound : index < capacity state) :
    ∃ next, state.set? index value = some next ∧ capacity next = capacity state := by
  unfold State.set?
  split
  · exact ⟨_, rfl, by simp [capacity]⟩
  · split
    · exact ⟨_, rfl, by simp [capacity]⟩
    · simp [capacity] at bound
      contradiction

theorem Agrees.write {source : LeanExe.IR.ScalarStore} {state next : State}
    {index : Nat} {value : Wasm.Value} (agree : Agrees source state)
    (above : source.length ≤ index) (written : state.set? index value = some next) :
    Agrees source next := by
  intro i v read
  have hi : i < source.length := List.getElem?_eq_some_iff.mp read |>.1
  rw [State.get_set?_ne (by omega) written]
  exact agree i v read

theorem write_scratch {source : LeanExe.IR.ScalarStore} {state : State}
    {index : Nat} (value : UInt64) (agree : Agrees source state)
    (above : source.length ≤ index) (bound : index < capacity state) :
    ∃ next, state.set? index (.i64 value) = some next ∧
      Agrees source next ∧ capacity next = capacity state := by
  obtain ⟨next, written, size⟩ := set_exists (.i64 value) bound
  exact ⟨next, written, agree.write above written, size⟩

@[simp] theorem operation_apply (op : LeanExe.Wasm.ScalarDescriptor.U64Op) (x y : UInt64) :
    (operation op).apply x y = op.apply x y := by
  cases op <;> try rfl
  · change (if y = 0 then 0 else x / y) = x / y
    split <;> simp_all
  · change (if y = 0 then x else x % y) = x % y
    split <;> simp_all
  · change UInt64.shiftLeft x (y % 64) = UInt64.shiftLeft x y
    simp [UInt64.shiftLeft, UInt64.mod]
  · change UInt64.shiftRight x (y % 64) = UInt64.shiftRight x y
    simp [UInt64.shiftRight, UInt64.mod]

end Project.Compiler.ScalarLowering
