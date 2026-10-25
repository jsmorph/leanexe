import Verified.Wasi.ProcessCode
import Verified.Wasi.OwnedScratch

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem processResult_denote (state : Ty) :
    (processResultTy state).denote = (Bool × UInt64 × state.denote) := by
  cases state <;> rfl

def processValue : (state : Ty) → ProcessStep state.denote → (processResultTy state).denote
  | .elem _, value => (value.running, value.status, value.state)
  | .pair _ _, value => (value.running, value.status, value.state)
  | .array _, value => (value.running, value.status, value.state)
  | .bytes, value => (value.running, value.status, value.state)
  | .tree _, value => (value.running, value.status, value.state)
  | .treeHeader _, value => (value.running, value.status, value.state)

def processNative : (state : Ty) → (processResultTy state).denote → ProcessStep state.denote
  | .elem _, value => ⟨value.1, value.2.1, value.2.2⟩
  | .pair _ _, value => ⟨value.1, value.2.1, value.2.2⟩
  | .array _, value => ⟨value.1, value.2.1, value.2.2⟩
  | .bytes, value => ⟨value.1, value.2.1, value.2.2⟩
  | .tree _, value => ⟨value.1, value.2.1, value.2.2⟩
  | .treeHeader _, value => ⟨value.1, value.2.1, value.2.2⟩

@[simp] theorem processNative_value (state : Ty) (value : ProcessStep state.denote) :
    processNative state (processValue state value) = value := by
  cases state <;> cases value <;> rfl

@[simp] theorem processValue_native (state : Ty) (value : (processResultTy state).denote) :
    processValue state (processNative state value) = value := by
  cases state <;> rfl

@[simp] theorem processResult_width (state : Ty) : (processResultTy state).width = 2 + state.width := by
  cases state <;> simp [processResultTy, Ty.width, Elem.width] <;> omega

@[simp] theorem processResult_types (state : Ty) :
    (processResultTy state).types = [.i64, .i64] ++ state.types := by
  cases state <;> rfl

private theorem pair_control_rep {state : Ty} {heap : Heap} {store : Store Unit}
    {words : List Value} {value : Bool × UInt64 × state.denote} :
    (Ty.pair .bool (.pair .word state)).Rep .owned heap store words value ↔
      ∃ stateWords, words = [.i64 (boolWord value.1), .i64 value.2.1] ++ stateWords ∧
        state.Rep .owned heap store stateWords value.2.2 := by
  constructor
  · rintro ⟨first, second, rfl, firstRep, secondRep, _⟩
    change first = [.i64 (boolWord value.1)] at firstRep
    subst first
    rcases secondRep with ⟨second, stateWords, rfl, secondRep, stateRep, _⟩
    change second = [.i64 value.2.1] at secondRep
    subst second
    exact ⟨stateWords, rfl, stateRep⟩
  · rintro ⟨stateWords, rfl, stateRep⟩
    refine ⟨[.i64 (boolWord value.1)], [.i64 value.2.1] ++ stateWords, rfl, rfl,
      ⟨[.i64 value.2.1], stateWords, rfl, rfl, stateRep, ?_⟩, ?_⟩
    · intro _ region member
      exact nomatch member
    · intro _ region member
      exact nomatch member

theorem processValue_rep {state : Ty} {heap : Heap} {store : Store Unit}
    {words : List Value} {value : ProcessStep state.denote} :
    (processResultTy state).Rep .owned heap store words (processValue state value) ↔
      ∃ stateWords, words = [.i64 (boolWord value.running), .i64 value.status] ++ stateWords ∧
        state.Rep .owned heap store stateWords value.state := by
  cases state with
  | elem element =>
      change words = [.i64 (boolWord value.running), .i64 value.status] ++ element.values value.state ↔ _
      constructor
      · intro same
        exact ⟨element.values value.state, same, rfl⟩
      · rintro ⟨stateWords, same, represented⟩
        change stateWords = element.values value.state at represented
        simpa only [represented] using same
  | pair first second | array element | bytes | tree shape | treeHeader shape =>
      exact pair_control_rep

theorem processValue_blocks (state : Ty) (store : Store Unit) (words : List Value)
    (value : ProcessStep state.denote) :
    (processResultTy state).blocks store words (processValue state value) =
      state.blocks store (words.drop 2) value.state := by
  cases state <;> simp [processResultTy, processValue, Ty.blocks, Ty.width,
    Elem.width, List.drop_drop]

def ProcessEntry.action (entry : ProcessEntry effectSigs) (functions : EffectFuns effectSigs)
    (state : entry.state.denote) : Action (ProcessStep entry.state.denote) :=
  Action.bind (functions.get entry.step (.cons state .nil)) fun result =>
    .pure (processNative entry.state result)

end Verified.Wasi
