import Project.Beck.ExecutionMemberCapacity
import Project.Beck.ExecutionMembershipRelease

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

theorem readMemberships_some_step (count : Nat) (words row out : Array UInt64) (position categories : Nat)
    (accepted : readMemberships (count + 1) words position categories row = some out) :
    words[position]!.toNat < categories ∧ row[words[position]!.toNat]! = 0 ∧
      readMemberships count words (position + 1) categories (row.set! words[position]!.toNat 1) = some out := by
  simp only [readMemberships] at accepted
  split at accepted
  · contradiction
  rename_i categoryBound
  split at accepted
  · contradiction
  rename_i fresh
  exact ⟨by omega, by simpa using fresh, accepted⟩

def membershipBytes (count categories : Nat) : Nat := count * (48 + 8 * (categories + 1))

theorem membershipBytes_succ (count categories : Nat) :
    membershipBytes (count + 1) categories = 48 + 8 * (categories + 1) + membershipBytes count categories := by
  simp [membershipBytes, Nat.add_mul, Nat.add_comm]

theorem membershipBytes_bound (count categories : Nat) (hCount : count ≤ 8) (hCategories : categories ≤ 8) :
    membershipBytes count categories ≤ 960 := by
  unfold membershipBytes
  nlinarith

abbrev MembershipTail := Fin 15 → UInt64

def membershipSaved (internal : UInt64) (saved : MemberSetSaved) (index : Fin 24) : Value :=
  if index.val = 0 then .i64 internal else if index.val = 1 ∨ index.val = 5 then .i64 0 else saved index

def membershipTail (tail : MembershipTail) : List Value :=
  [.i64 (tail 0), .i64 (tail 1), .i64 (tail 2), .i64 (tail 3), .i64 (tail 4),
    .i64 (tail 5), .i64 (tail 6), .i64 (tail 7), .i64 (tail 8), .i64 (tail 9),
    .i64 (tail 10), .i64 (tail 11), .i64 (tail 12), .i64 (tail 13), .i64 (tail 14)]

def membershipFrame (count position categories : Nat) (wordsOwner wordsPointer rowPointer internal : UInt64)
    (saved : MemberSetSaved) (tail : MembershipTail) : Locals :=
  { params := membershipParams count.toUInt64 wordsOwner wordsPointer position.toUInt64 categories.toUInt64 rowPointer rowPointer
    locals := memberSetPrefix (membershipSaved internal saved) ++ membershipTail tail }

def membershipFrameLocal (internal : UInt64) (saved : MemberSetSaved) (tail : MembershipTail) (index : Fin 39) : Value :=
  if h : index.val < 24 then membershipSaved internal saved ⟨index.val, h⟩
  else .i64 (tail ⟨index.val - 24, by omega⟩)

theorem membershipFrame_locals (count position categories : Nat) (wordsOwner wordsPointer rowPointer internal : UInt64)
    (saved : MemberSetSaved) (tail : MembershipTail) :
    (membershipFrame count position categories wordsOwner wordsPointer rowPointer internal saved tail).locals =
      List.ofFn (membershipFrameLocal internal saved tail) := rfl

theorem membership_local_read (frame : Locals) (index : Nat) (value : Value)
    (params : frame.params.length = 7) (locals : frame.locals.length = 39)
    (inside : index < 39) (read : frame.get (index + 7) = some value) : frame.locals[index]! = value := by
  have indexBound : index < frame.locals.length := by omega
  have read' : frame.locals[index]? = some value := by
    simpa [Locals.get, params, locals, show ¬index + 7 < 7 by omega,
      show index + 7 < 7 + 39 by omega, Nat.add_sub_cancel] using read
  simpa only [getElem?_pos frame.locals index indexBound, getElem!_pos frame.locals index indexBound,
    Option.some.injEq] using read'

theorem membershipFrame_reconstruct (frame : Locals) (count position categories : Nat)
    (wordsOwner wordsPointer rowPointer internal : UInt64) (tail : MembershipTail)
    (params : frame.params = membershipParams count.toUInt64 wordsOwner wordsPointer position.toUInt64 categories.toUInt64 rowPointer rowPointer)
    (locals : frame.locals.length = 39) (values : frame.values = [])
    (r7 : frame.get 7 = some (.i64 internal)) (r8 : frame.get 8 = some (.i64 0)) (r12 : frame.get 12 = some (.i64 0))
    (tailReads : ∀ index : Fin 15, frame.get (index.val + 31) = some (.i64 (tail index))) :
    frame = membershipFrame count position categories wordsOwner wordsPointer rowPointer internal
      (fun k => frame.locals[k.val]!) tail := by
  have paramsLength : frame.params.length = 7 := by simp [params, membershipParams]
  have a := membership_local_read frame 0 (.i64 internal) paramsLength locals (by decide) r7
  have b := membership_local_read frame 1 (.i64 0) paramsLength locals (by decide) r8
  have c := membership_local_read frame 5 (.i64 0) paramsLength locals (by decide) r12
  apply Frame.ext frame _ params _ values
  rw [membershipFrame_locals]
  apply List.ext_getElem
  · simp [locals]
  · intro i hi hj
    rw [List.getElem_ofFn]
    simp only [membershipFrameLocal]
    split_ifs with lower
    · simp only [membershipSaved]
      split_ifs with zero small
      · have equal : i = 0 := zero
        subst i
        simpa only [getElem!_pos frame.locals 0 hi] using a
      · rcases small with one | five
        · have equal : i = 1 := one
          subst i
          simpa only [getElem!_pos frame.locals 1 hi] using b
        · have equal : i = 5 := five
          subst i
          simpa only [getElem!_pos frame.locals 5 hi] using c
      · simp [getElem!_pos frame.locals i hi]
    · have upper : i < 39 := by omega
      have read := tailReads ⟨i - 24, by omega⟩
      have address : i - 24 + 31 = i + 7 := by omega
      simp only [address] at read
      simpa only [getElem!_pos frame.locals i hi] using
        membership_local_read frame i _ paramsLength locals upper read

#print axioms readMemberships_some_step
#print axioms membershipFrame_reconstruct

end Project.Beck.Execution
