import LeanExe.Extract.ScalarPrimitive
import LeanExe.Source.ScalarHead

namespace LeanExe.Extract.Core.ScalarPrimitive

def classNames : ScalarPrimitive → Lean.Name × Lean.Name × Lean.Name
  | .add => (``HAdd.hAdd, ``instHAdd, ``instAddUInt64)
  | .sub => (``HSub.hSub, ``instHSub, ``instSubUInt64)
  | .mul => (``HMul.hMul, ``instHMul, ``instMulUInt64)
  | .div => (``HDiv.hDiv, ``instHDiv, ``instDivUInt64)
  | .mod => (``HMod.hMod, ``instHMod, ``instModUInt64)
  | .land => (``HAnd.hAnd, ``instHAndOfAndOp, ``instAndOpUInt64)
  | .lor => (``HOr.hOr, ``instHOrOfOrOp, ``instOrOpUInt64)
  | .xor => (``HXor.hXor, ``instHXorOfXorOp, ``instXorOpUInt64)
  | .shiftLeft => (``HShiftLeft.hShiftLeft, ``instHShiftLeftOfShiftLeft, ``instShiftLeftUInt64)
  | .shiftRight => (``HShiftRight.hShiftRight, ``instHShiftRightOfShiftRight, ``instShiftRightUInt64)

def ofClass? (names : Lean.Name × Lean.Name × Lean.Name) : Option ScalarPrimitive :=
  all.find? (fun p => p.classNames == names)

@[simp] theorem ofClass_names (p : ScalarPrimitive) : ofClass? p.classNames = some p := by
  cases p <;> decide

theorem ofClass_sound {names : Lean.Name × Lean.Name × Lean.Name} {p : ScalarPrimitive}
    (h : ofClass? names = some p) : p.classNames = names := by
  simpa using List.find?_some h

def ofHead? : Lean.Expr → Option ScalarPrimitive
  | .const name _ => ofName? name
  | .app (.app (.app (.app (.const projection [.zero, .zero, .zero])
      (.const ``UInt64 [])) (.const ``UInt64 [])) (.const ``UInt64 []))
      (.app (.app (.const adapter [.zero]) (.const ``UInt64 [])) (.const instanceName [])) =>
    ofClass? (projection, adapter, instanceName)
  | _ => none

theorem source_meaning (p : ScalarPrimitive) :
    LeanExe.Source.Scalar.Binary p.name p.denote := by
  cases p <;> constructor

theorem source_class_meaning (p : ScalarPrimitive) :
    LeanExe.Source.Scalar.ClassBinary p.classNames p.denote := by
  cases p <;> constructor

theorem ofHead_sound {head : Lean.Expr} {p : ScalarPrimitive}
    (h : ofHead? head = some p) : LeanExe.Source.Scalar.Head head p.denote := by
  unfold ofHead? at h
  split at h
  · rename_i name levels
    have meaning := p.source_meaning
    rw [ofName_sound h] at meaning
    exact .direct meaning
  · have meaning := p.source_class_meaning
    rw [ofClass_sound h] at meaning
    exact .canonical meaning
  · contradiction

end LeanExe.Extract.Core.ScalarPrimitive

namespace LeanExe.Extract.Core

theorem sourceHead_recognized {head : Lean.Expr} {f : UInt64 → UInt64 → UInt64}
    (h : LeanExe.Source.Scalar.Head head f) :
    ∃ p : ScalarPrimitive, ScalarPrimitive.ofHead? head = some p ∧ p.denote = f := by
  cases h with
  | direct operation =>
    cases operation
    all_goals first
      | exact ⟨.add, by rfl, rfl⟩
      | exact ⟨.sub, by rfl, rfl⟩
      | exact ⟨.mul, by rfl, rfl⟩
      | exact ⟨.div, by rfl, rfl⟩
      | exact ⟨.mod, by rfl, rfl⟩
      | exact ⟨.land, by rfl, rfl⟩
      | exact ⟨.lor, by rfl, rfl⟩
      | exact ⟨.xor, by rfl, rfl⟩
      | exact ⟨.shiftLeft, by rfl, rfl⟩
      | exact ⟨.shiftRight, by rfl, rfl⟩
  | canonical operation =>
    cases operation
    all_goals first
      | exact ⟨.add, by rfl, rfl⟩
      | exact ⟨.sub, by rfl, rfl⟩
      | exact ⟨.mul, by rfl, rfl⟩
      | exact ⟨.div, by rfl, rfl⟩
      | exact ⟨.mod, by rfl, rfl⟩
      | exact ⟨.land, by rfl, rfl⟩
      | exact ⟨.lor, by rfl, rfl⟩
      | exact ⟨.xor, by rfl, rfl⟩
      | exact ⟨.shiftLeft, by rfl, rfl⟩
      | exact ⟨.shiftRight, by rfl, rfl⟩

end LeanExe.Extract.Core
