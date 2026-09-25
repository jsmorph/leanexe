import LeanExe.Extract.ScalarPrimitive
import LeanExe.Extract.ScalarDo
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
      leftType) rightType) resultType)
      (.app (.app (.const adapter [.zero]) instanceType) (.const instanceName [])) =>
    do
      let _ ← scalarResultType? leftType
      let _ ← scalarResultType? rightType
      let _ ← scalarResultType? resultType
      let _ ← scalarResultType? instanceType
      ofClass? (projection, adapter, instanceName)
  | _ => none

theorem source_meaning (p : ScalarPrimitive) :
    LeanExe.Source.Scalar.Binary p.name p.denote := by
  cases p <;> constructor

theorem source_class_meaning (p : ScalarPrimitive) :
    LeanExe.Source.Scalar.ClassBinary p.classNames p.denote := by
  cases p <;> constructor

@[simp] theorem ofHead_class (p : ScalarPrimitive) (result left right instanceType : LeanExe.Source.Scalar.ResultType) :
    ofHead? (LeanExe.Source.Scalar.classHead p.classNames result left right instanceType) = some p := by
  cases p <;> simp [ofHead?, LeanExe.Source.Scalar.classHead, classNames, ofClass?, all]

theorem ofHead_sound {head : Lean.Expr} {p : ScalarPrimitive}
    (h : ofHead? head = some p) : LeanExe.Source.Scalar.Head head p.denote := by
  unfold ofHead? at h
  split at h
  · rename_i name levels
    have meaning := p.source_meaning
    rw [ofName_sound h] at meaning
    exact .direct meaning
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨left, foundLeft, right, foundRight, result, foundResult, instanceType, foundInstance, matched⟩ := h
    have meaning := p.source_class_meaning
    rw [ofClass_sound matched] at meaning
    rw [scalarResultType_sound foundLeft, scalarResultType_sound foundRight,
      scalarResultType_sound foundResult, scalarResultType_sound foundInstance]
    exact .canonical meaning result left right instanceType
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
  | canonical operation result left right instanceType =>
    cases operation
    all_goals first
      | exact ⟨.add, ScalarPrimitive.ofHead_class .add result left right instanceType, rfl⟩
      | exact ⟨.sub, ScalarPrimitive.ofHead_class .sub result left right instanceType, rfl⟩
      | exact ⟨.mul, ScalarPrimitive.ofHead_class .mul result left right instanceType, rfl⟩
      | exact ⟨.div, ScalarPrimitive.ofHead_class .div result left right instanceType, rfl⟩
      | exact ⟨.mod, ScalarPrimitive.ofHead_class .mod result left right instanceType, rfl⟩
      | exact ⟨.land, ScalarPrimitive.ofHead_class .land result left right instanceType, rfl⟩
      | exact ⟨.lor, ScalarPrimitive.ofHead_class .lor result left right instanceType, rfl⟩
      | exact ⟨.xor, ScalarPrimitive.ofHead_class .xor result left right instanceType, rfl⟩
      | exact ⟨.shiftLeft, ScalarPrimitive.ofHead_class .shiftLeft result left right instanceType, rfl⟩
      | exact ⟨.shiftRight, ScalarPrimitive.ofHead_class .shiftRight result left right instanceType, rfl⟩

end LeanExe.Extract.Core
