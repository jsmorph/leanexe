import LeanExe.Extract.ScalarBindings

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Captured bindings match before and after allocating any later local suffix. -/
def SequenceBindingsMatch (locals : List ScalarBinding) (values : List Value)
    (saved : List UInt64) : Prop :=
  ∀ suffix, ScalarBindingsMatch locals values (saved ++ suffix)

theorem SequenceBindingsMatch.extend {locals : List ScalarBinding} {values : List Value}
    {saved : List UInt64} (matched : SequenceBindingsMatch locals values saved) (earlier : List UInt64) :
    SequenceBindingsMatch locals values (saved ++ earlier) := by
  intro suffix
  simpa only [List.append_assoc] using matched (earlier ++ suffix)

/-- A completed computation's local remains available to every later computation. -/
theorem SequenceBindingsMatch.result {locals : List ScalarBinding} {values : List Value}
    {saved : List UInt64} {index : Nat} {value : UInt64}
    (matched : SequenceBindingsMatch locals values saved)
    (present : saved[index]? = some value) :
    SequenceBindingsMatch (.word (.local index) :: locals) (.word value :: values) saved := by
  intro suffix
  apply (matched suffix).cons
  apply LeanExe.IR.Expr.ScalarEval.local
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
  exact present

/-- A saved Boolean keeps its native flag and zero/one representation. -/
theorem SequenceBindingsMatch.booleanResult {locals : List ScalarBinding} {values : List Value}
    {saved : List UInt64} {index : Nat} {flag : Bool}
    (matched : SequenceBindingsMatch locals values saved)
    (present : saved[index]? = some flag.toUInt64) :
    SequenceBindingsMatch (.boolean (.local index) :: locals) (.boolean flag :: values) saved := by
  intro suffix
  apply (matched suffix).cons
  apply LeanExe.IR.Expr.ScalarEval.local
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
  exact present

end LeanExe.Extract.Core
