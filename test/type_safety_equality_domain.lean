import LeanExe.TypeSafety

/-!
Equality admission checks all type components. Inhabited values, constructor
selection, and empty runtime arrays cannot hide a recursive or invalid type.
Global declaration formation remains a separate obligation.
-/
namespace LeanExe.TypeSafety.EqualityDomainTests

example : equalitySupported [] .unit = true := by rfl
example : equalitySupported [] .bool = true := by rfl
example : equalitySupported [] .nat64 = true := by rfl
example : equalitySupported [] (.word .w8) = true := by rfl
example : equalitySupported [] (.word .w32) = true := by rfl
example : equalitySupported [] (.word .w64) = true := by rfl
example : equalitySupported [] (.array (.prod .bool (.sum .unit (.word .w8)))) = true := by rfl
example : equalitySupported [] (.data 0) = false := by rfl
example : equalitySupported [] (.sum .unit (.data 0)) = false := by rfl
example : equalitySupported [] (.array (.data 0)) = false := by rfl

-- Empty declarations have no problematic fields; this does not prove inhabitance.
example : equalitySupported [[]] (.data 0) = true := by rfl
example : equalitySupported [[[]]] (.data 0) = true := by rfl
example : equalitySupported [[[.nat64, .bool]]] (.data 0) = true := by rfl
example : equalitySupported [[[.nat64], [.array (.word .w8)]]] (.data 0) = true := by rfl

-- Every constructor is checked, even when another one is nullary.
def natList : DataDecls := [[[], [.nat64, .data 0]]]
def hiddenArrayCycle : DataDecls := [[[], [.array (.data 0)]]]
def cycle : DataDecls := [[[.data 1]], [[.data 2]], [[.data 0]]]
example : declarationsWellFormed natList = true := by rfl
example : equalitySupported natList (.data 0) = false := by rfl
example : equalitySupported hiddenArrayCycle (.data 0) = false := by rfl
example : equalitySupported cycle (.data 0) = false := by rfl
example : equalitySupported cycle (.data 1) = false := by rfl
example : equalitySupported cycle (.data 2) = false := by rfl
example : equalitySupported [[[.prod .unit (.data 0)]]] (.data 0) = false := by rfl
example : equalitySupported [[[.sum .unit (.data 0)]]] (.data 0) = false := by rfl

-- The bound must permit a chain spanning the entire declaration table.
def forwardChain : DataDecls := [[[.data 1]], [[.data 2]], [[.data 3]], [[.nat64]]]
def backwardChain : DataDecls := [[[.nat64]], [[.data 0]], [[.data 1]], [[.data 2]]]
example : equalitySupported forwardChain (.data 0) = true := by rfl
example : equalitySupported backwardChain (.data 3) = true := by rfl
example : equalitySupported forwardChain (.array (.prod (.data 0) (.data 1))) = true := by rfl

-- Unrelated cycles do not invalidate an acyclic queried type.
def mixed : DataDecls := [[[.data 0]], [[.nat64]], [[.data 1, .array (.data 1)]]]
example : equalitySupported mixed (.data 0) = false := by rfl
example : equalitySupported mixed (.data 1) = true := by rfl
example : equalitySupported mixed (.data 2) = true := by rfl
example : equalitySupported mixed (.prod (.data 1) (.data 0)) = false := by rfl

-- Local equality admission is not the global program formation check.
def malformed : DataDecls := [[[.data 99]], [[.bool]]]
example : declarationsWellFormed malformed = false := by rfl
example : equalitySupported malformed .unit = true := by rfl
example : equalitySupported malformed (.data 0) = false := by rfl
example : equalitySupported malformed (.data 1) = true := by rfl
example : equalitySupported malformed (.data 99) = false := by rfl
example : equalitySupported [[[], [.data 99]]] (.data 0) = false := by rfl

-- The checker is connected to the independent domain judgment, not its definition.
example : EqTy forwardChain (.data 0) := equalitySupported_iff.mp rfl
example : ¬ EqTy natList (.data 0) := by
  intro admitted
  have impossible := equalitySupported_iff.mpr admitted
  cases impossible
example : TyWF mixed (.data 2) :=
  (equalitySupported_iff.mp (show equalitySupported mixed (.data 2) = true from rfl)).wellFormed

end LeanExe.TypeSafety.EqualityDomainTests
