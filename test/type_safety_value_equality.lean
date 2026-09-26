import LeanExe.TypeSafety

/-!
Raw comparison regressions. These do not assert source admission: the comparison
is total even on untyped values and values containing out-of-range literals.
-/
namespace LeanExe.TypeSafety.ValueEqualityTests

-- Scalar tags and widths remain observable, even when numeric payloads agree.
example : valueEq .unit (.bool false) = false := by rfl
example : valueEq (.nat 0) (.word .w64 0) = false := by rfl
example : valueEq (.word .w8 7) (.word .w32 7) = false := by rfl
example : valueEq (.word .w64 (nat64Limit - 1))
    (.word .w64 (nat64Limit - 1)) = true := by rfl
example : valueEq (.word .w8 256) (.word .w8 0) = false := by rfl
example : valueEq (.word .w8 256) (.word .w8 256) = true := by rfl
example : valueEq (.nat nat64Limit) (.nat nat64Limit) = true := by rfl

-- Ordered fields, tags, lengths, and nested contents all affect equality.
example : valueEq (.pair (.nat 1) (.nat 2)) (.pair (.nat 2) (.nat 1)) = false := by rfl
example : valueEq (.inl .unit) (.inr .unit) = false := by rfl
example : valueEq (.array []) .unit = false := by rfl
example : valueEq (.array [.nat 1, .nat 2]) (.array [.nat 1]) = false := by rfl
example : valueEq (.array [.nat 1]) (.array [.nat 1, .nat 2]) = false := by rfl
example : valueEq (.array [.nat 1, .nat 2]) (.array [.nat 2, .nat 1]) = false := by rfl
example : valueEq (.array [.array [.inl (.bool true)]])
    (.array [.array [.inl (.bool false)]]) = false := by rfl
example : valueEq (.array [.array [.inl (.bool true)]])
    (.array [.array [.inl (.bool true)]]) = true := by rfl

-- Nominal identity is not erased by identical layouts or constructor numbers.
example : valueEq (.data 0 0 []) (.data 1 0 []) = false := by rfl
example : valueEq (.data 0 0 []) (.data 0 1 []) = false := by rfl
example : valueEq (.data 0 0 []) (.data 0 0 [.unit]) = false := by rfl
example : valueEq (.data 0 0 [.nat 1, .nat 2])
    (.data 0 0 [.nat 2, .nat 1]) = false := by rfl
example : valueEq (.data 99 88 [.unit]) (.data 99 88 [.unit]) = true := by rfl

-- Finite recursive values can be compared; this does not admit recursive EqTy.
def chain : Nat → Value
  | 0 => .data 0 0 []
  | n + 1 => .data 0 1 [.nat n, chain n]
example : valueEq (chain 8) (chain 8) = true := by rfl
example : valueEq (chain 8) (chain 7) = false := by rfl
example : valueEq (.array [chain 8, chain 7]) (.array [chain 8, chain 6]) = false := by rfl
example : valuesEq [.unit, .bool true] [.unit, .bool true] = true := by rfl
example : valuesEq [.unit, .bool true] [.unit, .bool false] = false := by rfl

end LeanExe.TypeSafety.ValueEqualityTests
