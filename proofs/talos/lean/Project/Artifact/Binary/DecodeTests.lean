import Project.Artifact.Binary.Decode

namespace Wasm.Binary.Tests

private def bytes (values : List Nat) : ByteArray :=
  values.map UInt8.ofNat |>.toByteArray

private def header : List Nat :=
  [0, 97, 115, 109, 1, 0, 0, 0]

private def resultEq [BEq α] : Except Error α → Except Error α → Bool
  | .ok left, .ok right => left == right
  | .error left, .error right => decide (left = right)
  | _, _ => false

example : resultEq (decode (bytes header)) (.ok default) = true := by
  native_decide

example : resultEq (decode (bytes [0, 97, 115, 110, 1, 0, 0, 0]))
    (.error { offset := 3, kind := .expectedByte 109 110 }) = true := by
  native_decide

example : resultEq (decode (bytes (header ++ [2, 0])))
    (.error { offset := 9, kind := .unsupportedSection 2 }) = true := by
  native_decide

example : resultEq (decode (bytes (header ++ [1, 1, 0, 1, 1, 0])))
    (.error { offset := 12, kind := .duplicateSection .type }) = true := by
  native_decide

example : resultEq (decode (bytes (header ++ [3, 1, 0, 1, 1, 0])))
    (.error { offset := 12, kind := .sectionOutOfOrder .type }) = true := by
  native_decide

example : resultEq (decode (bytes (header ++ [1, 2, 0])))
    (.error { offset := 10, kind := .unexpectedEnd }) = true := by
  native_decide

example : resultEq (Parser.runAll expression (bytes [2, 64, 65, 1, 11, 11]))
    (.ok [.block .empty [.i32Const 1]]) = true := by
  native_decide

example : resultEq
    (Parser.runAll expression (bytes [4, 126, 66, 1, 5, 66, 2, 11, 11]))
    (.ok [.iff (.value .i64) [.i64Const 1] (some [.i64Const 2])]) = true := by
  native_decide

example : resultEq (Parser.runAll expression (bytes [255, 11]))
    (.error { offset := 1, kind := .unsupportedOpcode 255 }) = true := by
  native_decide

example : resultEq
    (Parser.runAll expression (bytes [160, 162, 189, 191, 11]))
    (.ok [.f64Add, .f64Mul, .i64ReinterpretF64, .f64ReinterpretI64]) = true := by
  native_decide

example : resultEq (Parser.runAll valType (bytes [124]))
    (.error { offset := 1, kind := .unsupportedType 124 }) = true := by
  native_decide

example : resultEq (Parser.runAll blockType (bytes [124]))
    (.error { offset := 1, kind := .unsupportedType 124 }) = true := by
  native_decide

example : resultEq (Parser.runAll expression (bytes [68, 11]))
    (.error { offset := 1, kind := .unsupportedOpcode 68 }) = true := by
  native_decide

end Wasm.Binary.Tests
