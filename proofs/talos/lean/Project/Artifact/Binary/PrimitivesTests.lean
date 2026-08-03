import Project.Artifact.Binary.Primitives

namespace Wasm.Binary.Tests

deriving instance DecidableEq for Except

private def bytes (values : List Nat) : ByteArray :=
  values.map UInt8.ofNat |>.toByteArray

private def parseU32 (values : List Nat) : Except Error UInt32 :=
  Parser.runAll Leb.u32 (bytes values)

private def parseS32 (values : List Nat) : Except Error Int :=
  Parser.runAll Leb.s32 (bytes values)

example : parseU32 [0] = .ok 0 := by native_decide
example : parseU32 [127] = .ok 127 := by native_decide
example : parseU32 [128, 1] = .ok 128 := by native_decide
example : parseU32 [128, 0] = .ok 0 := by native_decide
example : parseU32 [255, 255, 255, 255, 15] = .ok 4294967295 := by native_decide

example : parseU32 [] = .error { offset := 0, kind := .unexpectedEnd } := by
  native_decide
example : parseU32 [128] = .error { offset := 1, kind := .unexpectedEnd } := by
  native_decide
example : parseU32 [128, 128, 128, 128, 16] =
    .error { offset := 5, kind := .integerOverflow 32 } := by
  native_decide
example : parseU32 [128, 128, 128, 128, 128] =
    .error { offset := 5, kind := .integerTooLong 32 } := by
  native_decide
example : parseU32 [0, 0] = .error { offset := 1, kind := .trailingBytes } := by
  native_decide

example : parseS32 [0] = .ok 0 := by native_decide
example : parseS32 [127] = .ok (-1) := by native_decide
example : parseS32 [255, 127] = .ok (-1) := by native_decide
example : parseS32 [255, 255, 255, 255, 7] = .ok 2147483647 := by
  native_decide
example : parseS32 [128, 128, 128, 128, 120] = .ok (-2147483648) := by
  native_decide
example : parseS32 [128, 128, 128, 128, 8] =
    .error { offset := 5, kind := .integerOverflow 32 } := by
  native_decide
example : parseS32 [128, 128, 128, 128, 119] =
    .error { offset := 5, kind := .integerOverflow 32 } := by
  native_decide

example : Parser.runAll name (bytes [3, 97, 98, 99]) =
    .ok { bytes := [97, 98, 99], text := "abc" } := by
  native_decide
example : Parser.runAll name (bytes [2, 195, 40]) =
    .error { offset := 3, kind := .invalidUtf8 } := by
  native_decide
example : Parser.runAll (sized (Parser.readBytes 2)) (bytes [2, 1, 2]) =
    .ok [1, 2] := by
  native_decide
example : Parser.runAll (sized (Parser.readBytes 1)) (bytes [2, 1, 2]) =
    .error { offset := 2, kind := .trailingBytes } := by
  native_decide

end Wasm.Binary.Tests
