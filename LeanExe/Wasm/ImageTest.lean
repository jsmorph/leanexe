import LeanExe.Wasm.Image

namespace LeanExe.Wasm.ImageTest

open LeanExe.Wasm
open LeanExe.Wasm.Image

def allInstructions : List Instr :=
  [.constI64 18446744073709551615,
   .constI32 4294967295,
   .constI32NegOne,
   .localGet 0,
   .localSet 1,
   .localTee 2,
   .globalGet 0,
   .globalSet 1,
   .call 3,
   .addI64,
   .subI64,
   .mulI64,
   .divUI64,
   .remUI64,
   .andI64,
   .orI64,
   .xorI64,
   .shlI64,
   .shrUI64,
   .eqI64,
   .neI64,
   .ltUI64,
   .leUI64,
   .geUI64,
   .eqzI64,
   .eqI32,
   .eqzI32,
   .andI32,
   .wrapI64,
   .extendUI32,
   .load64,
   .load32,
   .load8U,
   .store64,
   .store32,
   .store8,
   .memorySize,
   .memoryGrow,
   .unreachable,
   .ret,
   .drop,
   .block [.constI64 1, .drop],
   .loop [.brIf 0, .br 0],
   .iff true [.constI64 2] (some [.constI64 3]),
   .iff false [] none,
   .iffI32 [.constI32 4] (some [.constI32NegOne]),
   .br 1,
   .brIf 2]

def sample : Module :=
  { memoryMinPages := 16
    globals := #[{ mutable_ := true, initial := 4096 },
      { mutable_ := false, initial := 18446744073709551615 }]
    functions := #[{ params := 3, results := 2, locals := 8, body := allInstructions }]
    exports := #[{ name := "memory".toUTF8, kind := .memory, index := 0 },
      { name := "run".toUTF8, kind := .func, index := 0 },
      { name := "counter".toUTF8, kind := .global, index := 1 }] }

def isOkModule (expected : Module) : Except ByteArray Module → Bool
  | Except.ok actual => actual == expected
  | Except.error _ => false

def isError (expected : ByteArray) : Except ByteArray Module → Bool
  | Except.error actual => actual == expected
  | Except.ok _ => false

#guard isOkModule sample (decodeModule (encodeModule sample))

#guard isError errorTruncated (decodeModule ByteArray.empty)

#guard isError errorTrailing (decodeModule (encodeModule sample |>.push 0))

def badVersion : ByteArray :=
  magic ++ encodeU64 2

#guard isError errorVersion (decodeModule badVersion)

def badProfile : ByteArray :=
  magic ++ encodeU64 schemaVersion ++ encodeU64 2

#guard isError errorProfile (decodeModule badProfile)

def badInteger : ByteArray :=
  magic ++ (ByteArray.empty.push 129 |>.push 0)

#guard isError errorNoncanonicalInteger (decodeModule badInteger)

def overflowingInteger : ByteArray :=
  magic ++ ByteArray.mk #[128, 128, 128, 128, 128, 128, 128, 128, 128, 2]

#guard isError errorInteger (decodeModule overflowingInteger)

def tooManyGlobals : ByteArray :=
  magic ++ encodeU64 schemaVersion ++ encodeU64 libraryProfile ++
    encodeNat 16 ++ encodeNat (maxGlobals + 1)

#guard isError errorLimit (decodeModule tooManyGlobals)

def badTag : ByteArray :=
  magic ++ encodeU64 schemaVersion ++ encodeU64 libraryProfile ++
    encodeNat 16 ++ encodeNat 0 ++ encodeNat 1 ++
    encodeNat 0 ++ encodeNat 0 ++ encodeNat 0 ++ encodeNat 1 ++ encodeNat 99 ++
    encodeNat 0

#guard isError errorInstructionTag (decodeModule badTag)

def badExportName : Module :=
  { memoryMinPages := 1
    globals := #[]
    functions := #[]
    exports := #[{ name := ByteArray.empty.push 255, kind := .memory, index := 0 }] }

#guard isError errorExportName (decodeModule (encodeModule badExportName))

end LeanExe.Wasm.ImageTest
