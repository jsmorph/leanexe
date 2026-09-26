import LeanExe.Extract.Core
namespace NarrowProbes
def byte (bytes : ByteArray) : UInt32 := bytes[0]!.toUInt32
def add (bytes : ByteArray) : UInt32 := (0x7f800000 : UInt32) + bytes[0]!.toUInt32
def addLocal (bytes : ByteArray) : UInt32 :=
  let value := bytes[0]!.toUInt32
  0x7f800000 + value
def word (bytes : ByteArray) : UInt64 := (0x7ff0000000000000 : UInt64) + bytes[0]!.toUInt64
def addByte (x y : UInt8) : UInt8 := x + y
def add32 (x y : UInt32) : UInt32 := x + y
end NarrowProbes
set_option pp.all true in
run_elab do
  let env ← Lean.getEnv
  for name in [`NarrowProbes.byte, `NarrowProbes.add, `NarrowProbes.addLocal,
      `NarrowProbes.word, `NarrowProbes.addByte, `NarrowProbes.add32] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {value}"
    Lean.logInfo m!"compile: {(LeanExe.Extract.Core.compileEnvironment env `NarrowProbes name).map (fun _ => true)}"
