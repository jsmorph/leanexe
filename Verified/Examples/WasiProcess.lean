import Verified.Wasi.ReflectCommand
import Verified.Wasi.ProcessCode
import LeanExe.Encoding.RoundTrip

namespace Verified.Examples.WasiProcess

open LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi

instance : Flat (ProcessStep UInt64) (Bool × UInt64 × UInt64) :=
  ⟨fun result => (result.running, result.status, result.state)⟩

def begin : Action (ProcessStep UInt64) := pure ⟨true, 0, 0⟩

def step (state : UInt64) : Action (ProcessStep UInt64) := do
  if state == 3 then pure ⟨false, 0, state⟩
  else
    let result ← writeStdoutSome (Bytes.build 1 fun _ => state + 65)
    if result.errno != 0 then pure ⟨false, result.errno, state⟩
    else pure ⟨true, 0, state + 1⟩

verified_compile_wasi compiled := [begin, step]

def entry : ProcessEntry [compiled.step.func.sig, compiled.begin.func.sig] :=
  { state := .word
    beginName := "begin"
    stepName := "step"
    begin := compiled.begin.callee
    step := compiled.step.callee }

def module : Wasm.Module :=
  compileProcess compiled.pure.module compiled.program entry compiled.literalPool

theorem bytes : ∃ bytes, Wasm.Encoding.encode module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok module :=
  Wasm.Encoding.round_trip module (by decide +kernel) (by decide +kernel)

#guard module.exports.map Wasm.Export.name = ["_start"]

end Verified.Examples.WasiProcess
