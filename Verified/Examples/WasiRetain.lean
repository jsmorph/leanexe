import Verified.Wasi.ReflectCommand

namespace Verified.Examples.WasiRetain

open LeanExe LeanExe.Wasi Verified.Wasi

def retain : Action Bytes :=
  loop 2 bytes![] (fun _ _ => true) fun _ previous => do
    let next ← readSome 1
    let _ ← writeStdoutSome previous
    pure next.bytes

verified_compile_wasi compiled := [retain]

def step : Command [] [] [.bytes, .word] (.value .bytes) :=
  .bind (.read (.word 1))
    (.bind (.write .stdout (.there .here))
      (.ret (.letPair (.var (.there .here)) (.var .here))))

def body : Command [] [] [] (.value .bytes) :=
  .loop (.word 2) (.bytesLiteral []) (.bool true) step

theorem source_body : compiled.retain.func.body = body := by rfl

#guard compiled.retain.func.params = []
#guard compiled.module.exports.map Wasm.Export.name = ["alloc", "release", "retain"]

end Verified.Examples.WasiRetain
