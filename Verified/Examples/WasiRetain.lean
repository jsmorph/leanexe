module

public import Verified.Wasi.ReflectCommand

@[expose] public section

namespace Verified.Examples.WasiRetain

open LeanExe LeanExe.Wasi Verified.Wasi

def retain : Action Bytes :=
  loop 2 (Bytes.build 1 fun _ => 0) (fun _ _ => true) fun _ previous => do
    let _ ← writeStdout previous 0 previous.size
    let next ← readStdin previous 0 1
    pure next.buffer

verified_compile_wasi compiled := [retain]

def step : Command [] [] [.bytes, .word] (.value .bytes) :=
  .bind
    (.bind (.ret (.word 0))
      (.bind (.ret (.bytesSize (.there .here)))
        (.write .stdout (.there (.there .here)) (.there .here) .here)))
    (.bind (intermediate := .value (wordsBytesTy 2))
      (.bind (.ret (.word 0))
        (.bind (.ret (.word 1)) (.read (.there (.there (.there .here))) (.there .here) .here)))
      (.letPair .here (.letPair .here (.ret (.var .here)))))

def body : Command [] [] [] (.value .bytes) :=
  .loop (.word 2) (.bytesBuild (.word 1) (.word 0)) (.bool true) step

theorem source_body : compiled.retain.func.body = body := by rfl

#guard compiled.retain.func.params = []
#guard compiled.module.exports.map Wasm.Export.name = ["alloc", "release", "retain"]

end Verified.Examples.WasiRetain
