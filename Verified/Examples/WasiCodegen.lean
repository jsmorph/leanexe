import Verified.Wasi.Program
import LeanExe.Encoding.RoundTrip

namespace Verified.Examples.WasiCodegen

open LeanExe.Wasi Verified.Wasi

private def writeBytes (output : Output) (bytes : List UInt8) :
    Command [] effectSigs context (.value .word) :=
  .bind (.ret (.bytesLiteral bytes))
    (.bind (.write output .here) (.ret (.proj .here (.snd .here))))

def writeLiteral (effectSigs : List EffectSig) : EffectFunc [] effectSigs where
  name := "writeLiteral"
  params := []
  modes := []
  result := .value .word
  body := writeBytes .stdout [65, 0, 255]

def echo (effectSigs : List EffectSig) : EffectFunc [] effectSigs where
  name := "echo"
  params := [.word]
  modes := [.borrowed]
  result := .value .word
  body := .bind (.read (.var .here))
    (.bind (.ret (.letPair (.var .here) (.var .here)))
      (.bind (.write .stdout .here) (.ret (.proj .here (.snd .here)))))

def discardRead (effectSigs : List EffectSig) : EffectFunc [] effectSigs where
  name := "discardRead"
  params := [.word]
  modes := [.borrowed]
  result := .value .word
  body := .bind (.read (.var .here)) (.ret (.word 7))

def branch (effectSigs : List EffectSig) : EffectFunc [] effectSigs where
  name := "branch"
  params := [.bool]
  modes := [.borrowed]
  result := .value .word
  body := .ite (.var .here) (writeBytes .stdout [89]) (writeBytes .stderr [78])

def wordLoop (effectSigs : List EffectSig) : EffectFunc [] effectSigs where
  name := "wordLoop"
  params := [.word]
  modes := [.borrowed]
  result := .value .word
  body := .loop (.var .here) (.word 0) (.cmp .lt (.var .here) (.word 3))
    (.bind (writeBytes .stdout [46])
      (.ret (.bin .add (.var (.there .here)) (.word 1))))

def helper (effectSigs : List EffectSig) : EffectFunc [] effectSigs where
  name := "helper"
  params := [.word]
  modes := [.borrowed]
  result := .value .word
  body := .bind (.ret (.bytesBuild (.word 1) (.var (.there .here))))
    (.bind (.write .stdout .here) (.ret (.proj .here (.snd .here))))

def bindHelper (effectSigs : List EffectSig) :
    EffectFunc [] ((helper effectSigs).sig :: effectSigs) where
  name := "bindHelper"
  params := [.word]
  modes := [.borrowed]
  result := .value .word
  body := .bind (.call .here (fun i => Fin.cases (.var .here) (fun j => Fin.elim0 j) i))
    (.ret (.bin .add (.var .here) (.var (.there .here))))

def exitCode (effectSigs : List EffectSig) : EffectFunc [] effectSigs where
  name := "exitCode"
  params := [.word]
  modes := [.borrowed]
  result := .value .word
  body := .bind (writeBytes .stdout [88]) (.exit (.var (.there .here)))

def exitMain (effectSigs : List EffectSig) : EffectFunc [] effectSigs where
  name := "exitMain"
  params := []
  modes := []
  result := .value .word
  body := .bind (writeBytes .stdout [88])
    (.bind (.exit (.word 4294967303) : Command [] effectSigs [.word] .unit)
      (writeBytes .stderr [90]))

def signatures : List EffectSig :=
  [(exitMain []).sig, (exitCode []).sig, (wordLoop []).sig, (branch []).sig,
    (discardRead []).sig, (echo []).sig, (writeLiteral []).sig, (bindHelper []).sig,
    (helper []).sig]

def program : EffectProg [] signatures :=
  .cons (exitMain _) (.cons (exitCode _) (.cons (wordLoop _) (.cons (branch _)
    (.cons (discardRead _) (.cons (echo _) (.cons (writeLiteral _)
      (.cons (bindHelper []) (.cons (helper []) .nil))))))))

def entries : List (EffectEntry signatures) :=
  [{ signature := _, callee := .here, tables := .nil },
    { signature := _, callee := .there .here, tables := .nil },
    { signature := _, callee := .there (.there .here), tables := .nil },
    { signature := _, callee := .there (.there (.there .here)), tables := .nil },
    { signature := _, callee := .there (.there (.there (.there .here))), tables := .nil },
    { signature := _, callee := .there (.there (.there (.there (.there .here)))), tables := .nil },
    { signature := _, callee := .there (.there (.there (.there (.there (.there .here))))), tables := .nil },
    { signature := _, callee := .there (.there (.there (.there (.there (.there (.there .here)))))), tables := .nil },
    { signature := _, callee := .there (.there (.there (.there (.there (.there (.there (.there .here))))))), tables := .nil }]

def pool : Bytes.LiteralPool := ⟨tablesEnd [], program.literals.eraseDups⟩

def source : Wasm.Module := compileWith Prog.nil [] [] pool

def callable : Wasm.Module := Verified.Wasi.compile source program entries none pool

def returnedCommand : Wasm.Module :=
  Verified.Wasi.compile source program []
    (some
      { name := "writeLiteral"
        tables := []
        callee := .there (.there (.there (.there (.there (.there .here))))) }) pool

def exitedCommand : Wasm.Module :=
  Verified.Wasi.compile source program []
    (some { name := "exitMain", tables := [], callee := .here }) pool

theorem covered : program.Covered pool := by
  unfold EffectProg.Covered
  decide +kernel

theorem pool_values : pool.values = [[65, 0, 255], [89], [78], [46], [88], [90]] := by
  decide +kernel

theorem callable_bytes : ∃ bytes, Wasm.Encoding.encode callable = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok callable :=
  Wasm.Encoding.round_trip callable (by decide +kernel) (by decide +kernel)

theorem returnedCommand_bytes : ∃ bytes, Wasm.Encoding.encode returnedCommand = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok returnedCommand :=
  Wasm.Encoding.round_trip returnedCommand (by decide +kernel) (by decide +kernel)

theorem exitedCommand_bytes : ∃ bytes, Wasm.Encoding.encode exitedCommand = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok exitedCommand :=
  Wasm.Encoding.round_trip exitedCommand (by decide +kernel) (by decide +kernel)

end Verified.Examples.WasiCodegen
