import Armv9rat
import Interpreter.Wasm.Float
import TestSupport.A64.FpVectors

/-!
Runs the vectors of F4's test (`tests/TestSupport/A64/FpVectors.lean`) through the model's
FPAdd, FPSub, FPMul, FPDiv, and FixedToFP at 64 bits under FPCR 0x02000000, with exact rationals
for the specification's real numbers (RatReal.lean), and compares each result with Talos's
function.  `vectors SEED COUNT` draws the same operand words as the Image of `a64-fpvectors gen
SEED COUNT`.  The file `FILE` receives one line a vector, `FORM CLASS A B TALOS MODEL` in
hexadecimal, with `-` for FPSqrt's model result, which the rational evaluation does not compute.
The run evaluates the forms named in `forms` and prints each class's counts.  The `#eval` at the
end draws 200,000 vectors of each form from seed 3 and writes `tmp/sail/vectors.txt`, the input of
`emu/check.sh`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9rat Armv9rat.Functions
open TestSupport.A64 TestSupport.A64.Fp

namespace F7Vectors

abbrev State := SequentialState RegisterType trivialChoiceSource

def emptyState : State := ⟨∅, (), ∅, (), 0, #[]⟩

/-- The registers that `sail_model_init` sets, with FEAT_AA64EL0 and FEAT_AA64EL1 added. -/
def configure : SailM Unit := do
  sail_model_init ()
  let v ← readReg Register.FeatureImpl
  let v := v.setIfInBounds (num_of_Feature .FEAT_AA64EL0).toNat true
  let v := v.setIfInBounds (num_of_Feature .FEAT_AA64EL1).toNat true
  writeReg Register.FeatureImpl v

def initState : Except String State :=
  match configure.run emptyState with
  | .ok _ s => .ok s
  | .error e _ => .error s!"configure: {e.print}"

def fpcr : BitVec 64 := 0x02000000#64

def run (s : State) (m : SailM (BitVec 64)) : Except String UInt64 :=
  match m.run s with
  | .ok r _ => pure (UInt64.ofNat r.toNat)
  | .error e _ => throw e.print

def bv (x : UInt64) : BitVec 64 := BitVec.ofNat 64 x.toNat

/-- The model's result for a form, or none for FPSqrt. -/
def model (s : State) (f : Form) (a b : UInt64) : Option (Except String UInt64) :=
  match f with
  | .fadd => some (run s (FPAdd (bv a) (bv b) fpcr))
  | .fsub => some (run s (FPSub (bv a) (bv b) fpcr))
  | .fmul => some (run s (FPMul (bv a) (bv b) fpcr))
  | .fdiv => some (run s (FPDiv (bv a) (bv b) fpcr))
  | .fsqrt => none
  | .ucvtf => some (run s (FixedToFP (bv a) 0 true fpcr .FPRounding_TIEEVEN 64))

def talos (f : Form) (a b : UInt64) : UInt64 :=
  match f with
  | .fadd => Wasm.f64Add a b
  | .fsub => Wasm.f64Sub a b
  | .fmul => Wasm.f64Mul a b
  | .fdiv => Wasm.f64Div a b
  | .fsqrt => Wasm.f64Sqrt a
  | .ucvtf => Wasm.f64ConvertI64U a

def hex (x : UInt64) : String :=
  let d := String.ofList (Nat.toDigits 16 x.toNat)
  "".pushn '0' (16 - d.length) ++ d

def word (data : ByteArray) (i : Nat) : UInt64 :=
  (List.range 8).foldl (fun acc k => acc ||| ((data.get! (i + k)).toUInt64 <<< (8 * k).toUInt64)) 0

def main (seed : UInt64) (count : Nat) (forms : List String) (file : String) : IO Unit := do
  let s ← IO.ofExcept initState
  let (data, blocks) := vectors seed count
  let h ← IO.FS.Handle.mk file .write
  let mut pos := 0
  let mut bad := 0
  for blk in blocks do
    let stride := if blk.form.binary then 16 else 8
    if !forms.contains blk.form.name then
      pos := pos + blk.count * stride
      continue
    let mut diff := 0
    let mut errs := 0
    for _ in [0:blk.count] do
      let a := word data pos
      let b := if blk.form.binary then word data (pos + 8) else 0
      pos := pos + stride
      let t := talos blk.form a b
      let m := model s blk.form a b
      let col ← match m with
        | none => pure "-"
        | some (.ok r) =>
          if r != t then
            if diff < 5 then
              IO.println s!"differ: {blk.form.name} {blk.cls} {hex a} {hex b}: model {hex r}, Talos {hex t}"
            diff := diff + 1
          pure (hex r)
        | some (.error e) =>
          if errs < 5 then IO.println s!"error: {blk.form.name} {blk.cls} {hex a} {hex b}: {e}"
          errs := errs + 1
          pure "error"
      h.putStrLn s!"{blk.form.name} {blk.cls} {hex a} {hex b} {hex t} {col}"
    bad := bad + diff + errs
    let what := if blk.form == .fsqrt then "not evaluated" else s!"{diff} differences, {errs} errors"
    IO.println s!"{blk.form.name} {blk.cls}: {blk.count} vectors, {what}"
  IO.println (if bad == 0 then "all agree" else s!"{bad} disagreements")

end F7Vectors

#eval F7Vectors.main 3 200000 ["fadd", "fsub", "fmul", "fdiv", "fsqrt", "ucvtf"]
  "tmp/sail/vectors.txt"
