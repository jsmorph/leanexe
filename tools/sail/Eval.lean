import Armv9rat
import Interpreter.Wasm.Float

/-!
Evaluates the model's FPAdd, FPSub, FPMul, FPDiv, and FixedToFP at 64 bits under FPCR
0x02000000 on concrete operands, with exact rationals for the specification's real numbers
(RatReal.lean), and compares each result with Talos's function of the same operation.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9rat Armv9rat.Functions

namespace F7Eval

abbrev State := SequentialState RegisterType trivialChoiceSource

def emptyState : State := ⟨∅, (), ∅, (), 0, #[]⟩

/-- The registers that `sail_model_init` sets, with Sail's fixed choice for unspecified values,
under which no feature is implemented, and with FEAT_AA64EL0 and FEAT_AA64EL1 added: without
AArch64, `UsingAArch32` fails its assertion.  FEAT_AFP and FEAT_SME stay absent. -/
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

def run (m : SailM (BitVec 64)) : Except String UInt64 := do
  let s ← initState
  match m.run s with
  | .ok r _ => pure (UInt64.ofNat r.toNat)
  | .error e _ => throw e.print

def bv (x : UInt64) : BitVec 64 := BitVec.ofNat 64 x.toNat

def armAdd (a b : UInt64) := run (FPAdd (bv a) (bv b) fpcr)
def armSub (a b : UInt64) := run (FPSub (bv a) (bv b) fpcr)
def armMul (a b : UInt64) := run (FPMul (bv a) (bv b) fpcr)
def armDiv (a b : UInt64) := run (FPDiv (bv a) (bv b) fpcr)
def armUcvtf (a : UInt64) := run (FixedToFP (bv a) 0 true fpcr .FPRounding_TIEEVEN 64)

def xorshift (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

/-- Pairs of random operands whose exponents differ by at most 2, and pairs of random bit
patterns, from the seed `seed`. -/
def randomPairs (seed : UInt64) (n : Nat) : List (UInt64 × UInt64) :=
  let rec go (x : UInt64) : Nat → List (UInt64 × UInt64)
    | 0 => []
    | k + 1 =>
      let a := xorshift x
      let b := xorshift a
      let c := xorshift b
      let e : UInt64 := (a >>> 52) &&& (0x7FF : UInt64)
      let e' : UInt64 := (e + c % 5 + 0x7FF - 2) % 0x7FF
      let near : UInt64 := (b &&& (0x800FFFFFFFFFFFFF : UInt64)) ||| (e' <<< (52 : UInt64))
      (a, near) :: (a, b) :: go c k
  go seed n

def specials : List UInt64 :=
  [0x0000000000000000, 0x8000000000000000, 0x0000000000000001, 0x8000000000000001,
   0x000FFFFFFFFFFFFF, 0x0010000000000000, 0x3CA0000000000000, 0x3CB8000000000000,
   0x3FB999999999999A, 0x3FC999999999999A, 0x3FF0000000000000, 0x3FF0000000000001,
   0xBFF0000000000000, 0x4000000000000000, 0x7FEFFFFFFFFFFFFF, 0xFFEFFFFFFFFFFFFF,
   0x7FF0000000000000, 0xFFF0000000000000, 0x7FF8000000000000, 0x7FF8000000000001,
   0x7FF0000000000001, 0xFFF4000000000000]

def specialPairs : List (UInt64 × UInt64) :=
  specials.flatMap fun a => specials.map fun b => (a, b)

def compare2 (name : String) (arm : UInt64 → UInt64 → Except String UInt64)
    (talos : UInt64 → UInt64 → UInt64) (pairs : List (UInt64 × UInt64)) : IO Bool := do
  let mut bad := 0
  for (a, b) in pairs do
    match arm a b with
    | .error e =>
      IO.println s!"{name} {a.toNat} {b.toNat}: error {e}"
      bad := bad + 1
    | .ok r =>
      if r != talos a b then
        if bad < 10 then
          IO.println s!"{name} {a.toNat} {b.toNat}: model {r.toNat}, Talos {(talos a b).toNat}"
        bad := bad + 1
  IO.println s!"{name}: {pairs.length} operand pairs, {bad} differences"
  return bad == 0

def compare1 (name : String) (arm : UInt64 → Except String UInt64) (talos : UInt64 → UInt64)
    (xs : List UInt64) : IO Bool := do
  let mut bad := 0
  for a in xs do
    match arm a with
    | .error e =>
      IO.println s!"{name} {a.toNat}: error {e}"
      bad := bad + 1
    | .ok r =>
      if r != talos a then
        if bad < 10 then
          IO.println s!"{name} {a.toNat}: model {r.toNat}, Talos {(talos a).toNat}"
        bad := bad + 1
  IO.println s!"{name}: {xs.length} operands, {bad} differences"
  return bad == 0

def main (n : Nat) : IO Unit := do
  let pairs := specialPairs ++ randomPairs 0x9E3779B97F4A7C15 n
  let ints := specials ++ (randomPairs 0x2545F4914F6CDD1D n).map (·.1) ++
    (List.range 64).map fun k => ((1 : UInt64) <<< k.toUInt64) + 1
  let ok ← [compare2 "FPAdd" armAdd Wasm.f64Add pairs, compare2 "FPSub" armSub Wasm.f64Sub pairs,
    compare2 "FPMul" armMul Wasm.f64Mul pairs, compare2 "FPDiv" armDiv Wasm.f64Div pairs,
    compare1 "FixedToFP" armUcvtf Wasm.f64ConvertI64U ints].mapM id
  IO.println (if ok.all id then "all agree" else "differences found")

end F7Eval

#eval F7Eval.main 5000
