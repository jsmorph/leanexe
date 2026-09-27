import LeanExe.Extract.ScalarFunc

namespace ExtendedMixedGuardTest

def extendedMixedJunction (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if (f (x == 0) && (x != y || f true)) ∧ x < y then x + 3 else y + 7

def extendedMixedChoice (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if x ≤ y ∨ (if x < y then f true else f false) then x + 1 else y

def extendedMixedLet (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if (let flag := f (x == 0); let word := x + flag.toUInt64; f (word != y)) ∧ x < y then x + y else x - y

def extendedMixedBind (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if x = 0 ∨ (Id.run do let flag ← pure (f (x == 0)); return f (!flag)) then x + 1 else y + 2

def extendedMixedWrapped (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let saved := decide ((Id.run (pure (f true))) ∧ x < y)
  saved.toUInt64 + x

def extendedMixedRelation (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun b : Bool => if (f b == b) ∧ x < y then f true else f false
  (g true).toUInt64 + (g false).toUInt64 + y

def rangeExtendedMixedStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != 0
    if (f (i.toUInt64 != seed) || f true) ∧ i.toUInt64 < a then break
    a := a + i.toUInt64 + 1
  return a

def rangeExtendedMixedContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => n != seed
    if a = 0 ∨ (let flag := f i.toUInt64; !flag) then
      a := a + 3
      continue
    a := a + i.toUInt64 + 1
  return a

def rangeExtendedMixedOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun n : UInt64 => n != seed
  let mut a := if (Id.run (pure (f true))) ∧ count < seed then seed + 1 else seed
  for i in [:count.toNat] do
    if (f (g i.toUInt64) != g a) ∧ a < seed then a := a + 2 else a := a + 1
  return a + (decide ((f true && g a) ∨ a = seed)).toUInt64

def rangeExtendedMixedHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => if (Id.run do let flag ← pure (f b); return f (!flag)) ∧ seed < count then !b else b
  let mut a := seed
  for i in [:count.toNat] do
    if (if a = 0 then g true else g false) ∧ i.toUInt64 < a then break
    a := a + (f (g true)).toUInt64 + 1
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end ExtendedMixedGuardTest

run_elab do
  let some info := (← Lean.getEnv).find? `ExtendedMixedGuardTest.extendedMixedLet | throwError "missing"
  let some value := info.value? | throwError "missing body"
  let .lam _ _ (.lam _ _ (.letE _ _ _ branch _ ) _) _ := value | throwError "unexpected shape"
  let args := branch.getAppArgs
  Lean.logInfo m!"condition: {args[1]!}"
  Lean.logInfo m!"evidence: {args[2]!}"
  Lean.logInfo m!"left evidence raw: {repr args[2]!.getAppArgs[2]!}"
  Lean.logInfo m!"left condition raw: {repr args[1]!.getAppArgs[0]!}"
  let parsed := LeanExe.Extract.Core.guardOperands? args[1]!
  Lean.logInfo m!"parsed: {repr parsed}"
  if let some guard := parsed then
    Lean.logInfo m!"evidence matches: {LeanExe.Extract.Core.guardDecision? guard args[2]!}"
    Lean.logInfo m!"canonical evidence: {guard.evidence}"

run_elab do
  for name in [`ExtendedMixedGuardTest.extendedMixedJunction, `ExtendedMixedGuardTest.extendedMixedChoice,
      `ExtendedMixedGuardTest.extendedMixedLet, `ExtendedMixedGuardTest.extendedMixedBind,
      `ExtendedMixedGuardTest.extendedMixedWrapped, `ExtendedMixedGuardTest.extendedMixedRelation,
      `ExtendedMixedGuardTest.rangeExtendedMixedStep, `ExtendedMixedGuardTest.rangeExtendedMixedContinue,
      `ExtendedMixedGuardTest.rangeExtendedMixedOuter, `ExtendedMixedGuardTest.rangeExtendedMixedHelper] do
    let some info := (← Lean.getEnv).find? name | throwError "missing"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type (info.value?.get!)).isSome}"
