module

public import Lean
public import LeanExe.Native.Translate

@[expose] public section

/-!
The loading of a module constant that `native-verified` and `native-bare` share.  `loadCap`
imports the compiled Lean module that defines the constant, evaluates the constant, and reads the
pages of `lx_mem` of the translation that `verified_compile` states its theorems about.
-/

open Lean LeanExe.Native

unsafe def loadEnv (moduleName constName : Name) : IO (Environment × Wasm.Module) := do
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := moduleName, importAll := false, isExported := true, isMeta := true }] {}
  return (env, ← IO.ofExcept <| env.evalConst Wasm.Module {} constName)

unsafe def loadModule (moduleName constName : Name) : IO Wasm.Module :=
  return (← loadEnv moduleName constName).2

/-- The number that `e` denotes, a raw literal or an `OfNat.ofNat` of one. -/
partial def natValue? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e => if e.isAppOfArity ``OfNat.ofNat 3 then natValue? (e.getArg! 1) else none

/-- The pages of `lx_mem` in the translation that `verified_compile` states its theorems about for
the module `constName`, `p.module`: the first argument of `translate` in `p.translation_eq`,
`nativeCap` or the cap of the option `(cap := C)`.  A module without that equation takes
`nativeCap`. -/
def translationCap (env : Environment) (constName : Name) : Except String Nat := do
  let eqName := constName.getPrefix ++ `translation_eq
  let some info := env.find? eqName | return nativeCap
  let some (_, lhs, _) := info.type.consumeMData.eq? | throw s!"{eqName} is not an equation"
  unless lhs.isAppOf ``translate do throw s!"{eqName} does not state a translation"
  let cap := lhs.getArg! 0
  if cap.isConstOf ``nativeCap then return nativeCap
  match natValue? cap with
  | some n => return n
  | none => throw s!"the cap of {eqName} is not a numeral"

unsafe def loadCap (moduleName constName : Name) : IO (Environment × Wasm.Module × Nat) := do
  let (env, m) ← loadEnv moduleName constName
  return (env, m, ← IO.ofExcept (translationCap env constName))
