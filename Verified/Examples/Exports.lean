module

public import Verified.Reflect.Command

@[expose] public section

/-!
A test of the option `(exports := …)` of `verified_compile`.  `quot` divides 1000 with Lean's
convention at a zero divisor, `checkedQuot` returns a status for a zero divisor and the quotient
otherwise, and `scaleWith` and its wrapper `scale` multiply each element of an array by the word of
the table `factor`.  The module of `compiled` exports `alloc`, `release`, `checkedQuot`, and
`scale`, and it keeps the functions and indices of the module without the option, whose exports
`all` lists.  The theorems of every definition hold of the restricted module: `checkedQuot_claims`
derives the status from `compiled.checkedQuot.trapFree`, and `quot_claims` uses the theorem of the
definition that the module does not export.  `literals` compiles a program with a byte literal,
whose theorems are `ImplementsStatic`, and exports `lookupMod` alone.
-/

namespace Verified.Examples.Exports

open LeanExe LeanExe.Pipeline

/-- 1000 divided by `b`, with Lean's convention at a zero divisor: `quot 0 = 0`. -/
def quot (b : UInt64) : UInt64 := 1000 / b

/-- Status 1 and 0 for a zero divisor, else status 0 and the quotient. -/
def checkedQuot (b : UInt64) : UInt64 × UInt64 :=
  if b == 0 then (1, 0) else (0, quot b)

/-- A table of one word. -/
def factor : Array UInt64 := #[3]

/-- The elements of `xs`, each times the first word of `t`. -/
def scaleWith (t : Array UInt64) (xs : Array UInt64) : Array UInt64 :=
  LeanExe.build xs.size.toUInt64 fun i => xs[i.toNat]! * t[(0 : UInt64).toNat]!

/-- `scaleWith` over `factor`. -/
def scale (xs : Array UInt64) : Array UInt64 := scaleWith factor xs

verified_compile (exports := [checkedQuot, scale]) compiled := [quot, checkedQuot, scaleWith, scale]

verified_compile all := [quot, checkedQuot, scaleWith, scale]

#guard compiled.module.exports.map (fun e => (e.name, e.funcIdx)) ==
  [("alloc", 0), ("release", 1), ("checkedQuot", 3), ("scale", 5)]
#guard all.module.exports.map (fun e => (e.name, e.funcIdx)) ==
  [("alloc", 0), ("release", 1), ("quot", 2), ("checkedQuot", 3), ("scaleWith", 4), ("scale", 5)]

/-- An exported function's theorem without a trap, with its status in the postcondition. -/
theorem checkedQuot_claims :
    ImplementsA false compiled.module 3 checkedQuot (fun _ _ _ => True)
      (fun b _ _ _ _ => (checkedQuot b).1 = if b == 0 then 1 else 0) :=
  compiled.checkedQuot.trapFree.mono (fun _ _ _ h => h) fun b _ _ _ _ _ _ => by
    cases h : b == 0 <;> simp [checkedQuot, h]

/-- The theorem of the definition that the module does not export holds at its index. -/
theorem quot_claims :
    ImplementsA false compiled.module 2 quot (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  compiled.quot.trapFree.mono (fun _ _ _ h => h) fun _ _ _ _ _ _ _ => trivial

/-- The byte at `index` of a literal of three bytes. -/
def lookup (index : UInt64) : UInt64 := (bytes![65, 0, 255]).get index

/-- `lookup` at `index % 3`. -/
def lookupMod (index : UInt64) : UInt64 := lookup (index % 3)

verified_compile (exports := [lookupMod]) literals := [lookup, lookupMod]

#guard literals.module.exports.map (fun e => (e.name, e.funcIdx)) ==
  [("alloc", 0), ("release", 1), ("lookupMod", 3)]

#print axioms Wasm.interp_exports
#print axioms Wasm.execOne_exports
#print axioms Wasm.exec_exports
#print axioms Wasm.run_exports
#print axioms Wasm.Runs.exports
#print axioms LeanExe.ProofKit.aligned_exports
#print axioms LeanExe.ProofKit.alignedRun_exports
#print axioms LeanExe.Pipeline.ImplementsA.selectExports
#print axioms LeanExe.Pipeline.ImplementsAligned.selectExports
#print axioms Verified.ImplementsTables.selectExports
#print axioms Verified.ImplementsTablesAligned.selectExports
#print axioms Verified.ImplementsStatic.selectExports
#print axioms compiled.checkedQuot.implements
#print axioms compiled.checkedQuot.trapFree
#print axioms compiled.checkedQuot.aligned
#print axioms compiled.scale.implements
#print axioms compiled.scale.trapFree
#print axioms compiled.quot.implements
#print axioms compiled.initial
#print axioms compiled.bytes
#print axioms compiled.scale.aligned
#print axioms literals.lookupMod.implements
#print axioms literals.lookup.trapFree
#print axioms literals.initial
#print axioms literals.bytes
#print axioms checkedQuot_claims
#print axioms quot_claims

end Verified.Examples.Exports
