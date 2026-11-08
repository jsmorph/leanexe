import TestSupport.A64.CicTable

/-!
The CIC filter of `TestSupport.A64.Cic` written over `Int64`: each pass of
`Library.Numerics.Filters.Cic` with `Array Int64` for `Array UInt64`, and `cicFirst` reading the
words of the table, which stays an `Array UInt64`, as `Int64` values.  `module_eq` states that the
verified compiler gives the same module, so the same bytes and the same AArch64 Image, as for the
filter over words: an `Int64` is its word, and its sums, differences, and literal 0 are the word
operations and the word 0.
-/

namespace TestSupport.A64.CicSigned

def integratePass (xs : Array Int64) : Array Int64 :=
  (xs.foldl (fun (state : Int64 × Array Int64) x =>
    let sum := state.1 + x
    (sum, state.2.push sum)) ((0 : Int64), (#[] : Array Int64))).2

def decimatePass (xs : Array Int64) : Array Int64 :=
  (xs.foldl (fun (state : UInt64 × Array Int64) x =>
    if state.1 == 7 then ((0 : UInt64), state.2.push x) else (state.1 + 1, state.2))
    ((0 : UInt64), (#[] : Array Int64))).2

def combPass (xs : Array Int64) : Array Int64 :=
  (xs.foldl (fun (state : Int64 × Array Int64) x =>
    (x, state.2.push (x - state.1))) ((0 : Int64), (#[] : Array Int64))).2

def cic (xs : Array Int64) : Array Int64 :=
  combPass (combPass (combPass (decimatePass (integratePass (integratePass
    (integratePass xs))))))

def cicFirst (xs : Array UInt64) (n : UInt64) : Array Int64 :=
  cic (LeanExe.build n fun i => xs[i.toNat]!.toInt64)

def cicCheck (n : UInt64) : Array Int64 := cicFirst TestSupport.A64.Cic.input n

verified_compile compiled := [integratePass, decimatePass, combPass, cic, cicFirst, cicCheck]

/-- The source program over `Int64` is the source program over words. -/
theorem program_eq : compiled.program = TestSupport.A64.Cic.compiled.program := by rfl

/-- The module over `Int64` is the module over words. -/
theorem module_eq : compiled.module = TestSupport.A64.Cic.compiled.module := by
  unfold compiled.module TestSupport.A64.Cic.compiled.module compiled.literalPool
    TestSupport.A64.Cic.compiled.literalPool
  rw [program_eq]
  rfl

#print axioms compiled.bytes
#print axioms module_eq

end TestSupport.A64.CicSigned
