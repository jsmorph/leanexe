import LeanExe.IR.Stmt
import LeanExe.Runtime.Defs

namespace LeanExe.IR

open Wasm

/-- A function whose parameters have the types `params`.  The first locals hold
the arguments, the next locals hold the compiler's variables, whose types are
`vars`, and the 64-bit locals after them are scratch space.  The function runs
`body` and returns the values of `results`, each an expression paired with its
type. -/
structure Func where
  params : List ScalarType
  vars : List ScalarType
  body : Stmt
  results : List ((type : ScalarType) × Expr type)

/-- The first scratch local. -/
def Func.scratch (func : Func) : Nat := func.params.length + func.vars.length

def Func.width (func : Func) : Nat :=
  max func.body.scratchWidth ((func.results.map (·.2.scratchWidth)).foldr max 0)

/-- The types of the locals after the parameters: the variables, then scratch. -/
def Func.locals (func : Func) : List ValueType :=
  func.vars.map ScalarType.valueType ++ List.replicate func.width .i64

/-- The local state on entry: the arguments, then zeroed variables and scratch
locals. -/
def Func.state (func : Func) (args : List Value) : State :=
  { params := args, locals := func.locals.map ValueType.zero }

def Func.type (func : Func) : FuncType :=
  { params := func.params.map ScalarType.valueType, results := func.results.map (·.1.valueType) }

def Func.function (func : Func) (typeIdx : Nat) : Wasm.Function :=
  { params := func.type.params
    locals := func.locals
    body := func.body.program func.scratch ++ func.results.flatMap (·.2.program func.scratch)
    results := func.type.results
    typeIdx := some typeIdx }

/-- Globals 0 through 3 hold the allocator state: the bump pointer, which starts
at the heap base 4096, the free-list head, and the allocation and free counters. -/
def runtimeGlobals : List GlobalDecl :=
  (4096 :: List.replicate 3 0).map fun value =>
    { init := .i64 value, declaredType := some .i64, isMut := true,
      sourceInit := some [.constI64 value] }

/-- Parameter and result types of the runtime functions: `alloc` takes and
returns a word, and `release` takes a word. -/
def wordToWord : FuncType := { params := [.i64], results := [.i64] }
def wordToNone : FuncType := { params := [.i64], results := [] }

/-- The module for the functions `funcs`, each exported under its name.
Functions 0 and 1 are the runtime's `alloc` and `release`, exported for hosts
together with the memory and the two counters, and function `2 + i` is `funcs[i]`,
with type `2 + i`.  Every module has a memory and the
runtime globals, so the allocator invariant can hold for its stores. -/
def compile (funcs : List (Func × String)) : Module :=
  let types := [wordToWord, wordToNone] ++ funcs.map (·.1.type)
  { funcs := [LeanExe.Runtime.allocFunction 0, LeanExe.Runtime.releaseFunction 1] ++
      funcs.mapIdx fun i entry => entry.1.function (2 + i)
    exports := [{ name := "alloc", funcIdx := 0 }, { name := "release", funcIdx := 1 }] ++
      funcs.mapIdx fun i entry => { name := entry.2, funcIdx := 2 + i }
    memory := some { pagesMin := 16, pagesMax := some 65535 }
    globals := runtimeGlobals
    types
    gcTypes := types.map fun type => { comp := .func type }
    globalExports := [("allocCount", 2), ("freeCount", 3)]
    memoryExports := [("memory", 0)] }

theorem compile_funcs {funcs : List (Func × String)} {i : Nat} {func : Func} {name : String}
    (h : funcs[i]? = some (func, name)) :
    (compile funcs).funcs[2 + i]? = some (func.function (2 + i)) := by
  conv_lhs => rw [show 2 + i = i + 1 + 1 by omega]
  simp [compile, List.getElem?_mapIdx, h]

end LeanExe.IR
