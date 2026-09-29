import Project.IR.Stmt
import Project.Runtime.Defs

namespace Project.IR

open Wasm Project.ProofKit.ScalarTransition

/-- A function of `params` 64-bit arguments.  Locals `0` to `params - 1` hold
the arguments, the next `vars` locals hold the compiler's variables, and the
locals after them are scratch space.  The function runs `body` and returns the
value of `result`. -/
structure Func where
  params : Nat
  vars : Nat
  body : Stmt
  result : Expr .u64
  deriving Repr

/-- The first scratch local. -/
def Func.scratch (func : Func) : Nat := func.params + func.vars

def Func.width (func : Func) : Nat := max func.body.scratchWidth func.result.scratchWidth

/-- The local state on entry: the arguments, then zeroed variables and scratch
locals. -/
def Func.state (func : Func) (args : List Value) : State :=
  { params := args, locals := List.replicate (func.vars + func.width) (.i64 0) }

def Func.type (func : Func) : FuncType :=
  { params := List.replicate func.params .i64, results := [.i64] }

def Func.function (func : Func) : Wasm.Function :=
  { params := func.type.params
    locals := List.replicate (func.vars + func.width) .i64
    body := func.body.program func.scratch ++ func.result.program func.scratch
    results := func.type.results
    typeIdx := some 0 }

/-- Globals 0 through 5 hold the allocator state: the bump pointer, which starts
at the heap base 4096, the free-list head, and four counters. -/
def runtimeGlobals : List GlobalDecl :=
  (4096 :: List.replicate 5 0).map fun value =>
    { init := .i64 value, declaredType := some .i64, isMut := true,
      sourceInit := some [.constI64 value] }

/-- Parameter and result types of the runtime functions: `alloc` and `retain`
take and return a word, and `release` takes a word. -/
def wordToWord : FuncType := { params := [.i64], results := [.i64] }
def wordToNone : FuncType := { params := [.i64], results := [] }

/-- The module for `func`, exported as `name`.  Function 0 is `func`; functions
1, 2, and 3 are the runtime's `alloc`, `retain`, and `release`, exported for
hosts together with the memory and the four counters.  Every module has a memory
and the runtime globals, so the allocator invariant can hold for its stores. -/
def compile (func : Func) (name : String) : Module :=
  let types := [func.type, wordToWord, wordToNone]
  { funcs := [func.function, Project.Runtime.allocFunction 1,
      Project.Runtime.retainFunction 1, Project.Runtime.releaseFunction 2]
    exports := [{ name, funcIdx := 0 }, { name := "alloc", funcIdx := 1 },
      { name := "retain", funcIdx := 2 }, { name := "release", funcIdx := 3 }]
    memory := some { pagesMin := 16 }
    globals := runtimeGlobals
    types
    gcTypes := types.map fun type => { comp := .func type }
    globalExports := [("allocCount", 2), ("retainCount", 3), ("releaseCount", 4),
      ("freeCount", 5)]
    memoryExports := [("memory", 0)] }

end Project.IR
