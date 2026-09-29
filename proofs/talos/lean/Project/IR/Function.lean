import Project.ProofKit.ScalarTransition

namespace Project.IR

open Wasm Project.ProofKit.ScalarTransition

/-- A function of `params` 64-bit arguments whose result is one expression.
Locals `0` to `params - 1` hold the arguments, and the locals after them are
the expression's scratch space. -/
structure Func where
  params : Nat
  result : Expr .u64
  deriving Repr

/-- The local state on entry: the arguments, then zeroed scratch locals. -/
def Func.state (func : Func) (args : List Value) : State :=
  { params := args, locals := List.replicate func.result.scratchWidth (.i64 0) }

def Func.type (func : Func) : FuncType :=
  { params := List.replicate func.params .i64, results := [.i64] }

def Func.function (func : Func) : Wasm.Function :=
  { params := func.type.params
    locals := List.replicate func.result.scratchWidth .i64
    body := func.result.program func.params
    results := func.type.results
    typeIdx := some 0 }

/-- Globals 0 through 5 hold the allocator state: the bump pointer, which starts
at the heap base 4096, the free-list head, and four counters. -/
def runtimeGlobals : List GlobalDecl :=
  (4096 :: List.replicate 5 0).map fun value =>
    { init := .i64 value, declaredType := some .i64, isMut := true,
      sourceInit := some [.constI64 value] }

/-- The module for `func`, exported as `name`.  Every compiled module has a
memory and the runtime globals, so the allocator invariant can hold for its
stores. -/
def compile (func : Func) (name : String) : Module :=
  { funcs := [func.function]
    exports := [{ name, funcIdx := 0 }]
    memory := some { pagesMin := 16 }
    globals := runtimeGlobals
    types := [func.type]
    gcTypes := [{ comp := .func func.type }]
    memoryExports := [("memory", 0)] }

end Project.IR
