import Verified.Source
import LeanExe.Runtime.Defs

/-! The verified compiler: a Lean function from source functions to a WebAssembly module.  The
module has the layout of `LeanExe`'s modules, with the runtime's `alloc` and `release` at
functions 0 and 1, so the runtime and its proofs serve both compilers. -/

namespace Verified

open Wasm

/-- The instructions that push the value of an expression, reading argument `i` from local `i`. -/
def Expr.code : Expr → Program
  | .const value => [.constI64 value]
  | .arg index => [.localGet index]
  | .add left right => left.code ++ right.code ++ [.addI64]
  | .sub left right => left.code ++ right.code ++ [.subI64]
  | .mul left right => left.code ++ right.code ++ [.mulI64]

def Func.type (func : Func) : FuncType :=
  { params := List.replicate func.arity .i64, results := [.i64] }

/-- The function's code: its arguments are its only locals, and its body leaves the result on the
stack. -/
def Func.function (func : Func) (typeIdx : Nat) : Wasm.Function :=
  { params := func.type.params
    locals := []
    body := func.body.code
    results := func.type.results
    typeIdx := some typeIdx }

/-- Globals 0 through 3 hold the allocator state: the bump pointer, which starts at the heap base
4096, the free-list head, and the allocation and free counters.  Copied from `LeanExe.IR`. -/
def runtimeGlobals : List GlobalDecl :=
  (4096 :: List.replicate 3 0).map fun value =>
    { init := .i64 value, declaredType := some .i64, isMut := true,
      sourceInit := some [.constI64 value] }

/-- Parameter and result types of the runtime functions.  Copied from `LeanExe.IR`. -/
def wordToWord : FuncType := { params := [.i64], results := [.i64] }
def wordToNone : FuncType := { params := [.i64], results := [] }

/-- The module for the functions `funcs`, each exported under its name.  Functions 0 and 1 are
the runtime's `alloc` and `release`, and function `2 + i` is `funcs[i]`, with type `2 + i`. -/
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

end Verified
