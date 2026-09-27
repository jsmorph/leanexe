import LeanExe.Core.Program
import Project.Core.Arguments

namespace Project.Core

open LeanExe.Core
open Project.Compiler.ScalarLowering
open LeanExe.Wasm.ScalarDescriptor (Expr)

def width : Stmt → Nat
  | .skip => 0
  | .assign _ value => value.scratchWidth
  | .seq a b => max (width a) (width b)
  | .branch test yes no => max test.scratchWidth (max (width yes) (width no))
  | .loop test body => max test.scratchWidth (width body)
  | .call _ _ args | .effect _ _ args => argumentsWidth args

/-- Every constructor is compiled directly to Talos syntax. No binary encoder
or recognition of elaborated Lean expressions participates in this function. -/
def statement (imports : Nat) (effectCode : Nat → Wasm.Program) (scratch : Nat) : Stmt → Wasm.Program
  | .skip => []
  | .assign destination value =>
      (expression value).program scratch ++ [.localSet destination]
  | .seq a b => statement imports effectCode scratch a ++ statement imports effectCode scratch b
  | .branch test yes no =>
      (condition test).program scratch ++
        [.iff 0 0 (statement imports effectCode scratch yes) (statement imports effectCode scratch no)]
  | .loop test body =>
      [.block 0 0 [.loop 0 0
        ((condition test).program scratch ++ [.eqz, .br_if 1] ++
          statement imports effectCode scratch body ++ [.br 0])]]
  | .call destination callee args =>
      argumentsCode args scratch ++ [.call (imports + callee), .localSet destination]
  | .effect destination operation args =>
      argumentsCode args scratch ++ effectCode operation ++ [.localSet destination]

def compileFunction (imports : Nat) (effectCode : Nat → Wasm.Program) (source : Function) : Wasm.Function :=
  { params := List.replicate source.params .i64
    locals := List.replicate (source.locals + max (width source.body) source.result.scratchWidth) .i64
    body := statement imports effectCode (source.params + source.locals) source.body ++
      (expression source.result).program (source.params + source.locals)
    results := [.i64]
    typeIdx := some source.params }

def functionSignature (arity : Nat) : Wasm.FuncType :=
  { params := List.replicate arity .i64, results := [.i64] }

def maxParams : LeanExe.Core.Module → Nat
  | [] => 0
  | function :: rest => max function.params (maxParams rest)

def signatures (source : LeanExe.Core.Module) (imports : List Wasm.ImportDecl) : List Wasm.FuncType :=
  (List.range (maxParams source + 1)).map functionSignature ++
    imports.map (fun decl => { params := decl.params, results := decl.results })

def compile (source : LeanExe.Core.Module) (effectCode : Nat → Wasm.Program := fun _ => [])
    (imports : List Wasm.ImportDecl := []) (exports : List Wasm.Export := [])
    (memory : Option Wasm.MemDecl := none) : Wasm.Module :=
  { funcs := source.map (compileFunction imports.length effectCode)
    imports, exports, memory
    types := signatures source imports
    gcTypes := (signatures source imports).map (fun type => { comp := .func type }) }

end Project.Core
