import Project.Correct.Scalar64.Backend

namespace Project.Correct.Scalar64
open Wasm
open Project.ProofKit.ScalarTransition

def Function.signature (function : Function) : Wasm.FuncType :=
  { params := List.replicate function.arity .i64, results := [.i64] }

/-- The entire module: no allocator, imports, memory, globals, or start function. -/
def assemble (functions : List Function) (exportName : String) (entry : Nat) : Module :=
  { funcs := functions.mapIdx (fun index function => function.lower index)
    exports := [{ name := exportName, funcIdx := entry }]
    types := functions.map Function.signature
    gcTypes := functions.map (fun function => { comp := .func function.signature }) }

theorem assemble_implements : Implements (assemble functions exportName entry) functions := by
  refine ⟨rfl, ?_⟩
  intro index function found
  simp [assemble, List.getElem?_mapIdx, found]

theorem assemble_no_effects :
    (assemble functions exportName entry).imports = [] ∧
    (assemble functions exportName entry).memory = none ∧
    (assemble functions exportName entry).globals = [] ∧
    (assemble functions exportName entry).startFunc = none := ⟨rfl, rfl, rfl, rfl⟩

def checkExpression (scratch capacity : Nat) (expression : Expr type) : Bool :=
  expression.reads.all (· < scratch) && scratch + expression.scratchWidth ≤ capacity

def checkCommand (functions : List Function) (current scratch capacity : Nat) : Command → Bool
  | .skip => true
  | .assign index expression => index < scratch && checkExpression scratch capacity expression
  | .seq first second => checkCommand functions current scratch capacity first &&
      checkCommand functions current scratch capacity second
  | .branch condition yes no => checkExpression scratch capacity condition &&
      checkCommand functions current scratch capacity yes && checkCommand functions current scratch capacity no
  | .loop condition body => checkExpression scratch capacity condition &&
      checkCommand functions current scratch capacity body
  | .call destination index arguments =>
      destination < scratch && index < current &&
      arguments.all (checkExpression scratch capacity) &&
      match functions[index]? with
      | none => false
      | some function => arguments.length == function.arity

def checkFunction (functions : List Function) (index : Nat) (function : Function) : Bool :=
  let capacity := function.arity + function.localCount
  capacity < 2^32 && function.arity ≤ function.scratch && function.scratch ≤ capacity &&
    checkCommand functions index function.scratch capacity function.body &&
    checkExpression function.scratch capacity function.result

/-- Calls point to earlier definitions, so the helper graph is acyclic. Iteration
    is explicit and cannot disguise recursion through the call table. -/
def checkModule (functions : List Function) (entry : Nat) : Bool :=
  functions.length < 2^32 && entry < functions.length &&
    (functions.zipIdx.all fun (function, index) => checkFunction functions index function)

end Project.Correct.Scalar64
