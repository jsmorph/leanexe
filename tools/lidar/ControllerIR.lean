import Controller
import Project.Compiler.ScalarResult
import Project.Lidar.Controller

namespace Project.Lidar.ControllerResult
open LeanExe.Extract.Core LeanExe.Wasm.ScalarDescriptor

def ir : LeanExe.IR.Expr := match ControllerArtifact.func.body with
  | .assign _ value => value
  | _ => .u64 0

def descriptor : Expr := (Expr.ofIR ir).getD (.const 0)
def body : Lean.Expr := (collectLambdas ControllerArtifact.source 4).getD (.bvar 0)

theorem shape : ControllerArtifact.func =
    scalarFunc `LeanExe.Examples.Lidar.parameters (some "parameters") 4 ir := rfl
theorem recognized : Expr.ofIR ir = some descriptor := by rfl
theorem extractedBody : extractScalarExpr [3,2,1,0] body = some ir := by cbv
theorem arithmetic : descriptor.Arithmetic := by
  obtain ⟨found, parsed, proof⟩ := extractScalarExpr_arithmetic extractedBody
  have same := Option.some.inj (recognized.symm.trans parsed)
  exact same.symm ▸ proof
theorem reads : ∀ index ∈ descriptor.reads, index < 2^32 := by
  simp [descriptor, ir, ControllerArtifact.func, Expr.ofIR, Cond.ofIR, U64Op.ofIR, Expr.reads, Cond.reads]


#print axioms extractedBody
#print axioms arithmetic
#print axioms reads
end Project.Lidar.ControllerResult
