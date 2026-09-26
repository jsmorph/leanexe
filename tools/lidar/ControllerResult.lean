import ControllerIR

namespace Project.Lidar.ControllerResult
open LeanExe.Extract.Core LeanExe.Wasm.ScalarDescriptor

theorem meaning (x y range mask : UInt64) :
    descriptor.eval [x,y,range,mask,0] =
      some (LeanExe.Examples.Lidar.parameters x y range mask) := by
  by_cases hx : x ≤ 4095 <;> by_cases hy : y ≤ 4095 <;>
    by_cases hr : range ≤ 4095 <;> by_cases hm : mask ≤ 15 <;>
    simp [descriptor, ir, ControllerArtifact.func, Expr.ofIR, Cond.ofIR, U64Op.ofIR,
      Expr.eval, Cond.eval, U64Op.apply, LeanExe.Examples.Lidar.parameters, hx, hy, hr, hm,
      show UInt64.land 1 1 = 1 from rfl, show UInt64.land 1 0 = 0 from rfl,
      show UInt64.land 0 1 = 0 from rfl, show UInt64.land 0 0 = 0 from rfl] <;> rfl

theorem evaluated (x y range mask : UInt64) :
    ir.ScalarEval [x,y,range,mask,0] (LeanExe.Examples.Lidar.parameters x y range mask)
      [x,y,range,mask,0] := by
  obtain ⟨value, semantics⟩ := (extractScalarExpr_supported extractedBody).evaluates
    [mask,range,y,x] (by rfl)
  have result := extractScalarExpr_correct semantics extractedBody
    (scalarArgumentLocals [x,y,range,mask] [0])
  have valueEq := (Expr.ofIR_eval result recognized).1
  change descriptor.eval [x,y,range,mask,0] = some value at valueEq
  rw [meaning] at valueEq
  exact (Option.some.inj valueEq).symm ▸ result

/-- For every controller input, the identified bytes terminate with exactly the
native Lean packing/rejection function's result in the WASM execution model. -/
theorem correct (x y range mask : UInt64) (host : Wasm.HostEnv Unit) (store : Wasm.Store Unit) :
    ∃ raw, Wasm.Binary.decode ControllerArtifact.bytes = .ok raw ∧
      (Wasm.Binary.Translation.module raw).findExport "parameters" = some 0 ∧
      ∃ N, ∀ fuel ≥ N, Wasm.run fuel (Wasm.Binary.Translation.module raw) 0 store
        ([x,y,range,mask].map Wasm.Value.i64).reverse host =
          .Success [.i64 (LeanExe.Examples.Lidar.parameters x y range mask)] store := by
  rw [← ControllerArtifact.emitted, shape]
  exact Project.Compiler.ArithmeticModule.scalar_result [x,y,range,mask]
    `LeanExe.Examples.Lidar.parameters "parameters" recognized arithmetic reads
    (evaluated x y range mask) (shape ▸ ControllerArtifact.fits) host store

#print axioms correct
end Project.Lidar.ControllerResult
