import Verified.Examples.CompositionBase
import Verified.ModuleComposition
import Verified.ScalarAtoms

namespace Verified.Examples.CompositionBase

open Wasm LeanExe.Pipeline

theorem add_pure {m : Module} (hm : Runtime m)
    (hPrefix : compiled.program.functions <+: m.funcs.drop 2) :
    ImplementsPureA false m 2 (fun p : UInt64 × UInt64 => add p.1 p.2) := by
  have calls : Calls m compiled.funs compiled.program.flags
      (compiled.program.boundsAt compiled.funs) (compiled.program.fitsAt compiled.funs) :=
    compiled.program.calls_prefix compiled.funs compiled.meaning m hm hPrefix
  have hImpl : ImplementsA false m 2 (fun p : UInt64 × UInt64 => add p.1 p.2)
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
    ImplementsA.lean ((calls (.there .here) 0).implementsB_unpaid rfl rfl).implementsA
  have hLookup : m.funcs[2]? = some (compiled.add.func.function 2) :=
    compiled.program.functions_prefix_lookup m hPrefix (k := 0) (by decide)
  have uniform : CodeUniform m (compiled.add.func.function 2).body := by
    change CodeUniform m [.localGet 0, .localGet 1, .addI64]
    exact CodeUniform.cons (OneUniform.localGet m 0)
      (CodeUniform.cons (OneUniform.localGet m 1)
        (CodeUniform.cons (OneUniform.addI64 m) (CodeUniform.nil m)))
  have safe : CodeNoReturnCall m (compiled.add.func.function 2).body := by
    change CodeNoReturnCall m [.localGet 0, .localGet 1, .addI64]
    exact CodeNoReturnCall.cons (OneNoReturnCall.localGet m 0)
      (CodeNoReturnCall.cons (OneNoReturnCall.localGet m 1)
        (CodeNoReturnCall.cons (OneNoReturnCall.addI64 m) (CodeNoReturnCall.nil m)))
  exact implementsPure_of_uniform hImpl (EntryUniform.of_code hm.imports hLookup uniform safe)

theorem scale_pure {m : Module} (hm : Runtime m)
    (hPrefix : compiled.program.functions <+: m.funcs.drop 2) :
    ImplementsPureA false m 3 scale := by
  have calls : Calls m compiled.funs compiled.program.flags
      (compiled.program.boundsAt compiled.funs) (compiled.program.fitsAt compiled.funs) :=
    compiled.program.calls_prefix compiled.funs compiled.meaning m hm hPrefix
  have hImpl : ImplementsA false m 3 scale
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
    ImplementsA.lean ((calls .here 0).implementsB_unpaid rfl rfl).implementsA
  have hLookup : m.funcs[3]? = some (compiled.scale.func.function 3) :=
    compiled.program.functions_prefix_lookup m hPrefix (k := 1) (by decide)
  have uniform : CodeUniform m (compiled.scale.func.function 3).body := by
    change CodeUniform m [.localGet 0, .localSet 1, .localGet 1,
      .f64Const 4609434218613702656, .f64Mul]
    exact CodeUniform.cons (OneUniform.localGet m 0)
      (CodeUniform.cons (OneUniform.localSet m 1)
        (CodeUniform.cons (OneUniform.localGet m 1)
          (CodeUniform.cons (OneUniform.f64Const m _)
            (CodeUniform.cons (OneUniform.f64Mul m) (CodeUniform.nil m)))))
  have safe : CodeNoReturnCall m (compiled.scale.func.function 3).body := by
    change CodeNoReturnCall m [.localGet 0, .localSet 1, .localGet 1,
      .f64Const 4609434218613702656, .f64Mul]
    exact CodeNoReturnCall.cons (OneNoReturnCall.localGet m 0)
      (CodeNoReturnCall.cons (OneNoReturnCall.localSet m 1)
        (CodeNoReturnCall.cons (OneNoReturnCall.localGet m 1)
          (CodeNoReturnCall.cons (OneNoReturnCall.f64Const m _)
            (CodeNoReturnCall.cons (OneNoReturnCall.f64Mul m) (CodeNoReturnCall.nil m)))))
  exact implementsPure_of_uniform hImpl (EntryUniform.of_code hm.imports hLookup uniform safe)

#print axioms add_pure
#print axioms scale_pure

end Verified.Examples.CompositionBase
