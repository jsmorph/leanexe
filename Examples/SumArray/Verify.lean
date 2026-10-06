import Examples.SumArray.Module
import Project.IR.Fold
import Project.Encoding.RoundTrip

namespace Examples.SumArray

open Project.Pipeline Project.IR

theorem sumArray_implements :
    Implements sumArray.module 2 Examples.SumArray.sumArray :=
  Func.foldl_implements [(sumArray.ir, "sumArray")] 0 sumArray.ir "sumArray" rfl .add 0
    (by decide) rfl rfl rfl rfl rfl

theorem productArray_implements :
    Implements folds.module 2 Examples.SumArray.productArray :=
  Func.foldl_implements folds.funcs 0 folds.productArray.ir "productArray" rfl .mul 1
    (by decide) rfl rfl rfl rfl rfl

theorem xorArray_implements :
    Implements folds.module 3 Examples.SumArray.xorArray :=
  Func.foldl_implements folds.funcs 1 folds.xorArray.ir "xorArray" rfl .bitXor 0
    (by decide) rfl rfl rfl rfl rfl

/-- `encode` succeeds on `sumArray.module`, and its bytes decode to a module that
computes `sumArray` exactly. -/
theorem sumArray_bytes : ∃ bytes, Wasm.Encoding.encode sumArray.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧
      Implements m 2 Examples.SumArray.sumArray := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip sumArray.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, sumArray.module, decoded, sumArray_implements⟩

/-- `encode` succeeds on `folds.module`, and its bytes decode to a module whose functions 2 and 3
compute `productArray` and `xorArray`. -/
theorem folds_bytes : ∃ bytes, Wasm.Encoding.encode folds.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧
      Implements m 2 Examples.SumArray.productArray ∧
      Implements m 3 Examples.SumArray.xorArray := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip folds.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, folds.module, decoded, productArray_implements, xorArray_implements⟩

end Examples.SumArray
