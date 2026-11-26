module

public import Examples.SumArray.Program
public import Verified.Reflect.Command

@[expose] public section

/-! The verified compiler's modules of the library's word reductions: `compiledSum` holds
`sumArray`, and `compiledFolds` holds `productArray` and `xorArray`.  The folds allocate nothing,
so each generated `implements` theorem states that its function returns without a trap. -/

namespace Examples.SumArray

verified_compile compiledSum := [sumArray]

verified_compile compiledFolds := [productArray, xorArray]

end Examples.SumArray
