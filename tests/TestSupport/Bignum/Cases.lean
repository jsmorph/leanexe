module

public import Library.Numerics.Bignum.Program
public import Library.Numerics.Bignum.Spec
public meta import Library.Numerics.Bignum.Program
public meta import Library.Numerics.Bignum.Spec

@[expose] public section

/-!
Cases of the library functions that the module compiles into its exports without exporting them:
the divisions of Lean's convention at a zero divisor, where a negative dividend leaves a negative
remainder in both signed divisions, and the four sign combinations of each division.  The theorems
`natDivMod_eq`, `intTDivMod_eq`, and `intEDivMod_eq` cover them; these cases evaluate the program.
-/

namespace TestSupport.Bignum.Cases

open Library.Numerics.Bignum

#guard natDivMod (limbsOf 5) #[] == natDivModSpec 5 0
#guard natDivMod #[] #[] == natDivModSpec 0 0
#guard intTDivMod (.ofInt (-5)) (.ofInt 0) == intTDivModSpec (-5) 0
#guard intEDivMod (.ofInt (-5)) (.ofInt 0) == intEDivModSpec (-5) 0
#guard intEDivMod (.ofInt (-5)) (.ofInt 0) == (.ofInt 0, ⟨true, #[5]⟩)
#guard intTDivMod (.ofInt (-7)) (.ofInt 2) == (.ofInt (-3), .ofInt (-1))
#guard intEDivMod (.ofInt (-7)) (.ofInt 2) == (.ofInt (-4), .ofInt 1)
#guard intEDivMod (.ofInt 7) (.ofInt (-2)) == (.ofInt (-3), .ofInt 1)
#guard intEDivMod (.ofInt (-7)) (.ofInt (-2)) == (.ofInt 4, .ofInt 1)
#guard intEDivMod (.ofInt (-6)) (.ofInt (-3)) == (.ofInt 2, .ofInt 0)

end TestSupport.Bignum.Cases
