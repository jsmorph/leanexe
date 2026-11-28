module

public import Library.Numerics.Bignum.Spec

@[expose] public section

/-!
The specification of the second iteration's one new function, the reader of naturals.  Every
other function of the second iteration has a specification of the first iteration: the products
`natMulKara` and `intMulKara` are `limbsOf (a * b)` and `BigInt.ofInt (a * b)`, and the integer
reader `intOfTextDC` is `readSpec`.

`natReadSpec s` reads the grammar of `readSpec` without the sign,

```
natural = "0" / nonzero *digit
```

and returns `(true, limbsOf n)` for a text that denotes `n`, and `(false, limbsOf 0)` for every
other array, among them the texts of negative integers, `-0`, the empty array, a leading zero, and
any word that is not a decimal digit.  It accepts a text exactly when `readSpec` accepts it with a
sign of `false`, and then returns the magnitude that `readSpec` returns (`natReadSpec_eq` in
`Reader.lean`).
-/

namespace Library.Numerics.Bignum

/-- The natural of a text of the grammar `"0" / nonzero *digit`. -/
def natReadSpec (s : Array UInt64) : Bool × Array UInt64 :=
  match Library.Numerics.Decimal.Int64Text.denote s.toList with
  | some z => if 0 ≤ z then (true, limbsOf z.toNat) else (false, limbsOf 0)
  | none => (false, limbsOf 0)

end Library.Numerics.Bignum
