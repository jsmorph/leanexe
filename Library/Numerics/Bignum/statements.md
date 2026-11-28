# Planned main statements

The statements were copied from the Lean files when the library was developed in another repository; this copy gives the library's present paths and names.

The definitions are those of `Spec.lean`.  `value`, `Digits`, and `base = 2^32` are leanexe's `Library.Numerics.MultiPrecision` definitions, and `denote` is `Library.Numerics.Decimal.Int64Text.denote`.  The names `natTrim`, `natCmp`, …, `textEMod` are the program's functions, written in leanexe's verified dialect.  In every statement, `u v w s t : Array UInt64` and `a b z : ℤ`.

## Canonical form

```lean
theorem value_limbsOf (n : ℕ) : value (limbsOf n) = n
theorem canonical_limbsOf (n : ℕ) : Canonical (limbsOf n)
theorem canonical_iff (u : Array UInt64) : Canonical u ↔ u = limbsOf (value u)
theorem canonical_ofInt (z : ℤ) : (BigInt.ofInt z).Canonical
theorem toInt_ofInt (z : ℤ) : (BigInt.ofInt z).toInt = z
```

## Naturals

Each theorem below has the premises `hu : Canonical u`, `hv : Canonical v`, `hsu : u.size < 2 ^ 32`, and `hsv : v.size < 2 ^ 32`, except `natTrim_eq`.

```lean
theorem natTrim_eq (hw : Digits w) (hs : w.size < 2 ^ 32) : natTrim w = limbsOf (value w)
theorem natCmp_eq : natCmp u v = cmpSpec (value u) (value v)
theorem natAdd_eq : natAdd u v = limbsOf (value u + value v)
theorem natSub_eq : natSub u v = natSubSpec (value u) (value v)
theorem natMul_eq : natMul u v = limbsOf (value u * value v)
theorem natDivMod_eq : natDivMod u v = natDivModSpec (value u) (value v)
theorem natDivModChecked_eq : natDivModChecked u v = natDivModCheckedSpec (value u) (value v)
```

## Integers

Each theorem below has the premises `ha : (BigInt.ofInt a).mag.size < 2 ^ 32` and, for the binary functions, `hb : (BigInt.ofInt b).mag.size < 2 ^ 32`.

```lean
theorem intNeg_eq : intNeg (.ofInt a) = .ofInt (-a)
theorem intCmp_eq : intCmp (.ofInt a) (.ofInt b) = cmpSpec a b
theorem intAdd_eq : intAdd (.ofInt a) (.ofInt b) = .ofInt (a + b)
theorem intSub_eq : intSub (.ofInt a) (.ofInt b) = .ofInt (a - b)
theorem intMul_eq : intMul (.ofInt a) (.ofInt b) = .ofInt (a * b)
theorem intTDivMod_eq : intTDivMod (.ofInt a) (.ofInt b) = intTDivModSpec a b
theorem intEDivMod_eq : intEDivMod (.ofInt a) (.ofInt b) = intEDivModSpec a b
theorem intTDivModChecked_eq : intTDivModChecked (.ofInt a) (.ofInt b) = intTDivModCheckedSpec a b
theorem intEDivModChecked_eq : intEDivModChecked (.ofInt a) (.ofInt b) = intEDivModCheckedSpec a b
```

## Text

```lean
theorem intToText_eq (h : (BigInt.ofInt z).mag.size < 2 ^ 32) : intToText (.ofInt z) = printSpec z
theorem intOfText_eq (hs : s.size < 2 ^ 32) : intOfText s = readSpec s
theorem readSpec_print (z : ℤ) : readSpec (printSpec z) = (true, .ofInt z)
theorem print_of_readSpec (h : readSpec s = (true, x)) : ∃ z, x = .ofInt z ∧ printSpec z = s
theorem readSpec_reject (h : ∀ z, printSpec z ≠ s) : readSpec s = (false, .ofInt 0)
theorem read_print (h : (printSpec z).size < 2 ^ 32) : intOfText (printSpec z) = (true, .ofInt z)
theorem textNeg_eq (hs : s.size < 2 ^ 32) : textNeg s = textNegSpec s
theorem textCmp_eq (hs : s.size < 2 ^ 32) (ht : t.size < 2 ^ 32) : textCmp s t = textCmpSpec s t
-- and the same form for textAdd, textSub, textMul, textTDiv, textTMod, textEDiv, textEMod
```

## Call theorems of the WebAssembly module

For each export `f` above, at its function index `k` in `compiled.module`, a theorem of the form

```lean
theorem natAdd_call :
    Verified.Call compiled.module compiled.tables k (fun x => limbsOf (value x.1 + value x.2))
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧
        heap.Within store compiled.module (compiled.natAdd.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.natAdd.bound x)
```

with the precondition `Canonical` on each natural argument, `x.Canonical` on each integer argument, and none on a text argument, and the specification's function of the exact result: `cmpSpec (value x.1) (value x.2)`, `natSubSpec`, `natDivModCheckedSpec`, `BigInt.ofInt (x.1.toInt + x.2.toInt)`, `printSpec x.toInt`, `readSpec`, `textAddSpec x.1 x.2`, and so on.  `Verified.Call` states that the function, called from a ready store with arguments that represent `x` and with the precondition, returns without a trap the representation of the specification's value and leaves a ready store, with every borrowed array kept and every region of the heap unchanged.  Each export also has a closed-form bound `compiled.f.bound x ≤ B`, where `B` is linear in the arguments' lengths.
