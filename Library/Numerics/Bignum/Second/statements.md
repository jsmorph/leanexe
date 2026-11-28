# Main statements of the second iteration

The statements were copied from the Lean files when the library was developed in another repository; this copy gives the library's present paths and names.

The statements below are copied from the Lean files with their proofs omitted.  `value`, `Digits`, and `base = 2^32` are leanexe's `Library.Numerics.MultiPrecision` definitions; `limbsOf`, `Canonical`, `BigInt`, `BigInt.ofInt`, `BigInt.toInt`, `readSpec`, `natMul`, `intMul`, `intOfText`, `decimalValue`, `natAdd`, `natSub`, and `natDivModChecked` are the first iteration's (`Library/Numerics/Bignum/Spec.lean`, `Library/Numerics/Bignum/Program.lean`); `natReadSpec` is the second iteration's (`Second/Spec.lean`); `SegDigits` and `segVal` are the second iteration's values of segments (`Second/Seg.lean`); and `compiled` is the second iteration's module (`Second/Compiled.lean`).

## `Kara.lean`

```lean
/-- The facts that `kara_spec` states of the result `R` of a call on operands of `n` limbs from
`ap` and `bp`, with the result from `rp` and the scratch from `tp`. -/
def KaraPost (n : ℕ) (W : Array UInt64) (ap bp rp tp : ℕ) (R : Array UInt64) : Prop :=
  R.size = W.size ∧
  (∀ q, ¬ (rp ≤ q ∧ q < rp + 2 * n) → ¬ (tp ≤ q ∧ q < tp + 6 * n) → R[q]! = W[q]!) ∧
  SegDigits R rp (2 * n) ∧ segVal R rp (2 * n) = segVal W ap n * segVal W bp n
```

```lean
/-- `kara` writes the product of two segments of `n` limbs over the `2 n` words from `rp`, and it
changes no word outside those and the `6 n` words of scratch from `tp`. -/
theorem kara_spec (t : UInt64) : ∀ (n : ℕ) (W : Array UInt64) (ap bp rp tp nn : UInt64),
    nn.toNat = n → W.size < 2 ^ 64 →
    ap.toNat + n ≤ rp.toNat → bp.toNat + n ≤ rp.toNat → rp.toNat + 2 * n ≤ tp.toNat →
    tp.toNat + 6 * n ≤ W.size →
    SegDigits W ap.toNat n → SegDigits W bp.toNat n →
    KaraPost n W ap.toNat bp.toNat rp.toNat tp.toNat (kara t W ap bp rp tp nn)
```

## `Mul.lean`

```lean
/-- The product of the second iteration, at any threshold, is the canonical form of the product
of the values. -/
theorem natMulKaraWith_eq (t : UInt64) {u v : Array UInt64} (hu : Digits u) (hv : Digits v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    natMulKaraWith t u v = limbsOf (value u * value v)
```

```lean
/-- `natMulKara` returns the canonical limbs of the product. -/
theorem natMulKara_eq {u v : Array UInt64} (hu : Digits u) (hv : Digits v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    natMulKara u v = limbsOf (value u * value v)
```

```lean
/-- `natMulKara` returns what the first iteration's `natMul` returns. -/
theorem natMulKara_eq_natMul {u v : Array UInt64} (hu : Digits u) (hv : Digits v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) : natMulKara u v = natMul u v
```

```lean
/-- `intMulKara` returns what the first iteration's `intMul` returns, on arrays of limbs. -/
theorem intMulKara_eq_intMul {x y : BigInt} (hx : Digits x.mag) (hy : Digits y.mag)
    (hsx : x.mag.size < 2 ^ 32) (hsy : y.mag.size < 2 ^ 32) : intMulKara x y = intMul x y
```

```lean
/-- `intMulKara` of two canonical integers is the canonical integer of the product. -/
theorem intMulKara_eq {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) :
    intMulKara (.ofInt a) (.ofInt b) = .ofInt (a * b)
```

```lean
/-- The result of `natMulKara` is canonical. -/
theorem natMulKara_canonical {u v : Array UInt64} (hu : Digits u) (hv : Digits v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) : Canonical (natMulKara u v)
```

```lean
/-- The result of `intMulKara` on canonical integers is canonical. -/
theorem intMulKara_canonical {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) : (intMulKara (.ofInt a) (.ofInt b)).Canonical
```

## `Read.lean`

```lean
/-- The second iteration's reader of digits returns the canonical limbs of the digits' value, as
the first iteration's `decimalValue` does. -/
theorem decimalValueDC_eq (t E : UInt64) (s : Array UInt64) (start count : UInt64)
    (hs : s.size < 2 ^ 32) (hsz : start.toNat + count.toNat = s.size) (hc : 1 ≤ count.toNat)
    (hdig : ∀ w ∈ s.toList.drop start.toNat, isDigitWord w = true) :
    decimalValueDC t E s start count = limbsOf (digitsValue (s.toList.drop start.toNat))
```

```lean
/-- The second iteration's reader of digits returns what the first iteration's returns. -/
theorem decimalValueDC_eq_decimalValue (t E : UInt64) (s : Array UInt64) (start count : UInt64)
    (hs : s.size < 2 ^ 32) (hsz : start.toNat + count.toNat = s.size) (hc : 1 ≤ count.toNat)
    (hdig : ∀ w ∈ s.toList.drop start.toNat, isDigitWord w = true) :
    decimalValueDC t E s start count = decimalValue s start count
```

## `Reader.lean`

```lean
/-- The integer reader of the second iteration returns what the first iteration's returns. -/
theorem intOfTextDC_eq_intOfText (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    intOfTextDC s = intOfText s
```

```lean
/-- The integer reader of the second iteration returns the specification's result. -/
theorem intOfTextDC_eq (s : Array UInt64) (hs : s.size < 2 ^ 32) : intOfTextDC s = readSpec s
```

```lean
/-- The natural reader of the second iteration on a text that starts with `-` rejects it, and on
any other text returns the flag and the magnitude of the first iteration's integer reader. -/
theorem natOfTextDCWith_eq_intOfText (t E : UInt64) (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    natOfTextDCWith t E s = if s[(0 : UInt64).toNat]! = 45 then (false, #[])
      else ((intOfText s).1, (intOfText s).2.mag)
```

```lean
/-- `natReadSpec` rejects a text that starts with `-` and on any other text returns the flag and
the magnitude of `readSpec`. -/
theorem natReadSpec_eq (s : Array UInt64) :
    natReadSpec s = if s[(0 : UInt64).toNat]! = 45 then (false, #[])
      else ((readSpec s).1, (readSpec s).2.mag)
```

```lean
/-- The natural reader of the second iteration returns the specification's result. -/
theorem natOfTextDCWith_eq (t E : UInt64) (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    natOfTextDCWith t E s = natReadSpec s
```

```lean
theorem natOfTextDC_eq (s : Array UInt64) (hs : s.size < 2 ^ 32) : natOfTextDC s = natReadSpec s
```

```lean
/-- The limbs that the natural reader returns are canonical. -/
theorem natOfTextDC_canonical (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    Canonical (natOfTextDC s).2
```

```lean
/-- The integer that the integer reader returns is canonical. -/
theorem intOfTextDC_canonical (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    (intOfTextDC s).2.Canonical
```

## `Loops.lean`

```lean
theorem natAddS_eq_natAdd : natAddS = natAdd
```

```lean
theorem natSubS_eq_natSub : natSubS = natSub
```

```lean
theorem natDivModCheckedS_eq_natDivModChecked : natDivModCheckedS = natDivModChecked
```

## `Bound.lean`

```lean
theorem kara_fits_all (k : ℕ) (hk : 64 ≤ k) (x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64) : compiled.kara.fits (k + 1) x = true
```

```lean
/-- The product allocates its workspace and its result: at most `24 (m + n) + 80 min(m, n) + 112`
bytes for operands of `m` and `n` limbs, at every threshold. -/
theorem natMulKaraWith_bound_le (k : ℕ) (t : UInt64) (u v : Array UInt64) (hu : u.size < 2 ^ 32)
    (hv : v.size < 2 ^ 32) :
    compiled.natMulKaraWith.bound (k + 1) (t, u, v) ≤
      24 * (u.size + v.size) + 80 * min u.size v.size + 112
```

```lean
/-- The natural reader allocates at most `19 s + 262` bytes for a text of `s` words, with any
bound `1 ≤ E ≤ 2^32` on its base elements. -/
theorem natOfTextDCWith_bound_le (k : ℕ) (t E : UInt64) (s : Array UInt64) (hE1 : 1 ≤ E.toNat)
    (hE : E.toNat ≤ 2 ^ 32) (hs : s.size < 2 ^ 32) :
    compiled.natOfTextDCWith.bound (k + 2) (t, E, s) ≤ 19 * s.size + 262
```

```lean
/-- The natural reader allocates at most `7 s + 168` bytes for a text of `s` words. -/
theorem natOfTextDC_bound_le (k : ℕ) (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    compiled.natOfTextDC.bound (k + 3) s ≤ 7 * s.size + 168
```

```lean
/-- The integer reader allocates at most `7 s + 168` bytes for a text of `s` words. -/
theorem intOfTextDC_bound_le (k : ℕ) (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    compiled.intOfTextDC.bound (k + 2) s ≤ 7 * s.size + 168
```

## `Call.lean`

```lean
/-- Function 20, `natMulKara`, called with two canonical naturals, returns the canonical limbs of
the product. -/
theorem natMulKara_call :
    Verified.Call compiled.module compiled.tables 20
      (fun x : Array UInt64 × Array UInt64 => limbsOf (value x.1 * value x.2))
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧
        heap.Within store compiled.module (compiled.natMulKara.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.natMulKara.bound 1000 x)
```

```lean
/-- Function 21, `intMulKara`, called with two canonical integers, returns the canonical integer of
the product. -/
theorem intMulKara_call :
    Verified.Call compiled.module compiled.tables 21
      (fun x : BigInt × BigInt => BigInt.ofInt (x.1.toInt * x.2.toInt))
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧
        heap.Within store compiled.module (compiled.intMulKara.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.intMulKara.bound 1000 x)
```

```lean
/-- Function 25, `natOfTextDC`, called with any array of words, returns `natReadSpec` of it. -/
theorem natOfTextDC_call :
    Verified.Call compiled.module compiled.tables 25 natReadSpec
      (fun s heap store => heap.Within store compiled.module (compiled.natOfTextDC.bound 1000 s))
      (fun s heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.natOfTextDC.bound 1000 s)
```

```lean
/-- Function 26, `intOfTextDC`, called with any array of words, returns `readSpec` of it, the
result of the first iteration's `intOfText`. -/
theorem intOfTextDC_call :
    Verified.Call compiled.module compiled.tables 26 readSpec
      (fun s heap store => heap.Within store compiled.module (compiled.intOfTextDC.bound 1000 s))
      (fun s heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.intOfTextDC.bound 1000 s)
```

```lean
/-- Function 19, `natMulKaraWith`, called with any threshold and two canonical naturals, returns the
canonical limbs of the product. -/
theorem natMulKaraWith_call :
    Verified.Call compiled.module compiled.tables 19
      (fun x : UInt64 × Array UInt64 × Array UInt64 => limbsOf (value x.2.1 * value x.2.2))
      (fun x heap store => (Canonical x.2.1 ∧ Canonical x.2.2) ∧
        heap.Within store compiled.module (compiled.natMulKaraWith.bound 1000 x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + compiled.natMulKaraWith.bound 1000 x)
```

```lean
/-- Function 24, `natOfTextDCWith`, called with any threshold, any bound on the base elements, and
any array of words, returns `natReadSpec` of the array. -/
theorem natOfTextDCWith_call :
    Verified.Call compiled.module compiled.tables 24
      (fun x : UInt64 × UInt64 × Array UInt64 => natReadSpec x.2.2)
      (fun x heap store => heap.Within store compiled.module (compiled.natOfTextDCWith.bound 1000 x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + compiled.natOfTextDCWith.bound 1000 x)
```

```lean
theorem natMulKara_room (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.natMulKara.bound 1000 (u, v) ≤ 24 * (u.size + v.size) + 80 * min u.size v.size + 112
```

```lean
theorem intMulKara_room (x y : BigInt) (hx : x.mag.size < 2 ^ 32) (hy : y.mag.size < 2 ^ 32) :
    compiled.intMulKara.bound 1000 (x, y) ≤
      24 * (x.mag.size + y.mag.size) + 80 * min x.mag.size y.mag.size + 112
```

```lean
theorem natOfTextDC_room (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    compiled.natOfTextDC.bound 1000 s ≤ 7 * s.size + 168
```

```lean
theorem intOfTextDC_room (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    compiled.intOfTextDC.bound 1000 s ≤ 7 * s.size + 168
```

```lean
theorem natMulKaraWith_room (t : UInt64) (u v : Array UInt64) (hu : u.size < 2 ^ 32)
    (hv : v.size < 2 ^ 32) :
    compiled.natMulKaraWith.bound 1000 (t, u, v) ≤
      24 * (u.size + v.size) + 80 * min u.size v.size + 112
```

```lean
theorem natOfTextDCWith_room (t E : UInt64) (s : Array UInt64) (hE1 : 1 ≤ E.toNat)
    (hE : E.toNat ≤ 2 ^ 32) (hs : s.size < 2 ^ 32) :
    compiled.natOfTextDCWith.bound 1000 (t, E, s) ≤ 19 * s.size + 262
```

```lean
/-- Function 18, `kara`, computes the Lean function in place for every argument, allocating
nothing, with no premise on the depth. -/
theorem kara_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 18
    (fun x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 =>
      kara x.1 x.2.1.val x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat)
```

```lean
/-- Function 22, `readPass`, computes the Lean function in place for every argument, allocating
nothing, with no premise on the depth. -/
theorem readPass_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 22
    (fun x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 =>
      readPass x.1 x.2.1.val x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat)
```

```lean
/-- Function 23, `decimalValueDC`, returns the Lean function's value, the canonical limbs of the
value of its digits (`decimalValueDC_eq`), from a ready store with room for its bound at 1,000
frames, which `decimalValueDC_bound_le` bounds. -/
theorem decimalValueDC_call :
    Verified.CallSpec compiled.module compiled.tables 23
      (fun x : UInt64 × UInt64 × Array UInt64 × UInt64 × UInt64 =>
        decimalValueDC x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (fun x => compiled.decimalValueDC.bound 1000 x)
```

## `Call.lean`: export indices and the helpers

Each `*_export` theorem has the form of `natMulKara_export` below, for the names and indices isDigitW 2, addGen 3, subGen 4, baseMul 5, trimSeg 7, mulAddSeg 11, readInit 12, kara 18, natMulKaraWith 19, natMulKara 20, intMulKara 21, readPass 22, decimalValueDC 23, natOfTextDCWith 24, natOfTextDC 25, and intOfTextDC 26.

```lean
theorem natMulKara_export :
    ({ name := "natMulKara", funcIdx := 20 } : Wasm.Export) ∈ compiled.module.exports
```

```lean
/-- Function 2, `isDigitW`, returns the Lean function's value, from a ready store with room for
its bound, 0. -/
theorem isDigitW_call :
    Verified.CallSpec compiled.module compiled.tables 2 (fun x : UInt64 => isDigitW x)
      compiled.isDigitW.bound
```

```lean
/-- Function 7, `trimSeg`, returns the Lean function's value, the canonical limbs of a segment of
limbs (`trimSeg_eq`), from a ready store with room for its bound, at most `8 len + 56` bytes. -/
theorem trimSeg_call :
    Verified.CallSpec compiled.module compiled.tables 7
      (fun x : Array UInt64 × UInt64 × UInt64 => trimSeg x.1 x.2.1 x.2.2) compiled.trimSeg.bound
```

```lean
/-- Function 12, `readInit`, returns the Lean function's value, from a ready store with room for
its bound, the block of `6 N` or `N` words. -/
theorem readInit_call :
    Verified.CallSpec compiled.module compiled.tables 12
      (fun x : Array UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 =>
        readInit x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) compiled.readInit.bound
```

```lean
/-- Function 3, `addGen`, computes the Lean function in place, allocating nothing. -/
theorem addGen_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 3
    (fun x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 =>
      addGen x.1.val x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat)
```

```lean
/-- Function 4, `subGen`, computes the Lean function in place, allocating nothing. -/
theorem subGen_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 4
    (fun x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 =>
      subGen x.1.val x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat)
```

```lean
/-- Function 5, `baseMul`, computes the Lean function in place, allocating nothing. -/
theorem baseMul_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 5
    (fun x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 =>
      baseMul x.1.val x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat)
```

```lean
/-- Function 11, `mulAddSeg`, computes the Lean function in place, allocating nothing. -/
theorem mulAddSeg_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 11
    (fun x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 =>
      mulAddSeg x.1.val x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat)
```


## `Bound.lean`: the reader of digits

```lean
/-- The reader of digits allocates its workspace of at most `6 N` limbs and its result of at most
`N` limbs, for the `N` limbs of its elements. -/
theorem decimalValueDC_bound_le (k : ℕ) (t E : UInt64) (s : Array UInt64) (start count : UInt64) :
    compiled.decimalValueDC.bound (k + 1) (t, E, s, start, count) ≤
      56 * ((((count + 8) / 9 + LeanExe.repeatWhile 32 1 (fun p => decide (E * p < (count + 8) / 9))
        (fun p => 2 * p) - 1) / LeanExe.repeatWhile 32 1 (fun p => decide (E * p < (count + 8) / 9))
        (fun p => 2 * p)) * LeanExe.repeatWhile 32 1 (fun p => decide (E * p < (count + 8) / 9))
        (fun p => 2 * p)).toNat + 112
```

```lean
/-- The reader of digits with `readBase` allocates at most `56 (C + C / 384) + 112` bytes for
`C = ⌈count / 9⌉` chunks. -/
theorem decimalValueDC_readBase_le (k : ℕ) (t : UInt64) (s : Array UInt64) (start count : UInt64)
    (hc : count.toNat < 2 ^ 32) (hc1 : 1 ≤ count.toNat) :
    compiled.decimalValueDC.bound (k + 1) (t, readBase, s, start, count) ≤
      56 * ((count.toNat + 8) / 9 + (count.toNat + 8) / 9 / 384) + 112
```


## `Native.lean`: the C form

Each of the six exports `natMulKara` (20), `intMulKara` (21), `natOfTextDC` (25), `intOfTextDC` (26), `natMulKaraWith` (19), and `natOfTextDCWith` (24) has the three theorems shown for `natMulKara` and `intOfTextDC`, with the precondition, specification, and closed form of its call theorem.  `ImplementsA.strengthen` is the rule of consequence of the first iteration's `Native.lean`.

```lean
/-- A precondition strengthened and a postcondition that uses it and the arguments'
representation, as the first iteration's `ImplementsA.strengthen`. -/
theorem ImplementsA.strengthen {α β : Type} [Represent α] [Represent β] {aborts : Bool}
    {m : Wasm.Module} {k : Nat} {f : α → β} {Pre Pre' : α → Heap → Wasm.Store Unit → Prop}
    {Post Post' : α → Heap → Wasm.Store Unit → Heap → Wasm.Store Unit → Prop}
    (h : ImplementsA aborts m k f Pre Post) (hpre : ∀ x heap store, Pre' x heap store → Pre x heap store)
    (hpost : ∀ heap store params x heap' final, Pre' x heap store →
      Represent.borrowed heap store params x → Post x heap store heap' final →
      Post' x heap store heap' final) :
    ImplementsA aborts m k f Pre' Post'
```

```lean
/-- Function 20, `natMulKara`, returns the Lean function's value, which meets its specification, and
raises `top` by at most the closed form of its bound. -/
theorem natMulKara_spec_trapFree :
    ImplementsA false compiled.module 20 (fun x : Array UInt64 × Array UInt64 => natMulKara x.1 x.2)
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧ heap.Within store compiled.module (compiled.natMulKara.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (24 * (x.1.size + x.2.size) + 80 * min x.1.size x.2.size + 112) ∧
        natMulKara x.1 x.2 = limbsOf (value x.1 * value x.2))
```

```lean
/-- The C function `lxf_natMulKara` computes `natMulKara` as `natMulKara_spec_trapFree` states, under every
`Archi` and every semantics of external functions. -/
theorem natMulKara_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natMulKara_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation
```

```lean
/-- `natMulKara_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natMulKara_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 20, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[20]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 × Array UInt64 => natMulKara x.1 x.2)
        (fun x heap _ => (Canonical x.1 ∧ Canonical x.2) ∧ (x.1.size < 2 ^ 32 ∧ x.2.size < 2 ^ 32) ∧
          heap.top.toNat + (24 * (x.1.size + x.2.size) + 80 * min x.1.size x.2.size + 112) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (24 * (x.1.size + x.2.size) + 80 * min x.1.size x.2.size + 112) ∧
          natMulKara x.1 x.2 = limbsOf (value x.1 * value x.2))
```

```lean
/-- Function 26, `intOfTextDC`, returns the Lean function's value, which meets its specification, and
raises `top` by at most the closed form of its bound. -/
theorem intOfTextDC_spec_trapFree :
    ImplementsA false compiled.module 26 (fun x : Array UInt64 => intOfTextDC x)
      (fun x heap store => (True) ∧ heap.Within store compiled.module (compiled.intOfTextDC.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (7 * x.size + 168) ∧
        intOfTextDC x = readSpec x)
```

```lean
/-- `intOfTextDC_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intOfTextDC_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 26, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[26]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 => intOfTextDC x)
        (fun x heap _ => (True) ∧ (x.size < 2 ^ 32) ∧
          heap.top.toNat + (7 * x.size + 168) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (7 * x.size + 168) ∧
          intOfTextDC x = readSpec x)
```

```lean
/-- Function 24, `natOfTextDCWith`, returns `natReadSpec` of its text for every threshold and every
bound `E`, and raises `top` by at most its generated bound. -/
theorem natOfTextDCWith_spec_trapFree :
    ImplementsA false compiled.module 24
      (fun x : UInt64 × UInt64 × Array UInt64 => natOfTextDCWith x.1 x.2.1 x.2.2)
      (fun x heap store => True ∧
        heap.Within store compiled.module (compiled.natOfTextDCWith.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.natOfTextDCWith.bound 1000 x ∧
        natOfTextDCWith x.1 x.2.1 x.2.2 = natReadSpec x.2.2)
```

```lean
/-- Function 24, `natOfTextDCWith`, with a bound `1 ≤ E ≤ 2^32` on the base elements, returns
`natReadSpec` of its text and raises `top` by at most the closed form of its bound. -/
theorem natOfTextDCWith_closed_trapFree :
    ImplementsA false compiled.module 24 (fun x : UInt64 × UInt64 × Array UInt64 => natOfTextDCWith x.1 x.2.1 x.2.2)
      (fun x heap store => (1 ≤ x.2.1.toNat ∧ x.2.1.toNat ≤ 2 ^ 32) ∧ heap.Within store compiled.module (compiled.natOfTextDCWith.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (19 * x.2.2.size + 262) ∧
        natOfTextDCWith x.1 x.2.1 x.2.2 = natReadSpec x.2.2)
```

## `NativeRuntime.lean`: names, start, and the runtime

```lean
/-- The C function of each export is `lxf_` followed by the export's name, and the functions whose
code takes the call depth are `lxf_` followed by their index (6, 8 to 10, and 13 to 17), the
bodies that the exported entries 18 to 26 call at depth 0; `lx_init`, `lx_status`, `lx_mem`, and the
result globals `lx_r0_l` to `lx_r2_l` that a host reads are the identifiers that the theorems name;
the translation has three result positions; and no two of its identifiers and no two of its names
coincide. -/
theorem native_names :
    (∀ p ∈ [(initId, "lx_init"),
      (statusId, "lx_status"),
      (memId, "lx_mem"),
      (resId 0 .i64, "lx_r0_l"),
      (resId 1 .i64, "lx_r1_l"),
      (resId 2 .i64, "lx_r2_l"),
      (funId 0, "lxf_alloc"),
      (funId 1, "lxf_release"),
      (funId 2, "lxf_isDigitW"),
      (funId 3, "lxf_addGen"),
      (funId 4, "lxf_subGen"),
      (funId 5, "lxf_baseMul"),
      (funId 6, "lxf_6"),
      (funId 7, "lxf_trimSeg"),
      (funId 8, "lxf_8"),
      (funId 9, "lxf_9"),
      (funId 10, "lxf_10"),
      (funId 11, "lxf_mulAddSeg"),
      (funId 12, "lxf_readInit"),
      (funId 13, "lxf_13"),
      (funId 14, "lxf_14"),
      (funId 15, "lxf_15"),
      (funId 16, "lxf_16"),
      (funId 17, "lxf_17"),
      (funId 18, "lxf_kara"),
      (funId 19, "lxf_natMulKaraWith"),
      (funId 20, "lxf_natMulKara"),
      (funId 21, "lxf_intMulKara"),
      (funId 22, "lxf_readPass"),
      (funId 23, "lxf_decimalValueDC"),
      (funId 24, "lxf_natOfTextDCWith"),
      (funId 25, "lxf_natOfTextDC"),
      (funId 26, "lxf_intOfTextDC")],
      p ∈ compiled.translation.names) ∧
    compiled.translation.nres = 3 ∧
    (compiled.translation.names.map Prod.fst).Nodup ∧
    (compiled.translation.names.map Prod.snd).Nodup
```

```lean
/-- The program's start meets the C theorems' premises on the environment, the memory, and the
heap: `init_mem` and `lx_init` give a memory related to `nativeStore` with `lx_status` 0, in the
program's environment, the initial heap meets the allocator invariant with `top` at 4,096 bytes, and
the store's memory has the cap of `nativeCap` pages. -/
theorem native_start (A : Archi) (X : ExtSem) :
    ∃ decl m0 m1, compiled.module.memory = some decl ∧
      init_mem A compiled.translation.cprogram = some m0 ∧
      (initId, globdef.Gfun (.Internal (initFunction nativeCap decl.data))) ∈
        compiled.translation.cprogram.prog_defs ∧
      eval_funcall A X (globalenv compiled.translation.cprogram) m0
        (.Internal (initFunction nativeCap decl.data)) [] E0 m1 .Vundef ∧
      StoreRel A (envOf compiled.translation compiled.module.globals.length nativeCap)
        (nativeStore compiled.module nativeCap) m1 ∧
      StatusRel A (envOf compiled.translation compiled.module.globals.length nativeCap) m1 0 ∧
      EnvOk (envOf compiled.translation compiled.module.globals.length nativeCap) ∧
      (envOf compiled.translation compiled.module.globals.length nativeCap).globals.length =
        compiled.module.globals.length ∧
      (envOf compiled.translation compiled.module.globals.length nativeCap).cap = nativeCap ∧
      compiled.translation.nres ≤
        (envOf compiled.translation compiled.module.globals.length nativeCap).nres ∧
      (∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ compiled.translation.cprogram.prog_defs →
        ∃ b, Genv.find_symbol
            (envOf compiled.translation compiled.module.globals.length nativeCap).ge (funId k) = some b ∧
          Genv.find_funct_ptr (envOf compiled.translation compiled.module.globals.length nativeCap).ge b =
            some (.Internal fd)) ∧
      (Verified.initialHeap compiled.tables).At (nativeStore compiled.module nativeCap) ∧
      (Verified.initialHeap compiled.tables).top.toNat = 4096 ∧
      (nativeStore compiled.module nativeCap).memoryCap compiled.module 0 = nativeCap
```

```lean
/-- The runtime's `alloc` at this translation: from a heap with room for the allocation, the C call
of `lxf_alloc` on `bytes` returns the new block's address with `lx_status` 0, in a memory related to
a store where the heap after the allocation meets the allocator invariant and the block is fresh. -/
theorem alloc_room_native {A : Archi} {X : ExtSem} {E : Env} (hE : EnvOk E)
    (hG : E.globals.length = compiled.module.globals.length) (hcap : E.cap = nativeCap)
    (hnres : compiled.translation.nres ≤ E.nres)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ compiled.translation.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧ Genv.find_funct_ptr E.ge b = some (.Internal fd))
    (heap : Heap) (store : Wasm.Store Unit) (bytes : UInt64) (hHeap : heap.At store)
    (hBytes : bytes.toNat ≤ 4294967296) (hCapS : store.memoryCap compiled.module 0 ≤ 65535)
    (hRoom : heap.Room store compiled.module (LeanExe.Pipeline.allocSize bytes)) (m : mem)
    (hst : StoreRel A E store m) (hs : StatusRel A E m 0) :
    ∃ fd, (funId 0, globdef.Gfun (fundef.Internal fd)) ∈ compiled.translation.cprogram.prog_defs ∧
      ∃ t m' vres st', eval_funcall A X E.ge m (.Internal fd) [.Vlong bytes] t m' vres ∧
        StoreRel A E st' m' ∧ StatusRel A E m' 0 ∧ heap.Fits (LeanExe.Pipeline.allocSize bytes) ∧
        st' = heap.allocateStore store (LeanExe.Pipeline.allocSize bytes) 1 ∧
        vres = .Vlong (LeanExe.ProofKit.FixedArrayAllocate.root heap.top
          (LeanExe.Pipeline.allocSize bytes) heap.free) ∧
        (heap.allocate (LeanExe.Pipeline.allocSize bytes)).At st' ∧
        (heap.allocate (LeanExe.Pipeline.allocSize bytes)).Block st'
          (LeanExe.ProofKit.FixedArrayAllocate.root heap.top (LeanExe.Pipeline.allocSize bytes)
            heap.free)
          (allocatedCapacity (LeanExe.Pipeline.allocSize bytes) heap.free) 1
```

```lean
/-- The runtime's `release` at this translation: the C call of `lxf_release` on an owned object
returns with `lx_status` 0 in a memory related to the store after the release, where the heap with
the object's block on the free list meets the allocator invariant. -/
theorem release_native {A : Archi} {X : ExtSem} {E : Env} (hE : EnvOk E)
    (hG : E.globals.length = compiled.module.globals.length) (hcap : E.cap = nativeCap)
    (hnres : compiled.translation.nres ≤ E.nres)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ compiled.translation.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧ Genv.find_funct_ptr E.ge b = some (.Internal fd))
    (heap : Heap) (store : Wasm.Store Unit) (ptr : UInt64) (words : Array UInt64)
    (hHeap : heap.At store) (hOwned : heap.Owned store ptr words) (m : mem)
    (hst : StoreRel A E store m) (hs : StatusRel A E m 0) :
    ∃ fd, (funId 1, globdef.Gfun (fundef.Internal fd)) ∈ compiled.translation.cprogram.prog_defs ∧
      ∃ t m', eval_funcall A X E.ge m (.Internal fd) [.Vlong ptr] t m' .Vundef ∧
        StoreRel A E (heap.releaseStore store ptr) m' ∧ StatusRel A E m' 0 ∧
        (heap.release ptr (store.mem.read64 (ptr - 32).toUInt32)).At (heap.releaseStore store ptr)
```


## `Bound.lean`: the frames of the callers

```lean
theorem natMulKaraWith_fits (k : ℕ) (hk : 65 ≤ k) (x : UInt64 × Array UInt64 × Array UInt64) :
    compiled.natMulKaraWith.fits (k + 1) x = true
```

```lean
theorem natMulKara_fits (k : ℕ) (hk : 66 ≤ k) (x : Array UInt64 × Array UInt64) :
    compiled.natMulKara.fits (k + 1) x = true
```

```lean
theorem intMulKara_fits (k : ℕ) (hk : 67 ≤ k) (x : BigInt × BigInt) :
    compiled.intMulKara.fits (k + 1) x = true
```

```lean
theorem decimalValueDC_fits (k : ℕ) (hk : 66 ≤ k)
    (x : UInt64 × UInt64 × Array UInt64 × UInt64 × UInt64) :
    compiled.decimalValueDC.fits (k + 1) x = true
```

```lean
theorem natOfTextDCWith_fits (k : ℕ) (hk : 67 ≤ k) (x : UInt64 × UInt64 × Array UInt64) :
    compiled.natOfTextDCWith.fits (k + 1) x = true
```

```lean
theorem natOfTextDC_fits (k : ℕ) (hk : 68 ≤ k) (s : Array UInt64) :
    compiled.natOfTextDC.fits (k + 1) s = true
```

```lean
theorem intOfTextDC_fits (k : ℕ) (hk : 67 ≤ k) (s : Array UInt64) :
    compiled.intOfTextDC.fits (k + 1) s = true
```


## `NativeRuntime.lean`: the helpers

Each helper has the theorem below for `kara`, with `isDigitW` 2, `compiled.isDigitW.trapFree`; `trimSeg` 7, `compiled.trimSeg.trapFree`; `readInit` 12, `compiled.readInit.trapFree`; `decimalValueDC` 23, `decimalValueDC_trapFree`; `addGen` 3, `subGen` 4, `baseMul` 5, `mulAddSeg` 11, and `readPass` 22, their `*_trapFree` of `Call.lean`.

```lean
/-- Function 23, `decimalValueDC`, computes the Lean function without a trap for every argument
within its generated bound at 1,000 frames. -/
theorem decimalValueDC_trapFree : ImplementsA false compiled.module 23
    (fun x : UInt64 × UInt64 × Array UInt64 × UInt64 × UInt64 =>
      decimalValueDC x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (fun x heap store => heap.Within store compiled.module (compiled.decimalValueDC.bound 1000 x))
    (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.decimalValueDC.bound 1000 x)
```

```lean
/-- The C function `lxf_kara`, function 18, computes the Lean function in place for every argument, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem kara_native (A : Archi) (X : ExtSem) :
    NativeImpl kara_trapFree A X nativeCap compiled.translation
```
