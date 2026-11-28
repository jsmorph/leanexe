module

public import Library.Numerics.Bignum.Program
public import Library.Numerics.Bignum.Spec
public import Library.Numerics.Bignum.Second.Spec
public import TestSupport.Host
public import TestSupport.Modules.MultiPrecision
public meta import Library.Numerics.Bignum.Program
public meta import Library.Numerics.Bignum.Spec

@[expose] public section

/-!
The cases of the bignum library.

The `#guard` cases evaluate the library functions that the modules compile into their exports
without exporting them: the divisions of Lean's convention at a zero divisor, where a negative
dividend leaves a negative remainder in both signed divisions, and the four sign combinations of
each division.  The theorems `natDivMod_eq`, `intTDivMod_eq`, and `intEDivMod_eq` cover them.

`bignum`, `bignum2`, and `bignum3` print the cases of the modules `bignum`, `bignum2`, and
`bignum3` in the form of `tests/verified/run.sh`, one line per call of an export with the result
that the library's specification gives in native Lean: `limbsOf`, `BigInt.ofInt`, `printSpec`,
`readSpec`, `natReadSpec`, and the specifications of the exports.  A natural is one `array-u64`
argument, a `BigInt` its sign as an `i64` and its magnitude, and a text an `array-u64` of one byte
to a word.  The inputs are those of `tests/bignum/check.mjs` and its companions at sizes that the
host's command line takes: 0, 1, `2^32 - 1`, `2^32`, `2^64 - 1`, runs of all-ones limbs, powers
of ten, arbitrary limbs, MultiPrecision's `divInputs`, which make step D3 decrease the trial
digit twice and step D6 add the divisor back, the dividends and divisors of the `#guard` cases in
every sign combination, zero divisors, and texts that the grammar rejects: the empty text, `-`,
`-0`, `+1`, `007`, white space, `1e3`, and words of 256 or more.  The second module's cases cover
the lengths around Karatsuba's threshold of 48 limbs and the texts around the reader's base case
of 768 chunks of nine digits, and the third module's the divisors around the recursive
division's threshold of 192 limbs and the numbers around the printer's threshold of 32 limbs,
each also at other thresholds through the entries with parameters.
-/

namespace TestSupport.Bignum.Cases

open Library.Numerics.Bignum
open TestSupport.Host

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

/-! ## Arguments and results in the host's kinds -/

/-- The argument of a natural: its canonical limbs. -/
def natArg (n : ℕ) : String := arrU (limbsOf n).toList

/-- The two arguments of an integer: its sign and the limbs of its magnitude. -/
def intArgs (z : ℤ) : List String := [u (if z < 0 then 1 else 0), natArg z.natAbs]

/-- The argument of a text. -/
def textArg (s : Array UInt64) : String := arrU s.toList

def flag (b : Bool) : String := if b then "1" else "0"

def arr (xs : Array UInt64) : String := arrOut xs.toList

def recOut (x : BigInt) : String := s!"{flag x.neg} {arr x.mag}"

/-- The text of a string, one byte to a word. -/
def text (s : String) : Array UInt64 := (s.toList.map fun c => c.toNat.toUInt64).toArray

/-! ## Inputs -/

/-- A natural of `len` arbitrary limbs whose top limb is not 0. -/
def arbNat (len seed : ℕ) : ℕ :=
  Library.Numerics.MultiPrecision.value
      (Library.Numerics.MultiPrecision.arbitraryDigits len seed).toArray +
    if len = 0 then 0 else 2 ^ (32 * (len - 1))

/-- `len` limbs of `2^32 - 1`. -/
def ones (len : ℕ) : ℕ := 2 ^ (32 * len) - 1

def specialNats : List ℕ :=
  [0, 1, 2, 5, 7, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1, 2 ^ 64 - 1, 2 ^ 64, ones 3, 2 ^ 128, 10 ^ 9,
    10 ^ 19, 10 ^ 40]

def arbitraryNats : List ℕ := [1, 2, 3, 5, 8, 13, 21, 40, 64].map fun len => arbNat len len

def natPairs : List (ℕ × ℕ) :=
  (specialNats.flatMap fun a => specialNats.map fun b => (a, b)) ++
  (arbitraryNats.flatMap fun a => arbitraryNats.map fun b => (a, b)) ++
  [(ones 60, ones 60), (ones 60, 1), (arbNat 100 3, arbNat 100 3), (arbNat 150 9, ones 45)]

/-- MultiPrecision's division inputs, as the values of their digits. -/
def divPairs : List (ℕ × ℕ) :=
  Library.Numerics.MultiPrecision.divInputs.map fun (u, v) =>
    (Library.Numerics.MultiPrecision.value u.toArray,
      Library.Numerics.MultiPrecision.value v.toArray)

/-- Arrays with zero limbs at the top, and canonical ones. -/
def trimInputs : List (Array UInt64) :=
  [#[], #[0], #[0, 0, 0], #[5, 0], #[1, 2, 0, 0], #[4294967295, 0], #[0, 0, 1], #[7, 8, 9]]

/-- The integers of the cases, among them the dividends and divisors of the `#guard` cases. -/
def specialInts : List ℤ :=
  [0, 1, -1, 2, -2, 3, -3, 5, -5, 6, -6, 7, -7, 2 ^ 32 - 1, -(2 ^ 32), 2 ^ 64 - 1, -(2 ^ 64 - 1),
    10 ^ 19, -(2 ^ 128) + 1, (arbNat 13 5 : ℤ), -(arbNat 21 6 : ℤ)]

def intPairs : List (ℤ × ℤ) := specialInts.flatMap fun a => specialInts.map fun b => (a, b)

/-- Texts that the grammar rejects. -/
def rejected : List (Array UInt64) :=
  [#[], text "-", text "-0", text "+1", text "007", text "00", text "-01", text " 1", text "1 ",
    text "1e3", text "--1", text "12a", #[49, 306], #[4294967344], #[48, 256]]

def validTexts : List (Array UInt64) :=
  (specialInts.map printSpec) ++ [printSpec (10 ^ 299), printSpec (-(10 ^ 300 - 1))]

/-- The texts of the binary text exports: some accepted and some rejected ones, in all pairs. -/
def textPairs : List (Array UInt64 × Array UInt64) :=
  let few := [text "0", text "1", text "-7", text "2", text "-3", printSpec (2 ^ 64),
    printSpec (-(10 ^ 40) - 3), text "-0", text "+1", text "007", #[]]
  few.flatMap fun s => few.map fun t => (s, t)

/-! ## The first module -/

def bignum : IO Unit := do
  for w in trimInputs do
    line "bignum" "natTrim" "array-u64" [arrU w.toList]
      (arr (limbsOf (Library.Numerics.MultiPrecision.value w)))
  for (a, b) in natPairs do
    let args := [natArg a, natArg b]
    line "bignum" "natCmp" "i64" args (toString (cmpSpec a b))
    line "bignum" "natAdd" "array-u64" args (arr (limbsOf (a + b)))
    let d := natSubSpec a b
    line "bignum" "natSub" "list:i64,array-u64" args s!"{flag d.1} {arr d.2}"
    line "bignum" "natMul" "array-u64" args (arr (limbsOf (a * b)))
  for (a, b) in natPairs ++ divPairs do
    let r := natDivModCheckedSpec a b
    line "bignum" "natDivModChecked" "list:i64,array-u64,array-u64" [natArg a, natArg b]
      s!"{r.1} {arr r.2.1} {arr r.2.2}"
  for a in specialInts do
    line "bignum" "intNeg" "list:i64,array-u64" (intArgs a) (recOut (.ofInt (-a)))
    line "bignum" "intToText" "array-u64" (intArgs a) (arr (printSpec a))
  for (a, b) in intPairs do
    let args := intArgs a ++ intArgs b
    line "bignum" "intCmp" "i64" args (toString (cmpSpec a b))
    line "bignum" "intAdd" "list:i64,array-u64" args (recOut (.ofInt (a + b)))
    line "bignum" "intSub" "list:i64,array-u64" args (recOut (.ofInt (a - b)))
    line "bignum" "intMul" "list:i64,array-u64" args (recOut (.ofInt (a * b)))
    let t := intTDivModCheckedSpec a b
    line "bignum" "intTDivModChecked" "list:i64,i64,array-u64,i64,array-u64" args
      s!"{t.1} {recOut t.2.1} {recOut t.2.2}"
    let e := intEDivModCheckedSpec a b
    line "bignum" "intEDivModChecked" "list:i64,i64,array-u64,i64,array-u64" args
      s!"{e.1} {recOut e.2.1} {recOut e.2.2}"
  for s in validTexts ++ rejected do
    let r := readSpec s
    line "bignum" "intOfText" "list:i64,i64,array-u64" [textArg s] s!"{flag r.1} {recOut r.2}"
    let n := textNegSpec s
    line "bignum" "textNeg" "list:i64,array-u64" [textArg s] s!"{n.1} {arr n.2}"
  for (s, t) in textPairs do
    let args := [textArg s, textArg t]
    let c := textCmpSpec s t
    line "bignum" "textCmp" "list:i64,i64" args s!"{c.1} {c.2}"
    for (name, f) in [("textAdd", textAddSpec), ("textSub", textSubSpec), ("textMul", textMulSpec),
        ("textTDiv", textTDivSpec), ("textTMod", textTModSpec), ("textEDiv", textEDivSpec),
        ("textEMod", textEModSpec)] do
      let r := f s t
      line "bignum" name "list:i64,array-u64" args s!"{r.1} {arr r.2}"

/-! ## The second module -/

/-- Products around Karatsuba's threshold, of all-ones operands, and of unequal lengths. -/
def mulPairs : List (ℕ × ℕ) :=
  ((List.range 5).flatMap fun i => (List.range 5).map fun j =>
    (arbNat (46 + i) (10 + i), arbNat (46 + j) (20 + j))) ++
  ((List.range 5).map fun i => (arbNat (94 + i) (30 + i), arbNat (98 - i) (40 + i))) ++
  ([1, 16, 47, 48, 49, 97, 200].map fun n => (ones n, ones n)) ++
  [(arbNat 3 1, arbNat 100 2), (arbNat 48 3, arbNat 100 4),
    (arbNat 150 5, arbNat 49 6), (arbNat 200 7, arbNat 60 8), (0, arbNat 60 9),
    (1, arbNat 60 9), (2 ^ 32 - 1, 2 ^ 32 - 1)]

/-- Texts around the boundaries of chunks of nine digits and of the reader's base case of 768
chunks. -/
def readTexts : List (Array UInt64) :=
  ([1, 8, 9, 10, 17, 18, 19, 300, 6911, 6912, 6913, 7000].map fun d => printSpec (10 ^ d - 1)) ++
  ([9, 6912].map fun d => printSpec (10 ^ d)) ++
  [printSpec (arbNat 30 11), printSpec (ones 100), printSpec (-(ones 100 : ℤ)),
    printSpec (-(10 ^ 6913 : ℤ) + 1)] ++ rejected

def bignum2 : IO Unit := do
  for (a, b) in mulPairs do
    let p := arr (limbsOf (a * b))
    line "bignum2" "natMulKara" "array-u64" [natArg a, natArg b] p
    for t in ([0, 16, 32, 100] : List UInt64) do
      line "bignum2" "natMulKaraWith" "array-u64" [u t, natArg a, natArg b] p
  for (a, b) in mulPairs.take 6 ++ [(ones 60, arbNat 50 3)] do
    let (x0, y0) : ℤ × ℤ := (a, b)
    for (x, y) in [(x0, y0), (-x0, y0), (x0, -y0), (-x0, -y0)] do
      line "bignum2" "intMulKara" "list:i64,array-u64" (intArgs x ++ intArgs y)
        (recOut (.ofInt (x * y)))
  for s in readTexts do
    let n := natReadSpec s
    line "bignum2" "natOfTextDC" "list:i64,array-u64" [textArg s] s!"{flag n.1} {arr n.2}"
    for e in ([1, 16, 64] : List UInt64) do
      line "bignum2" "natOfTextDCWith" "list:i64,array-u64" [u 48, u e, textArg s]
        s!"{flag n.1} {arr n.2}"
    let r := readSpec s
    line "bignum2" "intOfTextDC" "list:i64,i64,array-u64" [textArg s] s!"{flag r.1} {recOut r.2}"

/-! ## The third module -/

/-- Divisions around the thresholds of the recursion: divisors of 190 to 194 limbs with quotients
of 0 to 194 limbs, dividends of twice the divisor's length, divisors whose top limb is 1, all-ones
operands, dividends much longer than the divisor, and zero divisors. -/
def bzPairs : List (ℕ × ℕ) :=
  ((List.range 5).flatMap fun i => [0, 1, 31, 32, 33, 192, 194].map fun q =>
    (arbNat (190 + i + q) (50 + i + q), arbNat (190 + i) (60 + i))) ++
  ([30, 64, 100, 193, 385].map fun n => (arbNat (2 * n) n, 2 ^ (32 * (n - 1)) + arbNat 2 n)) ++
  ([2, 3, 200, 400].map fun n => (ones (2 * n + 1), ones n)) ++
  [(arbNat 2000 1, arbNat 10 2), (arbNat 1200 3, arbNat 200 4),
    (arbNat 600 5, arbNat 400 6), (arbNat 300 7, 0), (arbNat 10 8, arbNat 300 9)] ++
  divPairs

/-- Numbers around the printer's thresholds: 30 to 33 limbs, 60, 120, and 240 limbs, the powers
`10^(9·2^i)` by which it divides, one more and one less, and their squares. -/
def printNats : List ℕ :=
  [0, 1, 9, 10, 10 ^ 9 - 1, 10 ^ 9, 2 ^ 64 - 1, ones 3] ++
  ([1, 29, 30, 31, 32, 33, 60, 120, 240, 300].map fun n => arbNat n (70 + n)) ++
  ([31, 32, 33, 240].map ones) ++
  ((List.range 7).flatMap fun i =>
    let p := 10 ^ (9 * 2 ^ (i + 1))
    [p - 1, p, p + 1, p * p, p * (p - 1)])

def bignum3 : IO Unit := do
  for (a, b) in bzPairs do
    let r := natDivModCheckedSpec a b
    let out := s!"{r.1} {arr r.2.1} {arr r.2.2}"
    line "bignum3" "natDivModCheckedBZ" "list:i64,array-u64,array-u64" [natArg a, natArg b] out
    line "bignum3" "natDivModCheckedBZWith" "list:i64,array-u64,array-u64"
      [u 16, u 4, u 2, natArg a, natArg b] out
  for (a, b) in (bzPairs.take 8).map (fun (a, b) => ((a : ℤ), (b : ℤ))) ++
      [(5, 0), (-5, 0), (-7, 2), (7, -2), (-7, -2), (-6, -3), (0, -3)] do
    for (x, y) in [(a, b), (-a, b), (a, -b), (-a, -b)] do
      let args := intArgs x ++ intArgs y
      let t := intTDivModCheckedSpec x y
      line "bignum3" "intTDivModCheckedBZ" "list:i64,i64,array-u64,i64,array-u64" args
        s!"{t.1} {recOut t.2.1} {recOut t.2.2}"
      let e := intEDivModCheckedSpec x y
      line "bignum3" "intEDivModCheckedBZ" "list:i64,i64,array-u64,i64,array-u64" args
        s!"{e.1} {recOut e.2.1} {recOut e.2.2}"
  for n in printNats do
    let t := arr (printSpec n)
    line "bignum3" "natToTextDC" "array-u64" [natArg n] t
    line "bignum3" "natToTextDCWith" "array-u64" [u 16, u 4, u 1, u 0, natArg n] t
    line "bignum3" "intToTextDC" "array-u64" (intArgs n) t
    line "bignum3" "intToTextDC" "array-u64" (intArgs (-(n : ℤ))) (arr (printSpec (-(n : ℤ))))

end TestSupport.Bignum.Cases
