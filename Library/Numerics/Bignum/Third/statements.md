# Main statements of the third iteration

The statements were copied from the Lean files when the library was developed in another repository; this copy gives the library's present paths and names.

The statements below are copied from the Lean files with their proofs omitted.  `value`, `Digits`, and `base = 2^32` are leanexe's `Library.Numerics.MultiPrecision` definitions; `limbsOf`, `Canonical`, `BigInt`, `BigInt.ofInt`, `BigInt.toInt`, `natDivModSpec`, `natDivModCheckedSpec`, `intTDivModCheckedSpec`, `intEDivModCheckedSpec`, `printSpec`, `readSpec`, `natDivMod`, `natDivModChecked`, `intTDivModChecked`, `intEDivModChecked`, `intToText`, and `intOfText` are the first iteration's (`Library/Numerics/Bignum/Spec.lean`, `Library/Numerics/Bignum/Program.lean`); `SegDigits` and `segVal` are the second iteration's values of segments (`Second/Seg.lean`); and `compiled` is the third iteration's module (`Third/Compiled.lean`).  The functions are in `Third/Program.lean`.

The interface of the module is functions 65, 66, 67, 72, and 73: `natDivModCheckedBZ`, `intTDivModCheckedBZ`, `intEDivModCheckedBZ`, `natToTextDC`, and `intToTextDC`, with functions 64 and 71, `natDivModCheckedBZWith` and `natToTextDCWith`, which take the thresholds as arguments.  Each call theorem states the first iteration's specification of the result for canonical arguments, with no premise on the depth, and each room theorem bounds the allocation by a closed form linear in the lengths.

The C form's statements, in `Native.lean` and `NativeRuntime.lean`, use leanexe's `LeanExe.Native.NativeImpl` and `LeanExe.Native.NativeA`, which relate one call of the C function `lxf_f` in leanexe's Lean copy of CompCert's Clight to the module's `ImplementsA` theorem, and `compiled.translation`, the translation of the module with `lx_mem` of `nativeCap = 4096` pages.
Each of the seven exports has the three theorems `f_spec_trapFree`, `f_native_spec`, and `f_native_size`, of the forms shown below for `natDivModCheckedBZ`, with the export's index, function, specification, and closed form; the `_native_size` theorems of all seven are listed.  `NativeRuntime.lean` states a theorem `f_native` of the form of `rdiv_native` for each helper with a theorem in `Call.lean` or a generated one: `trialAt`, `mulSubSeg`, `baseDiv`, `subFix`, `divSmallSeg`, `signTDiv`, `signEDiv`, `leafChunks`, `textOfChunks`, `kara`, `mulChunk`, `mulAcc`, `halfStep`, `lowHalf`, `rdiv`, `tdiv`, `udiv`, `divSeg`, `powInit`, and `chunksDC`.

## `DivBase.lean`

```lean
/-- What a division in place leaves: the dividend's segment of `n + m` limbs at `ap` holds the
remainder by the `n` limbs at `bp`, the `m` limbs at `qp` and the returned top word hold the
quotient, and every word outside those two segments and the `S` words of scratch at `sp` keeps its
value. -/
def DivPost (W : Array UInt64) (ap bp qp sp n m S : ℕ) (r : UInt64 × Array UInt64) : Prop :=
  r.2.size = W.size ∧
  (∀ p, ¬ (ap ≤ p ∧ p < ap + n + m) → ¬ (qp ≤ p ∧ p < qp + m) → ¬ (sp ≤ p ∧ p < sp + S) →
    r.2[p]! = W[p]!) ∧
  SegDigits r.2 ap (n + m) ∧ SegDigits r.2 qp m ∧ r.1.toNat ≤ 1 ∧
  segVal r.2 ap (n + m) = segVal W ap (n + m) % segVal W bp n ∧
  segVal r.2 qp m + r.1.toNat * base ^ m = segVal W ap (n + m) / segVal W bp n
```

```lean
/-- Algorithm 1.6 with Knuth's steps: `baseDiv` divides the `n + m` limbs at `ap` by the
normalized `n ≥ 2` limbs at `bp`, for the quotient below the divisor and the divisor below the
dividend. -/
theorem baseDiv_spec (W : Array UInt64) (ap bp qp n m : UInt64) (hW : W.size < 2 ^ 62)
    (hn : 2 ≤ n.toNat) (hqb : qp.toNat + m.toNat ≤ bp.toNat) (hba : bp.toNat + n.toNat ≤ ap.toNat)
    (hsz : ap.toNat + n.toNat + m.toNat ≤ W.size)
    (hda : SegDigits W ap.toNat (n.toNat + m.toNat)) (hdb : SegDigits W bp.toNat n.toNat)
    (hv1 : base ≤ 2 * W[bp.toNat + n.toNat - 1]!.toNat) (sp : ℕ) :
    DivPost W ap.toNat bp.toNat qp.toNat sp n.toNat m.toNat 0 (baseDiv W ap bp qp n m)
```

## `DivRec.lean`

```lean
/-- Algorithm 1.8 divides the `n + m` limbs at `ap` by the normalized `n ≥ 2` limbs at `bp`, for
`m ≤ n`, the quotient below the divisor, the divisor below the dividend, and the dividend below
`6 m + 9` words of scratch. -/
theorem rdiv_spec (t T : UInt64) : ∀ (m : ℕ) (W : Array UInt64) (ap bp qp sp n mm : UInt64),
    mm.toNat = m → W.size < 2 ^ 62 → 2 ≤ n.toNat → m ≤ n.toNat →
    qp.toNat + m ≤ bp.toNat → bp.toNat + n.toNat ≤ ap.toNat →
    ap.toNat + n.toNat + m ≤ sp.toNat → sp.toNat + 6 * m + 9 ≤ W.size →
    SegDigits W ap.toNat (n.toNat + m) → SegDigits W bp.toNat n.toNat →
    base ≤ 2 * W[bp.toNat + n.toNat - 1]!.toNat →
    DivPost W ap.toNat bp.toNat qp.toNat sp.toNat n.toNat m (6 * m + 9)
      (rdiv t T W ap bp qp sp n mm)
```

## `DivTop.lean`

```lean
/-- The last part of Algorithm 1.9 for `2 ≤ m < n` quotient limbs: the top `2 m` limbs divided by
the top `m` limbs of the divisor, and the correction by the product with the low `n - m` limbs. -/
theorem tdiv_spec (t T : UInt64) (W : Array UInt64) (ap bp qp sp n mm : UInt64) (N m : ℕ)
    (hN : n.toNat = N) (hm : mm.toNat = m) (hW : W.size < 2 ^ 62) (hm2 : 2 ≤ m) (hmN : m < N)
    (hqb : qp.toNat + m ≤ bp.toNat) (hba : bp.toNat + N ≤ ap.toNat)
    (has : ap.toNat + N + m ≤ sp.toNat) (hsz : sp.toNat + 12 * N + 9 ≤ W.size)
    (hda : SegDigits W ap.toNat (N + m)) (hdb : SegDigits W bp.toNat N)
    (hv1 : base ≤ 2 * W[bp.toNat + N - 1]!.toNat) :
    DivPost W ap.toNat bp.toNat qp.toNat sp.toNat N m (12 * N + 9)
      (tdiv t T W ap bp qp sp n mm)
```

```lean
/-- Algorithm 1.9: `udiv` divides the `n + M` limbs at `ap`, below `β^M B`, by the normalized
`n ≥ 2` limbs `B` at `bp`, with the quotient in the `M` limbs at `qp` and the remainder over the
dividend's segment. -/
theorem udiv_spec (t T : UInt64) (W : Array UInt64) (ap bp qp sp n MM : UInt64) (N M : ℕ)
    (hN : n.toNat = N) (hM : MM.toNat = M) (hW : W.size < 2 ^ 62) (hn : 2 ≤ N) (hM1 : 1 ≤ M)
    (hqb : qp.toNat + M ≤ bp.toNat) (hba : bp.toNat + N ≤ ap.toNat)
    (has : ap.toNat + N + M ≤ sp.toNat) (hsz : sp.toNat + 12 * N + 9 ≤ W.size)
    (hda : SegDigits W ap.toNat (N + M)) (hdb : SegDigits W bp.toNat N)
    (hv1 : base ≤ 2 * W[bp.toNat + N - 1]!.toNat)
    (hlt : segVal W ap.toNat (N + M) < base ^ M * segVal W bp.toNat N) :
    (udiv t T W ap bp qp sp n MM).size = W.size ∧
    (∀ p, ¬ (ap.toNat ≤ p ∧ p < ap.toNat + N + M) → ¬ (qp.toNat ≤ p ∧ p < qp.toNat + M) →
      ¬ (sp.toNat ≤ p ∧ p < sp.toNat + (12 * N + 9)) → (udiv t T W ap bp qp sp n MM)[p]! = W[p]!) ∧
    SegDigits (udiv t T W ap bp qp sp n MM) ap.toNat (N + M) ∧
    SegDigits (udiv t T W ap bp qp sp n MM) qp.toNat M ∧
    segVal (udiv t T W ap bp qp sp n MM) ap.toNat (N + M) =
      segVal W ap.toNat (N + M) % segVal W bp.toNat N ∧
    segVal (udiv t T W ap bp qp sp n MM) qp.toNat M =
      segVal W ap.toNat (N + M) / segVal W bp.toNat N
```

## `DivNat.lean`

```lean
/-- `divSeg` divides the `lx` limbs `X` at `xp` by the `n ≥ 2` limbs `D` at `dp`, whose top limb
is not 0, for `n ≤ lx`: the `lx + 1 - n` limbs at `qp` receive `X / D`, the segment at `xp` holds
`X % D`, and every word outside those, and outside the `13 n + lx + 10` words of scratch at `sp`,
keeps its value. -/
theorem divSeg_spec (t T : UInt64) (W : Array UInt64) (xp lx dp n qp sp : UInt64) (N LX : ℕ)
    (hN : n.toNat = N) (hLX : lx.toNat = LX) (hW : W.size < 2 ^ 62) (hn : 2 ≤ N) (hNL : N ≤ LX)
    (hxq : xp.toNat + LX ≤ qp.toNat) (hdq : dp.toNat + N ≤ qp.toNat)
    (hqs : qp.toNat + (LX + 1 - N) ≤ sp.toNat) (hsz : sp.toNat + 13 * N + LX + 10 ≤ W.size)
    (hdx : SegDigits W xp.toNat LX) (hdd : SegDigits W dp.toNat N)
    (htop : W[dp.toNat + N - 1]! ≠ 0) :
    (divSeg t T W xp lx dp n qp sp).size = W.size ∧
    (∀ p, ¬ (xp.toNat ≤ p ∧ p < xp.toNat + LX) → ¬ (qp.toNat ≤ p ∧ p < qp.toNat + (LX + 1 - N)) →
      ¬ (sp.toNat ≤ p ∧ p < sp.toNat + (13 * N + LX + 10)) → (divSeg t T W xp lx dp n qp sp)[p]! = W[p]!) ∧
    SegDigits (divSeg t T W xp lx dp n qp sp) xp.toNat LX ∧
    SegDigits (divSeg t T W xp lx dp n qp sp) qp.toNat (LX + 1 - N) ∧
    segVal (divSeg t T W xp lx dp n qp sp) xp.toNat LX = segVal W xp.toNat LX % segVal W dp.toNat N ∧
    segVal (divSeg t T W xp lx dp n qp sp) qp.toNat (LX + 1 - N) =
      segVal W xp.toNat LX / segVal W dp.toNat N
```

```lean
/-- The natural division of the third iteration returns the canonical limbs of the quotient and
the remainder, with `u / 0 = 0` and `u % 0 = u`, at every threshold. -/
theorem natDivModBZWith_eq (t T D : UInt64) {u v : Array UInt64} (hu : Canonical u)
    (hv : Canonical v) (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    natDivModBZWith t T D u v = natDivModSpec (value u) (value v)
```

```lean
/-- The natural division of the third iteration returns what the first iteration's returns. -/
theorem natDivModBZ_eq_natDivMod {u v : Array UInt64} (hu : Canonical u) (hv : Canonical v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) : natDivModBZ u v = natDivMod u v
```

```lean
/-- The export of natural division with its thresholds: the status 1 and two zeros for a zero
divisor, and otherwise the status 0 and the canonical limbs of the quotient and the remainder, at
every threshold. -/
theorem natDivModCheckedBZWith_eq (t T D : UInt64) {u v : Array UInt64} (hu : Canonical u)
    (hv : Canonical v) (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    natDivModCheckedBZWith t T D u v = natDivModCheckedSpec (value u) (value v)
```

```lean
/-- The export of natural division: the status 1 and two zeros for a zero divisor, and otherwise
the status 0 and the canonical limbs of the quotient and the remainder. -/
theorem natDivModCheckedBZ_eq {u v : Array UInt64} (hu : Canonical u) (hv : Canonical v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    natDivModCheckedBZ u v = natDivModCheckedSpec (value u) (value v)
```

```lean
/-- The export of natural division returns what the first iteration's returns. -/
theorem natDivModCheckedBZ_eq_natDivModChecked {u v : Array UInt64} (hu : Canonical u)
    (hv : Canonical v) (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    natDivModCheckedBZ u v = natDivModChecked u v
```

```lean
/-- Truncated division returns what the first iteration's returns. -/
theorem intTDivModCheckedBZ_eq_intTDivModChecked {x y : BigInt} (hx : Canonical x.mag)
    (hy : Canonical y.mag) (hsx : x.mag.size < 2 ^ 32) (hsy : y.mag.size < 2 ^ 32) :
    intTDivModCheckedBZ x y = intTDivModChecked x y
```

```lean
/-- Euclidean division returns what the first iteration's returns. -/
theorem intEDivModCheckedBZ_eq_intEDivModChecked {x y : BigInt} (hx : Canonical x.mag)
    (hy : Canonical y.mag) (hsx : x.mag.size < 2 ^ 32) (hsy : y.mag.size < 2 ^ 32) :
    intEDivModCheckedBZ x y = intEDivModChecked x y
```

```lean
/-- The export of truncated division: the status 1 and two zeros for a zero divisor, and
otherwise the status 0 and the canonical integers of `Int.tdiv` and `Int.tmod`. -/
theorem intTDivModCheckedBZ_eq {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) :
    intTDivModCheckedBZ (.ofInt a) (.ofInt b) = intTDivModCheckedSpec a b
```

```lean
/-- The export of Euclidean division: the status 1 and two zeros for a zero divisor, and
otherwise the status 0 and the canonical integers of Lean's `/` and `%`. -/
theorem intEDivModCheckedBZ_eq {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) :
    intEDivModCheckedBZ (.ofInt a) (.ofInt b) = intEDivModCheckedSpec a b
```

```lean
/-- The quotient and the remainder of the natural division are canonical. -/
theorem natDivModBZ_canonical {u v : Array UInt64} (hu : Canonical u) (hv : Canonical v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    Canonical (natDivModBZ u v).1 ∧ Canonical (natDivModBZ u v).2
```

```lean
/-- The quotient and the remainder of the integer divisions are canonical. -/
theorem intDivModCheckedBZ_canonical {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) :
    (intTDivModCheckedBZ (.ofInt a) (.ofInt b)).2.1.Canonical ∧
    (intTDivModCheckedBZ (.ofInt a) (.ofInt b)).2.2.Canonical ∧
    (intEDivModCheckedBZ (.ofInt a) (.ofInt b)).2.1.Canonical ∧
    (intEDivModCheckedBZ (.ofInt a) (.ofInt b)).2.2.Canonical
```

## `PrintLeaf.lean`

```lean
/-- Entry `j` of the table of powers at `tb`: the position and the number of limbs of
`P_j = 10^(9·2^j)` within `2^(j+1)` words from `pb`, with at most `2^j` limbs and a top limb that
is not 0. -/
def PowOK (W : Array UInt64) (tb pb j : ℕ) : Prop :=
  pb ≤ W[tb + 2 * j]!.toNat ∧ W[tb + 2 * j]!.toNat + W[tb + 2 * j + 1]!.toNat ≤ pb + 2 ^ (j + 1) ∧
  1 ≤ W[tb + 2 * j + 1]!.toNat ∧ W[tb + 2 * j + 1]!.toNat ≤ 2 ^ j ∧
  SegDigits W W[tb + 2 * j]!.toNat W[tb + 2 * j + 1]!.toNat ∧
  segVal W W[tb + 2 * j]!.toNat W[tb + 2 * j + 1]!.toNat = 10 ^ (9 * 2 ^ j) ∧
  W[W[tb + 2 * j]!.toNat + W[tb + 2 * j + 1]!.toNat - 1]! ≠ 0
```

## `PrintRec.lean`

```lean
/-- What `toChunks` at level `i` leaves: the `2^(i+1)` chunks of `X` at `cp`, and every word
outside the number's `2 N` limbs at `p`, the chunks, and the `16 N + 11` words from `fp` kept. -/
def ChunksPost (W : Array UInt64) (p cp fp N X i : ℕ) (R : Array UInt64) : Prop :=
  R.size = W.size ∧
  (∀ q, ¬ (p ≤ q ∧ q < p + 2 * N) → ¬ (cp ≤ q ∧ q < cp + 2 ^ (i + 1)) →
    ¬ (fp ≤ q ∧ q < fp + 16 * N + 11) → R[q]! = W[q]!) ∧
  ∀ j, j < 2 ^ (i + 1) → R[cp + j]!.toNat = X / 10 ^ (9 * j) % 10 ^ 9
```

```lean
/-- Algorithm 1.26 at level `i`: `toChunks` writes the chunks of nine digits of the `2 n_i` limbs
at `p`, below `P_i²`, for the table of the powers below `p` and the chunks below the powers. -/
theorem toChunks_spec (t T L : UInt64) : ∀ (i : ℕ) (W : Array UInt64) (tb ii p cp fp : UInt64)
    (pb : ℕ), ii.toNat = i → i < 40 → W.size < 2 ^ 62 →
    (∀ j, j ≤ i → PowOK W tb.toNat pb j) →
    tb.toNat + 2 * i + 2 ≤ cp.toNat → cp.toNat + 2 ^ (i + 1) ≤ pb →
    (∀ j, j ≤ i → W[tb.toNat + 2 * j]!.toNat + W[tb.toNat + 2 * j + 1]!.toNat ≤ p.toNat) →
    p.toNat + 2 * W[tb.toNat + 2 * i + 1]!.toNat ≤ fp.toNat →
    fp.toNat + 16 * W[tb.toNat + 2 * i + 1]!.toNat + 11 ≤ W.size →
    SegDigits W p.toNat (2 * W[tb.toNat + 2 * i + 1]!.toNat) →
    segVal W p.toNat (2 * W[tb.toNat + 2 * i + 1]!.toNat) < 10 ^ (9 * 2 ^ (i + 1)) →
    ChunksPost W p.toNat cp.toNat fp.toNat W[tb.toNat + 2 * i + 1]!.toNat
      (segVal W p.toNat (2 * W[tb.toNat + 2 * i + 1]!.toNat)) i (toChunks t T L W tb ii p cp fp)
```

## `PrintText.lean`

```lean
/-- `chunksDC` writes the `2^(K+1)` chunks of nine digits of `u` from position `2 K + 2`. -/
theorem chunksDC_spec (t T L : UInt64) (u : Array UInt64) (hu : Digits u) (hs : u.size < 2 ^ 32)
    (j : ℕ) (hj : j < 2 ^ ((levelsFor (u.size.toUInt64 + u.size.toUInt64 / 14 + 2)).toNat + 1)) :
    (chunksDC t T L u)[2 * (levelsFor (u.size.toUInt64 + u.size.toUInt64 / 14 + 2)).toNat + 2 +
      j]!.toNat = value u / 10 ^ (9 * j) % 10 ^ 9
```

```lean
/-- The natural printer of the third iteration writes Lean's decimal text of the value, at every
threshold. -/
theorem natToTextDCWith_eq (t T L P : UInt64) {u : Array UInt64} (hu : Canonical u)
    (hs : u.size < 2 ^ 32) : natToTextDCWith t T L P u = printSpec (value u : ℤ)
```

```lean
theorem natToTextDC_eq {u : Array UInt64} (hu : Canonical u) (hs : u.size < 2 ^ 32) :
    natToTextDC u = printSpec (value u : ℤ)
```

```lean
/-- The natural printer writes the first iteration's text of the natural as an integer. -/
theorem natToTextDC_eq_intToText {u : Array UInt64} (hu : Canonical u) (hs : u.size < 2 ^ 32) :
    natToTextDC u = intToText ⟨false, u⟩
```

```lean
/-- The integer printer of the third iteration writes Lean's decimal text of the integer. -/
theorem intToTextDC_eq {z : ℤ} (h : (BigInt.ofInt z).mag.size < 2 ^ 32) :
    intToTextDC (.ofInt z) = printSpec z
```

```lean
/-- The integer printer writes the first iteration's text. -/
theorem intToTextDC_eq_intToText {z : ℤ} (h : (BigInt.ofInt z).mag.size < 2 ^ 32) :
    intToTextDC (.ofInt z) = intToText (.ofInt z)
```

```lean
/-- The integer printer writes the bytes of Lean's `toString`, one to a word. -/
theorem intToTextDC_toString {z : ℤ} (h : (BigInt.ofInt z).mag.size < 2 ^ 32) :
    intToTextDC (.ofInt z) = Library.Numerics.Decimal.Shared.StrconvGrammar.words
      (Library.Numerics.Decimal.Shared.StrconvGrammar.ascii (toString z))
```

```lean
/-- Reading the printer's text gives the integer back. -/
theorem readSpec_intToTextDC {z : ℤ} (h : (BigInt.ofInt z).mag.size < 2 ^ 32) :
    readSpec (intToTextDC (.ofInt z)) = (true, .ofInt z)
```

```lean
/-- The first iteration's reader reads the printer's text back. -/
theorem intOfText_intToTextDC {z : ℤ} (h : (BigInt.ofInt z).mag.size < 2 ^ 32)
    (hp : (printSpec z).size < 2 ^ 32) : intOfText (intToTextDC (.ofInt z)) = (true, .ofInt z)
```

## `Bound.lean`

```lean
/-- `rdiv` finds its frames for every argument with 135 frames. -/
theorem rdiv_fits_all (k : ℕ) (hk : 135 ≤ k) (x : UInt64 × UInt64 ×
    LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :
    compiled.rdiv.fits k x = true
```

```lean
theorem chunksDC_fits (k : ℕ) (hk : 180 ≤ k) (x : UInt64 × UInt64 × UInt64 × Array UInt64) :
    compiled.chunksDC.fits k x = true
```

```lean
theorem natDivModCheckedBZWith_fits (k : ℕ) (hk : 139 ≤ k)
    (x : UInt64 × UInt64 × UInt64 × Array UInt64 × Array UInt64) :
    compiled.natDivModCheckedBZWith.fits k x = true
```

```lean
theorem natToTextDCWith_fits (k : ℕ) (hk : 181 ≤ k)
    (x : UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64) :
    compiled.natToTextDCWith.fits k x = true
```

```lean
/-- The natural division allocates at most `128 m + 144 n + 824` bytes for operands of `m` and
`n` limbs, at every threshold: the first iteration's bound, which Algorithm D below the threshold
attains, and above it `32 m + 120 n + 264` for the workspace and the two results. -/
theorem natDivModCheckedBZWith_bound_le (k : ℕ) (t T D : UInt64) (u v : Array UInt64)
    (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.natDivModCheckedBZWith.bound (k + 1) (t, T, D, u, v) ≤
      128 * u.size + 144 * v.size + 824
```

```lean
theorem intTDivModCheckedBZ_bound_le (k : ℕ) (x y : BigInt) (hx : x.mag.size < 2 ^ 32)
    (hy : y.mag.size < 2 ^ 32) :
    compiled.intTDivModCheckedBZ.bound (k + 3) (x, y) ≤
      128 * x.mag.size + 144 * y.mag.size + 824
```

```lean
/-- The Euclidean division adds to the natural division the moves of its two results and, for a
negative dividend with a remainder, the successor of the quotient and the difference of the
divisor and the remainder. -/
theorem intEDivModCheckedBZ_bound_le (k : ℕ) (x y : BigInt) (hx : x.mag.size < 2 ^ 32)
    (hy : y.mag.size < 2 ^ 32) :
    compiled.intEDivModCheckedBZ.bound (k + 3) (x, y) ≤
      248 * x.mag.size + 248 * y.mag.size + 1472
```

```lean
/-- The natural printer allocates at most `438 n + 1968` bytes for `n` limbs, at every threshold
and every level of the leaves. -/
theorem natToTextDCWith_bound_le (k : ℕ) (t T L P : UInt64) (u : Array UInt64)
    (hs : u.size < 2 ^ 32) :
    compiled.natToTextDCWith.bound (k + 2) (t, T, L, P, u) ≤ 438 * u.size + 1968
```

```lean
/-- The integer printer allocates at most `438 n + 1968` bytes for a magnitude of `n` limbs. -/
theorem intToTextDC_bound_le (k : ℕ) (x : BigInt) (hs : x.mag.size < 2 ^ 32) :
    compiled.intToTextDC.bound (k + 2) x ≤ 438 * x.mag.size + 1968
```

## `Call.lean`

```lean
/-- Function 65, `natDivModCheckedBZ`, called with two canonical naturals, returns the status 1
and two zeros for a zero divisor, and otherwise the status 0 with the canonical limbs of the
quotient and the remainder: the first iteration's `natDivModCheckedSpec`. -/
theorem natDivModCheckedBZ_call :
    Verified.Call compiled.module compiled.tables 65
      (fun x : Array UInt64 × Array UInt64 => natDivModCheckedSpec (value x.1) (value x.2))
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧
        heap.Within store compiled.module (compiled.natDivModCheckedBZ.bound 1000 x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + compiled.natDivModCheckedBZ.bound 1000 x)
```

```lean
/-- Function 66, `intTDivModCheckedBZ`, called with two canonical integers, returns the status 1
and two zeros for a zero divisor, and otherwise the status 0 with `Int.tdiv` and `Int.tmod` of
their integers: the first iteration's `intTDivModCheckedSpec`. -/
theorem intTDivModCheckedBZ_call :
    Verified.Call compiled.module compiled.tables 66
      (fun x : BigInt × BigInt => intTDivModCheckedSpec x.1.toInt x.2.toInt)
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧
        heap.Within store compiled.module (compiled.intTDivModCheckedBZ.bound 1000 x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + compiled.intTDivModCheckedBZ.bound 1000 x)
```

```lean
/-- Function 67, `intEDivModCheckedBZ`, called with two canonical integers, returns the status 1
and two zeros for a zero divisor, and otherwise the status 0 with Lean's `/` and `%` of their
integers: the first iteration's `intEDivModCheckedSpec`. -/
theorem intEDivModCheckedBZ_call :
    Verified.Call compiled.module compiled.tables 67
      (fun x : BigInt × BigInt => intEDivModCheckedSpec x.1.toInt x.2.toInt)
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧
        heap.Within store compiled.module (compiled.intEDivModCheckedBZ.bound 1000 x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + compiled.intEDivModCheckedBZ.bound 1000 x)
```

```lean
/-- Function 72, `natToTextDC`, called with a canonical natural, returns the bytes of Lean's
`toString` of it, one byte to a word: `printSpec` of the natural as an integer, the text of the
first iteration's `intToText`. -/
theorem natToTextDC_call :
    Verified.Call compiled.module compiled.tables 72
      (fun u : Array UInt64 => printSpec (value u : ℤ))
      (fun u heap store => Canonical u ∧
        heap.Within store compiled.module (compiled.natToTextDC.bound 1000 u))
      (fun u heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.natToTextDC.bound 1000 u)
```

```lean
/-- Function 73, `intToTextDC`, called with a canonical integer, returns the bytes of Lean's
`toString` of its integer, one byte to a word: the first iteration's `printSpec`. -/
theorem intToTextDC_call :
    Verified.Call compiled.module compiled.tables 73
      (fun x : BigInt => printSpec x.toInt)
      (fun x heap store => x.Canonical ∧
        heap.Within store compiled.module (compiled.intToTextDC.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.intToTextDC.bound 1000 x)
```

```lean
/-- Function 64, `natDivModCheckedBZWith`, called with any thresholds and two canonical naturals,
returns `natDivModCheckedSpec` of them. -/
theorem natDivModCheckedBZWith_call :
    Verified.Call compiled.module compiled.tables 64
      (fun x : UInt64 × UInt64 × UInt64 × Array UInt64 × Array UInt64 =>
        natDivModCheckedSpec (value x.2.2.2.1) (value x.2.2.2.2))
      (fun x heap store => (Canonical x.2.2.2.1 ∧ Canonical x.2.2.2.2) ∧
        heap.Within store compiled.module (compiled.natDivModCheckedBZWith.bound 1000 x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + compiled.natDivModCheckedBZWith.bound 1000 x)
```

```lean
/-- Function 71, `natToTextDCWith`, called with any thresholds, any level of the leaves, and a
canonical natural, returns `printSpec` of the natural as an integer. -/
theorem natToTextDCWith_call :
    Verified.Call compiled.module compiled.tables 71
      (fun x : UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64 => printSpec (value x.2.2.2.2 : ℤ))
      (fun x heap store => Canonical x.2.2.2.2 ∧
        heap.Within store compiled.module (compiled.natToTextDCWith.bound 1000 x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + compiled.natToTextDCWith.bound 1000 x)
```

```lean
theorem natDivModCheckedBZ_room (u v : Array UInt64) (hu : u.size < 2 ^ 32)
    (hv : v.size < 2 ^ 32) :
    compiled.natDivModCheckedBZ.bound 1000 (u, v) ≤ 128 * u.size + 144 * v.size + 824
```

```lean
theorem intTDivModCheckedBZ_room (x y : BigInt) (hx : x.mag.size < 2 ^ 32)
    (hy : y.mag.size < 2 ^ 32) :
    compiled.intTDivModCheckedBZ.bound 1000 (x, y) ≤ 128 * x.mag.size + 144 * y.mag.size + 824
```

```lean
theorem intEDivModCheckedBZ_room (x y : BigInt) (hx : x.mag.size < 2 ^ 32)
    (hy : y.mag.size < 2 ^ 32) :
    compiled.intEDivModCheckedBZ.bound 1000 (x, y) ≤
      248 * x.mag.size + 248 * y.mag.size + 1472
```

```lean
theorem natToTextDC_room (u : Array UInt64) (hs : u.size < 2 ^ 32) :
    compiled.natToTextDC.bound 1000 u ≤ 438 * u.size + 1968
```

```lean
theorem intToTextDC_room (x : BigInt) (hs : x.mag.size < 2 ^ 32) :
    compiled.intToTextDC.bound 1000 x ≤ 438 * x.mag.size + 1968
```

```lean
theorem natDivModCheckedBZWith_room (t T D : UInt64) (u v : Array UInt64)
    (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.natDivModCheckedBZWith.bound 1000 (t, T, D, u, v) ≤
      128 * u.size + 144 * v.size + 824
```

```lean
theorem natToTextDCWith_room (t T L P : UInt64) (u : Array UInt64) (hs : u.size < 2 ^ 32) :
    compiled.natToTextDCWith.bound 1000 (t, T, L, P, u) ≤ 438 * u.size + 1968
```

```lean
/-- Function 60, `rdiv`, Algorithm 1.8, computes the Lean function in place for every argument,
allocating nothing, with no premise on the depth. -/
theorem rdiv_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 60
    (fun x : UInt64 × UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 ×
        UInt64 × UInt64 × UInt64 =>
      rdiv x.1 x.2.1 x.2.2.1.val x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
        x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat)
```

```lean
/-- Function 63, `divSeg`, the division of segments with the normalization, computes the Lean
function in place for every argument, allocating nothing, with no premise on the depth. -/
theorem divSeg_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 63
    (fun x : UInt64 × UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 ×
        UInt64 × UInt64 × UInt64 =>
      divSeg x.1 x.2.1 x.2.2.1.val x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
        x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat)
```

```lean
/-- Function 70, `chunksDC`, returns the Lean function's value, the chunks of nine digits of its
natural (`chunksDC_spec`), from a ready store with room for its bound at 1,000 frames, which
`chunksDC_bound_le` bounds, with no premise on the depth. -/
theorem chunksDC_call :
    Verified.CallSpec compiled.module compiled.tables 70
      (fun x : UInt64 × UInt64 × UInt64 × Array UInt64 => chunksDC x.1 x.2.1 x.2.2.1 x.2.2.2)
      (fun x => compiled.chunksDC.bound 1000 x)
```


## `Native.lean`

```lean
/-- Function 65, `natDivModCheckedBZ`, returns the Lean function's value, which meets its specification, and
raises `top` by at most the closed form of its bound. -/
theorem natDivModCheckedBZ_spec_trapFree :
    ImplementsA false compiled.module 65 (fun x : Array UInt64 × Array UInt64 => natDivModCheckedBZ x.1 x.2)
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧ heap.Within store compiled.module (compiled.natDivModCheckedBZ.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (128 * x.1.size + 144 * x.2.size + 824) ∧
        natDivModCheckedBZ x.1 x.2 = natDivModCheckedSpec (value x.1) (value x.2))
```

```lean
/-- The C function `lxf_natDivModCheckedBZ` computes `natDivModCheckedBZ` as `natDivModCheckedBZ_spec_trapFree` states, under every
`Archi` and every semantics of external functions. -/
theorem natDivModCheckedBZ_native_spec (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl natDivModCheckedBZ_spec_trapFree A X LeanExe.Native.nativeCap
      compiled.translation
```

```lean
/-- `natDivModCheckedBZ_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natDivModCheckedBZ_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 65, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[65]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 × Array UInt64 => natDivModCheckedBZ x.1 x.2)
        (fun x heap _ => (Canonical x.1 ∧ Canonical x.2) ∧ (x.1.size < 2 ^ 32 ∧ x.2.size < 2 ^ 32) ∧
          heap.top.toNat + (128 * x.1.size + 144 * x.2.size + 824) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (128 * x.1.size + 144 * x.2.size + 824) ∧
          natDivModCheckedBZ x.1 x.2 = natDivModCheckedSpec (value x.1) (value x.2))
```

```lean
/-- `intTDivModCheckedBZ_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intTDivModCheckedBZ_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 66, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[66]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : BigInt × BigInt => intTDivModCheckedBZ x.1 x.2)
        (fun x heap _ => (x.1.Canonical ∧ x.2.Canonical) ∧ (x.1.mag.size < 2 ^ 32 ∧ x.2.mag.size < 2 ^ 32) ∧
          heap.top.toNat + (128 * x.1.mag.size + 144 * x.2.mag.size + 824) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (128 * x.1.mag.size + 144 * x.2.mag.size + 824) ∧
          intTDivModCheckedBZ x.1 x.2 = intTDivModCheckedSpec x.1.toInt x.2.toInt)
```

```lean
/-- `intEDivModCheckedBZ_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intEDivModCheckedBZ_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 67, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[67]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : BigInt × BigInt => intEDivModCheckedBZ x.1 x.2)
        (fun x heap _ => (x.1.Canonical ∧ x.2.Canonical) ∧ (x.1.mag.size < 2 ^ 32 ∧ x.2.mag.size < 2 ^ 32) ∧
          heap.top.toNat + (248 * x.1.mag.size + 248 * x.2.mag.size + 1472) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (248 * x.1.mag.size + 248 * x.2.mag.size + 1472) ∧
          intEDivModCheckedBZ x.1 x.2 = intEDivModCheckedSpec x.1.toInt x.2.toInt)
```

```lean
/-- `natToTextDC_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natToTextDC_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 72, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[72]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : Array UInt64 => natToTextDC x)
        (fun x heap _ => (Canonical x) ∧ (x.size < 2 ^ 32) ∧
          heap.top.toNat + (438 * x.size + 1968) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (438 * x.size + 1968) ∧
          natToTextDC x = printSpec (value x : ℤ))
```

```lean
/-- `intToTextDC_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem intToTextDC_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 73, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[73]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : BigInt => intToTextDC x)
        (fun x heap _ => (x.Canonical) ∧ (x.mag.size < 2 ^ 32) ∧
          heap.top.toNat + (438 * x.mag.size + 1968) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (438 * x.mag.size + 1968) ∧
          intToTextDC x = printSpec x.toInt)
```

```lean
/-- `natDivModCheckedBZWith_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natDivModCheckedBZWith_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 64, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[64]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : UInt64 × UInt64 × UInt64 × Array UInt64 × Array UInt64 => natDivModCheckedBZWith x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
        (fun x heap _ => (Canonical x.2.2.2.1 ∧ Canonical x.2.2.2.2) ∧ (x.2.2.2.1.size < 2 ^ 32 ∧ x.2.2.2.2.size < 2 ^ 32) ∧
          heap.top.toNat + (128 * x.2.2.2.1.size + 144 * x.2.2.2.2.size + 824) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (128 * x.2.2.2.1.size + 144 * x.2.2.2.2.size + 824) ∧
          natDivModCheckedBZWith x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 = natDivModCheckedSpec (value x.2.2.2.1) (value x.2.2.2.2))
```

```lean
/-- `natToTextDCWith_native_spec` with its premise as arithmetic on the 256 MiB of `lx_mem`. -/
theorem natToTextDCWith_native_size (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 71, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[71]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X LeanExe.Native.nativeCap compiled.module compiled.translation
        ps rs fd false (fun x : UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64 => natToTextDCWith x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
        (fun x heap _ => (Canonical x.2.2.2.2) ∧ (x.2.2.2.2.size < 2 ^ 32) ∧
          heap.top.toNat + (438 * x.2.2.2.2.size + 1968) ≤ 2 ^ 28)
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + (438 * x.2.2.2.2.size + 1968) ∧
          natToTextDCWith x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 = printSpec (value x.2.2.2.2 : ℤ))
```

## `NativeRuntime.lean`

```lean
/-- The C function of each export is `lxf_` followed by the export's name, and the functions whose
code takes the call depth are `lxf_` followed by their index (19, 31, 32, 34, 35, 36, 37, 38, 40, 41, 42, 45, 46, 48, 49, 51, 52, 53, 54), the
bodies that the exported entries 55 to 73 call at depth 0; `lx_init`, `lx_status`, `lx_mem`, and the
result globals `lx_r0_l` to `lx_r4_l` that a host reads are the identifiers that the theorems name;
the translation has five result positions; and no two of its identifiers and no two of its names
coincide. -/
theorem native_names :
    (∀ p ∈ [(initId, "lx_init"),
      (statusId, "lx_status"),
      (memId, "lx_mem"),
      (resId 0 .i64, "lx_r0_l"),
      (resId 1 .i64, "lx_r1_l"),
      (resId 2 .i64, "lx_r2_l"),
      (resId 3 .i64, "lx_r3_l"),
      (resId 4 .i64, "lx_r4_l"),
      (funId 0, "lxf_alloc"),
      (funId 1, "lxf_release"),
      (funId 2, "lxf_width"),
      (funId 3, "lxf_add"),
      (funId 4, "lxf_sub"),
      (funId 5, "lxf_significant"),
      (funId 6, "lxf_mulSmall"),
      (funId 7, "lxf_wordBits"),
      (funId 8, "lxf_shortDiv"),
      (funId 9, "lxf_tooBig"),
      (funId 10, "lxf_trial"),
      (funId 11, "lxf_limb"),
      (funId 12, "lxf_cmpStep"),
      (funId 13, "lxf_le"),
      (funId 14, "lxf_digitCount"),
      (funId 15, "lxf_digitByte"),
      (funId 16, "lxf_addGen"),
      (funId 17, "lxf_subGen"),
      (funId 18, "lxf_baseMul"),
      (funId 19, "lxf_19"),
      (funId 20, "lxf_trimSeg"),
      (funId 21, "lxf_mulAddSeg"),
      (funId 22, "lxf_longDivS"),
      (funId 23, "lxf_divideS"),
      (funId 24, "lxf_natTrim"),
      (funId 25, "lxf_natAdd"),
      (funId 26, "lxf_natSub"),
      (funId 27, "lxf_intToText"),
      (funId 28, "lxf_trialAt"),
      (funId 29, "lxf_mulSubSeg"),
      (funId 30, "lxf_baseDiv"),
      (funId 31, "lxf_31"),
      (funId 32, "lxf_32"),
      (funId 33, "lxf_subFix"),
      (funId 34, "lxf_34"),
      (funId 35, "lxf_35"),
      (funId 36, "lxf_36"),
      (funId 37, "lxf_37"),
      (funId 38, "lxf_38"),
      (funId 39, "lxf_divSmallSeg"),
      (funId 40, "lxf_40"),
      (funId 41, "lxf_41"),
      (funId 42, "lxf_42"),
      (funId 43, "lxf_signTDiv"),
      (funId 44, "lxf_signEDiv"),
      (funId 45, "lxf_45"),
      (funId 46, "lxf_46"),
      (funId 47, "lxf_leafChunks"),
      (funId 48, "lxf_48"),
      (funId 49, "lxf_49"),
      (funId 50, "lxf_textOfChunks"),
      (funId 51, "lxf_51"),
      (funId 52, "lxf_52"),
      (funId 53, "lxf_53"),
      (funId 54, "lxf_54"),
      (funId 55, "lxf_kara"),
      (funId 56, "lxf_mulChunk"),
      (funId 57, "lxf_mulAcc"),
      (funId 58, "lxf_halfStep"),
      (funId 59, "lxf_lowHalf"),
      (funId 60, "lxf_rdiv"),
      (funId 61, "lxf_tdiv"),
      (funId 62, "lxf_udiv"),
      (funId 63, "lxf_divSeg"),
      (funId 64, "lxf_natDivModCheckedBZWith"),
      (funId 65, "lxf_natDivModCheckedBZ"),
      (funId 66, "lxf_intTDivModCheckedBZ"),
      (funId 67, "lxf_intEDivModCheckedBZ"),
      (funId 68, "lxf_powInit"),
      (funId 69, "lxf_toChunks"),
      (funId 70, "lxf_chunksDC"),
      (funId 71, "lxf_natToTextDCWith"),
      (funId 72, "lxf_natToTextDC"),
      (funId 73, "lxf_intToTextDC")],
      p ∈ compiled.translation.names) ∧
    compiled.translation.nres = 5 ∧
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

```lean
/-- The C function `lxf_rdiv`, function 60, computes the Lean function in place for every argument, with no room and no rise of `top`, under every `Archi` and every
semantics of external functions. -/
theorem rdiv_native (A : Archi) (X : ExtSem) :
    NativeImpl rdiv_trapFree A X nativeCap compiled.translation
```

