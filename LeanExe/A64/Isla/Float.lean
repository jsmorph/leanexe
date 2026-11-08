import LeanExe.A64.Isla.Walk

/-!
The equations of the floating-point functions that the traces of the floating-point forms leave
abstract, and the lemmas on the register `_Z` that the theorems of those forms use.

`tests/isla/armv9p4-checked-fp.diff` adds to the IR a monomorphic wrapper of each floating-point
function that the forms of `LeanExe/A64/Machine.lean` call, `FPAdd64`, `FPSub64`, `FPMul64`,
`FPDiv64`, `FPSqrt64`, `FixedToFP64`, and `FPToFixed64`, each of which calls the original function
at 64 bits, and `tests/isla/traces.sh` leaves each wrapper abstract with `--abstract`.  The trace of
a form then records the call with its arguments, among them the FPCR that the form read, and the
semantics of `Trace.lean` gives the call the meaning `A`.  Each equation below states, for one
wrapper, that `A` gives the reference interpreter's function of `Interpreter/Wasm/Float.lean` for
every operand under the startup's FPCR, `0x02000000`, which the traces record as the struct
`(_ struct (|bits| #x0000000002000000))`.  The theorem of a form takes its equation as a
hypothesis, so the theorem holds for the meaning of Arm's function as far as the equation does.
No theorem proves the equations, since Isla does not evaluate the pseudocode's arithmetic on real
numbers.

The traces read `_Z` as a whole and select the element of a symbolic register number with a chain
of 31 `ite` expressions from index 0 upward, which the walk evaluates to a chain of `cond`.
`upick` describes the chain, `zchain%` and `uchain%` write it as the walk leaves it, over the low
64 bits of the elements as natural numbers and as words, and `zchain_eq` and `uchain_eq` fold it
into the indexed D register.  A write of `_Z` sets the D registers one at a time, and `dwrite_eq`
folds the 32 writes of a trace that replaces one element into one update.  Other lemmas move the
reduction to the low 64 bits into the chains and through the masks of `V_set`, and reduce the
vector lengths that `V_set` computes from the 4-bit fields LEN of `SMCR_ELx` and `ZCR_ELx`, which
the traces compare as signed integers.  `fp_fwd` and `fp_bwd` are `mem_fwd` and `mem_bwd` of
`Walk.lean` with these rules, `fp_side` closes the goals that `fp_bwd` leaves, and `dreg_end` and
`xreg_end` compare the end of a path with `exec`'s state.
-/

namespace LeanExe.A64.Isla

/-- `FPAdd(a, b, FPCR) = Wasm.f64Add a b` under FPCR `0x02000000`, for the wrapper `FPAdd64`. -/
def FPAddEq (A : Abstract) : Prop :=
  ∀ a b : UInt64, A "FPAdd64" [.bits 64 a.toNat, .bits 64 b.toNat,
    .struct [("bits", .bits 64 0x2000000)]] = some (.bits 64 (Wasm.f64Add a b).toNat)

/-- `FPSub(a, b, FPCR) = Wasm.f64Sub a b` under FPCR `0x02000000`, for the wrapper `FPSub64`. -/
def FPSubEq (A : Abstract) : Prop :=
  ∀ a b : UInt64, A "FPSub64" [.bits 64 a.toNat, .bits 64 b.toNat,
    .struct [("bits", .bits 64 0x2000000)]] = some (.bits 64 (Wasm.f64Sub a b).toNat)

/-- `FPMul(a, b, FPCR) = Wasm.f64Mul a b` under FPCR `0x02000000`, for the wrapper `FPMul64`. -/
def FPMulEq (A : Abstract) : Prop :=
  ∀ a b : UInt64, A "FPMul64" [.bits 64 a.toNat, .bits 64 b.toNat,
    .struct [("bits", .bits 64 0x2000000)]] = some (.bits 64 (Wasm.f64Mul a b).toNat)

/-- `FPDiv(a, b, FPCR) = Wasm.f64Div a b` under FPCR `0x02000000`, for the wrapper `FPDiv64`. -/
def FPDivEq (A : Abstract) : Prop :=
  ∀ a b : UInt64, A "FPDiv64" [.bits 64 a.toNat, .bits 64 b.toNat,
    .struct [("bits", .bits 64 0x2000000)]] = some (.bits 64 (Wasm.f64Div a b).toNat)

/-- `FPSqrt(a, FPCR) = Wasm.f64Sqrt a` under FPCR `0x02000000`, for the wrapper `FPSqrt64`. -/
def FPSqrtEq (A : Abstract) : Prop :=
  ∀ a : UInt64, A "FPSqrt64" [.bits 64 a.toNat, .struct [("bits", .bits 64 0x2000000)]] =
    some (.bits 64 (Wasm.f64Sqrt a).toNat)

/-- `FixedToFP(a, 0, TRUE, FPCR, FPRounding_TIEEVEN, 64) = Wasm.f64ConvertI64U a` under FPCR
`0x02000000`, for the wrapper `FixedToFP64`: the conversion of the unsigned integer `a` with no
fraction bits, rounding to nearest with ties to even. -/
def FixedToFPEq (A : Abstract) : Prop :=
  ∀ a : UInt64, A "FixedToFP64" [.bits 64 a.toNat, .bits 128 0, .bool true,
    .struct [("bits", .bits 64 0x2000000)], .enum "FPRounding_TIEEVEN"] =
    some (.bits 64 (Wasm.f64ConvertI64U a).toNat)

/-- `FPToFixed(a, 0, TRUE, FPCR, FPRounding_ZERO, 64) = Wasm.i64TruncSatF64U a` under FPCR
`0x02000000`, for the wrapper `FPToFixed64`: the conversion of the double `a` to an unsigned 64-bit
integer with no fraction bits, rounding toward zero and saturating. -/
def FPToFixedEq (A : Abstract) : Prop :=
  ∀ a : UInt64, A "FPToFixed64" [.bits 64 a.toNat, .bits 128 0, .bool true,
    .struct [("bits", .bits 64 0x2000000)], .enum "FPRounding_ZERO"] =
    some (.bits 64 (Wasm.i64TruncSatF64U a).toNat)

/-- The flags N, Z, C, and V that `State.fcmp` sets from the doubles `a` and `b`, as the 4-bit
number NZCV: N is `IEEE64.lt a b`, Z is `IEEE64.eq a b`, C is the negation of N, and V holds when an
operand is a NaN. -/
def fcmpNZCV (a b : UInt64) : Nat :=
  8 * (Wasm.IEEE64.lt a b).toNat + 4 * (Wasm.IEEE64.eq a b).toNat +
    2 * (!Wasm.IEEE64.lt a b).toNat + (Wasm.IEEE64.isNaN a || Wasm.IEEE64.isNaN b).toNat

/-- `FPCompare(a, b, FALSE, FPCR)` gives the flags of `State.fcmp` under FPCR `0x02000000`: 0011 for
an unordered pair, 0110 for equal values, 1000 when `a` lies below `b`, and 0010 when it lies above.
`FCMP` calls `FPCompare` itself, whose result has 4 bits at every width, so the traces leave it
abstract without a wrapper, and a call on operands of another width carries arguments that the
equation does not name. -/
def FPCompareEq (A : Abstract) : Prop :=
  ∀ a b : UInt64, A "FPCompare" [.bits 64 a.toNat, .bits 64 b.toNat, .bool false,
    .struct [("bits", .bits 64 0x2000000)]] = some (.bits 4 (fcmpNZCV a b))

theorem nzcv_bits (n z c v : Bool) :
    decide ((8 * n.toNat + 4 * z.toNat + 2 * c.toNat + v.toNat) / 8 % 2 = 1) = n ∧
      decide ((8 * n.toNat + 4 * z.toNat + 2 * c.toNat + v.toNat) / 4 % 2 = 1) = z ∧
      decide ((8 * n.toNat + 4 * z.toNat + 2 * c.toNat + v.toNat) / 2 % 2 = 1) = c ∧
      decide ((8 * n.toNat + 4 * z.toNat + 2 * c.toNat + v.toNat) % 2 = 1) = v := by
  cases n <;> cases z <;> cases c <;> cases v <;> decide

theorem fcmpNZCV_lt (a b : UInt64) : fcmpNZCV a b < 16 := by
  unfold fcmpNZCV
  cases Wasm.IEEE64.lt a b <;> cases Wasm.IEEE64.eq a b <;>
    cases (Wasm.IEEE64.isNaN a || Wasm.IEEE64.isNaN b) <;> decide

theorem fcmpNZCV_n (a b : UInt64) :
    decide (fcmpNZCV a b / 8 % 2 = 1) = Wasm.IEEE64.lt a b := (nzcv_bits _ _ _ _).1

theorem fcmpNZCV_z (a b : UInt64) :
    decide (fcmpNZCV a b / 4 % 2 = 1) = Wasm.IEEE64.eq a b := (nzcv_bits _ _ _ _).2.1

theorem fcmpNZCV_c (a b : UInt64) :
    decide (fcmpNZCV a b / 2 % 2 = 1) = !Wasm.IEEE64.lt a b := (nzcv_bits _ _ _ _).2.2.1

theorem fcmpNZCV_v (a b : UInt64) :
    decide (fcmpNZCV a b % 2 = 1) = (Wasm.IEEE64.isNaN a || Wasm.IEEE64.isNaN b) :=
  (nzcv_bits _ _ _ _).2.2.2

/-! The equations of the 32-bit wrappers, which the traces of the single-precision forms leave
abstract: each states, for one wrapper, that `A` gives Talos's function of the binary32 operands
under FPCR `0x02000000`.  FCMP calls `FPCompare` at either width, and `FPCompare32Eq` gives its
meaning on 32-bit operands. -/

/-- `FPAdd(a, b, FPCR) = Wasm.f32Add a b` under FPCR `0x02000000`, for the wrapper `FPAdd32`. -/
def FPAdd32Eq (A : Abstract) : Prop :=
  ∀ a b : UInt32, A "FPAdd32" [.bits 32 a.toNat, .bits 32 b.toNat,
    .struct [("bits", .bits 64 0x2000000)]] = some (.bits 32 (Wasm.f32Add a b).toNat)

/-- `FPSub(a, b, FPCR) = Wasm.f32Sub a b` under FPCR `0x02000000`, for the wrapper `FPSub32`. -/
def FPSub32Eq (A : Abstract) : Prop :=
  ∀ a b : UInt32, A "FPSub32" [.bits 32 a.toNat, .bits 32 b.toNat,
    .struct [("bits", .bits 64 0x2000000)]] = some (.bits 32 (Wasm.f32Sub a b).toNat)

/-- `FPMul(a, b, FPCR) = Wasm.f32Mul a b` under FPCR `0x02000000`, for the wrapper `FPMul32`. -/
def FPMul32Eq (A : Abstract) : Prop :=
  ∀ a b : UInt32, A "FPMul32" [.bits 32 a.toNat, .bits 32 b.toNat,
    .struct [("bits", .bits 64 0x2000000)]] = some (.bits 32 (Wasm.f32Mul a b).toNat)

/-- `FPDiv(a, b, FPCR) = Wasm.f32Div a b` under FPCR `0x02000000`, for the wrapper `FPDiv32`. -/
def FPDiv32Eq (A : Abstract) : Prop :=
  ∀ a b : UInt32, A "FPDiv32" [.bits 32 a.toNat, .bits 32 b.toNat,
    .struct [("bits", .bits 64 0x2000000)]] = some (.bits 32 (Wasm.f32Div a b).toNat)

/-- `FPSqrt(a, FPCR) = Wasm.f32Sqrt a` under FPCR `0x02000000`, for the wrapper `FPSqrt32`. -/
def FPSqrt32Eq (A : Abstract) : Prop :=
  ∀ a : UInt32, A "FPSqrt32" [.bits 32 a.toNat, .struct [("bits", .bits 64 0x2000000)]] =
    some (.bits 32 (Wasm.f32Sqrt a).toNat)

/-- `FPRoundInt(a, FPCR, FPRounding_TIEEVEN, FALSE) = Wasm.f32Nearest a` under FPCR `0x02000000`,
for the wrapper `FPRoundInt32`: the rounding of `FRINTN` to an integral value with ties to even,
without the inexact exception. -/
def FPRoundInt32Eq (A : Abstract) : Prop :=
  ∀ a : UInt32, A "FPRoundInt32" [.bits 32 a.toNat, .struct [("bits", .bits 64 0x2000000)],
    .enum "FPRounding_TIEEVEN", .bool false] = some (.bits 32 (Wasm.f32Nearest a).toNat)

/-- `FixedToFP(a, 0, TRUE, FPCR, FPRounding_TIEEVEN, 32) = Wasm.f32ConvertI64U a` under FPCR
`0x02000000`, for the wrapper `FixedToFP64_32`: the conversion of the unsigned 64-bit integer `a`
to binary32. -/
def FixedToFP64_32Eq (A : Abstract) : Prop :=
  ∀ a : UInt64, A "FixedToFP64_32" [.bits 64 a.toNat, .bits 128 0, .bool true,
    .struct [("bits", .bits 64 0x2000000)], .enum "FPRounding_TIEEVEN"] =
    some (.bits 32 (Wasm.f32ConvertI64U a).toNat)

/-- `FixedToFP(a, 0, FALSE, FPCR, FPRounding_TIEEVEN, 32) = Wasm.f32ConvertI32S a` under FPCR
`0x02000000`, for the wrapper `FixedToFP32_32`: the conversion of the signed 32-bit integer `a` to
binary32. -/
def FixedToFP32_32Eq (A : Abstract) : Prop :=
  ∀ a : UInt32, A "FixedToFP32_32" [.bits 32 a.toNat, .bits 128 0, .bool false,
    .struct [("bits", .bits 64 0x2000000)], .enum "FPRounding_TIEEVEN"] =
    some (.bits 32 (Wasm.f32ConvertI32S a).toNat)

/-- `FPToFixed(a, 0, TRUE, FPCR, FPRounding_ZERO, 64) = Wasm.i64TruncSatF32U a` under FPCR
`0x02000000`, for the wrapper `FPToFixed32_64`: the conversion of the single `a` to an unsigned
64-bit integer, rounding toward zero and saturating, with 0 for a NaN. -/
def FPToFixed32_64Eq (A : Abstract) : Prop :=
  ∀ a : UInt32, A "FPToFixed32_64" [.bits 32 a.toNat, .bits 128 0, .bool true,
    .struct [("bits", .bits 64 0x2000000)], .enum "FPRounding_ZERO"] =
    some (.bits 64 (Wasm.i64TruncSatF32U a).toNat)

/-- `FPToFixed(a, 0, FALSE, FPCR, FPRounding_ZERO, 32) = Wasm.i32TruncSatF32S a` under FPCR
`0x02000000`, for the wrapper `FPToFixed32_32`: the conversion of the single `a` to a signed 32-bit
integer, rounding toward zero and saturating, with 0 for a NaN. -/
def FPToFixed32_32Eq (A : Abstract) : Prop :=
  ∀ a : UInt32, A "FPToFixed32_32" [.bits 32 a.toNat, .bits 128 0, .bool false,
    .struct [("bits", .bits 64 0x2000000)], .enum "FPRounding_ZERO"] =
    some (.bits 32 (Wasm.i32TruncSatF32S a).toNat)

/-- The flags N, Z, C, and V that `State.fcmpS` sets from the singles `a` and `b`, as the 4-bit
number NZCV. -/
def fcmpNZCV32 (a b : UInt32) : Nat :=
  8 * (Wasm.IEEE32.lt a b).toNat + 4 * (Wasm.IEEE32.eq a b).toNat +
    2 * (!Wasm.IEEE32.lt a b).toNat + (Wasm.IEEE32.isNaN a || Wasm.IEEE32.isNaN b).toNat

/-- `FPCompare(a, b, FALSE, FPCR)` of singles gives the flags of `State.fcmpS` under FPCR
`0x02000000`. -/
def FPCompare32Eq (A : Abstract) : Prop :=
  ∀ a b : UInt32, A "FPCompare" [.bits 32 a.toNat, .bits 32 b.toNat, .bool false,
    .struct [("bits", .bits 64 0x2000000)]] = some (.bits 4 (fcmpNZCV32 a b))

theorem fcmpNZCV32_lt (a b : UInt32) : fcmpNZCV32 a b < 16 := by
  unfold fcmpNZCV32
  cases Wasm.IEEE32.lt a b <;> cases Wasm.IEEE32.eq a b <;>
    cases (Wasm.IEEE32.isNaN a || Wasm.IEEE32.isNaN b) <;> decide

theorem fcmpNZCV32_n (a b : UInt32) :
    decide (fcmpNZCV32 a b / 8 % 2 = 1) = Wasm.IEEE32.lt a b := (nzcv_bits _ _ _ _).1

theorem fcmpNZCV32_z (a b : UInt32) :
    decide (fcmpNZCV32 a b / 4 % 2 = 1) = Wasm.IEEE32.eq a b := (nzcv_bits _ _ _ _).2.1

theorem fcmpNZCV32_c (a b : UInt32) :
    decide (fcmpNZCV32 a b / 2 % 2 = 1) = !Wasm.IEEE32.lt a b := (nzcv_bits _ _ _ _).2.2.1

theorem fcmpNZCV32_v (a b : UInt32) :
    decide (fcmpNZCV32 a b % 2 = 1) = (Wasm.IEEE32.isNaN a || Wasm.IEEE32.isNaN b) :=
  (nzcv_bits _ _ _ _).2.2.2

/-- The low 32 bits of a word as the number of its `toUInt32`, the form in which the
single-precision equations name their operands. -/
theorem low32_eq (x : UInt64) : x.toNat % 4294967296 = x.toUInt32.toNat := by
  simp only [UInt64.toNat_toUInt32, Nat.reducePow]

/-- The fields of `FCMP Dn, Dm`. -/
def fcmpFields (n m : Fin 32) : Fields := [("Rm", m.val), ("Rn", n.val)]

/-- The fields of a floating-point form of the registers `d` and `n`, such as `FSQRT Dd, Dn`. -/
def fpFields2 (d n : Fin 32) : Fields := [("Rn", n.val), ("Rd", d.val)]

/-- The fields of a floating-point form of the registers `d`, `n`, and `m`, such as
`FADD Dd, Dn, Dm`. -/
def fpFields3 (d n m : Fin 32) : Fields := [("Rm", m.val), ("Rn", n.val), ("Rd", d.val)]

/-- `cond (decide (k = j)) (f j) (... (cond (decide (k = j + n - 1)) (f (j + n - 1)) (f (j + n))))`,
the chain of `n` tests from index `j` upward that a trace computes for the element at the index
`k`. -/
def upick {α : Type} (k : Nat) (f : Nat → α) : Nat → Nat → α
  | j, 0 => f j
  | j, n + 1 => cond (decide (k = j)) (f j) (upick k f (j + 1) n)

theorem upick_eq {α : Type} (k : Nat) (f : Nat → α) :
    ∀ n j, j ≤ k → k ≤ j + n → upick k f j n = f k
  | 0, j, h1, h2 => by
    obtain rfl : j = k := by omega
    rfl
  | n + 1, j, h1, h2 => by
    unfold upick
    by_cases hk : k = j
    · rw [decide_eq_true hk, Bool.cond_true, hk]
    · rw [decide_eq_false hk, Bool.cond_false]
      exact upick_eq k f n (j + 1) (by omega) (by omega)

/-- The chain of the low 64 bits of the elements of `_Z` at the index `k`, as natural numbers, in
the form in which the walk leaves it. -/
syntax "zchain% " term:max term:max : term
macro_rules
  | `(zchain% $s $k) => do
    let mut t ← `(UInt64.toNat (dAt $s 31))
    for j' in [0:31] do
      let lit := Lean.Syntax.mkNumLit (toString (30 - j'))
      t ← `(cond (decide ($k = $lit)) (UInt64.toNat (dAt $s $lit)) $t)
    return t

/-- The chain of the low 64 bits of the elements of `_Z` at the index `k`, as words. -/
syntax "uchain% " term:max term:max : term
macro_rules
  | `(uchain% $s $k) => do
    let mut t ← `(dAt $s 31)
    for j' in [0:31] do
      let lit := Lean.Syntax.mkNumLit (toString (30 - j'))
      t ← `(cond (decide ($k = $lit)) (dAt $s $lit) $t)
    return t

theorem zchain_eq {s : State} {k : Nat} (hk : k < 32) : zchain% s k = (dAt s k).toNat :=
  upick_eq k (fun j => (dAt s j).toNat) 31 0 (Nat.zero_le _) (by omega)

theorem uchain_eq {s : State} {k : Nat} (hk : k < 32) : uchain% s k = dAt s k :=
  upick_eq k (dAt s) 31 0 (Nat.zero_le _) (by omega)

/-- The state after the writes of D registers 0 to `n - 1` from `b`, where D register `j` takes
`r` for `j = k` and D register `j` of `s` otherwise. -/
def wfold (b s : State) (k : Nat) (r : UInt64) : Nat → State
  | 0 => b
  | n + 1 => setDAt (wfold b s k r n) n (cond (decide (k = n)) r (dAt s n))

theorem wfold_eq (b s : State) (k : Nat) (r : UInt64) : ∀ n,
    wfold b s k r n = { b with dregs := fun i =>
      if i.val < n then (if i.val = k then r else s.dregs i) else b.dregs i }
  | 0 => by
    simp only [wfold, Nat.not_lt_zero, ↓reduceIte]
  | n + 1 => by
    rw [wfold, wfold_eq b s k r n]
    simp only [setDAt, State.mk.injEq, and_true, true_and]
    funext i
    by_cases hi : i.val = n
    · have hd : dAt s n = s.dregs i := by
        unfold dAt
        rw [dite_eq_left (by omega)]
        exact congrArg s.dregs (Fin.ext hi.symm)
      by_cases hk : k = n
      · simp [hi, hk]
      · simp [hi, hk, hd, Ne.symm hk]
    · simp only [hi, ↓reduceIte]
      by_cases hn : i.val < n
      · simp [hn, show i.val < n + 1 by omega]
      · simp [hn, show ¬ i.val < n + 1 by omega]

/-- The 32 writes of D registers 0 to 31 from `b`, where D register `j` takes `r` for `j = k` and
D register `j` of `s` otherwise, as the walk leaves them after a write of `_Z`. -/
syntax "dwrite% " term:max term:max term:max term:max : term
macro_rules
  | `(dwrite% $b $s $k $r) => do
    let mut t := b
    for j in [0:32] do
      let lit := Lean.Syntax.mkNumLit (toString j)
      t ← `(setDAt $t $lit (cond (decide ($k = $lit)) $r (dAt $s $lit)))
    return t

theorem dwrite_eq {b s : State} {k : Nat} {r : UInt64} :
    dwrite% b s k r = { b with dregs := fun i => if i.val = k then r else s.dregs i } := by
  have h := wfold_eq b s k r 32
  simp only [Fin.is_lt, ↓reduceIte] at h
  exact h

theorem cond_mod (b : Bool) (x y n : Nat) : cond b x y % n = cond b (x % n) (y % n) := by
  cases b <;> rfl

theorem cond_cond_same {α : Type} (b : Bool) (x y z : α) :
    cond b x (cond b y z) = cond b x z := by
  cases b <;> rfl

/-- The low 64 bits of an element of `_Z`, the upper bits `h` above the word `n`. -/
theorem hi_lo_mod (h n : Nat) :
    (h * 18446744073709551616 + n) % 18446744073709551616 = n % 18446744073709551616 := by
  omega

theorem ofNat_cond (b : Bool) (x y : Nat) :
    UInt64.ofNat (cond b x y) = cond b (UInt64.ofNat x) (UInt64.ofNat y) := by
  cases b <;> rfl

theorem ofNat_hi_lo (h n : Nat) :
    UInt64.ofNat (h * 18446744073709551616 + n) = UInt64.ofNat n := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofNat', Nat.reducePow]
  omega

theorem ofNat_mod (n : Nat) : UInt64.ofNat (n % 18446744073709551616) = UInt64.ofNat n := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofNat', Nat.reducePow, Nat.mod_mod]

/-- The low 64 bits of `x &&& M` for a mask `M` whose low 64 bits are set. -/
theorem ofNat_and_low {x M : Nat} (hM : M % 18446744073709551616 = 18446744073709551615) :
    UInt64.ofNat (x &&& M) = UInt64.ofNat x := by
  apply UInt64.toNat_inj.mp
  have h := @Nat.and_mod_two_pow x M 64
  have h1 := Nat.and_two_pow_sub_one_eq_mod (x % 2 ^ 64) 64
  simp only [Nat.reducePow, Nat.reduceSub, Nat.mod_mod] at h h1
  simp only [UInt64.toNat_ofNat', Nat.reducePow, h, hM, h1]

/-- The low 64 bits of `(x &&& M) ||| y` for a mask `M` whose low 64 bits are clear. -/
theorem ofNat_and_or {x M y : Nat} (hM : M % 18446744073709551616 = 0) :
    UInt64.ofNat ((x &&& M) ||| y) = UInt64.ofNat y := by
  apply UInt64.toNat_inj.mp
  have h := @Nat.or_mod_two_pow (x &&& M) y 64
  have h' := @Nat.and_mod_two_pow x M 64
  simp only [Nat.reducePow] at h h'
  simp only [UInt64.toNat_ofNat', Nat.reducePow, h, h', hM, Nat.and_zero, Nat.zero_or]

/-- The low 64 bits of `x &&& M` for a mask `M` whose low 64 bits are clear. -/
theorem ofNat_and_high {x M : Nat} (hM : M % 18446744073709551616 = 0) :
    UInt64.ofNat (x &&& M) = 0 := by
  apply UInt64.toNat_inj.mp
  have h := @Nat.and_mod_two_pow x M 64
  simp only [Nat.reducePow] at h
  simp only [UInt64.toNat_ofNat', Nat.reducePow, h, hM, Nat.and_zero, UInt64.toNat_zero]

/-! The vector lengths that `V_set` computes from the fields `LEN` of `SMCR_ELx` and `ZCR_ELx`,
4-bit values that the traces compare as signed integers of the model's 128 bits. -/

theorem len_mod64 (x : Nat) : x % 16 % 18446744073709551616 = x % 16 := by omega

theorem len_div63 (x : Nat) : x % 16 / 9223372036854775808 = 0 := by omega

theorem len_div127 (x : Nat) : x % 16 / 170141183460469231731687303715884105728 = 0 := by omega

theorem cond_div (b : Bool) (x y n : Nat) : cond b x y / n = cond b (x / n) (y / n) := by
  cases b <;> rfl

theorem natCast_lt_zero (n : Nat) : ((n : Int) < 0) ↔ False := ⟨fun h => by omega, False.elim⟩

theorem natCast_lt_natCast (a b : Nat) : ((a : Int) < (b : Int)) ↔ a < b := by omega

/-- An element of `_Z` from its upper bits and its word has 2048 bits. -/
theorem zword_lt {h : Nat} (hh : h < 2 ^ 1984) (d : UInt64) :
    h * 18446744073709551616 + d.toNat < 2 ^ 2048 := by
  have := toNat_lt d
  omega

/-- The model's D register at an index below 32. -/
theorem dAt_val (s : State) (n : Fin 32) : dAt s n.val = s.dregs n := by
  unfold dAt
  rw [dite_eq_left n.isLt]

/-- The rules that a walk of a floating-point trace adds to those of `mem_simp`: the reads and
writes of `_Z`, the folding of its chains and writes, the reduction of its elements to their low
64 bits, the abstract calls' arguments, and the vector lengths. -/
syntax "fp_fwd " ident " using " tacticSeq " with " "[" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic
macro_rules
  | `(tactic| fp_fwd $h using $d with [$xs,*]) => `(tactic| mem_fwd $h using $d with [
      zHigh, zGet, zJoin, zPut, zSplit, RVal.evalAll, List.length_cons, List.length_nil, cond_mod,
      hi_lo_mod, zchain_eq, uchain_eq, ofNat_cond, ofNat_hi_lo, UInt64.ofNat_toNat, ofNat_and_low,
      ofNat_and_or, ofNat_and_high, Nat.or_zero, cond_cond_same, len_mod64, len_div63,
      len_div127, cond_div, Bool.cond_self, Int.ofNat_zero, Int.sub_zero, natCast_lt_zero,
      natCast_lt_natCast, $xs,*])

/-- Builds a path of a floating-point trace with `mem_bwd` and the rules of `fp_fwd`. -/
syntax "fp_bwd " "using " tacticSeq " with " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| fp_bwd using $d with [$xs,*]) => `(tactic| mem_bwd using $d with [
      zHigh, zGet, zJoin, zPut, zSplit, RVal.evalAll, List.length_cons, List.length_nil, cond_mod,
      hi_lo_mod, zchain_eq, uchain_eq, ofNat_cond, ofNat_hi_lo, UInt64.ofNat_toNat, ofNat_and_low,
      ofNat_and_or, ofNat_and_high, Nat.or_zero, cond_cond_same, len_mod64, len_div63,
      len_div127, cond_div, Bool.cond_self, Int.ofNat_zero, Int.sub_zero, natCast_lt_zero,
      natCast_lt_natCast, $xs,*])

/-- Proves a goal that `fp_bwd` leaves, the bound of a declared variable's value or the condition
of a read or an assert, with the premise `hσ` and the lemmas in brackets.  An element of `_Z` has
the upper bits of `Unknown.z` above its word. -/
syntax "fp_side " term:max " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| fp_side $hσ [$xs,*]) => `(tactic| first
      | (mem_side $hσ [zHigh, zGet, zJoin, RVal.evalAll, List.length_cons, List.length_nil,
          cond_mod, hi_lo_mod, zchain_eq, $xs,*])
      | (mem_simp [Opaque.out $hσ, zHigh, zGet, zJoin, List.length_cons, List.length_nil, $xs,*]
         exact zword_lt (BitVec.isLt _) _))

theorem done_eq {s s' : State} {σ : Sys} (h : s = s') : Outcome.done s σ = .done s' σ :=
  h ▸ rfl

/-- Proves that the outcome at the end of a path of the trace of a form that writes a D register is
`exec`'s state with some registers outside the model that differ from `σ` only at the listed
ones: it reads `__BranchTaken`, folds the writes of the D registers, and compares the states. -/
macro "dreg_end" : tactic => `(tactic| (
  simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte]
  refine ⟨_, done_eq ?_, by frame_end⟩
  simp (disch := omega) only [dwrite_eq, State.setD, x_lt, x_31, dAt_val, Fin.ext_iff,
    UInt64.reduceOfNat, State.mk.injEq, and_true, true_and, and_self]))

/-- Proves that the outcome at the end of a path of the trace of `FMOV Xd, Dn` is `exec`'s: it
reads `__BranchTaken` and compares the write of the general register. -/
macro "xreg_end" : tactic => `(tactic| (
  done_end
  simp (disch := omega) only [setX_eq_setRegAt, setRegAt_pc, setRegAt_31, dAt_val,
    UInt64.ofNat_toNat, State.mk.injEq, and_true, true_and, and_self]))

/-- Proves that the outcome at the end of the path of the trace of `FCMP Dn, Dm` is `exec`'s: it
reads `__BranchTaken` and compares the flags that the trace writes from `FPCompare`'s result with
those of `State.fcmp`. -/
macro "flags_end" : tactic => `(tactic| (
  done_end
  simp (disch := omega) only [State.fcmp, dAt_val, fcmpNZCV_n, fcmpNZCV_z, fcmpNZCV_c,
    fcmpNZCV_v, Nat.div_one, State.mk.injEq, and_true, true_and, and_self]))

end LeanExe.A64.Isla
