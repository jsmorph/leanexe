import LeanExe.A64.Isla.Check
import LeanExe.A64.Isla.Profile

/-!
Theorems of `Agrees` for the register forms of `LeanExe/A64/Machine.lean`: ADD, SUB, AND, EOR,
ORR, ORR (W), SUBS, MADD, MSUB, LSLV, LSRV, and UDIV, from the traces of `tests/isla/tcg` and
`tests/isla/kvm` under the profiles `tcg` and `kvm` with the arguments `tcr`.  Each theorem holds
for every value of every register field, register 31 included, and every state.  The two traces of
a register form are equal, so the theorem under `kvm` follows from the theorem under `tcg`: the
kernel checks that the two footprints are equal, and `Agrees.of_reads` carries the theorem to
`kvm`, which agrees with `tcg` on the registers that the trace reads.
`tests/isla/theorems.sh` elaborates the module and prints the axioms of its theorems.

The forward direction of a proof takes each path of the trace to its outcome, and the backward
direction builds the path of each case of register 31 among the fields.  `reg_end` and `subs_end`
compare the outcome with `exec`'s state, and the lemmas before them state the trace's operators on
natural numbers as the model's operators on `UInt64`.  The traces of LSLV and LSRV compute the
shift amount with `bvsrem` by 64 on X[Rm] zero-extended to 128 bits and correct a negative
remainder, and `srem_toNat` and `slt_mod64` reduce the amount to X[Rm] modulo 64.  UDIV's trace
comes from the IR that `tests/isla/armv9p4-udiv.diff` edits.  It divides X[Rn] by X[Rm], both
zero-extended to 128 bits, with `bvsdiv`, which `sdiv_toNat` equates with the quotient of natural
numbers for a nonzero divisor, and it writes zero for a divisor of zero.
-/

namespace TestSupport.A64.Isla

open LeanExe.A64 LeanExe.A64.Isla

/-- The fields of a form of the three general registers `d`, `n`, and `m`, such as
`ADD Xd, Xn, Xm`. -/
def regFields (d n m : Fin 32) : Fields := [("Rd", d.val), ("Rn", n.val), ("Rm", m.val)]

/-- The fields of `MADD` and `MSUB` for the registers `d`, `n`, `m`, and `a`. -/
def regFields4 (d n m a : Fin 32) : Fields :=
  [("Rd", d.val), ("Rn", n.val), ("Ra", a.val), ("Rm", m.val)]

/-- The footprint of `ADD Xd, Xn, Xm` under the profile `tcg`. -/
def addRegTcg : Footprint := isla_trace% "tests/isla/tcg/add-reg"

/-- The footprint of `ADD Xd, Xn, Xm` under the profile `kvm`. -/
def addRegKvm : Footprint := isla_trace% "tests/isla/kvm/add-reg"

/-- The footprint of `SUB Xd, Xn, Xm` under the profile `tcg`. -/
def subRegTcg : Footprint := isla_trace% "tests/isla/tcg/sub-reg"

/-- The footprint of `SUB Xd, Xn, Xm` under the profile `kvm`. -/
def subRegKvm : Footprint := isla_trace% "tests/isla/kvm/sub-reg"

/-- The footprint of `AND Xd, Xn, Xm` under the profile `tcg`. -/
def andRegTcg : Footprint := isla_trace% "tests/isla/tcg/and-reg"

/-- The footprint of `AND Xd, Xn, Xm` under the profile `kvm`. -/
def andRegKvm : Footprint := isla_trace% "tests/isla/kvm/and-reg"

/-- The footprint of `EOR Xd, Xn, Xm` under the profile `tcg`. -/
def eorRegTcg : Footprint := isla_trace% "tests/isla/tcg/eor-reg"

/-- The footprint of `EOR Xd, Xn, Xm` under the profile `kvm`. -/
def eorRegKvm : Footprint := isla_trace% "tests/isla/kvm/eor-reg"

/-- The footprint of `ORR Xd, Xn, Xm` under the profile `tcg`. -/
def orrRegTcg : Footprint := isla_trace% "tests/isla/tcg/orr-reg"

/-- The footprint of `ORR Xd, Xn, Xm` under the profile `kvm`. -/
def orrRegKvm : Footprint := isla_trace% "tests/isla/kvm/orr-reg"

/-- The footprint of `ORR Wd, Wn, Wm` under the profile `tcg`. -/
def orrWTcg : Footprint := isla_trace% "tests/isla/tcg/orr-w"

/-- The footprint of `ORR Wd, Wn, Wm` under the profile `kvm`. -/
def orrWKvm : Footprint := isla_trace% "tests/isla/kvm/orr-w"

/-- The footprint of `SUBS Xd, Xn, Xm` under the profile `tcg`. -/
def subsRegTcg : Footprint := isla_trace% "tests/isla/tcg/subs-reg"

/-- The footprint of `SUBS Xd, Xn, Xm` under the profile `kvm`. -/
def subsRegKvm : Footprint := isla_trace% "tests/isla/kvm/subs-reg"

/-- The footprint of `MADD Xd, Xn, Xm, Xa` under the profile `tcg`. -/
def maddTcg : Footprint := isla_trace% "tests/isla/tcg/madd"

/-- The footprint of `MADD Xd, Xn, Xm, Xa` under the profile `kvm`. -/
def maddKvm : Footprint := isla_trace% "tests/isla/kvm/madd"

/-- The footprint of `MSUB Xd, Xn, Xm, Xa` under the profile `tcg`. -/
def msubTcg : Footprint := isla_trace% "tests/isla/tcg/msub"

/-- The footprint of `MSUB Xd, Xn, Xm, Xa` under the profile `kvm`. -/
def msubKvm : Footprint := isla_trace% "tests/isla/kvm/msub"

/-- The footprint of `LSLV Xd, Xn, Xm` under the profile `tcg`. -/
def lslvTcg : Footprint := isla_trace% "tests/isla/tcg/lslv"

/-- The footprint of `LSLV Xd, Xn, Xm` under the profile `kvm`. -/
def lslvKvm : Footprint := isla_trace% "tests/isla/kvm/lslv"

/-- The footprint of `LSRV Xd, Xn, Xm` under the profile `tcg`. -/
def lsrvTcg : Footprint := isla_trace% "tests/isla/tcg/lsrv"

/-- The footprint of `LSRV Xd, Xn, Xm` under the profile `kvm`. -/
def lsrvKvm : Footprint := isla_trace% "tests/isla/kvm/lsrv"

/-- The footprint of `UDIV Xd, Xn, Xm` under the profile `tcg`. -/
def udivTcg : Footprint := isla_trace% "tests/isla/tcg/udiv"

/-- The footprint of `UDIV Xd, Xn, Xm` under the profile `kvm`. -/
def udivKvm : Footprint := isla_trace% "tests/isla/kvm/udiv"

/-! The trace's operators on registers as the model's. -/

theorem and_toNat_mod (a b : UInt64) :
    (a.toNat &&& b.toNat) % 18446744073709551616 = a.toNat &&& b.toNat :=
  Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (toNat_lt b))

theorem or_toNat_mod (a b : UInt64) :
    (a.toNat ||| b.toNat) % 18446744073709551616 = a.toNat ||| b.toNat :=
  Nat.mod_eq_of_lt (Nat.or_lt_two_pow (toNat_lt a) (toNat_lt b))

theorem xor_toNat_mod (a b : UInt64) :
    (a.toNat ^^^ b.toNat) % 18446744073709551616 = a.toNat ^^^ b.toNat :=
  Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (toNat_lt a) (toNat_lt b))

/-- The low 32 bits of an OR, as `toUInt32` takes them. -/
theorem or_mod32 (a b : Nat) : (a ||| b) % 4294967296 = a % 4294967296 ||| b % 4294967296 :=
  Nat.or_mod_two_pow (n := 32)

/-- The OR of two values of 32 bits, as ORR (W) writes it zero-extended. -/
theorem or32_mod (a b : Nat) : (a % 4294967296 ||| b % 4294967296) % 18446744073709551616 =
    a % 4294967296 ||| b % 4294967296 :=
  Nat.mod_eq_of_lt (Nat.or_lt_two_pow (n := 64) (by omega) (by omega))

/-- The low 64 bits of a product of 128 bits, as MADD and MSUB extract them. -/
theorem mod128_mod64 (x : Nat) :
    x % 340282366920938463463374607431768211456 % 18446744073709551616 =
      x % 18446744073709551616 := by omega

/-- `bvsrem` by 64 of a register zero-extended to 128 bits, the remainder of the shift amount. -/
theorem srem_toNat (x : UInt64) : srem 128 x.toNat 64 = x.toNat % 64 := by
  have := toNat_lt x
  rw [srem, ite_eq_right (by omega), ite_eq_right (by omega), urem, ite_eq_right (by omega)]

/-- The remainder of the shift amount is not negative, so the trace keeps it. -/
theorem slt_mod64 (x : Nat) : decide (sint 128 (x % 64) < sint 128 0) = false := by
  apply decide_eq_false
  simp only [sint, Nat.reduceSub, Nat.reducePow]
  omega

theorem mod64_mod (x : Nat) : x % 64 % 18446744073709551616 = x % 64 := by omega

theorem mod64_div (x : Nat) : x % 64 / 9223372036854775808 = 0 := by omega

theorem mod64_lt (x : Nat) : x % 64 < 64 := Nat.mod_lt _ (by decide)

theorem div_toNat_mod (a : UInt64) (k : Nat) :
    a.toNat / k % 18446744073709551616 = a.toNat / k :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (toNat_lt a))

/-- `bvsdiv` of two registers zero-extended to 128 bits is their quotient for a nonzero
divisor. -/
theorem sdiv_toNat {x y : UInt64} (h : y.toNat ≠ 0) :
    sdiv 128 x.toNat y.toNat = x.toNat / y.toNat :=
  sdiv_128 (Nat.lt_trans (toNat_lt x) (by decide)) (Nat.lt_trans (toNat_lt y) (by decide))
    (Nat.pos_of_ne_zero h)

/-- `bvsdiv` of zero, the zero register, by a nonzero register is zero. -/
theorem sdiv_zero {y : UInt64} (h : y.toNat ≠ 0) : sdiv 128 0 y.toNat = 0 := by
  rw [sdiv_128 (by decide) (Nat.lt_trans (toNat_lt y) (by decide)) (Nat.pos_of_ne_zero h),
    Nat.zero_div]

/-- The model's division by a register that holds zero. -/
theorem div_of_zero {a b : Nat} (h : b = 0) : a / b = 0 := by rw [h, Nat.div_zero]

/-! The flags of `SUBS (register)`.  For the values `A` of X[Rn] and `B` of X[Rm], the trace
computes `A + NOT B + 1` in 128 bits, and it reads N from bit 63 of the low 64 bits, Z from the low
64 bits being zero, C from the sum exceeding 64 bits, and V from the sign extension of the low 64
bits differing from the sum of the sign-extended operands.  The lemmas state each condition, as
`isla_simp` and `subs_end` leave it, as the condition that `nflag`, `zflag`, `cflag`, or `vflag`
gives for `State.subs`, and `subs_r` states the low 64 bits as the model's difference.  Register 31
reads as zero, so the trace takes one shape when neither source is 31, another for `m` = 31
(`_m31`), and a third for `n` = 31 (`_n31`), and it writes constant flags when both are.  `M64`,
`P64`, `H63`, `P128`, `K64`, and `M128` stand for the literals 2^64 - 1, 2^64, 2^63, 2^128,
2^128 - 2^64, and 2^128 - 1.  Each proof replaces the truncated subtractions by variables, since
`omega` splits on every truncated subtraction, and the proofs of V give `omega` the signs and the
carry. -/

local notation "M64" => (18446744073709551615 : Nat)
local notation "P64" => (18446744073709551616 : Nat)
local notation "H63" => (9223372036854775808 : Nat)
local notation "P128" => (340282366920938463463374607431768211456 : Nat)
local notation "K64" => (340282366920938463444927863358058659840 : Nat)
local notation "M128" => (340282366920938463463374607431768211455 : Nat)

theorem subs_r {A B : Nat} (hB : B < P64) :
    ((A + (M64 - B)) % P128 + 1) % P128 % P64 = (P64 - B + A) % P64 := by
  have : M64 - B + B = M64 := by omega
  have : P64 - B + B = P64 := by omega
  generalize M64 - B = NB at *
  generalize P64 - B = PB at *
  omega

theorem subs_n {A B : Nat} (hB : B < P64) :
    ((A + (M64 - B)) % P128 + 1) % P128 % P64 / H63 % 2 = 1 ↔ (P64 - B + A) % P64 / H63 = 1 := by
  have : M64 - B + B = M64 := by omega
  have : P64 - B + B = P64 := by omega
  generalize M64 - B = NB at *
  generalize P64 - B = PB at *
  omega

theorem subs_z {A B : Nat} (hB : B < P64) :
    ((A + (M64 - B)) % P128 + 1) % P128 % P64 = 0 ↔ (P64 - B + A) % P64 = 0 := by
  have : M64 - B + B = M64 := by omega
  have : P64 - B + B = P64 := by omega
  generalize M64 - B = NB at *
  generalize P64 - B = PB at *
  omega

theorem subs_c {A B : Nat} (hA : A < P64) (hB : B < P64) :
    ((A + (M64 - B)) % P128 + 1) % P128 % P64 = ((A + (M64 - B)) % P128 + 1) % P128 ↔
      ¬B ≤ A := by
  have : M64 - B + B = M64 := by omega
  have : P64 - B + B = P64 := by omega
  generalize M64 - B = NB at *
  generalize P64 - B = PB at *
  omega

theorem subs_v {A B : Nat} (hA : A < P64) (hB : B < P64) :
    ((A + (M64 - B)) % P128 + 1) % P128 % P64 +
        ((A + (M64 - B)) % P128 + 1) % P128 % P64 / H63 * K64 =
      ((A + A / H63 * K64 + (M64 - B + (M64 - B) / H63 * K64)) % P128 + 1) % P128 ↔
      ¬(A / H63 ≠ B / H63 ∧ A / H63 ≠ (P64 - B + A) % P64 / H63) := by
  have : M64 - B + B = M64 := by omega
  have : P64 - B + B = P64 := by omega
  generalize M64 - B = NB at *
  generalize P64 - B = PB at *
  rcases Nat.lt_or_ge A H63 with _ | _ <;> rcases Nat.lt_or_ge B H63 with _ | _ <;>
    rcases Nat.lt_or_ge B (A + 1) with _ | _ <;>
    rcases Nat.lt_or_ge ((PB + A) % P64) H63 with _ | _ <;> omega

theorem subs_r_m31 (A : Nat) :
    ((A + M64) % P128 + 1) % P128 % P64 = (P64 - 0 + A) % P64 := by
  omega

theorem subs_n_m31 {A : Nat} (hA : A < P64) :
    ((A + M64) % P128 + 1) % P128 % P64 / H63 % 2 = 1 ↔ (P64 - 0 + A) % P64 / H63 = 1 := by
  omega

theorem subs_z_m31 {A : Nat} (hA : A < P64) :
    ((A + M64) % P128 + 1) % P128 % P64 = 0 ↔ (P64 - 0 + A) % P64 = 0 := by
  omega

theorem subs_c_m31 {A : Nat} (hA : A < P64) :
    ((A + M64) % P128 + 1) % P128 % P64 = ((A + M64) % P128 + 1) % P128 ↔ ¬0 ≤ A := by
  omega

theorem subs_v_m31 {A : Nat} (hA : A < P64) :
    ((A + M64) % P128 + 1) % P128 % P64 + ((A + M64) % P128 + 1) % P128 % P64 / H63 * K64 =
      ((A + A / H63 * K64 + M128) % P128 + 1) % P128 ↔
      ¬(A / H63 ≠ 0 / H63 ∧ A / H63 ≠ (P64 - 0 + A) % P64 / H63) := by
  rcases Nat.lt_or_ge A H63 with _ | _ <;> omega

theorem subs_r_n31 {B : Nat} (hB : B < P64) :
    (M64 - B + 1) % P128 % P64 = (P64 - B + 0) % P64 := by
  have : M64 - B + B = M64 := by omega
  have : P64 - B + B = P64 := by omega
  generalize M64 - B = NB at *
  generalize P64 - B = PB at *
  omega

theorem subs_n_n31 {B : Nat} (hB : B < P64) :
    (M64 - B + 1) % P128 % P64 / H63 % 2 = 1 ↔ (P64 - B + 0) % P64 / H63 = 1 := by
  have : M64 - B + B = M64 := by omega
  have : P64 - B + B = P64 := by omega
  generalize M64 - B = NB at *
  generalize P64 - B = PB at *
  omega

theorem subs_z_n31 {B : Nat} (hB : B < P64) :
    (M64 - B + 1) % P128 % P64 = 0 ↔ (P64 - B + 0) % P64 = 0 := by
  have : M64 - B + B = M64 := by omega
  have : P64 - B + B = P64 := by omega
  generalize M64 - B = NB at *
  generalize P64 - B = PB at *
  omega

theorem subs_c_n31 {B : Nat} (hB : B < P64) :
    (M64 - B + 1) % P128 % P64 = (M64 - B + 1) % P128 ↔ ¬B ≤ 0 := by
  have : M64 - B + B = M64 := by omega
  have : P64 - B + B = P64 := by omega
  generalize M64 - B = NB at *
  generalize P64 - B = PB at *
  omega

theorem subs_v_n31 {B : Nat} (hB : B < P64) :
    (M64 - B + 1) % P128 % P64 + (M64 - B + 1) % P128 % P64 / H63 * K64 =
      (M64 - B + (M64 - B) / H63 * K64 + 1) % P128 ↔
      ¬(0 / H63 ≠ B / H63 ∧ 0 / H63 ≠ (P64 - B + 0) % P64 / H63) := by
  have : M64 - B + B = M64 := by omega
  have : P64 - B + B = P64 := by omega
  generalize M64 - B = NB at *
  generalize P64 - B = PB at *
  rcases Nat.lt_or_ge B H63 with _ | _ <;>
    rcases Nat.lt_or_ge (PB % P64) H63 with _ | _ <;> omega

/-- The trace's bit of a condition, as the trace of `SUBS` builds C and V. -/
theorem ite_one (p : Prop) [Decidable p] : ((if p then 1 else 0 : Nat) = 1) ↔ p := by
  by_cases h : p <;> simp [h]

/-- The trace's bit of a condition, as the trace of `SUBS` builds Z. -/
theorem ite_not_zero (p : Prop) [Decidable (¬p)] : ((if ¬p then 0 else 1 : Nat) = 1) ↔ p := by
  by_cases h : p <;> simp [h]

/-- Proves that the outcome at the end of a path of the trace of a form that writes one general
register is `exec`'s, as `gpr_end` does: it reads `__BranchTaken`, reduces the reads and writes of
registers at an index with the path's facts on the fields, and compares the written values as
natural numbers with the lemmas above.  It compares the written values up to reducible unfolding
before it compares them as numbers, since `rfl` on SUB's values unfolds `UInt64` subtraction and
exceeds the maximum recursion depth, an error that `try` does not catch. -/
macro "reg_end" : tactic => `(tactic| (
  simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte, Outcome.done.injEq, and_true,
    true_and]
  simp (disch := omega) only [x_lt, x_31, setX_eq_setRegAt, setRegAt_lt, setRegAt_31,
    State.mk.injEq, and_true, true_and]
  try (funext j; split <;> (try with_reducible rfl))
  try (apply UInt64.toNat_inj.mp
       simp (disch := omega) only [UInt64.toNat_ofNat', UInt64.toNat_ofNat, UInt64.toNat_zero,
         UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_div,
         UInt64.toNat_mod, UInt64.toNat_and, UInt64.toNat_or, UInt64.toNat_xor,
         UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, UInt64.toNat_toUInt32,
         UInt32.toNat_toUInt64, toNat_mod, and_toNat_mod, or_toNat_mod, xor_toNat_mod, or_mod32,
         or32_mod, mod128_mod64, div_toNat_mod, sdiv_toNat, sdiv_zero, div_of_zero,
         Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.zero_add, Nat.add_zero, Nat.zero_mul,
         Nat.mul_zero, Nat.mul_one, Nat.zero_div, Nat.div_zero, Nat.div_one, Nat.zero_mod,
         Nat.pow_zero, Nat.mod_mod, Nat.zero_and, Nat.and_zero, Nat.zero_or, Nat.or_zero,
         Nat.zero_xor, Nat.xor_zero, Nat.reducePow, Nat.reduceMod] <;> omega)))

/-- Proves that the outcome at the end of a path of the trace of `SUBS (register)` is `exec`'s,
where `hA` and `hB` bound the values of registers `n` and `m`.  The trace computes the flags as the
bits of a word of 4 bits, which `word_n`, `word_z`, `word_c`, and `word_v` read back, and the
lemmas on the flags turn each of the trace's conditions into the model's.  `vflag` rewrites the V
flag before `nflag`, whose pattern also matches it.  A path on which both sources are register 31
writes constant flags, which `decide` compares. -/
syntax "subs_end " term:max term:max : tactic
macro_rules
  | `(tactic| subs_end $hA $hB) => `(tactic| (
    simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte, Outcome.done.injEq, and_true,
      true_and]
    simp (disch := omega) only [State.subs, x_lt, x_31, setX_eq_setRegAt, setRegAt_lt,
      setRegAt_31, State.mk.injEq, vflag, and_true, true_and]
    simp -failIfUnchanged only [nflag, zflag, cflag, UInt64.toNat_sub, UInt64.toNat_zero,
      Bool.cond_eq_ite, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
      Nat.reducePow]
    simp -failIfUnchanged (disch := first | omega | (split <;> omega)) only [word_n, word_z,
      word_c, word_v]
    simp -failIfUnchanged only [decide_eq_decide, subs_n $hB, subs_z $hB,
      subs_c $hA $hB, subs_v $hA $hB, subs_n_m31 $hA, subs_z_m31 $hA, subs_c_m31 $hA,
      subs_v_m31 $hA, subs_n_n31 $hB, subs_z_n31 $hB, subs_c_n31 $hB, subs_v_n31 $hB,
      Classical.not_not, ite_one, ite_not_zero, iff_self, and_true, true_and]
    repeat' apply And.intro
    all_goals first
      | (funext j
         split <;> (try with_reducible rfl)
         apply UInt64.toNat_inj.mp
         simp only [UInt64.toNat_ofNat', UInt64.toNat_sub, UInt64.toNat_zero, Nat.reducePow,
           Nat.mod_mod, subs_r $hB, subs_r_m31, subs_r_n31 $hB])
      | decide))

set_option maxHeartbeats 4000000 in
/-- The trace of `ADD Xd, Xn, Xm` under `tcg` agrees with `exec` for every register number, with
register 31 the zero register, and every state.  The backward direction builds the path of each of
the 8 cases of register 31 among `d`, `n`, and `m`, and the 706 events that the two directions
evaluate take more than the default budget of heartbeats. -/
theorem addReg_tcg (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] addRegTcg (regFields d n m)
      (.addReg d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, addRegTcg, regFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      isla_reads [addRegTcg, Profile.sys_get, Profile.sys] at hσ
      refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 14),
        fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
      · unfold Footprint.Run at h
        simp only [addRegTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD] at h
        isla_fwd h using omega with [hσ]
        all_goals gpr_end
      · subst h
        unfold Footprint.Run
        simp only [addRegTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD]
        by_cases hn : n.val = 31 <;> by_cases hm : m.val = 31 <;> by_cases hd : d.val = 31
        all_goals
          isla_bwd [s.pc.toNat] using omega with [hσ, hn, hm, hd]
          try isla_gprs s using omega with [hσ, hn, hm, hd]
        all_goals first
          | exact toNat_lt _
          | gpr_end
          | (simp only [sint]; omega)
          | omega

/-- The trace of `ADD Xd, Xn, Xm` under `kvm` agrees with `exec` for every register number and
every state. -/
theorem addReg_kvm (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] addRegKvm (regFields d n m)
      (.addReg d n m) s := by
  rw [show addRegKvm = addRegTcg from rfl]
  exact (addReg_tcg P u d n m s).of_reads
    (by isla_reads [addRegTcg, Profile.sys_get, Profile.sys])

set_option maxHeartbeats 4000000 in
/-- The trace of `SUB Xd, Xn, Xm` under `tcg` agrees with `exec` for every register number, with
register 31 the zero register, and every state. -/
theorem subReg_tcg (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] subRegTcg (regFields d n m)
      (.subReg d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, subRegTcg, regFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      isla_reads [subRegTcg, Profile.sys_get, Profile.sys] at hσ
      have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
      have : (regAt s m.val).toNat < 18446744073709551616 := toNat_lt _
      refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 16),
        fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
      · unfold Footprint.Run at h
        simp only [subRegTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD] at h
        isla_fwd h using omega with [hσ]
        all_goals reg_end
      · subst h
        unfold Footprint.Run
        simp only [subRegTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD]
        by_cases hn : n.val = 31 <;> by_cases hm : m.val = 31 <;> by_cases hd : d.val = 31
        all_goals
          isla_bwd [s.pc.toNat] using omega with [hσ, hn, hm, hd]
          try isla_gprs s using omega with [hσ, hn, hm, hd]
        all_goals first
          | exact toNat_lt _
          | reg_end
          | (simp only [sint]; omega)
          | omega

/-- The trace of `SUB Xd, Xn, Xm` under `kvm` agrees with `exec` for every register number and
every state. -/
theorem subReg_kvm (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] subRegKvm (regFields d n m)
      (.subReg d n m) s := by
  rw [show subRegKvm = subRegTcg from rfl]
  exact (subReg_tcg P u d n m s).of_reads
    (by isla_reads [subRegTcg, Profile.sys_get, Profile.sys])

set_option maxHeartbeats 4000000 in
/-- The trace of `AND Xd, Xn, Xm` under `tcg` agrees with `exec` for every register number, with
register 31 the zero register, and every state. -/
theorem andReg_tcg (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] andRegTcg (regFields d n m)
      (.andReg d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, andRegTcg, regFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      isla_reads [andRegTcg, Profile.sys_get, Profile.sys] at hσ
      refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 48),
        fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
      · unfold Footprint.Run at h
        simp only [andRegTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD] at h
        isla_fwd h using omega with [hσ]
        all_goals reg_end
      · subst h
        unfold Footprint.Run
        simp only [andRegTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD]
        by_cases hn : n.val = 31 <;> by_cases hm : m.val = 31 <;> by_cases hd : d.val = 31
        all_goals
          isla_bwd [s.pc.toNat] using omega with [hσ, hn, hm, hd]
          try isla_gprs s using omega with [hσ, hn, hm, hd]
        all_goals first
          | exact toNat_lt _
          | reg_end
          | (simp only [sint]; omega)
          | omega

/-- The trace of `AND Xd, Xn, Xm` under `kvm` agrees with `exec` for every register number and
every state. -/
theorem andReg_kvm (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] andRegKvm (regFields d n m)
      (.andReg d n m) s := by
  rw [show andRegKvm = andRegTcg from rfl]
  exact (andReg_tcg P u d n m s).of_reads
    (by isla_reads [andRegTcg, Profile.sys_get, Profile.sys])

set_option maxHeartbeats 4000000 in
/-- The trace of `EOR Xd, Xn, Xm` under `tcg` agrees with `exec` for every register number, with
register 31 the zero register, and every state. -/
theorem eorReg_tcg (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] eorRegTcg (regFields d n m)
      (.eorReg d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, eorRegTcg, regFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      isla_reads [eorRegTcg, Profile.sys_get, Profile.sys] at hσ
      refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 53),
        fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
      · unfold Footprint.Run at h
        simp only [eorRegTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD] at h
        isla_fwd h using omega with [hσ]
        all_goals reg_end
      · subst h
        unfold Footprint.Run
        simp only [eorRegTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD]
        by_cases hn : n.val = 31 <;> by_cases hm : m.val = 31 <;> by_cases hd : d.val = 31
        all_goals
          isla_bwd [s.pc.toNat] using omega with [hσ, hn, hm, hd]
          try isla_gprs s using omega with [hσ, hn, hm, hd]
        all_goals first
          | exact toNat_lt _
          | reg_end
          | (simp only [sint]; omega)
          | omega

/-- The trace of `EOR Xd, Xn, Xm` under `kvm` agrees with `exec` for every register number and
every state. -/
theorem eorReg_kvm (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] eorRegKvm (regFields d n m)
      (.eorReg d n m) s := by
  rw [show eorRegKvm = eorRegTcg from rfl]
  exact (eorReg_tcg P u d n m s).of_reads
    (by isla_reads [eorRegTcg, Profile.sys_get, Profile.sys])

set_option maxHeartbeats 4000000 in
/-- The trace of `ORR Xd, Xn, Xm` under `tcg` agrees with `exec` for every register number, with
register 31 the zero register, and every state. -/
theorem orrReg_tcg (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] orrRegTcg (regFields d n m)
      (.orrReg d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, orrRegTcg, regFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      isla_reads [orrRegTcg, Profile.sys_get, Profile.sys] at hσ
      refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 55),
        fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
      · unfold Footprint.Run at h
        simp only [orrRegTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD] at h
        isla_fwd h using omega with [hσ]
        all_goals reg_end
      · subst h
        unfold Footprint.Run
        simp only [orrRegTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD]
        by_cases hn : n.val = 31 <;> by_cases hm : m.val = 31 <;> by_cases hd : d.val = 31
        all_goals
          isla_bwd [s.pc.toNat] using omega with [hσ, hn, hm, hd]
          try isla_gprs s using omega with [hσ, hn, hm, hd]
        all_goals first
          | exact toNat_lt _
          | reg_end
          | (simp only [sint]; omega)
          | omega

/-- The trace of `ORR Xd, Xn, Xm` under `kvm` agrees with `exec` for every register number and
every state. -/
theorem orrReg_kvm (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] orrRegKvm (regFields d n m)
      (.orrReg d n m) s := by
  rw [show orrRegKvm = orrRegTcg from rfl]
  exact (orrReg_tcg P u d n m s).of_reads
    (by isla_reads [orrRegTcg, Profile.sys_get, Profile.sys])

set_option maxHeartbeats 4000000 in
/-- The trace of `ORR Wd, Wn, Wm` under `tcg` agrees with `exec` for every register number, with
register 31 the zero register, and every state. The model writes the OR of the low 32 bits
zero-extended, as the trace does. -/
theorem orrW_tcg (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] orrWTcg (regFields d n m)
      (.orrW d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, orrWTcg, regFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      isla_reads [orrWTcg, Profile.sys_get, Profile.sys] at hσ
      refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 55),
        fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
      · unfold Footprint.Run at h
        simp only [orrWTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD] at h
        isla_fwd h using omega with [hσ]
        all_goals reg_end
      · subst h
        unfold Footprint.Run
        simp only [orrWTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD]
        by_cases hn : n.val = 31 <;> by_cases hm : m.val = 31 <;> by_cases hd : d.val = 31
        all_goals
          isla_bwd [s.pc.toNat] using omega with [hσ, hn, hm, hd]
          try isla_gprs s using omega with [hσ, hn, hm, hd]
        all_goals first
          | exact toNat_lt _
          | reg_end
          | (simp only [sint]; omega)
          | omega

/-- The trace of `ORR Wd, Wn, Wm` under `kvm` agrees with `exec` for every register number and
every state. -/
theorem orrW_kvm (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] orrWKvm (regFields d n m)
      (.orrW d n m) s := by
  rw [show orrWKvm = orrWTcg from rfl]
  exact (orrW_tcg P u d n m s).of_reads
    (by isla_reads [orrWTcg, Profile.sys_get, Profile.sys])

set_option maxHeartbeats 8000000 in
/-- The trace of `SUBS Xd, Xn, Xm` under `tcg` agrees with `exec` for every register number, with
register 31 the zero register, and every state. The trace sets the flags of `AddWithCarry`, which
`-L AddWithCarry` linearizes, and writes no register for `d` = 31, `CMP Xn, Xm`. -/
theorem subsReg_tcg (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] subsRegTcg (regFields d n m)
      (.subsReg d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, subsRegTcg, regFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      isla_reads [subsRegTcg, Profile.sys_get, Profile.sys] at hσ
      have hA : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
      have hB : (regAt s m.val).toNat < 18446744073709551616 := toNat_lt _
      refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 17),
        fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
      · unfold Footprint.Run at h
        simp only [subsRegTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD] at h
        isla_fwd h using omega with [hσ]
        all_goals subs_end hA hB
      · subst h
        unfold Footprint.Run
        simp only [subsRegTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD]
        by_cases hn : n.val = 31 <;> by_cases hm : m.val = 31 <;> by_cases hd : d.val = 31
        all_goals
          isla_bwd [s.pc.toNat] using omega with [hσ, hn, hm, hd]
          try isla_gprs s using omega with [hσ, hn, hm, hd]
        all_goals first
          | exact toNat_lt _
          | subs_end hA hB
          | (simp only [sint]; omega)
          | omega

/-- The trace of `SUBS Xd, Xn, Xm` under `kvm` agrees with `exec` for every register number and
every state. -/
theorem subsReg_kvm (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] subsRegKvm (regFields d n m)
      (.subsReg d n m) s := by
  rw [show subsRegKvm = subsRegTcg from rfl]
  exact (subsReg_tcg P u d n m s).of_reads
    (by isla_reads [subsRegTcg, Profile.sys_get, Profile.sys])

set_option maxHeartbeats 8000000 in
/-- The trace of `MADD Xd, Xn, Xm, Xa` under `tcg` agrees with `exec` for every register number,
with register 31 the zero register, and every state. The backward direction builds the path of each
of the 16 cases of register 31 among `d`, `n`, `m`, and `a`. -/
theorem madd_tcg (P : Platform) (u : Unknown) (d n m a : Fin 32) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] maddTcg (regFields4 d n m a)
      (.madd d n m a) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, maddTcg, regFields4, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      isla_reads [maddTcg, Profile.sys_get, Profile.sys] at hσ
      refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 690),
        fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
      · unfold Footprint.Run at h
        simp only [maddTcg, Footprint.vars, regFields4, List.foldl, List.lookup,
          String.reduceBEq, Option.getD] at h
        isla_fwd h using omega with [hσ]
        all_goals reg_end
      · subst h
        unfold Footprint.Run
        simp only [maddTcg, Footprint.vars, regFields4, List.foldl, List.lookup,
          String.reduceBEq, Option.getD]
        by_cases hn : n.val = 31 <;> by_cases hm : m.val = 31 <;> by_cases ha : a.val = 31 <;>
          by_cases hd : d.val = 31
        all_goals
          isla_bwd [s.pc.toNat] using omega with [hσ, hn, hm, ha, hd]
          try isla_gprs s using omega with [hσ, hn, hm, ha, hd]
        all_goals first
          | exact toNat_lt _
          | reg_end
          | (simp only [sint]; omega)
          | omega

/-- The trace of `MADD Xd, Xn, Xm, Xa` under `kvm` agrees with `exec` for every register number and
every state. -/
theorem madd_kvm (P : Platform) (u : Unknown) (d n m a : Fin 32) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] maddKvm (regFields4 d n m a)
      (.madd d n m a) s := by
  rw [show maddKvm = maddTcg from rfl]
  exact (madd_tcg P u d n m a s).of_reads
    (by isla_reads [maddTcg, Profile.sys_get, Profile.sys])

set_option maxHeartbeats 8000000 in
/-- The trace of `MSUB Xd, Xn, Xm, Xa` under `tcg` agrees with `exec` for every register number,
with register 31 the zero register, and every state. The backward direction builds the path of each
of the 16 cases of register 31 among `d`, `n`, `m`, and `a`. -/
theorem msub_tcg (P : Platform) (u : Unknown) (d n m a : Fin 32) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] msubTcg (regFields4 d n m a)
      (.msub d n m a) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, msubTcg, regFields4, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      isla_reads [msubTcg, Profile.sys_get, Profile.sys] at hσ
      refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 691),
        fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
      · unfold Footprint.Run at h
        simp only [msubTcg, Footprint.vars, regFields4, List.foldl, List.lookup,
          String.reduceBEq, Option.getD] at h
        isla_fwd h using omega with [hσ]
        all_goals reg_end
      · subst h
        unfold Footprint.Run
        simp only [msubTcg, Footprint.vars, regFields4, List.foldl, List.lookup,
          String.reduceBEq, Option.getD]
        by_cases hn : n.val = 31 <;> by_cases hm : m.val = 31 <;> by_cases ha : a.val = 31 <;>
          by_cases hd : d.val = 31
        all_goals
          isla_bwd [s.pc.toNat] using omega with [hσ, hn, hm, ha, hd]
          try isla_gprs s using omega with [hσ, hn, hm, ha, hd]
        all_goals first
          | exact toNat_lt _
          | reg_end
          | (simp only [sint]; omega)
          | omega

/-- The trace of `MSUB Xd, Xn, Xm, Xa` under `kvm` agrees with `exec` for every register number and
every state. -/
theorem msub_kvm (P : Platform) (u : Unknown) (d n m a : Fin 32) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] msubKvm (regFields4 d n m a)
      (.msub d n m a) s := by
  rw [show msubKvm = msubTcg from rfl]
  exact (msub_tcg P u d n m a s).of_reads
    (by isla_reads [msubTcg, Profile.sys_get, Profile.sys])

set_option maxHeartbeats 4000000 in
/-- The trace of `LSLV Xd, Xn, Xm` under `tcg` agrees with `exec` for every register number, with
register 31 the zero register, and every state. -/
theorem lslv_tcg (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] lslvTcg (regFields d n m)
      (.lslv d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, lslvTcg, regFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      isla_reads [lslvTcg, Profile.sys_get, Profile.sys] at hσ
      refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 57),
        fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
      · unfold Footprint.Run at h
        simp only [lslvTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD] at h
        isla_fwd h using omega with [hσ, srem_toNat, slt_mod64, mod64_mod, mod64_div, mod64_lt]
        all_goals reg_end
      · subst h
        unfold Footprint.Run
        simp only [lslvTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD]
        by_cases hn : n.val = 31 <;> by_cases hm : m.val = 31 <;> by_cases hd : d.val = 31
        all_goals
          isla_bwd [s.pc.toNat] using omega
            with [hσ, hn, hm, hd, srem_toNat, slt_mod64, mod64_mod, mod64_div, mod64_lt]
          try isla_gprs s using omega
            with [hσ, hn, hm, hd, srem_toNat, slt_mod64, mod64_mod, mod64_div, mod64_lt]
        all_goals first
          | exact toNat_lt _
          | reg_end
          | (simp only [sint]; omega)
          | omega

/-- The trace of `LSLV Xd, Xn, Xm` under `kvm` agrees with `exec` for every register number and
every state. -/
theorem lslv_kvm (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] lslvKvm (regFields d n m)
      (.lslv d n m) s := by
  rw [show lslvKvm = lslvTcg from rfl]
  exact (lslv_tcg P u d n m s).of_reads
    (by isla_reads [lslvTcg, Profile.sys_get, Profile.sys])

set_option maxHeartbeats 4000000 in
/-- The trace of `LSRV Xd, Xn, Xm` under `tcg` agrees with `exec` for every register number, with
register 31 the zero register, and every state. -/
theorem lsrv_tcg (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] lsrvTcg (regFields d n m)
      (.lsrv d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, lsrvTcg, regFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      isla_reads [lsrvTcg, Profile.sys_get, Profile.sys] at hσ
      refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 58),
        fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
      · unfold Footprint.Run at h
        simp only [lsrvTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD] at h
        isla_fwd h using omega with [hσ, srem_toNat, slt_mod64, mod64_mod, mod64_div, mod64_lt]
        all_goals reg_end
      · subst h
        unfold Footprint.Run
        simp only [lsrvTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD]
        by_cases hn : n.val = 31 <;> by_cases hm : m.val = 31 <;> by_cases hd : d.val = 31
        all_goals
          isla_bwd [s.pc.toNat] using omega
            with [hσ, hn, hm, hd, srem_toNat, slt_mod64, mod64_mod, mod64_div, mod64_lt]
          try isla_gprs s using omega
            with [hσ, hn, hm, hd, srem_toNat, slt_mod64, mod64_mod, mod64_div, mod64_lt]
        all_goals first
          | exact toNat_lt _
          | reg_end
          | (simp only [sint]; omega)
          | omega

/-- The trace of `LSRV Xd, Xn, Xm` under `kvm` agrees with `exec` for every register number and
every state. -/
theorem lsrv_kvm (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] lsrvKvm (regFields d n m)
      (.lsrv d n m) s := by
  rw [show lsrvKvm = lsrvTcg from rfl]
  exact (lsrv_tcg P u d n m s).of_reads
    (by isla_reads [lsrvTcg, Profile.sys_get, Profile.sys])

set_option maxHeartbeats 4000000 in
/-- The trace of `UDIV Xd, Xn, Xm` under `tcg` agrees with `exec` for every register number, with
register 31 the zero register, and every state. The backward direction also splits on whether
register `m` holds zero, which the trace tests when `m` is not 31, and both the model and the trace
write zero for a divisor of zero. -/
theorem udiv_tcg (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] udivTcg (regFields d n m)
      (.udiv d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, udivTcg, regFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      isla_reads [udivTcg, Profile.sys_get, Profile.sys] at hσ
      refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 782),
        fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
      · unfold Footprint.Run at h
        simp only [udivTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD] at h
        isla_fwd h using omega with [hσ]
        all_goals reg_end
      · subst h
        unfold Footprint.Run
        simp only [udivTcg, Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD]
        by_cases hn : n.val = 31 <;> by_cases hm : m.val = 31 <;> by_cases hd : d.val = 31 <;>
          by_cases hz : (regAt s m.val).toNat = 0
        all_goals
          isla_bwd [s.pc.toNat] using omega with [hσ, hn, hm, hd, hz]
          try isla_gprs s using omega with [hσ, hn, hm, hd, hz]
        all_goals first
          | exact toNat_lt _
          | reg_end
          | (simp only [sint]; omega)
          | omega

/-- The trace of `UDIV Xd, Xn, Xm` under `kvm` agrees with `exec` for every register number and
every state. -/
theorem udiv_kvm (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] udivKvm (regFields d n m)
      (.udiv d n m) s := by
  rw [show udivKvm = udivTcg from rfl]
  exact (udiv_tcg P u d n m s).of_reads
    (by isla_reads [udivTcg, Profile.sys_get, Profile.sys])

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.addReg_tcg
#print axioms TestSupport.A64.Isla.addReg_kvm
#print axioms TestSupport.A64.Isla.subReg_tcg
#print axioms TestSupport.A64.Isla.subReg_kvm
#print axioms TestSupport.A64.Isla.andReg_tcg
#print axioms TestSupport.A64.Isla.andReg_kvm
#print axioms TestSupport.A64.Isla.eorReg_tcg
#print axioms TestSupport.A64.Isla.eorReg_kvm
#print axioms TestSupport.A64.Isla.orrReg_tcg
#print axioms TestSupport.A64.Isla.orrReg_kvm
#print axioms TestSupport.A64.Isla.orrW_tcg
#print axioms TestSupport.A64.Isla.orrW_kvm
#print axioms TestSupport.A64.Isla.subsReg_tcg
#print axioms TestSupport.A64.Isla.subsReg_kvm
#print axioms TestSupport.A64.Isla.madd_tcg
#print axioms TestSupport.A64.Isla.madd_kvm
#print axioms TestSupport.A64.Isla.msub_tcg
#print axioms TestSupport.A64.Isla.msub_kvm
#print axioms TestSupport.A64.Isla.lslv_tcg
#print axioms TestSupport.A64.Isla.lslv_kvm
#print axioms TestSupport.A64.Isla.lsrv_tcg
#print axioms TestSupport.A64.Isla.lsrv_kvm
#print axioms TestSupport.A64.Isla.udiv_tcg
#print axioms TestSupport.A64.Isla.udiv_kvm
