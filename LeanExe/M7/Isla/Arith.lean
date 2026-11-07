import LeanExe.M7.Isla.Check
import LeanExe.M7.Proof.Pair

/-!
Lemmas and tactics for the theorems of `Agrees` of the forms that compute `AddWithCarry` and of
the shifts.

The traces compute `AddWithCarry` in 128 bits and test the overflow V by comparing the sign
extension of the 32-bit result with the sum of the sign-extended operands, terms of the form
`r + r / 2^31 * (2^128 - 2^32)`.  With such a term in a flag, the kernel's check of the walk of
`SUB{S}` exceeded an 8 GiB cap at the second flag write: there `simp` reduces the projections of
the machine's structure instance, and the kernel checks the reduced type against the unreduced
one.  A proof by `rfl` that a projection of such an update equals
`decide (x * (2^128 - 2^32) % 2 = 1)` reproduced the growth.  `awc_v`, `awc_v_c`, and `awc_v_b`
rewrite the comparison during the walk into a condition on the signs of 32-bit values, after
which the walk of `SUB{S}` checks in 2.3 GiB.
-/

namespace LeanExe.M7.Isla

/-! The overflow of `AddWithCarry` as the traces compute it. -/

/-- The overflow test of a sum without a carry, as the trace of `ADD` computes it: the sign
extension of the result equals the sum of the sign-extended operands unless the operands have one
sign and the result the other. -/
theorem awc_v {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296) :
    ((a + b) % 340282366920938463463374607431768211456 % 4294967296 +
        (a + b) % 340282366920938463463374607431768211456 % 4294967296 / 2147483648 *
          340282366920938463463374607427473244160 =
      (a + a / 2147483648 * 340282366920938463463374607427473244160 +
          (b + b / 2147483648 * 340282366920938463463374607427473244160)) %
        340282366920938463463374607431768211456) ↔
      ¬(a / 2147483648 = b / 2147483648 ∧
        (a + b) % 4294967296 / 2147483648 ≠ a / 2147483648) := by
  have h1 : (a + b) % 340282366920938463463374607431768211456 = a + b :=
    Nat.mod_eq_of_lt (by omega)
  rw [h1]
  rcases Nat.lt_or_ge a 2147483648 with h3 | h3 <;>
    rcases Nat.lt_or_ge b 2147483648 with h4 | h4 <;>
    rcases Nat.lt_or_ge ((a + b) % 4294967296) 2147483648 with h5 | h5 <;> omega

/-- The overflow test of a sum with the carry `c`, as the traces of `SUB` and `CMP` compute it. -/
theorem awc_v_c {a b c : Nat} (ha : a < 4294967296) (hb : b < 4294967296) (hc : c ≤ 1) :
    (((a + b) % 340282366920938463463374607431768211456 + c) %
          340282366920938463463374607431768211456 % 4294967296 +
        ((a + b) % 340282366920938463463374607431768211456 + c) %
            340282366920938463463374607431768211456 % 4294967296 / 2147483648 *
          340282366920938463463374607427473244160 =
      ((a + a / 2147483648 * 340282366920938463463374607427473244160 +
            (b + b / 2147483648 * 340282366920938463463374607427473244160)) %
          340282366920938463463374607431768211456 + c) %
        340282366920938463463374607431768211456) ↔
      ¬(a / 2147483648 = b / 2147483648 ∧
        (a + b + c) % 4294967296 / 2147483648 ≠ a / 2147483648) := by
  have h1 : (a + b) % 340282366920938463463374607431768211456 = a + b :=
    Nat.mod_eq_of_lt (by omega)
  have h2 : (a + b + c) % 340282366920938463463374607431768211456 = a + b + c :=
    Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]
  rcases Nat.lt_or_ge a 2147483648 with h3 | h3 <;>
    rcases Nat.lt_or_ge b 2147483648 with h4 | h4 <;>
    rcases Nat.lt_or_ge ((a + b + c) % 4294967296) 2147483648 with h5 | h5 <;> omega

/-- The overflow test of a sum with the carry flag `f` as a number, as the trace of `SBC` computes
it. -/
theorem awc_v_b {a b : Nat} (f : Bool) (ha : a < 4294967296) (hb : b < 4294967296) :
    (((a + b) % 340282366920938463463374607431768211456 + if f = true then 1 else 0) %
          340282366920938463463374607431768211456 % 4294967296 +
        ((a + b) % 340282366920938463463374607431768211456 + if f = true then 1 else 0) %
            340282366920938463463374607431768211456 % 4294967296 / 2147483648 *
          340282366920938463463374607427473244160 =
      ((a + a / 2147483648 * 340282366920938463463374607427473244160 +
            (b + b / 2147483648 * 340282366920938463463374607427473244160)) %
          340282366920938463463374607431768211456 + if f = true then 1 else 0) %
        340282366920938463463374607431768211456) ↔
      ¬(a / 2147483648 = b / 2147483648 ∧
        (a + b + if f = true then 1 else 0) % 4294967296 / 2147483648 ≠ a / 2147483648) :=
  awc_v_c ha hb (by split <;> omega)

/-! `AddWithCarry` of the model as natural numbers. -/

/-- `addWithCarry` of the model: the low 32 bits of the sum, the carry out when the sum reaches
2^32, and the overflow when the operands have one sign and the result the other. -/
theorem awc_eq (x y : UInt32) (c : Bool) :
    addWithCarry x y c =
      (UInt32.ofNat (x.toNat + y.toNat + c.toNat),
        decide (4294967296 ≤ x.toNat + y.toNat + c.toNat),
        decide (x.toNat / 2147483648 = y.toNat / 2147483648 ∧
          (x.toNat + y.toNat + c.toNat) % 4294967296 / 2147483648 ≠ x.toNat / 2147483648)) := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have hc : c.toNat ≤ 1 := Bool.toNat_le c
  simp only [addWithCarry, Prod.mk.injEq, true_and]
  generalize c.toNat = k at *
  constructor
  · apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, ne_eq, UInt32.toNat_ofNat', decide_eq_true_eq, Nat.reducePow]
    omega
  · apply Bool.eq_iff_iff.mpr
    simp only [sint, UInt32.toNat_ofNat', bne_iff_ne, ne_eq, decide_eq_true_eq, Nat.reducePow]
    rcases Nat.lt_or_ge x.toNat 2147483648 with h3 | h3 <;>
      rcases Nat.lt_or_ge y.toNat 2147483648 with h4 | h4 <;>
      rcases Nat.lt_or_ge ((x.toNat + y.toNat + k) % 4294967296) 2147483648 with h5 | h5 <;>
      simp only [h3, h4, h5, ↓reduceIte, Nat.not_lt.mpr, Nat.lt_irrefl] <;> omega

/-! The flags as the traces write them: bits 3 to 0 of the word `NZCV`, built with `concat` from
bit 31 of the result and the three Boolean tests. -/

theorem word_n {n : Nat} (hn : n < 2) (z c v : Bool) :
    (((n * 2 + cond z 0 1) * 2 + cond c 1 0) * 2 + cond v 1 0) / 8 % 2 = n := by
  cases z <;> cases c <;> cases v <;> simp only [cond_true, cond_false] <;> omega

theorem word_z (n : Nat) (z c v : Bool) :
    (((n * 2 + cond z 0 1) * 2 + cond c 1 0) * 2 + cond v 1 0) / 4 % 2 = cond z 0 1 := by
  cases z <;> cases c <;> cases v <;> simp only [cond_true, cond_false] <;> omega

theorem word_c (n : Nat) (z c v : Bool) :
    (((n * 2 + cond z 0 1) * 2 + cond c 1 0) * 2 + cond v 1 0) / 2 % 2 = cond c 1 0 := by
  cases z <;> cases c <;> cases v <;> simp only [cond_true, cond_false] <;> omega

theorem word_v (n : Nat) (z c v : Bool) :
    (((n * 2 + cond z 0 1) * 2 + cond c 1 0) * 2 + cond v 1 0) % 2 = cond v 1 0 := by
  cases z <;> cases c <;> cases v <;> simp only [cond_true, cond_false] <;> omega

theorem cond01 (z : Bool) : decide (cond z 0 1 = 1) = !z := by cases z <;> rfl

theorem cond10 (c : Bool) : decide (cond c 1 0 = 1) = c := by cases c <;> rfl

theorem not_decide (p : Prop) [Decidable p] : (!decide p) = decide ¬p := (decide_not).symm

/-- Two words whose values agree modulo 2^32. -/
theorem ofNat32_congr {a b : Nat} (h : a % 4294967296 = b % 4294967296) :
    UInt32.ofNat a = UInt32.ofNat b := by
  rw [← ofNat_mod32 a, ← ofNat_mod32 b, h]

theorem ite_toNat (b : Bool) : (if b = true then 1 else 0) = b.toNat := by cases b <;> rfl

theorem toNat_mod32 (x : UInt32) : x.toNat % 4294967296 = x.toNat := Nat.mod_eq_of_lt x.toNat_lt

theorem four_mul (a : Nat) : 4 * a = a * 4 := Nat.mul_comm 4 a

theorem imm5_lt32 (a : Fin 8) (b : Fin 4) : (a.val * 4 + b.val < 32) = True := eq_true (by omega)

/-! SP, the low word of X13. -/

theorem low_sp (s : State) : low s 13 = s.sp := by
  unfold low
  simp

theorem setLow_sp (s : State) (v : UInt32) : setLow s 13 v = { s with sp := v } := by
  unfold setLow
  simp

/-- A word that is a multiple of 4 keeps its value when bits 1 and 0 are cleared. -/
theorem and_fffffffc {r : UInt32} (h : r % 4 = 0) : r &&& 0xFFFFFFFC = r := by
  have h4 : r.toNat % 4 = 0 := by
    have := congrArg UInt32.toNat h
    rw [UInt32.toNat_mod] at this
    exact this
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, show (0xFFFFFFFC : UInt32).toNat = 4294967292 from rfl]
  have hr := r.toNat_lt
  have h1 : (r.toNat &&& 4294967292) % 2 ^ 2 = 0 := by
    rw [Nat.and_mod_two_pow, show (4294967292 : Nat) % 2 ^ 2 = 0 from rfl, Nat.and_zero]
  have h2 : (r.toNat &&& 4294967292) >>> 2 = r.toNat >>> 2 := by
    rw [Nat.shiftRight_and_distrib, show (4294967292 : Nat) >>> 2 = 2 ^ 30 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt]
    rw [Nat.shiftRight_eq_div_pow]
    omega
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at h2
  omega

/-- A word given by a number equals a sum of words when the number agrees with the sum modulo
2^32. -/
theorem ofNat_eq_add {v : Nat} {x y : UInt32}
    (h : v % 4294967296 = (x.toNat + y.toNat) % 4294967296) : UInt32.ofNat v = x + y := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', UInt32.toNat_add]
  exact h

/-- A word given by a number equals a difference of words when the number agrees with the
difference modulo 2^32. -/
theorem ofNat_eq_sub {v : Nat} {x y : UInt32}
    (h : v % 4294967296 = (4294967296 - y.toNat + x.toNat) % 4294967296) :
    UInt32.ofNat v = x - y := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', UInt32.toNat_sub]
  exact h

/-- Proves a side condition of a path of a trace, as `t32_side` does, with the case split of a
flag's number tried before the lemmas and with `rfl` only for the equation of `FeatureImpl` with
the profile's. -/
macro "t32_side'" : tactic => `(tactic| first
  | omega
  | (split <;> omega)
  | (simp only [LeanExe.A64.Isla.sint]; omega)
  | exact x_lt_pow _ _
  | exact Nat.lt_trans (UInt32.toNat_lt _) (by decide)
  | (show List.map LeanExe.A64.Isla.Val.bool _ ++ _ = _; rfl))

/-- Builds a path of a trace with `t32_bwd`, giving the 30 declared variables that hold Isla's
values of `R0` to `R12` and `R14` to `R30` the values of the X registers of the machine `m`, for a
read of the register vector in which an earlier read of `R13` by its name gives the value of
`R13`. -/
syntax "t32_gprs13 " term " using " tacticSeq " with " "[" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic
macro_rules
  | `(tactic| t32_gprs13 $m using $d with [$xs,*]) => `(tactic| t32_bwd [
      Mach.x $m 0, Mach.x $m 1, Mach.x $m 2, Mach.x $m 3, Mach.x $m 4, Mach.x $m 5, Mach.x $m 6,
      Mach.x $m 7, Mach.x $m 8, Mach.x $m 9, Mach.x $m 10, Mach.x $m 11, Mach.x $m 12,
      Mach.x $m 14, Mach.x $m 15, Mach.x $m 16, Mach.x $m 17, Mach.x $m 18, Mach.x $m 19,
      Mach.x $m 20, Mach.x $m 21, Mach.x $m 22, Mach.x $m 23, Mach.x $m 24, Mach.x $m 25,
      Mach.x $m 26, Mach.x $m 27, Mach.x $m 28, Mach.x $m 29, Mach.x $m 30]
      using $d with [$xs,*])

open Lean Elab Tactic Meta in
/-- Clears the hypotheses `¬a = k` with a numeral `k` of at least 16: the tests of the decode
against the patterns of other encodings, which no comparison of outcomes needs, so that `omega`
in the closing steps works on the facts of the path. -/
elab "t32_clear" : tactic => withMainContext do
  let mut fvs := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if let some p := t.not? then
      if let some (_, _, rhs) := p.eq? then
        if let some k := rhs.nat? then
          if 16 ≤ k then fvs := fvs.push d.fvarId
  liftMetaTactic fun g => return [← g.tryClearMany fvs]

open Lean Elab Tactic Meta in
/-- The terms `Bool.toNat b` of an expression. -/
partial def collectToNat (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.isAppOfArity ``Bool.toNat 1 && !e.hasLooseBVars then
    if acc.contains e.appArg! then acc else acc.push e.appArg!
  else match e with
    | .app f a => collectToNat a (collectToNat f acc)
    | .lam _ t b _ => collectToNat b (collectToNat t acc)
    | .forallE _ t b _ => collectToNat b (collectToNat t acc)
    | .mdata _ b => collectToNat b acc
    | .proj _ _ b => collectToNat b acc
    | _ => acc

open Lean Elab Tactic Meta in
/-- Adds `b.toNat ≤ 1` for each term `Bool.toNat b` of the goal, a bound that `omega` lacks. -/
elab "t32_bool_bounds" : tactic => withMainContext do
  let bs := collectToNat (← instantiateMVars (← getMainTarget)) #[]
  liftMetaTactic fun g => do
    let mut g := g
    for b in bs do
      let pf ← mkAppM ``Bool.toNat_le #[b]
      g ← g.assert `hb (← inferType pf) pf
      let (_, g') ← g.intro1P
      g := g'
    return [g]

/-- Rewrites the comparison of the model's state after a form that computes `AddWithCarry` with the
trace's, in stages: the sums of 128 bits below 2^128 as natural numbers, the low words of the X
registers as the model's registers with the lemmas in brackets, `addWithCarry` and the flags as
natural numbers and the bits of the trace's word, and the Boolean tests as propositions; then
proves the remaining equations of the written register and the flags. -/
syntax "t32_awc_state " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| t32_awc_state [$xs,*]) => `(tactic| (
    simp -failIfUnchanged only [ite_toNat] at *
    all_goals t32_bool_bounds
    all_goals simp -failIfUnchanged (disch := omega) only [Nat.mod_eq_of_lt]
    all_goals simp -failIfUnchanged (disch := omega) only [setLow_r, setLow_sp, x_mod, low_r,
      low_sp, $xs,*] at *
    all_goals simp -failIfUnchanged (disch := omega) only [State.result, State.setNZCV,
      State.setR, ↓reduceIte, State.mk.injEq, awc_eq, nflag32, zflag32, UInt32.toNat_not,
      UInt32.toNat_ofNat', Bool.toNat_true, Bool.toNat_false, LeanExe.A64.Isla.nat_add_zero,
      UInt32.size, Nat.reducePow, Nat.reduceSub, ofNat_mod32, ofNat_four, word_n, word_z, word_c,
      word_v, LeanExe.A64.Isla.fin_mod, toNat_shl, four_mul, toNat_mod32, Nat.pow_zero,
      Nat.mul_one, imm12, true_and, and_true, *]
    all_goals simp -failIfUnchanged only [cond01, cond10, Bool.not_not, not_decide,
      Classical.not_not, decide_eq_decide, true_and, and_true]
    all_goals first
      | with_reducible rfl
      | (funext j; split <;> first | with_reducible rfl | (apply ofNat32_congr; omega))
      | (refine ⟨?_, ?_⟩ <;> omega)
      | (apply ofNat_eq_add; simp -failIfUnchanged only [UInt32.toNat_ofNat', Nat.reducePow]
         omega)
      | (apply ofNat_eq_sub; simp -failIfUnchanged only [UInt32.toNat_ofNat', Nat.reducePow]
         omega)
      | omega))

/-- Proves that the outcome at the end of a path of the trace of a form that writes the register
`d` of r0 to r7 with a sum of `AddWithCarry` and, when the trace writes them, the flags, is
`exec`'s, with `t32_awc_state`. -/
syntax "t32_awc_end " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| t32_awc_end [$xs,*]) => `(tactic| (
    t32_clear
    simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
    t32_pc
    simp only [Outcome.done.injEq, and_true, true_and]
    simp -failIfUnchanged (disch := first | omega | t32_lt) only [setX_low, setX_keep]
    apply exists_mach
    · t32_awc_state [$xs,*]
    · rfl
    · rfl))

/-- Proves that the outcome of `exec` equals the outcome at the end of the path of the trace that
keeps bits 63 to 32 of the written register, as `t32_awc_end` does. -/
syntax "t32_awc_bwd " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| t32_awc_bwd [$xs,*]) => `(tactic| (
    t32_clear
    simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
    t32_pc
    simp only [Outcome.done.injEq, and_true, true_and]
    simp -failIfUnchanged (disch := first | omega | t32_lt) only [setX_keep]
    congr 1
    apply Eq.symm
    t32_awc_state [$xs,*]))

/-! The shifts.  A shift amount reaches the shift through a sign extension of a value below 2^8,
the bottom byte of a register or `imm3:imm2`, which these lemmas drop. -/

theorem mod256_mod64 (x : Nat) : x % 256 % 18446744073709551616 = x % 256 := by omega

theorem mod256_div63 (x : Nat) : x % 256 / 9223372036854775808 = 0 := by omega

theorem mod256_mod32 (x : Nat) : x % 256 % 4294967296 = x % 256 := by omega

theorem imm5_mod64 (a : Fin 8) (b : Fin 4) :
    (a.val * 4 + b.val) % 18446744073709551616 = a.val * 4 + b.val := by omega

theorem imm5_div63 (a : Fin 8) (b : Fin 4) : (a.val * 4 + b.val) / 9223372036854775808 = 0 := by
  omega

theorem imm5_mod32 (a : Fin 8) (b : Fin 4) :
    (a.val * 4 + b.val) % 4294967296 = a.val * 4 + b.val := by omega

/-- A number below 2^127 read as a signed number of 128 bits. -/
theorem sint128_of_lt {x : Nat} (h : x < 170141183460469231731687303715884105728) :
    LeanExe.A64.Isla.sint 128 x = (x : Int) := by
  unfold LeanExe.A64.Isla.sint
  rw [Nat.div_eq_of_lt (by simp only [Nat.reduceSub, Nat.reducePow]; omega), Nat.zero_mul]
  simp

theorem sint_mod256 (x : Nat) : LeanExe.A64.Isla.sint 128 (x % 256) = ((x % 256 : Nat) : Int) :=
  sint128_of_lt (by omega)

theorem sint_imm5 (a : Fin 8) (b : Fin 4) :
    LeanExe.A64.Isla.sint 128 (a.val * 4 + b.val) = ((a.val * 4 + b.val : Nat) : Int) :=
  sint128_of_lt (by omega)

theorem sint_zero : LeanExe.A64.Isla.sint 128 0 = 0 := sint128_of_lt (by decide)

theorem sint_32 : LeanExe.A64.Isla.sint 128 32 = 32 := sint128_of_lt (by decide)

/-- `bvshl` of 32 bits as the model's `shl`. -/
theorem ofNat_shl (a : UInt32) (k : Nat) :
    UInt32.ofNat (if k < 32 then a.toNat * 2 ^ k % 4294967296 else 0) = shl a k := by
  apply UInt32.toNat_inj.mp
  rw [toNat_shl, UInt32.toNat_ofNat']
  split
  · simp only [Nat.reducePow, Nat.mod_mod]
  · rename_i hk
    rw [show 2 ^ k = 4294967296 * 2 ^ (k - 32) by
      rw [show (4294967296 : Nat) = 2 ^ 32 from rfl, ← Nat.pow_add]; congr 1; omega]
    rw [Nat.mul_left_comm, Nat.mul_mod_right, Nat.zero_mod]

/-- `bvlshr` of 32 bits as the model's `shr`. -/
theorem ofNat_shr (a : UInt32) (k : Nat) :
    UInt32.ofNat (if k < 32 then a.toNat / 2 ^ k else 0) = shr a k := by
  apply UInt32.toNat_inj.mp
  rw [toNat_shr, UInt32.toNat_ofNat']
  split
  · exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.toNat_lt)
  · rename_i hk
    rw [Nat.zero_mod, Nat.div_eq_of_lt]
    calc a.toNat < 2 ^ 32 := a.toNat_lt
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)

theorem ofNat_shl_lt (a : UInt32) {k : Nat} (h : k < 32) :
    UInt32.ofNat (a.toNat * 2 ^ k % 4294967296) = shl a k := by
  rw [← ofNat_shl, if_pos h]

theorem ofNat_shr_lt (a : UInt32) {k : Nat} (h : k < 32) :
    UInt32.ofNat (a.toNat / 2 ^ k) = shr a k := by
  rw [← ofNat_shr, if_pos h]

theorem shr_32 (x : UInt32) : shr x 32 = 0 := by simp [shr]

theorem shr_zero (x : UInt32) : shr x 0 = x := by
  apply UInt32.toNat_inj.mp
  rw [toNat_shr, Nat.pow_zero, Nat.div_one]

theorem ite_lt32 {c : Prop} [Decidable c] {a b : Nat} (ha : a < 4294967296)
    (hb : b < 4294967296) : (if c then a else b) < 4294967296 := by
  split <;> assumption

theorem div_lt32 (a b : Nat) : a % 4294967296 / b < 4294967296 :=
  Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide))

/-- Proves that a value that a trace writes to the low word of a register is below 2^32, as
`t32_lt` does, also for a quotient of a word and for a value that a test on the shift amount
chooses. -/
macro "t32_lt'" : tactic => `(tactic| first
  | t32_lt
  | apply div_lt32
  | (apply ite_lt32 <;> first | omega | apply div_lt32))

/-- Proves that the outcome at the end of a path of the trace of a form that writes one register
of r0 to r7 is `exec`'s, as `t32_reg_end` does, with the facts of the path on the operands rewritten
as the model's registers and the lemmas in brackets. -/
syntax "t32_val_end " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| t32_val_end [$xs,*]) => `(tactic| (
    t32_clear
    simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
    t32_pc
    simp only [Outcome.done.injEq, and_true, true_and]
    simp (disch := first | omega | t32_lt') only [setX_low, setX_keep]
    apply exists_mach
    · simp -failIfUnchanged (disch := omega) only [setLow_r, x_mod, low_r] at *
      all_goals apply state_eq
      all_goals simp -failIfUnchanged (disch := omega) only [ofNat_toNat32, ofNat_zero32,
        ↓reduceIte, $xs,*, *]
    · rfl
    · rfl))

/-- Proves that the outcome of `exec` equals the outcome at the end of the path of the trace that
keeps bits 63 to 32 of the written register, as `t32_val_end` does. -/
syntax "t32_val_bwd " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| t32_val_bwd [$xs,*]) => `(tactic| (
    t32_clear
    simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
    t32_pc
    simp only [Outcome.done.injEq, and_true, true_and]
    simp (disch := first | omega | t32_lt') only [setX_keep]
    simp -failIfUnchanged (disch := omega) only [setLow_r, x_mod, low_r] at *
    all_goals congr 1
    all_goals apply Eq.symm
    all_goals apply state_eq
    all_goals simp -failIfUnchanged (disch := omega) only [ofNat_toNat32, ofNat_zero32,
      ↓reduceIte, $xs,*, *]))

end LeanExe.M7.Isla
