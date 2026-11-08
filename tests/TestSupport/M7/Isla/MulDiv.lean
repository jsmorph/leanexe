import LeanExe.M7.Isla.Check
import LeanExe.M7.Isla.Profile

/-!
Theorems of `Agrees` for the multiply and divide forms of `LeanExe/M7/Machine.lean`, MLA, MLS,
UMULL, and UDIV, from the traces of `tests/isla/m7` under the profile `sys` of
`LeanExe/M7/Isla/Profile.lean`.  Each theorem holds for every register of r0 to r7 in each field,
every machine whose program counter plus 4 is below 2^32, every platform, and every sequence of
device values.  `tests/isla/m7-theorems.sh` elaborates the module and prints the axioms of its
theorems.

MLA and MLS sign-extend each operand to 128 bits, cut it to 64, and sign-extend it again, multiply
in 128 bits, add or subtract in 64, and write the low 32 bits of the result.  Every sign extension
adds a multiple of 2^32, so `mla_val` and `mls_val` reduce the trace's value modulo 2^32 to the
model's `Ra + Rn * Rm` and `Ra - Rn * Rm`.  UMULL and UDIV zero-extend each operand to 128 bits,
cut it to 64, and sign-extend it again, which `zx_mod` reduces to the operand, since bit 63 is
clear.  UMULL writes RdHi before RdLo, and Isla gives the second write the registers after the
first as `ite` expressions, which `cond_setX_keep` folds into the registers of the machine after
the first write.  UDIV's trace comes from the IR that `tests/isla/armv9p4-t32-udiv.diff` edits,
which divides with `tdiv_int`, and its value is `bvsdiv` of the operands, which `sdiv_128` equates
with the quotient for a nonzero divisor.  The trace writes 0 for a divisor of 0, where `exec`
stops, so `Agrees`, which concerns the states that `exec` gives, covers no zero divisor, and the
theorem of UDIV takes no premise on the divisor.
-/

namespace TestSupport.M7.Isla

open LeanExe.M7 LeanExe.M7.Isla
open LeanExe.A64.Isla (Footprint Fields Opcode sdiv sdiv_128)

/-- The fields of MLA and MLS for the registers `d`, `n`, `m`, and `a`. -/
def mulFields (d n m a : Fin 8) : Fields :=
  [("Rn", n.val), ("Ra", a.val), ("Rd", d.val), ("Rm", m.val)]

/-- The fields of UMULL for the registers `lo`, `hi`, `n`, and `m`. -/
def umullFields (lo hi n m : Fin 8) : Fields :=
  [("Rn", n.val), ("RdLo", lo.val), ("RdHi", hi.val), ("Rm", m.val)]

/-- The fields of UDIV for the registers `d`, `n`, and `m`. -/
def udivFields (d n m : Fin 8) : Fields := [("Rn", n.val), ("Rd", d.val), ("Rm", m.val)]

/-- The footprint of `MLA Rd, Rn, Rm, Ra`. -/
def mlaT : Footprint := isla_trace% "tests/isla/m7/mla"

/-- The footprint of `MLS Rd, Rn, Rm, Ra`. -/
def mlsT : Footprint := isla_trace% "tests/isla/m7/mls"

/-- The footprint of `UMULL RdLo, RdHi, Rn, Rm`. -/
def umullT : Footprint := isla_trace% "tests/isla/m7/umull"

/-- The footprint of `UDIV Rd, Rn, Rm`. -/
def udivT : Footprint := isla_trace% "tests/isla/m7/udiv"

/-! The values of MLA and MLS.  `ext% x` is a word `x` sign-extended to 128 bits, cut to 64, and
sign-extended to 128 again, and `sx% x` a 64-bit value sign-extended to 128 bits, as `t32_simp`
writes them. -/

local notation "C1" => (340282366920938463463374607427473244160 : Nat)
local notation "C2" => (340282366920938463444927863358058659840 : Nat)
local notation "P64" => (18446744073709551616 : Nat)
local notation "P128" => (340282366920938463463374607431768211456 : Nat)

local notation "ext% " x:max =>
  (x + x / 2147483648 * C1) % P64 + (x + x / 2147483648 * C1) % P64 / 9223372036854775808 * C2

local notation "sx% " x:max => x + x / 9223372036854775808 * C2

/-- A word sign-extended twice keeps its low 32 bits. -/
theorem ext_mod (x : UInt32) : (ext% x.toNat) % 4294967296 = x.toNat := by
  have := x.toNat_lt
  omega

/-- The product of two words sign-extended twice agrees with theirs in the low 32 bits. -/
theorem ext_mul (x y : UInt32) :
    (ext% x.toNat) * (ext% y.toNat) % 4294967296 = x.toNat * y.toNat % 4294967296 := by
  rw [Nat.mul_mod, ext_mod, ext_mod]

/-- MLA's value modulo 2^32, for a product `p` and an addend `q` that agree with the model's in
the low 32 bits. -/
theorem mla_mod {p q A NK : Nat} (hp : p % 4294967296 = NK % 4294967296)
    (hq : q % 4294967296 = A) :
    (sx% ((sx% (p % P128 % P64) % P64 + q % P64) % P64)) % 4294967296 =
      (A + NK % 4294967296) % 4294967296 := by
  omega

/-- The value of MLA as the trace computes it is the model's `a + n * k`. -/
theorem mla_val (n k a : UInt32) :
    UInt32.ofNat ((sx% ((sx% ((ext% n.toNat) * (ext% k.toNat) % P128 % P64) % P64 +
      (ext% a.toNat) % P64) % P64)) % 4294967296) = a + n * k := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat', UInt32.toNat_add, UInt32.toNat_mul, Nat.reducePow, Nat.mod_mod]
  exact mla_mod (ext_mul n k) (ext_mod a)

/-- MLS's value modulo 2^32, as `mla_mod` states MLA's.  The proof replaces the truncated
subtractions by variables. -/
theorem mls_mod {p q A NK : Nat} (hp : p % 4294967296 = NK % 4294967296)
    (hq : q % 4294967296 = A) :
    (sx% ((q % P64 + (P64 - (sx% (p % P128 % P64)) % P64)) % P64)) % 4294967296 =
      (4294967296 - NK % 4294967296 + A) % 4294967296 := by
  have hb : (sx% (p % P128 % P64)) % P64 < P64 := Nat.mod_lt _ (by decide)
  have hm : (sx% (p % P128 % P64)) % P64 % 4294967296 = NK % 4294967296 := by omega
  generalize (sx% (p % P128 % P64)) % P64 = r at hb hm ⊢
  have hr : P64 - r + r = P64 := by omega
  generalize P64 - r = t at hr ⊢
  have hn : 4294967296 - NK % 4294967296 + NK % 4294967296 = 4294967296 := by omega
  generalize 4294967296 - NK % 4294967296 = w at hn ⊢
  omega

/-- The value of MLS as the trace computes it is the model's `a - n * k`. -/
theorem mls_val (n k a : UInt32) :
    UInt32.ofNat ((sx% (((ext% a.toNat) % P64 +
      (P64 - (sx% ((ext% n.toNat) * (ext% k.toNat) % P128 % P64)) % P64)) % P64)) %
        4294967296) = a - n * k := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat', UInt32.toNat_sub, UInt32.toNat_mul, Nat.reducePow, Nat.mod_mod]
  exact mls_mod (ext_mul n k) (ext_mod a)

/-! The values of UMULL and UDIV. -/

/-- A word zero-extended to 128 bits, cut to 64, and sign-extended to 128 is the word. -/
theorem zx_mod (x : Nat) :
    x % 4294967296 % P64 + x % 4294967296 % P64 / 9223372036854775808 * C2 = x % 4294967296 := by
  omega

/-- The product of two words. -/
theorem mul_le32 (x y : UInt32) : x.toNat * y.toNat ≤ 4294967295 * 4294967295 := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  exact Nat.mul_le_mul (by omega) (by omega)

/-- The high word of UMULL's product, bits 63 to 32 of the 128-bit product. -/
theorem umull_hi (x y : UInt32) :
    UInt32.ofNat (x.toNat * y.toNat % P128 / 4294967296 % 4294967296) =
      UInt32.ofNat (x.toNat * y.toNat / 4294967296) := by
  have := mul_le32 x y
  generalize x.toNat * y.toNat = p at *
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat', Nat.reducePow]
  omega

/-- The low word of UMULL's product. -/
theorem umull_lo (x y : UInt32) :
    UInt32.ofNat (x.toNat * y.toNat % P128 % 4294967296) = UInt32.ofNat (x.toNat * y.toNat) := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat', Nat.reducePow]
  omega

/-- The value of UDIV for a nonzero divisor, `bvsdiv` of the words, is the model's `n / k`. -/
theorem udiv_val (n k : UInt32) (hk : k ≠ 0) :
    UInt32.ofNat (sdiv 128 n.toNat k.toNat % 4294967296) = n / k := by
  have hn := n.toNat_lt
  have hk' : k.toNat ≠ 0 := fun h => hk ((toNat_zero_iff k).mp h)
  have h : n.toNat / k.toNat < 4294967296 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn
  rw [sdiv_128 (by omega) (by have := k.toNat_lt; omega) (by omega)]
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat', UInt32.toNat_div, Nat.reducePow, Nat.mod_eq_of_lt h]

/-! The registers after UMULL's first write. -/

/-- The low word of X register `j` below 15 after a write of the low word of X register `i`. -/
theorem low_setLow {i j : Nat} (s : State) (hi : i < 15) (hj : j < 15) (v : UInt32) :
    low (setLow s i v) j = if i = j then v else low s j := by
  unfold low setLow
  by_cases h1 : i < 13 <;> by_cases h2 : i = 13 <;> by_cases h3 : j < 13 <;>
    by_cases h4 : j = 13 <;> by_cases h5 : i = j <;>
    simp [h1, h2, h3, h4, h5] <;> omega

/-- X register `j` after a write of X register `i` with a 64-bit value. -/
theorem setX_x (m : Mach) {i n : Nat} (j : Nat) (hi : i < 31) (hn : n < P64) (hj : j < 31) :
    (m.setX i n).x j = if i = j then n else m.x j := by
  by_cases h3 : i = j
  · subst h3
    rw [ite_eq_left rfl]
    unfold Mach.setX Mach.x
    by_cases h1 : i < 15
    · simp [h1, low_setLow, UInt32.toNat_ofNat']
      omega
    · simp [h1, hi, Nat.sub_add_cancel (Nat.le_of_not_lt h1), UInt64.toNat_ofNat']
      omega
  · have h3' : ¬j = i := fun h => h3 h.symm
    rw [ite_eq_right h3]
    unfold Mach.setX Mach.x
    by_cases h1 : i < 15 <;> by_cases h2 : j < 15
    · simp [h1, h2, h3, h3', low_setLow]
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2, hj, Nat.sub_add_cancel (Nat.le_of_not_lt h2), h3']

/-- Isla's value of X register `j` after a write of `n` to X register `i`, an `ite` on the index,
is register `j` of the machine after the write. -/
theorem cond_setX (m : Mach) {i n : Nat} (j : Nat) (hi : i < 31) (hn : n < P64) (hj : j < 31) :
    cond (decide (i = j)) n (m.x j) = (m.setX i n).x j := by
  rw [setX_x m j hi hn hj]
  by_cases h : i = j <;> simp [h]

/-- A write that keeps bits 63 to 32 of an X register has 64 bits. -/
theorem keep_lt64 (m : Mach) (i : Nat) {v : Nat} (hv : v < 4294967296) :
    m.x i &&& 18446744069414584320 ||| v < P64 :=
  Nat.or_lt_two_pow (n := 64) (Nat.lt_of_le_of_lt Nat.and_le_left (x_lt_pow m i)) (by omega)

/-- `cond_setX` for the write that keeps bits 63 to 32, the write of the path that the backward
direction builds. -/
theorem cond_setX_keep (m : Mach) {i v : Nat} (j : Nat) (hi : i < 31) (hv : v < 4294967296)
    (hj : j < 31) :
    cond (decide (i = j)) (m.x i &&& 18446744069414584320 ||| v) (m.x j) =
      (m.setX i (m.x i &&& 18446744069414584320 ||| v)).x j :=
  cond_setX m j hi (keep_lt64 m i hv) hj

/-- The model's state after a form that writes register `d` with `a` and then `e` with `b`, as the
trace's outcome gives it, is `exec`'s. -/
theorem state_eq2 {s : State} {d e : Fin 8} {a b a' b' : UInt32} (h1 : a = a') (h2 : b = b') :
    { (s.setR d a).setR e b with pc := ((s.setR d a).setR e b).pc + UInt32.ofNat 4 } =
      { (s.setR d a').setR e b' with pc := s.pc + 4 } := by
  subst h1 h2
  rfl

/-- Proves that the outcome at the end of a path of UMULL's trace is `exec`'s, as `t32_reg_end`
does for one register. -/
macro "umull_end" : tactic => `(tactic| (
  simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
  t32_pc
  simp only [Outcome.done.injEq, and_true, true_and]
  simp (disch := first | omega | t32_lt) only [setX_low, setX_keep]
  apply exists_mach
  · simp only [setLow_r]
    apply state_eq2
    · simp (disch := omega) only [x_mod, low_r, umull_hi]
    · simp (disch := omega) only [x_mod, low_r, umull_lo]
  · rfl
  · rfl))

/-- Proves that the outcome of `exec` equals the outcome at the end of the path of UMULL's trace
that keeps bits 63 to 32 of both written registers. -/
macro "umull_bwd" : tactic => `(tactic| (
  simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
  t32_pc
  simp only [Outcome.done.injEq, and_true, true_and]
  simp (disch := first | omega | t32_lt) only [setX_keep]
  simp only [setLow_r]
  congr 1
  apply Eq.symm
  apply state_eq2
  · simp (disch := omega) only [x_mod, low_r, umull_hi]
  · simp (disch := omega) only [x_mod, low_r, umull_lo]))

/-- Proves the first three parts of `Agrees` for a 32-bit form: the header's fields, the width,
and the decode of the opcode's word for the fields `fs`. -/
syntax "md_decode " ident ident : tactic
macro_rules
  | `(tactic| md_decode $F $fs) => `(tactic| (
    refine ⟨by decide, by decide, ?_, ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, $F:ident, $fs:ident, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega))

/-- Unfolds `footRun` for the footprint `F` and the fields `fs`, at a hypothesis or in the
goal. -/
syntax "md_run " ident ident (" at " ident)? : tactic
macro_rules
  | `(tactic| md_run $F $fs at $h) => `(tactic| (
    unfold footRun at $h:ident
    simp only [$F:ident, LeanExe.A64.Isla.Footprint.vars, $fs:ident, List.foldl, List.lookup,
      String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
      Nat.reduceDiv] at $h:ident))
  | `(tactic| md_run $F $fs) => `(tactic| (
    unfold footRun
    simp only [$F:ident, LeanExe.A64.Isla.Footprint.vars, $fs:ident, List.foldl, List.lookup,
      String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
      Nat.reduceDiv]))

/-- Proves the rest of `Agrees` for the footprint `F` of MLA or MLS with the fields `fs`, after
`md_decode`: the premise on `σ`, every path of the trace by `t32_fwd` and `t32_reg_end`, and the
path that keeps the high words, with the values `vs` before the reads of `R0` to `R30`,
`t32_gprs` of the machine `m`, and `false` for the Boolean that chooses the write of the register.
`k` is the number of the decode clause, which the trace writes to `SEE`, and the lemma `v` turns
the written value into the model's. -/
syntax "mul_agrees " ident ident num term:max "[" term,* "]" term : tactic
macro_rules
  | `(tactic| mul_agrees $F $fs $k $m [$vs,*] $v) => `(tactic| (
    intro σ hσ s' hs
    simp only [exec, Option.some.injEq] at hs
    subst hs
    t32_reads [$F:ident, sys_get, sys] at hσ
    refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
      (.bits 128 $k), fun o h => ?_, ?_, by t32_frame⟩
    · md_run $F $fs at h
      t32_fwd h using omega with [hσ]
      all_goals t32_reg_end [$v:term]
    · md_run $F $fs
      t32_bwd [$vs,*] using omega with [hσ]
      t32_gprs $m using omega with [hσ]
      t32_bwd [false] using omega with [hσ]
      all_goals first
        | t32_reg_bwd [$v:term]
        | t32_side))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `MLA Rd, Rn, Rm, Ra` agrees with `exec` for every register of r0 to r7 in each
field and every machine whose program counter plus 4 is below 2^32. -/
theorem mla_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d n k a : Fin 8)
    (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] mlaT (mulFields d n k a)
      (.mla d n k a) m := by
  without_info
    md_decode mlaT mulFields
    mul_agrees mlaT mulFields 3006 m [u.feature, m.s.pc.toNat] mla_val

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `MLS Rd, Rn, Rm, Ra` agrees with `exec` for every register of r0 to r7 in each
field and every machine whose program counter plus 4 is below 2^32. -/
theorem mls_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d n k a : Fin 8)
    (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] mlsT (mulFields d n k a)
      (.mls d n k a) m := by
  without_info
    md_decode mlsT mulFields
    mul_agrees mlsT mulFields 3008 m [u.feature, m.s.pc.toNat] mls_val

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `UDIV Rd, Rn, Rm` agrees with `exec` for every register of r0 to r7 in each field
and every machine whose program counter plus 4 is below 2^32.  `exec` gives a state only for a
nonzero divisor, so `hz` holds on every path that the proof follows, and with it the trace's test
of the divisor takes the branch that divides. -/
theorem udiv_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d n k : Fin 8) (m : Mach)
    (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] udivT (udivFields d n k)
      (.udiv d n k) m := by
  without_info
    md_decode udivT udivFields
    intro σ hσ s' hs
    simp only [exec] at hs
    split at hs
    · cases hs
    rename_i hne
    simp only [Option.some.injEq] at hs
    subst hs
    have hz : ¬m.x k.val % 4294967296 = 0 := by
      rw [x_mod m (by omega), low_r, toNat_zero_iff]
      exact hne
    t32_reads [udivT, sys_get, sys] at hσ
    refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
      (.bits 128 3291), fun o h => ?_, ?_, by t32_frame⟩
    · md_run udivT udivFields at h
      t32_fwd h using omega with [hσ, hz, zx_mod]
      all_goals t32_reg_end [udiv_val _ _ hne]
    · md_run udivT udivFields
      t32_bwd [u.feature, m.s.pc.toNat] using omega with [hσ, hz, zx_mod]
      t32_gprs m using omega with [hσ, hz, zx_mod]
      t32_bwd [false] using omega with [hσ, hz, zx_mod]
      all_goals first
        | t32_reg_bwd [udiv_val _ _ hne]
        | t32_side

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `UMULL RdLo, RdHi, Rn, Rm` agrees with `exec` for every register of r0 to r7 in
each field with distinct destinations and every machine whose program counter plus 4 is below
2^32.  The destinations differ in every instruction of the form, so the trace's `assume` of the
configuration's constraint holds.  The trace forks at each of the two writes, and the backward
direction builds the path that keeps bits 63 to 32 of both. -/
theorem umull_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (lo hi n k : Fin 8)
    (h : lo ≠ hi) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] umullT (umullFields lo hi n k)
      (.umull lo hi n k h) m := by
  without_info
    md_decode umullT umullFields
    intro σ hσ s' hs
    simp only [exec, Option.some.injEq] at hs
    subst hs
    have hlh : lo.val ≠ hi.val := fun e => h (Fin.ext e)
    t32_reads [umullT, sys_get, sys] at hσ
    refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
      (.bits 128 3309), fun o h' => ?_, ?_, by t32_frame⟩
    · md_run umullT umullFields at h'
      t32_fwd h' using omega with [hσ, zx_mod]
      all_goals umull_end
    · md_run umullT umullFields
      t32_bwd [u.feature, m.s.pc.toNat] using omega with [hσ, zx_mod]
      t32_gprs m using omega with [hσ, zx_mod]
      t32_bwd [false, false] using omega with [hσ, zx_mod, cond_setX_keep]
      all_goals first
        | umull_bwd
        | t32_side

#print axioms mla_agrees
#print axioms mls_agrees
#print axioms udiv_agrees
#print axioms umull_agrees

end TestSupport.M7.Isla
