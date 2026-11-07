import LeanExe.A64.Isla.Check
import LeanExe.A64.Isla.Profile

/-!
Theorems of `Agrees` for the branch forms of `LeanExe/A64/Machine.lean`, `B`, `BL`, `CBZ`,
`CBNZ`, `B.cond`, and `RET`, from the traces of `tests/isla/tcg` and `tests/isla/kvm` under the
profiles `tcg` and `kvm` with the group `branch`, which leaves `TCR_EL1` undefined.  Each theorem
holds for every value of every field of its opcode, register 31 included, and every state.  The
two traces of a form differ, since the FEAT_PAuth of `kvm` adds the tests of TBID0 and TBID1, so
each form has a proof under each profile.  `tests/isla/theorems.sh` elaborates the module and
prints the axioms of its theorems.

`AArch64.BranchAddr` tests bit 55 of a branch's target and TBI0 or TBI1 of `TCR_EL1`, and under
`kvm` TBID0 or TBID1, and on some paths replaces the target's top byte, while `exec` sets the
program counter to the target.  Each theorem therefore assumes `Untagged` of `u.tcr`, the value of
`TCR_EL1`, and the target, which the rule `plain` of `BootStep` in `LeanExe/A64/Boot.lean`
requires of a step's next program counter.  A conditional branch assumes it only when it branches,
and `RET` assumes it of `Xn`, which is 0 for register 31.  The paths that replace the top byte
contradict the premise, and the other paths set the program counter to the target.

A branch writes `_PC` and sets `__BranchTaken`, which `finish` reads to keep the written program
counter.  Outside the model, a taken branch also writes `SEE` and `Branchtypetaken`, and `RET`
writes `BTypeNext`, so these registers with `__BranchTaken` form `W`.  A conditional branch that
is not taken writes only `SEE`, so its theorem's `σ'` depends on the condition.

The forward direction of each proof takes the hypothesis through the trace with `isla_fwd`.  The
backward direction gives `isla_bwd` the values of the variables that the trace declares before its
first `cases`: the last element of `FeatureImpl`, `TCR_EL1`, the program counter, and for `B.cond`
the flags.  At a `cases` whose condition the facts at hand do not decide, the walk of `isla_bwd`
evaluates both branches, each to its end or to its next `declare-const` of a free variable, into a
disjunction whose disjuncts open with complementary conditions, and `br_tree` splits it on the
condition.  In `CBZ`, `CBNZ`, and `RET`, the branch of a register other than 31 declares Isla's
values of `R0` to `R30`, which `isla_gprs` gives.  Each path ends in an equation of outcomes that
`jump_end`, `link_end`, `cond_end`, or `ret_end` proves, or refutes from the path's conditions and
the premise.  Every trace compares `FeatureImpl`, a vector of 259 Booleans, which recurses deeper
than the default limit, and the evaluation of each trace takes more than the default budget of
heartbeats.
-/

namespace TestSupport.A64.Isla

open LeanExe.A64 LeanExe.A64.Isla

/-- A branch to `a` under the translation control `tcr` sets the program counter to `a`: `a` lies
below 2^55, or TBI0 and TBI1, bits 37 and 38 of `tcr`, are clear.  `Sys.untagged` of
`LeanExe/A64/Boot.lean` states the second case for a value of `TCR_EL1` as
`tcr &&& 0x6000000000 == 0`. -/
def Untagged (tcr : BitVec 64) (a : UInt64) : Prop :=
  a.toNat < 2 ^ 55 ∨ tcr.toNat / 2 ^ 37 % 4 = 0

/-- The target of `B` and `BL` as the traces compute it: the program counter plus `imm * 4`, a
number of 28 bits sign-extended to 64. -/
theorem target26 (pc : UInt64) {imm : Nat} (h : imm < 67108864) :
    (pc + sext 26 imm * 4).toNat =
      (pc.toNat + (imm * 4 + imm * 4 / 134217728 * 18446744073441116160) %
        18446744073709551616) % 18446744073709551616 := by
  have := toNat_lt pc
  unfold sext
  split <;> simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_sub, UInt64.toNat_ofNat',
    UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceSub, Nat.reduceMod] at * <;> omega

/-- The target of `CBZ`, `CBNZ`, and `B.cond` as the traces compute it: the program counter plus
`imm * 4`, a number of 21 bits sign-extended to 64. -/
theorem target19 (pc : UInt64) {imm : Nat} (h : imm < 524288) :
    (pc + sext 19 imm * 4).toNat =
      (pc.toNat + (imm * 4 + imm * 4 / 1048576 * 18446744073707454464) %
        18446744073709551616) % 18446744073709551616 := by
  have := toNat_lt pc
  unfold sext
  split <;> simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_sub, UInt64.toNat_ofNat',
    UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceSub, Nat.reduceMod] at * <;> omega

/-- A number below 2^56 equals its AND with `0x00ffffffffffffff`, with which `AArch64.BranchAddr`
clears the top byte of a target whose bit 55 is clear. -/
theorem and_low {a : Nat} (h : a < 72057594037927936) : a &&& 72057594037927935 = a := by
  have e : (72057594037927935 : Nat) = 2 ^ 56 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt h

/-- A disjunction of two branches holds when each branch holds under its condition and the
conditions cover every case. -/
theorem or_cases {p q a b : Prop} (h : p ∨ q) (ha : p → a) (hb : q → b) : p ∧ a ∨ q ∧ b :=
  h.elim (fun hp => .inl ⟨hp, ha hp⟩) (fun hq => .inr ⟨hq, hb hq⟩)

/-- Splits the goals that `isla_bwd` leaves.  It evaluates the events of a path, splits a
disjunction whose disjuncts open with complementary conditions, a proposition and its negation or
a Boolean that is true and false, into one goal per disjunct with its condition as a hypothesis,
and splits conjunctions.  It leaves the conditions of reads and asserts, the `declare-const`
events of free variables, and the ends of paths. -/
syntax "br_tree " "using " tacticSeq " with " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| br_tree using $d with [$xs,*]) => `(tactic| repeat' (first
      | (rw [Trace.Run]; isla_simp [$xs,*])
      | refine or_cases (Classical.em _) (fun _ => ?_) (fun _ => ?_)
      | refine or_cases (Classical.em _).symm (fun _ => ?_) (fun _ => ?_)
      | refine or_cases (Bool.eq_false_or_eq_true _) (fun _ => ?_) (fun _ => ?_)
      | refine or_cases (Bool.eq_false_or_eq_true _).symm (fun _ => ?_) (fun _ => ?_)
      | (guard_target = And _ _; apply And.intro)
      | focus (rw [ite_eq_left]; rotate_left; ($d))))

/-- Refutes a path from its conditions and the premise on the top byte, or proves the equation
`UInt64.ofNat x = a` between the program counter that the path writes and `exec`'s as an
equation of natural numbers, rewriting with the lemmas in brackets and clearing the top byte of a
value below 2^56. -/
syntax "pc_close " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| pc_close [$xs,*]) => `(tactic| first
      | (exfalso; omega)
      | (apply UInt64.toNat_inj.mp
         simp (disch := omega) only [UInt64.toNat_ofNat', and_low, Nat.reducePow, toNat_mod,
           $xs,*] <;> omega))

/-- Proves that the outcome at the end of a path of `B` is `exec`'s. -/
syntax "jump_end " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| jump_end [$xs,*]) => `(tactic| (
      done_end
      simp only [State.mk.injEq, and_true, true_and]
      all_goals pc_close [$xs,*]))

/-- Proves that the outcome at the end of a path of `BL` is `exec`'s: the path writes the program
counter plus 4 to `R30` and the target to the program counter. -/
syntax "link_end " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| link_end [$xs,*]) => `(tactic| (
      done_end
      simp only [setX_eq (d := 30) (i := 30) rfl, State.mk.injEq, and_true, true_and]
      all_goals first
        | (exfalso; omega)
        | (refine ⟨?_, ?_⟩
           · funext j
             by_cases hj : j = 30 <;> simp only [hj, eq_self_iff_true, ↓reduceIte]
             apply UInt64.toNat_inj.mp
             simp only [UInt64.toNat_ofNat', UInt64.toNat_add, UInt64.toNat_ofNat,
               Nat.reducePow, Nat.reduceMod]
             omega
           · pc_close [$xs,*])))

/-- Proves that the outcome at the end of a path of a conditional branch is `exec`'s.  It splits
on the condition `c` of `exec`, names it `hk`, and in each case refutes the path with the tactic
after `using` or, when the branch is taken, applies the premise `ht` to `hk` and compares the
program counters. -/
syntax "cond_end " ident " : " term " ; " term " using " tacticSeq " with "
  "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| cond_end $hk : $c ; $ht using $contra with [$xs,*]) => `(tactic| (
      done_end
      by_cases $hk:ident : $c
      · simp only [ite_eq_left $hk:ident, State.mk.injEq, and_true, true_and]
        all_goals first
          | (exfalso; ($contra))
          | (have ht' := $ht $hk:ident
             pc_close [$xs,*])
      · simp only [ite_eq_right $hk:ident, State.mk.injEq, and_true, true_and]
        all_goals (exfalso; ($contra))))

/-- Refutes a path of `CBZ` or `CBNZ` whose test of `Xt` disagrees with `hk`, the condition of
`exec` on `s.x t`. -/
syntax "cb_contra " ident : tactic
macro_rules
  | `(tactic| cb_contra $hk) => `(tactic|
      (simp -failIfUnchanged (disch := omega) only [x_lt, x_31, ne_eq, ← UInt64.toNat_inj,
        UInt64.toNat_zero, not_true_eq_false] at $hk:ident) <;> omega)

/-- Proves that the outcome at the end of a path of `RET` is `exec`'s: it reads `Xn` in the premise
`ht` and in `exec`'s program counter as the register or, for register 31, as 0. -/
syntax "ret_end " ident : tactic
macro_rules
  | `(tactic| ret_end $ht) => `(tactic| (
      done_end
      simp only [State.mk.injEq, and_true, true_and]
      simp -failIfUnchanged (disch := omega) only [x_lt, x_31, UInt64.toNat_zero] at $ht:ident
      all_goals pc_close [x_lt, x_31, UInt64.toNat_zero]))

/-- Refutes a path of `B.cond` whose condition disagrees with `hk`, the value of
`State.condHolds s c`.  It replaces the flags of `s` and the value of `c` by variables, reverts the
hypotheses that mention the flags, among them the path's condition, which the trace computes from
the field and the flags as `-L ConditionHolds` linearizes it, and decides the statement over the
16 conditions and the 16 values of the flags.  The instance of `Decidable` for the statement
exceeds the default limit on the size of an instance. -/
syntax "cond_dec " term:max term:max ident : tactic
macro_rules
  | `(tactic| cond_dec $s $c $hk) => `(tactic| (
      unfold State.condHolds at $hk:ident
      generalize State.nFlag $s = n at *
      generalize State.zFlag $s = z at *
      generalize State.cFlag $s = cf at *
      generalize State.vFlag $s = v at *
      revert n z cf v
      have hlt := Fin.isLt $c
      generalize Fin.val $c = k at hlt ⊢
      revert k
      set_option synthInstance.maxSize 100000 in decide))

/-- Proves that registers `σ'` that depend on a condition, each case of which sets the registers of
the list `W` in `σ`, agree with `σ` outside `W`. -/
macro "frame_if" : tactic => `(tactic| (
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  split <;> simp only [Sys.set_apply, hr, ↓reduceIte]))

/-! B -/

/-- The footprint of `B` under the profile `tcg`. -/
def bTcg : Footprint := isla_trace% "tests/isla/tcg/b"

/-- The footprint of `B` under the profile `kvm`. -/
def bKvm : Footprint := isla_trace% "tests/isla/kvm/b"

/-- The fields of `B` and `BL` for the immediate `imm`. -/
def bFields (imm : Fin 67108864) : Fields := [("imm26", imm.val)]

/-- The opcode of `B` gives `B`'s encoding. -/
theorem b_word (imm : Fin 67108864) :
    Opcode.word [.bits 6 5, .field "imm26" 26] (bFields imm) = encodeNat (.b imm) := by
  simp only [Opcode.word, Opcode.wordFrom, bFields, encodeNat, List.lookup, String.reduceBEq,
    Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  all_goals omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The trace of `B` under `tcg` agrees with `exec` for every immediate and every state whose
target keeps its top byte. -/
theorem b_tcg (P : Platform) (u : Unknown) (imm : Fin 67108864) (s : State)
    (ht : Untagged u.tcr (s.pc + sext 26 imm.val * 4)) :
    Agrees P (tcg.sys .branch u) ["SEE", "Branchtypetaken", "__BranchTaken"] bTcg (bFields imm)
      (.b imm) s := by
  have hT := target26 s.pc imm.isLt
  have htcr := u.tcr.isLt
  simp only [Untagged, hT, Nat.reducePow] at ht htcr
  refine ⟨by decide, by decide, decode_word (b_word imm), fun σ hσ s' hs => ?_⟩
  simp only [exec, Option.some.injEq] at hs
  subst hs
  isla_reads [bTcg, Profile.sys_get, Profile.sys, tcg, sysreg, bv, eq_self_iff_true,
    List.map_cons, List.map_nil] at hσ
  refine ⟨(((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 67)).set
    "Branchtypetaken" (.enum "BranchType_DIR")).set "__BranchTaken" (.bool true),
    fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
  · unfold Footprint.Run at h
    simp only [bTcg, Footprint.vars, bFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD] at h
    isla_fwd h using omega with [hσ]
    all_goals jump_end [hT]
  · subst h
    unfold Footprint.Run
    simp only [bTcg, Footprint.vars, bFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD]
    isla_bwd [u.feature, u.tcr.toNat, s.pc.toNat] using omega with [hσ]
    br_tree using omega with [hσ]
    all_goals first
      | (apply Eq.symm; jump_end [hT])
      | exact toNat_lt _
      | omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The trace of `B` under `kvm` agrees with `exec` for every immediate and every state whose
target keeps its top byte. -/
theorem b_kvm (P : Platform) (u : Unknown) (imm : Fin 67108864) (s : State)
    (ht : Untagged u.tcr (s.pc + sext 26 imm.val * 4)) :
    Agrees P (kvm.sys .branch u) ["SEE", "Branchtypetaken", "__BranchTaken"] bKvm (bFields imm)
      (.b imm) s := by
  have hT := target26 s.pc imm.isLt
  have htcr := u.tcr.isLt
  simp only [Untagged, hT, Nat.reducePow] at ht htcr
  refine ⟨by decide, by decide, decode_word (b_word imm), fun σ hσ s' hs => ?_⟩
  simp only [exec, Option.some.injEq] at hs
  subst hs
  isla_reads [bKvm, Profile.sys_get, Profile.sys, kvm, sysreg, bv, eq_self_iff_true,
    List.map_cons, List.map_nil] at hσ
  refine ⟨(((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 67)).set
    "Branchtypetaken" (.enum "BranchType_DIR")).set "__BranchTaken" (.bool true),
    fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
  · unfold Footprint.Run at h
    simp only [bKvm, Footprint.vars, bFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD] at h
    isla_fwd h using omega with [hσ]
    all_goals jump_end [hT]
  · subst h
    unfold Footprint.Run
    simp only [bKvm, Footprint.vars, bFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD]
    isla_bwd [u.feature, u.tcr.toNat, s.pc.toNat] using omega with [hσ]
    br_tree using omega with [hσ]
    all_goals first
      | (apply Eq.symm; jump_end [hT])
      | exact toNat_lt _
      | omega

/-! BL -/

/-- The footprint of `BL` under the profile `tcg`. -/
def blTcg : Footprint := isla_trace% "tests/isla/tcg/bl"

/-- The footprint of `BL` under the profile `kvm`. -/
def blKvm : Footprint := isla_trace% "tests/isla/kvm/bl"

/-- The opcode of `BL` gives `BL`'s encoding. -/
theorem bl_word (imm : Fin 67108864) :
    Opcode.word [.bits 6 37, .field "imm26" 26] (bFields imm) = encodeNat (.bl imm) := by
  simp only [Opcode.word, Opcode.wordFrom, bFields, encodeNat, List.lookup, String.reduceBEq,
    Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  all_goals omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The trace of `BL` under `tcg` agrees with `exec` for every immediate and every state whose
target keeps its top byte: it writes the program counter plus 4 to `R30`. -/
theorem bl_tcg (P : Platform) (u : Unknown) (imm : Fin 67108864) (s : State)
    (ht : Untagged u.tcr (s.pc + sext 26 imm.val * 4)) :
    Agrees P (tcg.sys .branch u) ["SEE", "Branchtypetaken", "__BranchTaken"] blTcg (bFields imm)
      (.bl imm) s := by
  have hT := target26 s.pc imm.isLt
  have htcr := u.tcr.isLt
  simp only [Untagged, hT, Nat.reducePow] at ht htcr
  refine ⟨by decide, by decide, decode_word (bl_word imm), fun σ hσ s' hs => ?_⟩
  simp only [exec, Option.some.injEq] at hs
  subst hs
  isla_reads [blTcg, Profile.sys_get, Profile.sys, tcg, sysreg, bv, eq_self_iff_true,
    List.map_cons, List.map_nil] at hσ
  refine ⟨(((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 68)).set
    "Branchtypetaken" (.enum "BranchType_DIRCALL")).set "__BranchTaken" (.bool true),
    fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
  · unfold Footprint.Run at h
    simp only [blTcg, Footprint.vars, bFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD] at h
    isla_fwd h using omega with [hσ]
    all_goals link_end [hT]
  · subst h
    unfold Footprint.Run
    simp only [blTcg, Footprint.vars, bFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD]
    isla_bwd [u.feature, u.tcr.toNat, s.pc.toNat] using omega with [hσ]
    br_tree using omega with [hσ]
    all_goals first
      | (apply Eq.symm; link_end [hT])
      | exact toNat_lt _
      | omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The trace of `BL` under `kvm` agrees with `exec` for every immediate and every state whose
target keeps its top byte. -/
theorem bl_kvm (P : Platform) (u : Unknown) (imm : Fin 67108864) (s : State)
    (ht : Untagged u.tcr (s.pc + sext 26 imm.val * 4)) :
    Agrees P (kvm.sys .branch u) ["SEE", "Branchtypetaken", "__BranchTaken"] blKvm (bFields imm)
      (.bl imm) s := by
  have hT := target26 s.pc imm.isLt
  have htcr := u.tcr.isLt
  simp only [Untagged, hT, Nat.reducePow] at ht htcr
  refine ⟨by decide, by decide, decode_word (bl_word imm), fun σ hσ s' hs => ?_⟩
  simp only [exec, Option.some.injEq] at hs
  subst hs
  isla_reads [blKvm, Profile.sys_get, Profile.sys, kvm, sysreg, bv, eq_self_iff_true,
    List.map_cons, List.map_nil] at hσ
  refine ⟨(((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 68)).set
    "Branchtypetaken" (.enum "BranchType_DIRCALL")).set "__BranchTaken" (.bool true),
    fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
  · unfold Footprint.Run at h
    simp only [blKvm, Footprint.vars, bFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD] at h
    isla_fwd h using omega with [hσ]
    all_goals link_end [hT]
  · subst h
    unfold Footprint.Run
    simp only [blKvm, Footprint.vars, bFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD]
    isla_bwd [u.feature, u.tcr.toNat, s.pc.toNat] using omega with [hσ]
    br_tree using omega with [hσ]
    all_goals first
      | (apply Eq.symm; link_end [hT])
      | exact toNat_lt _
      | omega

/-! CBZ and CBNZ -/

/-- The footprint of `CBZ` under the profile `tcg`. -/
def cbzTcg : Footprint := isla_trace% "tests/isla/tcg/cbz"

/-- The footprint of `CBZ` under the profile `kvm`. -/
def cbzKvm : Footprint := isla_trace% "tests/isla/kvm/cbz"

/-- The footprint of `CBNZ` under the profile `tcg`. -/
def cbnzTcg : Footprint := isla_trace% "tests/isla/tcg/cbnz"

/-- The footprint of `CBNZ` under the profile `kvm`. -/
def cbnzKvm : Footprint := isla_trace% "tests/isla/kvm/cbnz"

/-- The fields of `CBZ` and `CBNZ` for the register `t` and the immediate `imm`. -/
def cbFields (t : Fin 32) (imm : Fin 524288) : Fields := [("imm19", imm.val), ("Rt", t.val)]

/-- The opcode of `CBZ` gives `CBZ`'s encoding. -/
theorem cbz_word (t : Fin 32) (imm : Fin 524288) :
    Opcode.word [.bits 8 180, .field "imm19" 19, .field "Rt" 5] (cbFields t imm) =
      encodeNat (.cbz t imm) := by
  simp only [Opcode.word, Opcode.wordFrom, cbFields, encodeNat, List.lookup, String.reduceBEq,
    Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  all_goals omega

/-- The opcode of `CBNZ` gives `CBNZ`'s encoding. -/
theorem cbnz_word (t : Fin 32) (imm : Fin 524288) :
    Opcode.word [.bits 8 181, .field "imm19" 19, .field "Rt" 5] (cbFields t imm) =
      encodeNat (.cbnz t imm) := by
  simp only [Opcode.word, Opcode.wordFrom, cbFields, encodeNat, List.lookup, String.reduceBEq,
    Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  all_goals omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The trace of `CBZ` under `tcg` agrees with `exec` for every register number, with register
31 the zero register, every immediate, and every state whose target keeps its top byte when the
branch is taken.  Isla reads `Xt` from the vector of `R0` to `R30` for a register other than 31. -/
theorem cbz_tcg (P : Platform) (u : Unknown) (t : Fin 32) (imm : Fin 524288) (s : State)
    (ht : s.x t = 0 → Untagged u.tcr (s.pc + sext 19 imm.val * 4)) :
    Agrees P (tcg.sys .branch u) ["SEE", "Branchtypetaken", "__BranchTaken"] cbzTcg
      (cbFields t imm) (.cbz t imm) s := by
  have hT := target19 s.pc imm.isLt
  have htcr := u.tcr.isLt
  have := t.isLt
  simp only [Untagged, hT, Nat.reducePow] at ht htcr
  refine ⟨by decide, by decide, decode_word (cbz_word t imm), fun σ hσ s' hs => ?_⟩
  simp only [exec, Option.some.injEq] at hs
  subst hs
  isla_reads [cbzTcg, Profile.sys_get, Profile.sys, tcg, sysreg, bv, eq_self_iff_true,
    List.map_cons, List.map_nil] at hσ
  refine ⟨if s.x t = 0 then
      (((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 118)).set
        "Branchtypetaken" (.enum "BranchType_DIR")).set "__BranchTaken" (.bool true)
    else (σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 118),
    fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_if⟩
  · unfold Footprint.Run at h
    simp only [cbzTcg, Footprint.vars, cbFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD] at h
    isla_fwd h using omega with [hσ]
    all_goals cond_end hk : s.x t = 0 ; ht using cb_contra hk with [hT]
  · subst h
    unfold Footprint.Run
    simp only [cbzTcg, Footprint.vars, cbFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD]
    isla_bwd [u.feature, u.tcr.toNat, s.pc.toNat] using omega with [hσ]
    br_tree using omega with [hσ]
    all_goals try (guard_target = Exists _
                   isla_gprs s using omega with [hσ]
                   all_goals try isla_simp [hσ])
    br_tree using omega with [hσ]
    all_goals first
      | (apply Eq.symm; cond_end hk : s.x t = 0 ; ht using cb_contra hk with [hT])
      | exact toNat_lt _
      | (simp only [sint]; omega)
      | omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The trace of `CBZ` under `kvm` agrees with `exec` for every register number, every
immediate, and every state whose target keeps its top byte when the branch is taken. -/
theorem cbz_kvm (P : Platform) (u : Unknown) (t : Fin 32) (imm : Fin 524288) (s : State)
    (ht : s.x t = 0 → Untagged u.tcr (s.pc + sext 19 imm.val * 4)) :
    Agrees P (kvm.sys .branch u) ["SEE", "Branchtypetaken", "__BranchTaken"] cbzKvm
      (cbFields t imm) (.cbz t imm) s := by
  have hT := target19 s.pc imm.isLt
  have htcr := u.tcr.isLt
  have := t.isLt
  simp only [Untagged, hT, Nat.reducePow] at ht htcr
  refine ⟨by decide, by decide, decode_word (cbz_word t imm), fun σ hσ s' hs => ?_⟩
  simp only [exec, Option.some.injEq] at hs
  subst hs
  isla_reads [cbzKvm, Profile.sys_get, Profile.sys, kvm, sysreg, bv, eq_self_iff_true,
    List.map_cons, List.map_nil] at hσ
  refine ⟨if s.x t = 0 then
      (((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 118)).set
        "Branchtypetaken" (.enum "BranchType_DIR")).set "__BranchTaken" (.bool true)
    else (σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 118),
    fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_if⟩
  · unfold Footprint.Run at h
    simp only [cbzKvm, Footprint.vars, cbFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD] at h
    isla_fwd h using omega with [hσ]
    all_goals cond_end hk : s.x t = 0 ; ht using cb_contra hk with [hT]
  · subst h
    unfold Footprint.Run
    simp only [cbzKvm, Footprint.vars, cbFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD]
    isla_bwd [u.feature, u.tcr.toNat, s.pc.toNat] using omega with [hσ]
    br_tree using omega with [hσ]
    all_goals try (guard_target = Exists _
                   isla_gprs s using omega with [hσ]
                   all_goals try isla_simp [hσ])
    br_tree using omega with [hσ]
    all_goals first
      | (apply Eq.symm; cond_end hk : s.x t = 0 ; ht using cb_contra hk with [hT])
      | exact toNat_lt _
      | (simp only [sint]; omega)
      | omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The trace of `CBNZ` under `tcg` agrees with `exec` for every register number, with register
31 the zero register, every immediate, and every state whose target keeps its top byte when the
branch is taken. -/
theorem cbnz_tcg (P : Platform) (u : Unknown) (t : Fin 32) (imm : Fin 524288) (s : State)
    (ht : s.x t ≠ 0 → Untagged u.tcr (s.pc + sext 19 imm.val * 4)) :
    Agrees P (tcg.sys .branch u) ["SEE", "Branchtypetaken", "__BranchTaken"] cbnzTcg
      (cbFields t imm) (.cbnz t imm) s := by
  have hT := target19 s.pc imm.isLt
  have htcr := u.tcr.isLt
  have := t.isLt
  simp only [Untagged, hT, Nat.reducePow] at ht htcr
  refine ⟨by decide, by decide, decode_word (cbnz_word t imm), fun σ hσ s' hs => ?_⟩
  simp only [exec, Option.some.injEq] at hs
  subst hs
  isla_reads [cbnzTcg, Profile.sys_get, Profile.sys, tcg, sysreg, bv, eq_self_iff_true,
    List.map_cons, List.map_nil] at hσ
  refine ⟨if s.x t ≠ 0 then
      (((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 117)).set
        "Branchtypetaken" (.enum "BranchType_DIR")).set "__BranchTaken" (.bool true)
    else (σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 117),
    fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_if⟩
  · unfold Footprint.Run at h
    simp only [cbnzTcg, Footprint.vars, cbFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD] at h
    isla_fwd h using omega with [hσ]
    all_goals cond_end hk : s.x t ≠ 0 ; ht using cb_contra hk with [hT]
  · subst h
    unfold Footprint.Run
    simp only [cbnzTcg, Footprint.vars, cbFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD]
    isla_bwd [u.feature, u.tcr.toNat, s.pc.toNat] using omega with [hσ]
    br_tree using omega with [hσ]
    all_goals try (guard_target = Exists _
                   isla_gprs s using omega with [hσ]
                   all_goals try isla_simp [hσ])
    br_tree using omega with [hσ]
    all_goals first
      | (apply Eq.symm; cond_end hk : s.x t ≠ 0 ; ht using cb_contra hk with [hT])
      | exact toNat_lt _
      | (simp only [sint]; omega)
      | omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The trace of `CBNZ` under `kvm` agrees with `exec` for every register number, every
immediate, and every state whose target keeps its top byte when the branch is taken. -/
theorem cbnz_kvm (P : Platform) (u : Unknown) (t : Fin 32) (imm : Fin 524288) (s : State)
    (ht : s.x t ≠ 0 → Untagged u.tcr (s.pc + sext 19 imm.val * 4)) :
    Agrees P (kvm.sys .branch u) ["SEE", "Branchtypetaken", "__BranchTaken"] cbnzKvm
      (cbFields t imm) (.cbnz t imm) s := by
  have hT := target19 s.pc imm.isLt
  have htcr := u.tcr.isLt
  have := t.isLt
  simp only [Untagged, hT, Nat.reducePow] at ht htcr
  refine ⟨by decide, by decide, decode_word (cbnz_word t imm), fun σ hσ s' hs => ?_⟩
  simp only [exec, Option.some.injEq] at hs
  subst hs
  isla_reads [cbnzKvm, Profile.sys_get, Profile.sys, kvm, sysreg, bv, eq_self_iff_true,
    List.map_cons, List.map_nil] at hσ
  refine ⟨if s.x t ≠ 0 then
      (((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 117)).set
        "Branchtypetaken" (.enum "BranchType_DIR")).set "__BranchTaken" (.bool true)
    else (σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 117),
    fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_if⟩
  · unfold Footprint.Run at h
    simp only [cbnzKvm, Footprint.vars, cbFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD] at h
    isla_fwd h using omega with [hσ]
    all_goals cond_end hk : s.x t ≠ 0 ; ht using cb_contra hk with [hT]
  · subst h
    unfold Footprint.Run
    simp only [cbnzKvm, Footprint.vars, cbFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD]
    isla_bwd [u.feature, u.tcr.toNat, s.pc.toNat] using omega with [hσ]
    br_tree using omega with [hσ]
    all_goals try (guard_target = Exists _
                   isla_gprs s using omega with [hσ]
                   all_goals try isla_simp [hσ])
    br_tree using omega with [hσ]
    all_goals first
      | (apply Eq.symm; cond_end hk : s.x t ≠ 0 ; ht using cb_contra hk with [hT])
      | exact toNat_lt _
      | (simp only [sint]; omega)
      | omega

/-! B.cond -/

/-- The footprint of `B.cond` under the profile `tcg`. -/
def bcondTcg : Footprint := isla_trace% "tests/isla/tcg/b-cond"

/-- The footprint of `B.cond` under the profile `kvm`. -/
def bcondKvm : Footprint := isla_trace% "tests/isla/kvm/b-cond"

/-- The fields of `B.cond` for the condition `cond` and the immediate `imm`. -/
def bcondFields (cond : Fin 16) (imm : Fin 524288) : Fields :=
  [("imm19", imm.val), ("cond", cond.val)]

/-- The opcode of `B.cond` gives `B.cond`'s encoding. -/
theorem bcond_word (cond : Fin 16) (imm : Fin 524288) :
    Opcode.word [.bits 8 84, .field "imm19" 19, .bits 1 0, .field "cond" 4]
      (bcondFields cond imm) = encodeNat (.bcond cond imm) := by
  simp only [Opcode.word, Opcode.wordFrom, bcondFields, encodeNat, List.lookup, String.reduceBEq,
    Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  all_goals omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The trace of `B.cond` under `tcg` agrees with `exec` for every condition, every immediate, and
every state whose target keeps its top byte when the condition holds.  The trace reads the four
flags and computes the condition from them and the field `cond`, and `cond_dec` compares it with
`State.condHolds`. -/
theorem bcond_tcg (P : Platform) (u : Unknown) (cond : Fin 16) (imm : Fin 524288) (s : State)
    (ht : s.condHolds cond = true → Untagged u.tcr (s.pc + sext 19 imm.val * 4)) :
    Agrees P (tcg.sys .branch u) ["SEE", "Branchtypetaken", "__BranchTaken"] bcondTcg
      (bcondFields cond imm) (.bcond cond imm) s := by
  have hT := target19 s.pc imm.isLt
  have htcr := u.tcr.isLt
  simp only [Untagged, hT, Nat.reducePow] at ht htcr
  refine ⟨by decide, by decide, decode_word (bcond_word cond imm), fun σ hσ s' hs => ?_⟩
  simp only [exec, Option.some.injEq] at hs
  subst hs
  isla_reads [bcondTcg, Profile.sys_get, Profile.sys, tcg, sysreg, bv, eq_self_iff_true,
    List.map_cons, List.map_nil] at hσ
  refine ⟨if s.condHolds cond = true then
      (((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 69)).set
        "Branchtypetaken" (.enum "BranchType_DIR")).set "__BranchTaken" (.bool true)
    else (σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 69),
    fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_if⟩
  · unfold Footprint.Run at h
    simp only [bcondTcg, Footprint.vars, bcondFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD] at h
    isla_fwd h using omega with [hσ]
    all_goals cond_end hk : s.condHolds cond = true ; ht using cond_dec s cond hk with [hT]
  · subst h
    unfold Footprint.Run
    simp only [bcondTcg, Footprint.vars, bcondFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD]
    isla_bwd [u.feature, (if s.zFlag then 1 else 0), (if s.cFlag then 1 else 0),
      (if s.nFlag then 1 else 0), (if s.vFlag then 1 else 0), u.tcr.toNat, s.pc.toNat]
      using omega with [hσ]
    br_tree using omega with [hσ]
    all_goals first
      | (apply Eq.symm
         cond_end hk : s.condHolds cond = true ; ht using cond_dec s cond hk with [hT])
      | exact toNat_lt _
      | (split <;> omega)
      | omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The trace of `B.cond` under `kvm` agrees with `exec` for every condition, every immediate, and
every state whose target keeps its top byte when the condition holds. -/
theorem bcond_kvm (P : Platform) (u : Unknown) (cond : Fin 16) (imm : Fin 524288) (s : State)
    (ht : s.condHolds cond = true → Untagged u.tcr (s.pc + sext 19 imm.val * 4)) :
    Agrees P (kvm.sys .branch u) ["SEE", "Branchtypetaken", "__BranchTaken"] bcondKvm
      (bcondFields cond imm) (.bcond cond imm) s := by
  have hT := target19 s.pc imm.isLt
  have htcr := u.tcr.isLt
  simp only [Untagged, hT, Nat.reducePow] at ht htcr
  refine ⟨by decide, by decide, decode_word (bcond_word cond imm), fun σ hσ s' hs => ?_⟩
  simp only [exec, Option.some.injEq] at hs
  subst hs
  isla_reads [bcondKvm, Profile.sys_get, Profile.sys, kvm, sysreg, bv, eq_self_iff_true,
    List.map_cons, List.map_nil] at hσ
  refine ⟨if s.condHolds cond = true then
      (((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 69)).set
        "Branchtypetaken" (.enum "BranchType_DIR")).set "__BranchTaken" (.bool true)
    else (σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 69),
    fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_if⟩
  · unfold Footprint.Run at h
    simp only [bcondKvm, Footprint.vars, bcondFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD] at h
    isla_fwd h using omega with [hσ]
    all_goals cond_end hk : s.condHolds cond = true ; ht using cond_dec s cond hk with [hT]
  · subst h
    unfold Footprint.Run
    simp only [bcondKvm, Footprint.vars, bcondFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD]
    isla_bwd [u.feature, (if s.zFlag then 1 else 0), (if s.cFlag then 1 else 0),
      (if s.nFlag then 1 else 0), (if s.vFlag then 1 else 0), u.tcr.toNat, s.pc.toNat]
      using omega with [hσ]
    br_tree using omega with [hσ]
    all_goals first
      | (apply Eq.symm
         cond_end hk : s.condHolds cond = true ; ht using cond_dec s cond hk with [hT])
      | exact toNat_lt _
      | (split <;> omega)
      | omega

/-! RET -/

/-- The footprint of `RET` under the profile `tcg`. -/
def retTcg : Footprint := isla_trace% "tests/isla/tcg/ret"

/-- The footprint of `RET` under the profile `kvm`. -/
def retKvm : Footprint := isla_trace% "tests/isla/kvm/ret"

/-- The fields of `RET` for the register `n`. -/
def retFields (n : Fin 32) : Fields := [("Rn", n.val)]

/-- The opcode of `RET` gives `RET`'s encoding. -/
theorem ret_word (n : Fin 32) :
    Opcode.word [.bits 22 3512256, .field "Rn" 5, .bits 5 0] (retFields n) =
      encodeNat (.ret n) := by
  simp only [Opcode.word, Opcode.wordFrom, retFields, encodeNat, List.lookup, String.reduceBEq,
    Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  all_goals omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The trace of `RET` under `tcg` agrees with `exec` for every register number, with register 31
the zero register, and every state whose target `Xn` keeps its top byte.  Every path writes 0 to
`BTypeNext`. -/
theorem ret_tcg (P : Platform) (u : Unknown) (n : Fin 32) (s : State)
    (ht : Untagged u.tcr (s.x n)) :
    Agrees P (tcg.sys .branch u) ["SEE", "BTypeNext", "Branchtypetaken", "__BranchTaken"] retTcg
      (retFields n) (.ret n) s := by
  have htcr := u.tcr.isLt
  have := n.isLt
  simp only [Untagged, Nat.reducePow] at ht htcr
  refine ⟨by decide, by decide, decode_word (ret_word n), fun σ hσ s' hs => ?_⟩
  simp only [exec, Option.some.injEq] at hs
  subst hs
  isla_reads [retTcg, Profile.sys_get, Profile.sys, tcg, sysreg, bv, eq_self_iff_true,
    List.map_cons, List.map_nil] at hσ
  refine ⟨((((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 94)).set
    "BTypeNext" (.bits 2 0)).set "Branchtypetaken" (.enum "BranchType_RET")).set "__BranchTaken"
    (.bool true), fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
  · unfold Footprint.Run at h
    simp only [retTcg, Footprint.vars, retFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD] at h
    isla_fwd h using omega with [hσ]
    all_goals ret_end ht
  · subst h
    unfold Footprint.Run
    simp only [retTcg, Footprint.vars, retFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD]
    isla_bwd [u.feature, u.tcr.toNat, s.pc.toNat] using omega with [hσ]
    br_tree using omega with [hσ]
    all_goals try (guard_target = Exists _
                   isla_gprs s using omega with [hσ]
                   all_goals try isla_simp [hσ])
    br_tree using omega with [hσ]
    all_goals first
      | (apply Eq.symm; ret_end ht)
      | exact toNat_lt _
      | (simp only [sint]; omega)
      | omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The trace of `RET` under `kvm` agrees with `exec` for every register number and every state
whose target `Xn` keeps its top byte. -/
theorem ret_kvm (P : Platform) (u : Unknown) (n : Fin 32) (s : State)
    (ht : Untagged u.tcr (s.x n)) :
    Agrees P (kvm.sys .branch u) ["SEE", "BTypeNext", "Branchtypetaken", "__BranchTaken"] retKvm
      (retFields n) (.ret n) s := by
  have htcr := u.tcr.isLt
  have := n.isLt
  simp only [Untagged, Nat.reducePow] at ht htcr
  refine ⟨by decide, by decide, decode_word (ret_word n), fun σ hσ s' hs => ?_⟩
  simp only [exec, Option.some.injEq] at hs
  subst hs
  isla_reads [retKvm, Profile.sys_get, Profile.sys, kvm, sysreg, bv, eq_self_iff_true,
    List.map_cons, List.map_nil] at hσ
  refine ⟨((((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 94)).set
    "BTypeNext" (.bits 2 0)).set "Branchtypetaken" (.enum "BranchType_RET")).set "__BranchTaken"
    (.bool true), fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
  · unfold Footprint.Run at h
    simp only [retKvm, Footprint.vars, retFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD] at h
    isla_fwd h using omega with [hσ]
    all_goals ret_end ht
  · subst h
    unfold Footprint.Run
    simp only [retKvm, Footprint.vars, retFields, List.foldl, List.lookup, String.reduceBEq,
      Option.getD]
    isla_bwd [u.feature, u.tcr.toNat, s.pc.toNat] using omega with [hσ]
    br_tree using omega with [hσ]
    all_goals try (guard_target = Exists _
                   isla_gprs s using omega with [hσ]
                   all_goals try isla_simp [hσ])
    br_tree using omega with [hσ]
    all_goals first
      | (apply Eq.symm; ret_end ht)
      | exact toNat_lt _
      | (simp only [sint]; omega)
      | omega

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.b_tcg
#print axioms TestSupport.A64.Isla.b_kvm
#print axioms TestSupport.A64.Isla.bl_tcg
#print axioms TestSupport.A64.Isla.bl_kvm
#print axioms TestSupport.A64.Isla.cbz_tcg
#print axioms TestSupport.A64.Isla.cbz_kvm
#print axioms TestSupport.A64.Isla.cbnz_tcg
#print axioms TestSupport.A64.Isla.cbnz_kvm
#print axioms TestSupport.A64.Isla.bcond_tcg
#print axioms TestSupport.A64.Isla.bcond_kvm
#print axioms TestSupport.A64.Isla.ret_tcg
#print axioms TestSupport.A64.Isla.ret_kvm
