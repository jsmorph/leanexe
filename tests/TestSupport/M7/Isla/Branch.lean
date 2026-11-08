import LeanExe.M7.Isla.Walk

/-!
Theorems of `Agrees` for the branches of `LeanExe/M7/Machine.lean`: `B.W` (T4), `B<cond>.W` (T3),
`BL`, and `BX LR`, from the traces of `tests/isla/m7` under the profile `sys` of
`LeanExe/M7/Isla/Profile.lean`.  Each theorem holds for every value of the offset's fields, every
platform, and every sequence of device values, and the theorem of `B<cond>.W` holds for every
condition from EQ to LE.  `tests/isla/m7-theorems.sh` elaborates the module and prints the axioms
of its theorems.

A taken branch writes `_PC` and sets `__BranchTaken`, so the program counter does not advance at
the end of the path, and the theorems of `B.W`, `BL`, and `BX LR` need no premise on its bound.
The theorem of `B<cond>.W` takes the program counter plus 4 below 2^32 for the path that does not
branch.  The traces clear bit 0 of the target, as `BranchWritePC` of DDI 0403E.e A2.3.1 does, and
`exec` adds the offset to the program counter unmasked, so the theorems of `B.W` and `BL` take an
even program counter, and the theorem of `B<cond>.W` takes one when the condition holds, which the
generator's code keeps.  The traces write `Branchtypetaken`, and those of `BL` and `BX LR` write
`PSTATE.T` with 1, so these registers join the registers that `σ'` may change.

The opcodes of `B.W`, `B<cond>.W`, and `BL` match the patterns of earlier decode clauses, whose
tests on bits of `imm10`, or of the condition and `imm6`, fork the trace, and every fork leads back
to the branch's own clause.  The forward direction takes every path, and the backward direction
chooses the path of the opcode by cases on those tests.  The trace of `B<cond>.W` evaluates
`ConditionHolds` on the condition's bits and the flags of `PSTATE`, and `cond_cases` proves each
fact of a path on them by cases on the condition and the flags.  `BX LR` forks on bit 0 of LR: the
path with bit 0 set writes `PSTATE.T` with 1 and branches to LR with bit 0 clear, and the paths with
bit 0 clear write `PSTATE.T` with 0, the A32 state, and take a CONSTRAINED UNPREDICTABLE choice on
bit 1.  `exec` stops when bit 0 is clear, so the theorem of `BX LR` holds for every machine and
states the first path, and the others need no counterpart.

The theorems of the branches with an offset name the offset's number `b` and the target's number
`v`, and the walk rewrites the trace's computations of them to the names with the equations `hoff`
and `htgt`, which `Opaque` hides from `omega`.  With the terms in place of the names, the kernel's
check of the walk's steps evaluates products with large powers of 2 from the offset and from
`Mach.x`, and the job runs out of memory.
-/

namespace TestSupport.M7.Isla

open LeanExe.M7 LeanExe.M7.Isla
open LeanExe.A64.Isla (Footprint Fields Opcode Val Sys acc upd Opaque)

/-- The footprint of `B.W` (T4). -/
def bT : Footprint := isla_trace% "tests/isla/m7/b"

/-- The footprint of `BL`. -/
def blT : Footprint := isla_trace% "tests/isla/m7/bl"

/-- The footprint of `B<cond>.W` (T3). -/
def bcondT : Footprint := isla_trace% "tests/isla/m7/b-cond"

/-- The footprint of `BX LR`. -/
def bxLrT : Footprint := isla_trace% "tests/isla/m7/bx-lr"

/-- The fields of `B.W` and `BL`. -/
def branchFields (s j1 j2 : Fin 2) (imm10 : Fin 1024) (imm11 : Fin 2048) : Fields :=
  [("S", s.val), ("imm10", imm10.val), ("J1", j1.val), ("J2", j2.val), ("imm11", imm11.val)]

/-- The fields of `B<cond>.W`. -/
def bcondFields (cond : Fin 14) (s j1 j2 : Fin 2) (imm6 : Fin 64) (imm11 : Fin 2048) : Fields :=
  [("S", s.val), ("cond", cond.val), ("imm6", imm6.val), ("J1", j1.val), ("J2", j2.val),
    ("imm11", imm11.val)]

/-! The target and the link value. -/

theorem xor_bit {a b : Nat} (ha : a < 2) (hb : b < 2) : a ^^^ b = (a + b) % 2 := by
  rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> first | rfl | omega

/-- The mask that clears bit 0 of a 32-bit target. -/
theorem and_fffffffe (x : Nat) : x &&& 4294967294 = x % 4294967296 / 2 * 2 := by
  rw [show (4294967294 : Nat) = (2 ^ 31 - 1) * 2 ^ 1 from rfl,
    LeanExe.A64.Isla.and_mul_two_pow, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem or_one (x : Nat) : x ||| 1 = x / 2 * 2 + 1 := by
  have h := Nat.two_pow_add_eq_or_of_lt (i := 1) (b := 1) (by decide) (x / 2)
  have hx : x ||| 1 = 2 ^ 1 * (x / 2) ||| 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or, Nat.testBit_or]
    rcases i with _ | i
    · simp only [Nat.testBit_zero, Nat.one_mod, decide_true, Bool.or_true]
    · rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
        show 2 ^ 1 * (x / 2) / 2 = x / 2 by omega, show (1 : Nat) / 2 = 0 from rfl]
  rw [hx, ← h]
  omega

/-- The offset of `B.W` and `BL` as a natural number below 2^25. -/
def offsetNat (s j1 j2 : Fin 2) (imm10 : Fin 1024) (imm11 : Fin 2048) : Nat :=
  s.val * 16777216 + (1 - (j1.val + s.val) % 2) * 8388608 + (1 - (j2.val + s.val) % 2) * 4194304 +
    imm10.val * 4096 + imm11.val * 2

theorem toNat_sext25 {v : Nat} (hv : v < 33554432) :
    (sext 25 v).toNat = v + v / 16777216 * 4261412864 := by
  unfold sext
  split
  · rename_i h
    have h' : v < 16777216 := h
    rw [UInt32.toNat_ofNat', show (2 : Nat) ^ 32 = 4294967296 from rfl]
    omega
  · rename_i h
    have h' : ¬ v < 16777216 := h
    rw [UInt32.toNat_sub, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
      show (2 : Nat) ^ 32 = 4294967296 from rfl, show (2 : Nat) ^ 25 = 33554432 from rfl]
    omega

theorem toNat_branchOffset (s j1 j2 : Fin 2) (imm10 : Fin 1024) (imm11 : Fin 2048) :
    (branchOffset s j1 j2 imm10 imm11).toNat =
      offsetNat s j1 j2 imm10 imm11 + offsetNat s j1 j2 imm10 imm11 / 16777216 * 4261412864 := by
  have hv : offsetNat s j1 j2 imm10 imm11 < 33554432 := by
    unfold offsetNat
    omega
  exact toNat_sext25 hv

/-- The target of a branch as the traces compute it, from an even program counter and an even
offset: the 32-bit sum of the program counter plus 4 and the offset, with bit 0 cleared. -/
theorem target_eq {pc d : UInt32} (hpc : pc.toNat % 2 = 0) (hd : d.toNat % 2 = 0) :
    ((pc.toNat % 4294967296 + 4) % 4294967296 + d.toNat) % 4294967296 / 2 * 2 =
      (pc + 4 + d).toNat := by
  have hp := pc.toNat_lt
  have hq := d.toNat_lt
  rw [UInt32.toNat_add, UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl,
    show (2 : Nat) ^ 32 = 4294967296 from rfl]
  omega

/-- The offset's bits as the traces concatenate them, `I1` and `I2` from exclusive ORs. -/
theorem offset_bits (s j1 j2 : Fin 2) (imm10 : Fin 1024) (imm11 : Fin 2048) :
    ((((s.val * 2 + (1 - (j1.val ^^^ s.val))) * 2 + (1 - (j2.val ^^^ s.val))) * 1024 + imm10.val) *
      2048 + imm11.val) * 2 = offsetNat s j1 j2 imm10 imm11 := by
  rw [xor_bit j1.isLt s.isLt, xor_bit j2.isLt s.isLt]
  unfold offsetNat
  omega

/-- The offset of `B.W` and `BL` as the traces sign-extend it from 25 bits. -/
theorem offset_eq (s j1 j2 : Fin 2) (imm10 : Fin 1024) (imm11 : Fin 2048) :
    ((((s.val * 2 + (1 - (j1.val ^^^ s.val))) * 2 + (1 - (j2.val ^^^ s.val))) * 1024 + imm10.val) *
        2048 + imm11.val) * 2 +
      ((((s.val * 2 + (1 - (j1.val ^^^ s.val))) * 2 + (1 - (j2.val ^^^ s.val))) * 1024 +
        imm10.val) * 2048 + imm11.val) * 2 / 16777216 * 4261412864 =
      (branchOffset s j1 j2 imm10 imm11).toNat := by
  rw [toNat_branchOffset, offset_bits]

theorem offset_even (s j1 j2 : Fin 2) (imm10 : Fin 1024) (imm11 : Fin 2048) :
    (branchOffset s j1 j2 imm10 imm11).toNat % 2 = 0 := by
  rw [toNat_branchOffset]
  unfold offsetNat
  omega

theorem toNat_sext21 {v : Nat} (hv : v < 2097152) :
    (sext 21 v).toNat = v + v / 1048576 * 4292870144 := by
  unfold sext
  split
  · rename_i h
    have h' : v < 1048576 := h
    rw [UInt32.toNat_ofNat', show (2 : Nat) ^ 32 = 4294967296 from rfl]
    omega
  · rename_i h
    have h' : ¬ v < 1048576 := h
    rw [UInt32.toNat_sub, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
      show (2 : Nat) ^ 32 = 4294967296 from rfl, show (2 : Nat) ^ 21 = 2097152 from rfl]
    omega

/-- The offset of `B<cond>.W` as the trace concatenates and sign-extends it from 21 bits. -/
theorem offset21_eq (s j1 j2 : Fin 2) (imm6 : Fin 64) (imm11 : Fin 2048) :
    ((((s.val * 2 + j2.val) * 2 + j1.val) * 64 + imm6.val) * 2048 + imm11.val) * 2 +
      ((((s.val * 2 + j2.val) * 2 + j1.val) * 64 + imm6.val) * 2048 + imm11.val) * 2 / 1048576 *
        4292870144 = (bcondOffset s j1 j2 imm6 imm11).toNat := by
  have hs := s.isLt
  have h1 := j1.isLt
  have h2 := j2.isLt
  have h6 := imm6.isLt
  have h11 := imm11.isLt
  unfold bcondOffset
  rw [toNat_sext21 (v := s.val * 1048576 + j2.val * 524288 + j1.val * 262144 + imm6.val * 4096 +
    imm11.val * 2) (by omega)]
  omega

theorem offset21_even (s j1 j2 : Fin 2) (imm6 : Fin 64) (imm11 : Fin 2048) :
    (bcondOffset s j1 j2 imm6 imm11).toNat % 2 = 0 := by
  rw [← offset21_eq]
  omega

theorem toNat_fffffffe : (0xFFFFFFFE : UInt32).toNat = 4294967294 := rfl

/-- The low word of X14 is LR. -/
theorem low_lr (s : State) : low s 14 = s.lr := by
  unfold low
  simp only [Nat.reduceLT, ↓reduceDIte, Nat.reduceEqDiff, ↓reduceIte]

/-! The condition of `B<cond>.W`. -/

open Lean Meta Elab Tactic in
/-- Reverts every hypothesis that names a flag of the model's state, such as the facts of a path
of `B<cond>.W` on its linearized `ConditionHolds`. -/
elab "revert_flags" : tactic => withMainContext do
  let flags := [``State.nFlag, ``State.zFlag, ``State.cFlag, ``State.vFlag, ``State.condHolds]
  let mut fs := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if !(← isProp d.type) then continue
    let t ← instantiateMVars d.type
    if flags.any (fun c => (t.find? (·.isConstOf c)).isSome) then fs := fs.push d.fvarId
  let g ← getMainGoal
  let (_, g') ← g.revert fs
  replaceMainGoal [g']

open Lean Meta Elab Tactic in
/-- Succeeds when the goal names a flag of the model's state, so that `cond_cases` applies only to
the conditions of `B<cond>.W` and fails at once on the decode's. -/
elab "guard_flags" : tactic => withMainContext do
  let flags := [``State.nFlag, ``State.zFlag, ``State.cFlag, ``State.vFlag, ``State.condHolds]
  let t ← instantiateMVars (← getMainTarget)
  unless flags.any (fun c => (t.find? (·.isConstOf c)).isSome) do
    throwError "guard_flags: the goal names no flag"

/-- Proves a goal about the condition `c`, the flags of the machine `m`, and facts of the path on
them, by cases on the condition and the flags, after which `simp` evaluates every fact, or fails. -/
syntax "cond_cases " term:max term:max : tactic
macro_rules
  | `(tactic| cond_cases $m $c) => `(tactic| focus (
    revert_flags
    obtain ⟨k, hk⟩ := $c
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    all_goals try simp only [Fin.val_mk, Nat.zero_add, Nat.reduceAdd] at *
    all_goals first
      | omega
      | (simp only [State.condHolds, Nat.reduceDiv, Nat.reduceMod, ↓reduceIte, Nat.reduceEqDiff]
         cases hn : State.nFlag (Mach.s $m) <;> cases hz : State.zFlag (Mach.s $m) <;>
           cases hc : State.cFlag (Mach.s $m) <;> cases hv : State.vFlag (Mach.s $m) <;>
           first | (simp; done) | omega | (simp at *; done) | (simp at *; omega))))

/-- The discharger of the walk of `B<cond>.W`: `mem_omega`, or `cond_cases` on a goal that names a
flag.  `first` runs its last alternative with error recovery, under which `cond_cases` would log
its failures and close the goal with `sorry`, and the walk, which proves the condition of a
disjunction's left branch in a `by` block, would take a branch whose condition is false.  The
final `fail` keeps `cond_cases` out of that position. -/
syntax "cond_disch " term:max term:max : tactic
macro_rules
  | `(tactic| cond_disch $m $c) => `(tactic|
    first | mem_omega | (guard_flags; cond_cases $m $c) | fail "cond_disch: no proof")

/-! `PSTATE.T`, which `BL` and `BX LR` write with 1. -/

/-- The fields of `PSTATE` with `T` set to 1. -/
def setT (fs : List (String × Val)) : List (String × Val) :=
  fs.map fun p => if p.1 = "T" then ("T", .bits 1 1) else p

/-- A register whose field `f` the premise on `σ` names holds a struct. -/
theorem get_field {σ : Sys} {r f : String} {v : Val} (h : σ.get r [f] = some v) :
    ∃ fs, σ r = some (.struct fs) ∧ fs.lookup f = some v := by
  unfold LeanExe.A64.Isla.Sys.get at h
  cases hr : σ r with
  | none => rw [hr] at h; cases h
  | some w =>
    rw [hr] at h
    cases w with
    | struct fs =>
      refine ⟨fs, rfl, ?_⟩
      cases hl : fs.lookup f with
      | none => simp only [Option.bind, acc, hl] at h; cases h
      | some x => simp only [Option.bind, acc, hl] at h; exact h ▸ rfl
    | _ => simp only [Option.bind, acc] at h; cases h

theorem upd_T {fs : List (String × Val)} {w : Val} (h : fs.lookup "T" = some w) :
    upd ["T"] (.struct fs) (.bits 1 1) = some (.struct (setT fs)) := by
  simp only [upd, h, Option.bind, Option.map, setT]

theorem lookup_setT : ∀ {fs : List (String × Val)} {w : Val}, fs.lookup "T" = some w →
    (setT fs).lookup "T" = some (.bits 1 1)
  | [], _, h => by simp only [List.lookup] at h; cases h
  | (k, v) :: fs, w, h => by
    by_cases hk : k = "T"
    · subst hk
      simp only [setT, List.map_cons, ↓reduceIte, List.lookup, beq_self_eq_true]
    · have hb : ("T" == k) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun e => hk e.symm
      simp only [List.lookup, hb] at h
      have := lookup_setT h
      simp only [setT, List.map_cons, hk, ↓reduceIte, List.lookup, hb] at this ⊢
      exact this

/-- Two machines that differ only in their program counters are equal when the counters are. -/
theorem mach_pc {m : Mach} {a b : UInt32} (h : a = b) :
    ({ m with s := { m.s with pc := a } } : Mach) =
      { m with s := { m.s with pc := b }, hi := m.hi } := by
  rw [h]

theorem toNat_lt32 (a : UInt32) : a.toNat < 4294967296 := a.toNat_lt

/-- The link value of `BL`, `PC<31:1>:'1'` with PC the instruction's address plus 4, as the trace
computes it. -/
theorem lr_eq (pc : UInt32) :
    (pc.toNat % 4294967296 + 4) % 4294967296 / 2 % 2147483648 * 2 + 1 = ((pc + 4) ||| 1).toNat := by
  have hp := pc.toNat_lt
  rw [UInt32.toNat_or, UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl,
    show (1 : UInt32).toNat = 1 from rfl, or_one, show (2 : Nat) ^ 32 = 4294967296 from rfl]
  omega

/-- Proves that the outcome at the end of a path of `BL`, which writes LR with the value `lv` that
`hlv` names and branches to the target `v` that `hv` names, is `exec`'s. -/
syntax "bl_end " term:max term:max : tactic
macro_rules
  | `(tactic| bl_end $hlv $hv) => `(tactic| (
    simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
    simp only [Outcome.done.injEq, and_true]
    simp (disch := first | omega | exact toNat_lt32 _) only [setX_low, setX_keep]
    apply exists_mach
    · simp only [setLow, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ← $hlv:term, ← $hv:term,
        ofNat_toNat32]
    · rfl
    · rfl))

/-- The backward counterpart of `bl_end`, for the path that keeps bits 63 to 32 of X14. -/
syntax "bl_bwd_end " term:max term:max : tactic
macro_rules
  | `(tactic| bl_bwd_end $hlv $hv) => `(tactic| (
    simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
    simp only [Outcome.done.injEq, and_true]
    simp (disch := first | omega | exact toNat_lt32 _) only [setX_keep]
    simp only [setLow, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ← $hlv:term, ← $hv:term,
      ofNat_toNat32]))

/-- Proves that the outcome at the end of a path of a branch from the machine `m` that writes only
the program counter, with the target `v` that `hv` names, is `exec`'s target. -/
syntax "br_end " term:max term:max : tactic
macro_rules
  | `(tactic| br_end $m $hv) => `(tactic| (
    simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
    refine ⟨Mach.hi $m, ?_⟩
    simp only [Outcome.done.injEq, and_true]
    apply mach_pc
    rw [← $hv:term]
    exact ofNat_toNat32 _))

/-- The backward counterpart of `br_end`. -/
syntax "br_bwd_end " term:max : tactic
macro_rules
  | `(tactic| br_bwd_end $hv) => `(tactic| (
    simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
    simp only [Outcome.done.injEq, and_true]
    apply Eq.symm
    apply mach_pc
    rw [← $hv:term]
    exact ofNat_toNat32 _))

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8000 in
/-- The trace of `B.W` (T4) agrees with `exec` for every value of the offset's fields and every
machine whose program counter is even. -/
theorem b_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (s j1 j2 : Fin 2)
    (imm10 : Fin 1024) (imm11 : Fin 2048) (m : Mach) (hpc : m.s.pc.toNat % 2 = 0) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond", "Branchtypetaken"] bT
      (branchFields s j1 j2 imm10 imm11) (.b s j1 j2 imm10 imm11) m := by
  have hoff := offset_eq s j1 j2 imm10 imm11
  have htgt := target_eq hpc (offset_even s j1 j2 imm10 imm11)
  obtain ⟨b, hb⟩ : ∃ b, (branchOffset s j1 j2 imm10 imm11).toNat = b := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, (m.s.pc + 4 + branchOffset s j1 j2 imm10 imm11).toNat = v :=
    ⟨_, rfl⟩
  rw [hb] at hoff htgt
  rw [hv] at htgt
  have hv32 : v < 4294967296 := hv ▸ UInt32.toNat_lt _
  replace hoff : Opaque _ := hoff
  replace htgt : Opaque _ := htgt
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, bT, branchFields, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [bT, sys_get, sys] at hσ
      refine ⟨((((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set
        "SEE" (.bits 128 2855)).set "Branchtypetaken" (.enum "BranchType_DIR")).set "__BranchTaken"
        (.bool true), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [bT, LeanExe.A64.Isla.Footprint.vars, branchFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        m7_fwd h using mem_omega with [hσ, and_fffffffe, Opaque.out hoff, Opaque.out htgt]
        all_goals br_end m hv
      · unfold footRun
        simp only [bT, LeanExe.A64.Isla.Footprint.vars, branchFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        by_cases h1 : imm10.val / 32 % 32 = 10 <;>
          by_cases h2 : imm10.val / 32 % 32 = 8 <;>
          by_cases h3 : imm10.val / 16 % 64 = 32 <;>
          by_cases h4 : imm10.val / 32 % 32 = 0
        all_goals first
          | (exfalso; omega)
          | (m7_bwd [u.feature, m.s.pc.toNat] using mem_omega
              with [hσ, and_fffffffe, Opaque.out hoff, Opaque.out htgt]
             all_goals first
               | br_bwd_end hv
               | t32_side)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8000 in
/-- The trace of `BL` agrees with `exec` for every value of the offset's fields and every machine
whose program counter is even. -/
theorem bl_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (s j1 j2 : Fin 2)
    (imm10 : Fin 1024) (imm11 : Fin 2048) (m : Mach) (hpc : m.s.pc.toNat % 2 = 0) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond", "PSTATE", "Branchtypetaken"] blT
      (branchFields s j1 j2 imm10 imm11) (.bl s j1 j2 imm10 imm11) m := by
  have hoff := offset_eq s j1 j2 imm10 imm11
  have htgt := target_eq hpc (offset_even s j1 j2 imm10 imm11)
  have hlr := lr_eq m.s.pc
  obtain ⟨b, hb⟩ : ∃ b, (branchOffset s j1 j2 imm10 imm11).toNat = b := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, (m.s.pc + 4 + branchOffset s j1 j2 imm10 imm11).toNat = v :=
    ⟨_, rfl⟩
  obtain ⟨lv, hlv⟩ : ∃ lv, ((m.s.pc + 4) ||| 1).toNat = lv := ⟨_, rfl⟩
  rw [hb] at hoff htgt
  rw [hv] at htgt
  rw [hlv] at hlr
  have hv32 : v < 4294967296 := hv ▸ UInt32.toNat_lt _
  have hlv32 : lv < 4294967296 := hlv ▸ UInt32.toNat_lt _
  replace hoff : Opaque _ := hoff
  replace htgt : Opaque _ := htgt
  replace hlr : Opaque _ := hlr
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, blT, branchFields, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [blT, sys_get, sys] at hσ
      have hT0 : σ.get "PSTATE" ["T"] = some (.bits 1 1) := by simp only [hσ]
      obtain ⟨fs, hfs, hT⟩ := get_field hT0
      refine ⟨(((((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set
        "SEE" (.bits 128 2870)).set "PSTATE" (.struct (setT fs))).set "Branchtypetaken"
        (.enum "BranchType_DIRCALL")).set "__BranchTaken" (.bool true), fun o h => ?_, ?_,
        by t32_frame⟩
      · unfold footRun at h
        simp only [blT, LeanExe.A64.Isla.Footprint.vars, branchFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        m7_fwd h using mem_omega with [hσ, hfs, ↓upd_T hT, lookup_setT hT, and_fffffffe,
          Opaque.out hoff, Opaque.out htgt, Opaque.out hlr]
        all_goals bl_end hlv hv
      · unfold footRun
        simp only [blT, LeanExe.A64.Isla.Footprint.vars, branchFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        by_cases h1 : imm10.val / 32 % 32 = 10 <;>
          by_cases h2 : imm10.val / 32 % 32 = 8 <;>
          by_cases h3 : imm10.val / 16 % 64 = 32 <;>
          by_cases h4 : imm10.val / 32 % 32 = 0 <;>
          by_cases h5 : (60 + s.val) * 64 + imm10.val / 16 % 64 = 3894 <;>
          by_cases h6 : imm10.val / 32 % 32 = 1
        all_goals first
          | (exfalso; omega)
          | (m7_bwd [u.feature, m.s.pc.toNat, false, m.x 14] using mem_omega
              with [hσ, hfs, ↓upd_T hT, lookup_setT hT, and_fffffffe, Opaque.out hoff,
                Opaque.out htgt, Opaque.out hlr]
             all_goals first
               | bl_bwd_end hlv hv
               | t32_side)

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- The trace of `B<cond>.W` (T3) agrees with `exec` for every condition from EQ to LE, every value
of the offset's fields, and every machine whose program counter plus 4 is below 2^32 and, when the
branch is taken, is even.  The trace writes the condition to `__currentCond` in the decode clause,
and the taken branch writes `Branchtypetaken`, so `σ'` depends on the condition and on whether
it holds. -/
theorem bcond_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (cc : Fin 14)
    (s j1 j2 : Fin 2) (imm6 : Fin 64) (imm11 : Fin 2048) (m : Mach)
    (hpc : m.s.pc.toNat + 4 < 4294967296)
    (hpc2 : m.s.condHolds cc = true → m.s.pc.toNat % 2 = 0) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond", "Branchtypetaken"] bcondT
      (bcondFields cc s j1 j2 imm6 imm11) (.bcond cc s j1 j2 imm6 imm11) m := by
  have hoff := offset21_eq s j1 j2 imm6 imm11
  obtain ⟨b, hb⟩ : ∃ b, (bcondOffset s j1 j2 imm6 imm11).toNat = b := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, (m.s.pc + 4 + bcondOffset s j1 j2 imm6 imm11).toNat = v :=
    ⟨_, rfl⟩
  have hv32 : v < 4294967296 := hv ▸ UInt32.toNat_lt _
  rw [hb] at hoff
  replace hoff : Opaque _ := hoff
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, bcondT, bcondFields, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [bcondT, sys_get, sys] at hσ
      by_cases hc : m.s.condHolds cc = true
      · have htgt := target_eq (hpc2 hc) (offset21_even s j1 j2 imm6 imm11)
        rw [hb, hv] at htgt
        replace htgt : Opaque _ := htgt
        refine ⟨(((((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set
          "SEE" (.bits 128 2854)).set "__currentCond" (.bits 4 cc.val)).set "Branchtypetaken"
          (.enum "BranchType_DIR")).set "__BranchTaken" (.bool true), fun o h => ?_, ?_,
          by t32_frame⟩
        · unfold footRun at h
          simp only [bcondT, LeanExe.A64.Isla.Footprint.vars, bcondFields, List.foldl,
            List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
            Nat.reduceAdd, Nat.reduceDiv] at h
          m7_fwd h using mem_omega with [hσ, and_fffffffe, Opaque.out hoff, Opaque.out htgt]
          all_goals first
            | (simp -failIfUnchanged only [hc, ↓reduceIte, Bool.cond_true]; br_end m hv)
            | (exfalso; cond_cases m cc)
        · unfold footRun
          simp only [bcondT, LeanExe.A64.Isla.Footprint.vars, bcondFields, List.foldl,
            List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
            Nat.reduceAdd, Nat.reduceDiv]
          by_cases h1 : cc.val * 2 + imm6.val / 32 % 2 = 10 <;>
            by_cases h2 : cc.val * 2 + imm6.val / 32 % 2 = 8 <;>
            by_cases h3 : cc.val * 4 + imm6.val / 16 % 4 = 32 <;>
            by_cases h4 : cc.val * 2 + imm6.val / 32 % 2 = 0
          all_goals first
            | (exfalso; omega)
            | (m7_auto using (cond_disch m cc)
                with [hσ, and_fffffffe, Opaque.out hoff, Opaque.out htgt]
               all_goals first
                 | (simp -failIfUnchanged only [hc, ↓reduceIte, Bool.cond_true]; br_bwd_end hv)
                 | t32_side
                 | cond_cases m cc)
      · have hc' : m.s.condHolds cc = false := by simpa using hc
        refine ⟨(((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set
          "SEE" (.bits 128 2854)).set "__currentCond" (.bits 4 cc.val), fun o h => ?_, ?_,
          by t32_frame⟩
        · unfold footRun at h
          simp only [bcondT, LeanExe.A64.Isla.Footprint.vars, bcondFields, List.foldl,
            List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
            Nat.reduceAdd, Nat.reduceDiv] at h
          m7_fwd h using mem_omega with [hσ, and_fffffffe, Opaque.out hoff]
          all_goals first
            | (simp -failIfUnchanged only [hc', Bool.false_eq_true, ↓reduceIte, Bool.cond_false]
               simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
               t32_pc
               exact ⟨m.hi, rfl⟩)
            | (exfalso; cond_cases m cc)
        · unfold footRun
          simp only [bcondT, LeanExe.A64.Isla.Footprint.vars, bcondFields, List.foldl,
            List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
            Nat.reduceAdd, Nat.reduceDiv]
          by_cases h1 : cc.val * 2 + imm6.val / 32 % 2 = 10 <;>
            by_cases h2 : cc.val * 2 + imm6.val / 32 % 2 = 8 <;>
            by_cases h3 : cc.val * 4 + imm6.val / 16 % 4 = 32 <;>
            by_cases h4 : cc.val * 2 + imm6.val / 32 % 2 = 0
          all_goals first
            | (exfalso; omega)
            | (m7_auto using (cond_disch m cc)
                with [hσ, and_fffffffe, Opaque.out hoff]
               all_goals first
                 | (simp -failIfUnchanged only [hc', Bool.false_eq_true, ↓reduceIte,
                      Bool.cond_false]
                    simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq,
                      ↓reduceIte]
                    t32_pc
                    rfl)
                 | t32_side
                 | cond_cases m cc)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8000 in
/-- The trace of `BX LR` agrees with `exec` for every machine: when bit 0 of LR is set, its path
writes `PSTATE.T` with 1 and branches to LR with bit 0 clear, and when it is clear, `exec` stops. -/
theorem bxLr_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (m : Mach) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond", "PSTATE", "Branchtypetaken"]
      bxLrT [] .bxLr m := by
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves_bxLr (by decide)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, bxLrT, encodeNat, List.lookup,
        Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] <;> omega
    · simp only [exec] at hs
      split at hs
      · rename_i hlr
        simp only [Option.some.injEq] at hs
        subst hs
        t32_reads [bxLrT, sys_get, sys] at hσ
        have hT0 : σ.get "PSTATE" ["T"] = some (.bits 1 1) := by simp only [hσ]
        obtain ⟨fs, hfs, hT⟩ := get_field hT0
        have hlr' : m.s.lr.toNat % 2 = 1 := by
          have := congrArg UInt32.toNat hlr
          simpa only [UInt32.toNat_mod, show (2 : UInt32).toNat = 2 from rfl,
            show (1 : UInt32).toNat = 1 from rfl] using this
        have hx14 : m.x 14 % 4294967296 = m.s.lr.toNat := by
          rw [x_mod m (k := 14) (by omega), low_lr]
        have hmask : m.s.lr.toNat % 4294967296 / 2 * 2 = (m.s.lr &&& 0xFFFFFFFE).toNat := by
          rw [UInt32.toNat_and, toNat_fffffffe, and_fffffffe]
        obtain ⟨v, hv⟩ : ∃ v, (m.s.lr &&& 0xFFFFFFFE).toNat = v := ⟨_, rfl⟩
        rw [hv] at hmask
        have hv32 : v < 4294967296 := hv ▸ UInt32.toNat_lt _
        replace hmask : Opaque _ := hmask
        refine ⟨(((((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set
          "SEE" (.bits 128 2875)).set "PSTATE" (.struct (setT fs))).set "Branchtypetaken"
          (.enum "BranchType_INDIR")).set "__BranchTaken" (.bool true), fun o h => ?_, ?_,
          by t32_frame⟩
        · unfold footRun at h
          simp only [bxLrT, LeanExe.A64.Isla.Footprint.vars, List.foldl,
            LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd, Nat.reduceDiv] at h
          m7_fwd h using mem_omega with [hσ, hfs, ↓upd_T hT, hx14, hlr', and_fffffffe,
            Opaque.out hmask]
          all_goals br_end m hv
        · unfold footRun
          simp only [bxLrT, LeanExe.A64.Isla.Footprint.vars, List.foldl,
            LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd, Nat.reduceDiv]
          m7_bwd [u.feature, m.s.pc.toNat, m.x 14] using mem_omega
            with [hσ, hfs, ↓upd_T hT, hx14, hlr', and_fffffffe,
            Opaque.out hmask]
          all_goals first
            | br_bwd_end hv
            | t32_side
      · cases hs

#print axioms b_agrees
#print axioms bl_agrees
#print axioms bcond_agrees
#print axioms bxLr_agrees

end TestSupport.M7.Isla
