import LeanExe.M7.Proof.Machine

/-!
Runs of straight-line code and of branches in the Cortex-M7 model.  `execSeq` executes a list of
instructions one after another, and `reach_seq` shows that the model reaches its result from the
list's first address when no instruction of the list branches.  `Keeps s t` states that `t` has the
SP, LR, r8 to r12, memory, device trace, and read count of `s`, which every form that writes only
r0 to r7, the flags, and the program counter keeps.  `exec_bcondTo` gives the target of a
conditional branch that `Instr.bcondTo` builds from a byte offset, and `reach_bxLr` the return of
`BX LR`.  `run_block` and `run_branch` run placed register code, the second followed by a
conditional branch.  The tactic `state_simp` reads the registers and flags of a state that `exec`
built, and `addr_eq` proves equations of addresses.
-/

namespace LeanExe.M7

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-! ## Registers -/

namespace State

theorem r_setR_same (s : State) (d : Fin 8) (v : UInt32) : (s.setR d v).r d = v := by
  simp [r, setR]

theorem r_setR_ne (s : State) {d e : Fin 8} (v : UInt32) (h : e ≠ d) :
    (s.setR d v).r e = s.r e := by
  have : e.val ≠ d.val := fun hv => h (Fin.ext hv)
  simp [r, setR, this]

/-! The lemmas below state the effect of the state updates that `exec` applies, for variable
arguments.  Proofs about placed code rewrite with them, and each proof splits the state first, so
that `simp` uses it as an equation instead of a definitional unfolding.  An unfolding leaves the
kernel to check that a state's field equals the value that a lemma names, and when the value is a
sum of a word and a large numeral, such as `CMP` with `#0` gives, the kernel's check can unfold the
numeral one successor at a time. -/

theorem r_withPc (s : State) (p : UInt32) (i : Fin 8) :
    ({ s with pc := p } : State).r i = s.r i := by
  cases s; rfl

theorem r_setNZCV (s : State) (f : UInt32 × Bool × Bool) (i : Fin 8) :
    (s.setNZCV f).r i = s.r i := by
  cases s; rfl

theorem r_of_regs {s t : State} (h : s.regs = t.regs) (i : Fin 8) : s.r i = t.r i := by
  simp [r, h]

theorem zFlag_withPc (s : State) (p : UInt32) : ({ s with pc := p } : State).zFlag = s.zFlag := by
  cases s; rfl

theorem cFlag_withPc (s : State) (p : UInt32) : ({ s with pc := p } : State).cFlag = s.cFlag := by
  cases s; rfl

theorem zFlag_setR (s : State) (d : Fin 8) (v : UInt32) : (s.setR d v).zFlag = s.zFlag := by
  cases s; rfl

theorem cFlag_setR (s : State) (d : Fin 8) (v : UInt32) : (s.setR d v).cFlag = s.cFlag := by
  cases s; rfl

theorem zFlag_setNZCV' (s : State) (f : UInt32 × Bool × Bool) :
    (s.setNZCV f).zFlag = (f.1 == 0) := by
  cases s; rfl

theorem cFlag_setNZCV' (s : State) (f : UInt32 × Bool × Bool) : (s.setNZCV f).cFlag = f.2.1 := by
  cases s; rfl

theorem r_result_one (s : State) (d : Fin 8) (f : UInt32 × Bool × Bool) (i : Fin 8) :
    (s.result 1 d f).r i = (s.setR d f.1).r i := by
  cases s; rfl

theorem r_result_zero (s : State) (d : Fin 8) (f : UInt32 × Bool × Bool) (i : Fin 8) :
    (s.result 0 d f).r i = (s.setR d f.1).r i := by
  cases s; rfl

theorem zFlag_result_one (s : State) (d : Fin 8) (f : UInt32 × Bool × Bool) :
    (s.result 1 d f).zFlag = (f.1 == 0) := by
  cases s; rfl

theorem cFlag_result_one (s : State) (d : Fin 8) (f : UInt32 × Bool × Bool) :
    (s.result 1 d f).cFlag = f.2.1 := by
  cases s; rfl

theorem zFlag_result_zero (s : State) (d : Fin 8) (f : UInt32 × Bool × Bool) :
    (s.result 0 d f).zFlag = s.zFlag := by
  cases s; rfl

theorem cFlag_result_zero (s : State) (d : Fin 8) (f : UInt32 × Bool × Bool) :
    (s.result 0 d f).cFlag = s.cFlag := by
  cases s; rfl

end State

/-! ## Straight-line code -/

/-- The forms that do not branch: every form but `B<cond>.W`, `B.W`, `BL`, and `BX LR`. -/
def Instr.falls : Instr → Bool
  | .bcond .. | .b .. | .bl .. | .bxLr => false
  | _ => true

/-- A form that does not branch places the next instruction 4 bytes on. -/
theorem exec_falls_pc {i : Instr} {s t : State} (hf : i.falls = true)
    (he : exec P σ i s = some t) : t.pc = s.pc + 4 := by
  cases i <;> simp only [Instr.falls, Bool.false_eq_true] at hf <;> simp only [exec] at he <;>
    first
    | (cases he; rfl)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp he; rfl)
    | (split at he
       · cases he
       · cases he; rfl)

theorem size_of_falls {i : Instr} (hf : i.falls = true) : i.size = 4 := by
  cases i <;> first | rfl | simp [Instr.falls] at hf

/-- The state after the instructions `is`, executed one after another from `s` without a fetch, or
`none` when one of them stops the model. -/
def execSeq (P : Platform) (σ : Nat → UInt32) : List Instr → State → Option State
  | [], s => some s
  | i :: is, s => (exec P σ i s).bind (execSeq P σ is)

/-- Placed instructions that do not branch take the model from their first address to the state
that `execSeq` gives, at the address after them. -/
theorem reach_seq {is : List Instr} {s t : State} (hf : is.all Instr.falls = true)
    (hc : CodeAt code s.pc is) (he : execSeq P σ is s = some t) :
    Reach P σ code s t ∧ t.pc = s.pc + UInt32.ofNat (codeSize is) := by
  induction is generalizing s with
  | nil =>
      cases he
      exact ⟨.refl _, by simp [codeSize]⟩
  | cons i is ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hf
      simp only [execSeq, Option.bind_eq_some_iff] at he
      obtain ⟨u, hu, hut⟩ := he
      obtain ⟨hci, hcs⟩ := CodeAt.cons.mp hc
      have hpc := exec_falls_pc hf.1 hu
      rw [size_of_falls hf.1, show s.pc + UInt32.ofNat 4 = u.pc from hpc.symm] at hcs
      obtain ⟨hr, hp⟩ := ih hf.2 hcs hut
      refine ⟨reach_exec hci hu hr, ?_⟩
      rw [hp, hpc, codeSize_cons, size_of_falls hf.1, ← add_ofNat_add]
      rfl

/-- `UDIV` with a nonzero divisor writes the quotient. -/
theorem exec_udiv {d n m : Fin 8} {s : State} (h : s.r m ≠ 0) :
    exec P σ (.udiv d n m) s = some { s.setR d (s.r n / s.r m) with pc := s.pc + 4 } := by
  simp only [exec, h, ↓reduceIte]

/-! ## What register-only forms keep -/

/-- `t` has the SP, LR, r8 to r12, memory, device trace, and number of device reads of `s`. -/
structure Keeps (s t : State) : Prop where
  sp : t.sp = s.sp
  lr : t.lr = s.lr
  high : ∀ i : Fin 13, 8 ≤ i.val → t.regs i = s.regs i
  mem : t.mem = s.mem
  trace : t.trace = s.trace
  reads : t.reads = s.reads

theorem Keeps.refl (s : State) : Keeps s s := ⟨rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {s t u : State} (h1 : Keeps s t) (h2 : Keeps t u) : Keeps s u :=
  ⟨h2.sp.trans h1.sp, h2.lr.trans h1.lr, fun i hi => (h2.high i hi).trans (h1.high i hi),
    h2.mem.trans h1.mem, h2.trace.trans h1.trace, h2.reads.trans h1.reads⟩

theorem Keeps.setR {s t : State} (h : Keeps s t) (d : Fin 8) (v : UInt32) :
    Keeps s (t.setR d v) :=
  ⟨h.sp, h.lr, fun i hi => by
    have : i.val ≠ d.val := by have := d.isLt; omega
    simp only [State.setR, this, ↓reduceIte]
    exact h.high i hi, h.mem, h.trace, h.reads⟩

theorem Keeps.setNZCV {s t : State} (h : Keeps s t) (f : UInt32 × Bool × Bool) :
    Keeps s (t.setNZCV f) := ⟨h.sp, h.lr, h.high, h.mem, h.trace, h.reads⟩

theorem Keeps.result {s t : State} (h : Keeps s t) (sf : Fin 2) (d : Fin 8)
    (f : UInt32 × Bool × Bool) : Keeps s (t.result sf d f) := by
  unfold State.result
  split
  · exact (h.setR d f.1).setNZCV f
  · exact h.setR d f.1

theorem Keeps.withPc {s t : State} (h : Keeps s t) (p : UInt32) : Keeps s { t with pc := p } :=
  ⟨h.sp, h.lr, h.high, h.mem, h.trace, h.reads⟩

/-- The forms that write only r0 to r7, the flags, and the program counter: every form but the
loads, the stores, the writes of SP, and `BL`. -/
def Instr.regOnly : Instr → Bool
  | .ldr .. | .str .. | .ldrSp .. | .strSp .. | .ldrLr .. | .strLr .. | .addwSpSp ..
  | .subwSpSp .. | .bl .. => false
  | _ => true

theorem exec_keeps {i : Instr} {s t : State} (hr : i.regOnly = true)
    (he : exec P σ i s = some t) : Keeps s t := by
  have k := Keeps.refl s
  cases i <;> simp only [Instr.regOnly, Bool.false_eq_true] at hr <;> simp only [exec] at he <;>
    first
    | (cases he; first
        | exact (k.result _ _ _).withPc _
        | exact (k.setR _ _).withPc _
        | exact (k.setNZCV _).withPc _
        | exact ((k.setR _ _).setR _ _).withPc _
        | exact k.withPc _)
    | (split at he
       · cases he
       · cases he; exact (k.setR _ _).withPc _)
    | (split at he
       · cases he; exact k.withPc _
       · cases he)

theorem execSeq_keeps {is : List Instr} {s t : State} (hr : is.all Instr.regOnly = true)
    (he : execSeq P σ is s = some t) : Keeps s t := by
  induction is generalizing s with
  | nil => cases he; exact Keeps.refl _
  | cons i is ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hr
      simp only [execSeq, Option.bind_eq_some_iff] at he
      obtain ⟨u, hu, hut⟩ := he
      exact (exec_keeps hr.1 hu).trans (ih hr.2 hut)

/-! ## Branches -/

/-- The offset fields that `Instr.bcondTo` computes from an even byte offset from -2^20 to
2^20 - 2 give that offset as a 32-bit word. -/
theorem bcondOffset_bcondTo {off : Int} (he : off % 2 = 0) (hlo : -1048576 ≤ off)
    (hhi : off < 1048576) :
    bcondOffset (field 2 ((off % 2097152).toNat / 1048576))
      (field 2 ((off % 2097152).toNat / 262144)) (field 2 ((off % 2097152).toNat / 524288))
      (field 64 ((off % 2097152).toNat / 4096)) (field 2048 ((off % 2097152).toNat / 2)) =
      UInt32.ofInt off := by
  generalize hv : (off % 2097152).toNat = v
  have hv' : (v : Int) = off % 2097152 := by
    rw [← hv]; exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  have hsum : v / 1048576 % 2 * 1048576 + v / 524288 % 2 * 524288 + v / 262144 % 2 * 262144 +
      v / 4096 % 64 * 4096 + v / 2 % 2048 * 2 = v := by omega
  simp only [bcondOffset, field]
  rw [hsum]
  apply UInt32.toNat_inj.mp
  simp only [sext, UInt32.ofInt, Nat.reduceSub, Nat.reducePow, Int.reducePow]
  split
  · rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat']
    omega
  · rw [UInt32.toNat_sub, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat']
    omega

/-- `B<cond>.W` that `Instr.bcondTo` builds from an even byte offset from -2^20 to 2^20 - 2
branches by that offset from its address plus 4 when its condition holds. -/
theorem exec_bcondTo (cond : Fin 14) {off : Int} (he : off % 2 = 0) (hlo : -1048576 ≤ off)
    (hhi : off < 1048576) (s : State) :
    exec P σ (Instr.bcondTo cond off) s =
      some { s with pc := if s.condHolds cond then s.pc + 4 + UInt32.ofInt off else s.pc + 4 } := by
  rw [← bcondOffset_bcondTo he hlo hhi]
  rfl

theorem condHolds_eq (s : State) : s.condHolds 0 = s.zFlag := by cases s; rfl
theorem condHolds_ne (s : State) : s.condHolds 1 = !s.zFlag := by cases s; rfl
theorem condHolds_cs (s : State) : s.condHolds 2 = s.cFlag := by cases s; rfl
theorem condHolds_cc (s : State) : s.condHolds 3 = !s.cFlag := by cases s; rfl

/-- A placed `B<cond>.W` from `Instr.bcondTo` reaches its target when its condition holds and the
next instruction otherwise. -/
theorem reach_bcondTo {cond : Fin 14} {off : Int} {s : State} (he : off % 2 = 0)
    (hlo : -1048576 ≤ off) (hhi : off < 1048576) (hc : CodeAt code s.pc [Instr.bcondTo cond off]) :
    Reach P σ code s
      { s with pc := if s.condHolds cond then s.pc + 4 + UInt32.ofInt off else s.pc + 4 } :=
  reach_exec hc (exec_bcondTo cond he hlo hhi s) (.refl _)

/-- A placed `BX LR` returns to LR with bit 0 clear when bit 0 is set. -/
theorem reach_bxLr {s : State} (hc : CodeAt code s.pc [.bxLr]) (hlr : s.lr % 2 = 1) :
    Reach P σ code s { s with pc := s.lr &&& 0xFFFFFFFE } :=
  reach_exec hc (by simp [exec, hlr]) (.refl _)

/-- A placed `B<cond>.W` from `Instr.bcondTo` whose target, its address plus 4 plus the offset,
is `target`. -/
theorem reach_branch {cond : Fin 14} {off : Int} {s : State} (target : UInt32) (he : off % 2 = 0)
    (hlo : -1048576 ≤ off) (hhi : off < 1048576) (hc : CodeAt code s.pc [Instr.bcondTo cond off])
    (ht : s.pc + 4 + UInt32.ofInt off = target) :
    Reach P σ code s { s with pc := if s.condHolds cond then target else s.pc + 4 } := by
  rw [← ht]
  exact reach_bcondTo he hlo hhi hc

/-! ## Placed register code and the tactics that read its states -/

/-- Placed straight-line register code reaches the state that `execSeq` gives and keeps what
`Keeps` names. -/
theorem run_block {is : List Instr} {s t : State} (hf : is.all Instr.falls = true)
    (hr : is.all Instr.regOnly = true) (hc : CodeAt code s.pc is)
    (he : execSeq P σ is s = some t) :
    Reach P σ code s t ∧ t.pc = s.pc + UInt32.ofNat (codeSize is) ∧ Keeps s t :=
  ⟨(reach_seq hf hc he).1, (reach_seq hf hc he).2, execSeq_keeps hr he⟩

/-- Placed straight-line register code followed by a placed `B<cond>.W` from `Instr.bcondTo`
reaches the branch's target `target` when its condition holds of the code's last state and the
next address `next` otherwise.  The program counter is stated with `cond`, whose condition is a
`Bool` without a `Decidable` instance, so a proof can rewrite the condition alone. -/
theorem run_branch {xs : List Instr} {c : Fin 14} {off : Int} {s t : State}
    (target next : UInt32) (hf : xs.all Instr.falls = true) (hr : xs.all Instr.regOnly = true)
    (hc : CodeAt code s.pc (xs ++ [Instr.bcondTo c off])) (he : execSeq P σ xs s = some t)
    (heven : off % 2 = 0) (hlo : -1048576 ≤ off) (hhi : off < 1048576)
    (ht : s.pc + UInt32.ofNat (codeSize xs) + 4 + UInt32.ofInt off = target)
    (hn : s.pc + UInt32.ofNat (codeSize xs) + 4 = next) :
    ∃ u, Reach P σ code s u ∧ Keeps s u ∧ u.regs = t.regs ∧
      u.pc = cond (t.condHolds c) target next := by
  obtain ⟨c1, c2⟩ := CodeAt.append.mp hc
  obtain ⟨r1, p1, k1⟩ := run_block hf hr c1 he
  rw [← p1] at c2 ht hn
  exact ⟨_, r1.trans (reach_branch target heven hlo hhi c2 ht), k1.withPc _, rfl,
    by rw [hn, Bool.cond_eq_ite]⟩

/-- Proves an equation of addresses, a word plus numerals and byte counts of explicit lists of
instructions, through `toNat`. -/
macro "addr_eq" : tactic =>
  `(tactic| (
      apply UInt32.toNat_inj.mp
      simp only [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.toNat_ofNat', UInt32.ofInt,
        codeSize_cons, codeSize_nil, codeSize_append, List.cons_append, List.nil_append,
        ↓size_bcondTo, ↓size_lslBy, ↓size_lsrBy, ↓size_addLsl, Instr.size, Int.reducePow,
        Int.reduceMod, Int.reduceNeg, Int.reduceToNat, Nat.reducePow, Nat.reduceAdd] <;>
      omega))

theorem field_val (n x : Nat) (h : 0 < n) : (field n x h).val = x % n := rfl

/-- Reads the registers r0 to r7, Z, and C of a state that `exec` built, and the conditions of
the branches, with the lemmas of `State` for variable arguments, deciding the inequalities of
register numbers.  Each lemma rewrites a read of a state before the terms below it, so that every
read meets the lemma about the state's outermost update while the update keeps the form that the
lemma names.  The simprocs evaluate the shift amounts that the constructors from numbers leave as
arithmetic on numerals, and no other simproc runs, so the immediates keep the form that the lemmas
about instructions' values name. -/
macro "state_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic|
    simp (disch := decide) only [↓State.r_withPc, ↓State.r_setNZCV, ↓State.r_result_one,
      ↓State.r_result_zero, ↓State.r_setR_same, ↓State.r_setR_ne, ↓State.zFlag_withPc,
      ↓State.cFlag_withPc, ↓State.zFlag_setR, ↓State.cFlag_setR, ↓State.zFlag_setNZCV',
      ↓State.cFlag_setNZCV', ↓State.zFlag_result_one, ↓State.cFlag_result_one,
      ↓State.zFlag_result_zero, ↓State.cFlag_result_zero, ↓condHolds_eq, ↓condHolds_ne,
      ↓condHolds_cs, ↓condHolds_cc,
      field_val, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff,
      ↓reduceIte] $(loc)?)

end LeanExe.M7
