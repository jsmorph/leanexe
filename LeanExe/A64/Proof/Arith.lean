import LeanExe.A64.Proof.Traps
import LeanExe.ProofKit.Exec

/-!
The simulation of the integer comparisons and operations beyond GCD's loop.  `genCmp` compares
the two values on top with `SUBS` and sets the lower one's register to 1 or 0 with `CSINC` and a
condition: `neI64` with `EQ`, `ltUI64` with `HS`, `leUI64` with `HI`, and `geUI64` with `LO`,
each the inverse of the comparison's.  `genBin` replaces them by the result of one instruction:
`ADD`, `SUB`, `MADD` with `XZR` for `mulI64`, `AND` for `andI64` and the `i32` `and`, `ORR`,
`EOR`, `LSLV`, and `LSRV`.  `wrapI64` is a 32-bit `ORR`, whose result the processor
zero-extends.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-! ## Comparisons -/

/-- `SUBS XZR` of `x` and `y`, which `he` executes, followed by `CSINC r, XZR, XZR, c`, sets
register `r`, below 31, to 0 when the condition `c` holds of the flags of the subtraction and to 1
otherwise. -/
theorem run_csetc {s : State} {a : UInt64} {i0 : Instr} {r : Fin 32} {x y : UInt64}
    {c : Fin 16} (hr : r.val < 31) (hc0 : code a = some (encode i0))
    (hc1 : code (after a 1) = some (encode (.csinc r 31 31 c))) (hpc : s.pc = a)
    (he : LeanExe.A64.exec P i0 s = some { s.subs 31 x y with pc := s.pc + 4 }) :
    ∃ s', Reach P code s s' ∧ s'.pc = after a 2 ∧
      s'.x r = (if (s.subs 31 x y).condHolds c then 0 else 1) ∧
      (∀ q, q ≠ r → s'.x q = s.x q) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.out = s.out := by
  let s1 : State := { s.subs 31 x y with pc := s.pc + 4 }
  have hx1 : ∀ q, s1.x q = s.x q := by
    intro q
    show (s.setX 31 (x - y)).x q = s.x q
    unfold State.setX; rw [ite_eq_right (by decide)]
  have p1 : s1.pc = after a 1 := by simp [s1, hpc, after]
  refine ⟨{ s1.setX r (if s1.condHolds c then s1.x 31 else s1.x 31 + 1) with pc := s1.pc + 4 },
    reach_exec P code (by rw [hpc]; exact hc0) he
      (reach_exec P code (by rw [p1]; exact hc1) rfl (.refl _)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show s1.pc + 4 = after a 2
    rw [p1]; exact (after_succ a 1).symm
  · rw [State.x_withPc, State.x_setX_same hr]
    have h31 : s1.x 31 = 0 := by unfold State.x; rw [dite_eq_right (by decide)]
    rw [h31]
    rfl
  · intro q hq
    rw [State.x_withPc, State.x_setX_ne (Ne.symm hq), hx1]
  · show (s1.setX r _).sp = s.sp
    rw [State.setX_sp]; exact State.setX_sp
  · show (s1.setX r _).mem = s.mem
    rw [State.setX_mem]; exact State.setX_mem
  · show (s1.setX r _).out = s.out
    rw [State.setX_out]; exact State.setX_out

theorem subs_z (s : State) (x y : UInt64) : (s.subs 31 x y).zFlag = decide (x = y) := by
  show (x - y == 0) = decide (x = y)
  by_cases h : x = y
  · subst h; simp
  · have : ¬ x - y = 0 := fun e => h ((sub_eq_zero_iff' x y).mp e)
    simp [h, this]

theorem subs_c (s : State) (x y : UInt64) : (s.subs 31 x y).cFlag = decide (y ≤ x) := rfl

/-- The register of `CSINC` after `SUBS` holds the result of the comparison `R` as an `i32`, for
the condition `c` that inverts `R`. -/
def CsetOk (c : Fin 16) (R : UInt64 → UInt64 → Prop) [DecidableRel R] : Prop :=
  ∀ (s : State) (x y : UInt64),
    (if (s.subs 31 x y).condHolds c then (0 : UInt64) else 1) =
      (if R x y then (1 : UInt32) else 0).toUInt64

theorem condHolds_0 (s : State) : s.condHolds 0 = s.zFlag := rfl
theorem condHolds_2 (s : State) : s.condHolds 2 = s.cFlag := rfl
theorem condHolds_3 (s : State) : s.condHolds 3 = !s.cFlag := rfl
theorem condHolds_8 (s : State) : s.condHolds 8 = (s.cFlag && !s.zFlag) := rfl

theorem cset_ne : CsetOk 0 (fun x y => x ≠ y) := by
  intro s x y
  rw [condHolds_0, subs_z]
  by_cases h : x = y <;> simp [h] <;> rfl

theorem cset_ltU : CsetOk 2 (fun x y => x < y) := by
  intro s x y
  rw [condHolds_2, subs_c]
  by_cases h : y ≤ x
  · have : ¬ x < y := by
      rw [UInt64.lt_iff_toNat_lt]; rw [UInt64.le_iff_toNat_le] at h; omega
    simp [h, this]
  · have : x < y := by
      rw [UInt64.lt_iff_toNat_lt]; rw [UInt64.le_iff_toNat_le] at h; omega
    simp [h, this]

theorem cset_geU : CsetOk 3 (fun x y => x ≥ y) := by
  intro s x y
  rw [condHolds_3, subs_c]
  by_cases h : y ≤ x <;> simp [h]

theorem cset_leU : CsetOk 8 (fun x y => x ≤ y) := by
  intro s x y
  rw [condHolds_8, subs_c, subs_z]
  have hle := UInt64.le_iff_toNat_le (a := x) (b := y)
  have hle' := UInt64.le_iff_toNat_le (a := y) (b := x)
  have heq : x = y ↔ x.toNat = y.toNat := ⟨fun e => e ▸ rfl, UInt64.toNat_inj.mp⟩
  by_cases h2 : x = y
  · subst h2
    simp
  · by_cases h1 : y ≤ x
    · have : ¬ x ≤ y := by rw [hle]; rw [hle'] at h1; rw [heq] at h2; omega
      simp [h1, h2, this]
    · have : x ≤ y := by rw [hle]; rw [hle'] at h1; omega
      simp [h1, h2, this]

theorem sim_cmp_of {F : Nat} {inst : Instruction} {c : Fin 16}
    (R : UInt64 → UInt64 → Prop) [DecidableRel R] (hR : CsetOk c R)
    (hgen : ∀ E ctl h a, genInstr E ctl h a inst = genCmp ctl h c)
    (hcase : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals),
      (∃ va vb vs, sl.values = vb :: va :: vs ∧ ∀ wa wb, ValRel va wa → ValRel vb wb →
        execOne (f + 1) m st sl inst =
          .Fallthrough st { sl with values := .i32 (if R wa wb then 1 else 0) :: vs }) ∨
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    InstrSim P code F inst := by
  intro E ctl h a is fin hg hcode hb hctl α m st sl ms hinv hh hpc _
  rw [hgen] at hg
  obtain ⟨hhb, hlt, rfl, rfl⟩ := genCmp_ok hg
  cases F with
  | zero => rw [ProofKit.execOne_zero]; exact .inr trivial
  | succ f =>
      rcases hcase f m st sl with ⟨va, vb, vs, hvs, hex⟩ | ⟨msg, hex⟩
      · have hvl : vs.length = h - 2 := by rw [hvs] at hh; simp at hh; omega
        have hst := hinv.stack
        rw [hvs] at hst
        have hb' : ValRel vb (ms.x (regOf (h - 1))) := by
          have := hst.top
          rwa [show (va :: vs).length = h - 1 by simp; omega] at this
        have ha' : ValRel va (ms.x (regOf (h - 2))) := by
          have := hst.pop.top
          rwa [hvl] at this
        rw [hex _ _ ha' hb']
        obtain ⟨ms', hr, hp, hres, hkeep, hsp, hmem, hout⟩ :=
          run_csetc P code (x := ms.x (regOf (h - 2))) (y := ms.x (regOf (h - 1)))
            (regOf_lt_31 (h - 2) (by omega)) (by simpa [after_zero] using hcode 0 (by simp))
            (by simpa using hcode 1 (by simp)) hpc rfl
        rw [show h - 1 = vs.length + 1 by omega]
        apply cmp_outcome P code _ hinv (vs := vs) (by omega) (by omega) hst.pop.pop hr hp _ _
          hsp hmem hout
        · rw [hvl, hres, show h - 2 + 1 = h - 1 by omega]
          exact hR ms _ _
        · rw [hvl]; exact hkeep
      · rw [hex]; exact .inr trivial

/-! ## Operations -/

theorem genBin_ok {ctl : List Ctl} {h : Nat} {op : Fin 32 → Fin 32 → Fin 32 → Instr}
    {is : List Instr} {fin : Option Nat} (hg : genBin ctl h op = .ok (is, fin)) :
    curBase ctl + 2 ≤ h ∧ h - 1 < 26 ∧
      is = [op (regOf (h - 2)) (regOf (h - 2)) (regOf (h - 1))] ∧ fin = some (h - 1) := by
  by_cases hc : h < curBase ctl + 2
  · simp [genBin, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases hlt : h - 1 < 26
  · simp [genBin, hc, opReg_ok hlt, opReg_ok (show h - 2 < 26 by omega), bind, Except.bind,
      pure, Except.pure] at hg
    exact ⟨by omega, hlt, hg.1.symm, hg.2.symm⟩
  · obtain ⟨e, he⟩ := opReg_error hlt
    by_cases hlt2 : h - 2 < 26
    · simp [genBin, hc, he, opReg_ok hlt2, bind, Except.bind] at hg
    · obtain ⟨e2, he2⟩ := opReg_error hlt2
      simp [genBin, hc, he2, bind, Except.bind] at hg

theorem sim_bin_of {F : Nat} {inst : Instruction} {op : Fin 32 → Fin 32 → Fin 32 → Instr}
    (g : UInt64 → UInt64 → UInt64)
    (hgen : ∀ E ctl h a, genInstr E ctl h a inst = genBin ctl h op)
    (hexec : ∀ (s : State) (d n m : Fin 32), LeanExe.A64.exec P (op d n m) s =
      some { s.setX d (g (s.x n) (s.x m)) with pc := s.pc + 4 })
    (hcase : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals),
      (∃ va vb vs, sl.values = vb :: va :: vs ∧ ∀ wa wb, ValRel va wa → ValRel vb wb →
        ∃ vr, ValRel vr (g wa wb) ∧
          execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := vr :: vs }) ∨
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    InstrSim P code F inst := by
  intro E ctl h a is fin hg hcode hb hctl α m st sl ms hinv hh hpc _
  rw [hgen] at hg
  obtain ⟨hhb, hlt, rfl, rfl⟩ := genBin_ok hg
  cases F with
  | zero => rw [ProofKit.execOne_zero]; exact .inr trivial
  | succ f =>
      rcases hcase f m st sl with ⟨va, vb, vs, hvs, hex⟩ | ⟨msg, hex⟩
      · have hvl : vs.length = h - 2 := by rw [hvs] at hh; simp at hh; omega
        have hst := hinv.stack
        rw [hvs] at hst
        have hb' : ValRel vb (ms.x (regOf (h - 1))) := by
          have := hst.top
          rwa [show (va :: vs).length = h - 1 by simp; omega] at this
        have ha' : ValRel va (ms.x (regOf (h - 2))) := by
          have := hst.pop.top
          rwa [hvl] at this
        obtain ⟨vr, hvr, hex'⟩ := hex _ _ ha' hb'
        rw [hex']
        have hc0 : code ms.pc = some (encode (op (regOf (h - 2)) (regOf (h - 2))
            (regOf (h - 1)))) := by
          rw [hpc]; simpa [after_zero] using hcode 0 (by simp)
        have hr := reach_exec P code hc0 (hexec ms _ _ _) (.refl _)
        have hd := regOf_lt_31 (h - 2) (by omega)
        apply res_outcome P code hvr (vs := vs) (by omega) hinv (by omega) (by omega)
          hst.pop.pop hr
        · show ms.pc + 4 = _
          rw [hpc]; simp [after]
        · rw [State.x_withPc, hvl, State.x_setX_same hd]
        · intro k hk
          rw [State.x_withPc, State.x_setX_ne (fun e => absurd
            (regOf_inj (h - 2) (by omega) k (by omega) e) (by omega))]
        · rw [State.x_withPc, State.x_setX_ne (regOf_ne_18 _ (by omega))]
        · exact State.setX_sp
        · exact State.setX_mem
        · exact State.setX_out
      · rw [hex]; exact .inr trivial

/-! ## The forms -/

/-- Talos's cases of an `i64` operation whose rule replaces `.i64 b :: .i64 a` by
`.i64 (t a b)`, for a machine operation `g` that agrees with `t`. -/
theorem i64_bin_case {inst : Instruction} (t g : UInt64 → UInt64 → UInt64)
    (htg : ∀ a b, g a b = t a b) {f : Nat} {α : Type} {m : Module} {st : Store α} {sl : Locals}
    (hgood : ∀ a b vs, sl.values = .i64 b :: .i64 a :: vs →
      execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := .i64 (t a b) :: vs })
    (hbad : (∀ a b vs, sl.values ≠ .i64 b :: .i64 a :: vs) →
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    (∃ va vb vs, sl.values = vb :: va :: vs ∧ ∀ wa wb, ValRel va wa → ValRel vb wb →
      ∃ vr, ValRel vr (g wa wb) ∧
        execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := vr :: vs }) ∨
    ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg := by
  by_cases h : ∃ a b vs, sl.values = .i64 b :: .i64 a :: vs
  · obtain ⟨a, b, vs, hv⟩ := h
    refine .inl ⟨.i64 a, .i64 b, vs, hv, fun wa wb ha hb => ⟨.i64 (t a b), ?_, hgood a b vs hv⟩⟩
    simp only [ValRel] at ha hb ⊢
    rw [ha, hb, htg]
  · exact .inr (hbad fun a b vs hv => h ⟨a, b, vs, hv⟩)

/-- Talos's cases of an `i64` comparison whose rule replaces `.i64 b :: .i64 a` by the `i32` of
`R a b`. -/
theorem i64_cmp_case {inst : Instruction} (R : UInt64 → UInt64 → Prop) [DecidableRel R]
    {f : Nat} {α : Type} {m : Module} {st : Store α} {sl : Locals}
    (hgood : ∀ a b vs, sl.values = .i64 b :: .i64 a :: vs →
      execOne (f + 1) m st sl inst =
        .Fallthrough st { sl with values := .i32 (if R a b then 1 else 0) :: vs })
    (hbad : (∀ a b vs, sl.values ≠ .i64 b :: .i64 a :: vs) →
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    (∃ va vb vs, sl.values = vb :: va :: vs ∧ ∀ wa wb, ValRel va wa → ValRel vb wb →
      execOne (f + 1) m st sl inst =
        .Fallthrough st { sl with values := .i32 (if R wa wb then 1 else 0) :: vs }) ∨
    ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg := by
  by_cases h : ∃ a b vs, sl.values = .i64 b :: .i64 a :: vs
  · obtain ⟨a, b, vs, hv⟩ := h
    refine .inl ⟨.i64 a, .i64 b, vs, hv, fun wa wb ha hb => ?_⟩
    simp only [ValRel] at ha hb
    rw [ha, hb]
    exact hgood a b vs hv
  · exact .inr (hbad fun a b vs hv => h ⟨a, b, vs, hv⟩)

/-- Proves the premises of `i64_bin_case` and `i64_cmp_case` from Talos's rule. -/
syntax "i64_rule_tac" : tactic
macro_rules
  | `(tactic| i64_rule_tac) => `(tactic| (
      · intro a b vs hv
        simp only [execOne.eq_def, hv]
      · intro hne
        simp only [execOne.eq_def]
        split
        · rename_i b a vs hv
          exact absurd hv (hne a b vs)
        · exact ⟨_, rfl⟩))

theorem sim_neI64 (F : Nat) : InstrSim P code F .neI64 :=
  sim_cmp_of P code (inst := .neI64)
    (fun x y => x ≠ y) cset_ne (fun _ _ _ _ => by simp only [genInstr])
    fun _ _ _ _ _ => by
      apply i64_cmp_case (fun x y => x ≠ y)
      i64_rule_tac

theorem sim_ltUI64 (F : Nat) : InstrSim P code F .ltUI64 :=
  sim_cmp_of P code (inst := .ltUI64)
    (fun x y => x < y) cset_ltU (fun _ _ _ _ => by simp only [genInstr])
    fun _ _ _ _ _ => by
      apply i64_cmp_case (fun x y => x < y)
      i64_rule_tac

theorem sim_leUI64 (F : Nat) : InstrSim P code F .leUI64 :=
  sim_cmp_of P code (inst := .leUI64)
    (fun x y => x ≤ y) cset_leU (fun _ _ _ _ => by simp only [genInstr])
    fun _ _ _ _ _ => by
      apply i64_cmp_case (fun x y => x ≤ y)
      i64_rule_tac

theorem sim_geUI64 (F : Nat) : InstrSim P code F .geUI64 :=
  sim_cmp_of P code (inst := .geUI64)
    (fun x y => x ≥ y) cset_geU (fun _ _ _ _ => by simp only [genInstr])
    fun _ _ _ _ _ => by
      apply i64_cmp_case (fun x y => x ≥ y)
      i64_rule_tac

theorem sim_addI64 (F : Nat) : InstrSim P code F .addI64 :=
  sim_bin_of P code (inst := .addI64) (op := Instr.addReg) (fun x y => x + y)
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply i64_bin_case (fun a b => a + b) _ (fun _ _ => rfl)
      i64_rule_tac

theorem sim_subI64 (F : Nat) : InstrSim P code F .subI64 :=
  sim_bin_of P code (inst := .subI64) (op := Instr.subReg) (fun x y => x - y)
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply i64_bin_case (fun a b => a - b) _ (fun _ _ => rfl)
      i64_rule_tac

theorem sim_mulI64 (F : Nat) : InstrSim P code F .mulI64 :=
  sim_bin_of P code (inst := .mulI64) (op := (fun d n m => Instr.madd d n m 31))
    (fun x y => 0 + x * y)
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply i64_bin_case (fun a b => a * b) _ (fun _ _ => UInt64.zero_add _)
      i64_rule_tac

theorem sim_andI64 (F : Nat) : InstrSim P code F .andI64 :=
  sim_bin_of P code (inst := .andI64) (op := Instr.andReg) (fun x y => x &&& y)
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply i64_bin_case (fun a b => a &&& b) _ (fun _ _ => rfl)
      i64_rule_tac

theorem sim_orI64 (F : Nat) : InstrSim P code F .orI64 :=
  sim_bin_of P code (inst := .orI64) (op := Instr.orrReg) (fun x y => x ||| y)
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply i64_bin_case (fun a b => a ||| b) _ (fun _ _ => rfl)
      i64_rule_tac

theorem sim_xorI64 (F : Nat) : InstrSim P code F .xorI64 :=
  sim_bin_of P code (inst := .xorI64) (op := Instr.eorReg) (fun x y => x ^^^ y)
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply i64_bin_case (fun a b => a ^^^ b) _ (fun _ _ => rfl)
      i64_rule_tac

theorem sim_shlI64 (F : Nat) : InstrSim P code F .shlI64 :=
  sim_bin_of P code (inst := .shlI64) (op := Instr.lslv) (fun x y => x <<< (y % 64))
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply i64_bin_case (fun a b => a <<< (b % 64)) _ (fun _ _ => rfl)
      i64_rule_tac

theorem sim_shrUI64 (F : Nat) : InstrSim P code F .shrUI64 :=
  sim_bin_of P code (inst := .shrUI64) (op := Instr.lsrv) (fun x y => x >>> (y % 64))
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply i64_bin_case (fun a b => a >>> (b % 64)) _ (fun _ _ => rfl)
      i64_rule_tac

theorem sim_and (F : Nat) : InstrSim P code F .and :=
  sim_bin_of P code (inst := .and) (op := Instr.andReg) (fun x y => x &&& y)
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun f α m st sl => by
      by_cases h : ∃ a b vs, sl.values = .i32 a :: .i32 b :: vs
      · obtain ⟨a, b, vs, hv⟩ := h
        refine .inl ⟨.i32 b, .i32 a, vs, hv, fun wa wb ha hb => ⟨.i32 (a &&& b), ?_, ?_⟩⟩
        · simp only [ValRel] at ha hb ⊢
          rw [ha, hb, UInt32.toUInt64_and, UInt64.and_comm]
        · simp only [execOne.eq_def, hv]
      · refine .inr ?_
        simp only [execOne.eq_def]
        split
        · rename_i a b vs hv
          exact absurd ⟨a, b, vs, hv⟩ h
        · exact ⟨_, rfl⟩

theorem gen_wrap {E : Env} {ctl : List Ctl} {h : Nat} {a : UInt64} {is : List Instr}
    {fin : Option Nat} (hg : genInstr E ctl h a .wrapI64 = .ok (is, fin)) :
    curBase ctl + 1 ≤ h ∧ h - 1 < 26 ∧ is = [.orrW (regOf (h - 1)) 31 (regOf (h - 1))] ∧
      fin = some h := by
  by_cases hc : h < curBase ctl + 1
  · simp [genInstr, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases hlt : h - 1 < 26
  · simp [genInstr, hc, opReg_ok hlt, bind, Except.bind, pure, Except.pure] at hg
    exact ⟨by omega, hlt, hg.1.symm, hg.2.symm⟩
  · obtain ⟨e, he⟩ := opReg_error hlt
    simp [genInstr, hc, he, bind, Except.bind] at hg

theorem wrap_val (x : UInt64) :
    ((0 : UInt64) ||| x).toUInt32.toUInt64 = (UInt32.ofNat (x.toNat % 2 ^ 32)).toUInt64 := by
  congr 1
  apply UInt32.toNat_inj.mp
  rw [UInt64.zero_or, UInt64.toNat_toUInt32, UInt32.toNat_ofNat', Nat.mod_mod]

theorem sim_wrapI64 (F : Nat) : InstrSim P code F .wrapI64 := by
  intro E ctl h a is fin hg hcode hb hctl α m st sl ms hinv hh hpc _
  obtain ⟨hhb, hlt, rfl, rfl⟩ := gen_wrap hg
  cases F with
  | zero => rw [ProofKit.execOne_zero]; exact .inr trivial
  | succ f =>
      simp only [execOne.eq_def]
      split
      · rename_i x vs hv
        have hvl : vs.length = h - 1 := by rw [hv] at hh; simp at hh; omega
        have hst := hinv.stack
        rw [hv] at hst
        have hx : ms.x (regOf (h - 1)) = x := by
          have := hst.top; rw [hvl] at this; exact this
        have hc0 : code ms.pc = some (encode (.orrW (regOf (h - 1)) 31 (regOf (h - 1)))) := by
          rw [hpc]; simpa [after_zero] using hcode 0 (by simp)
        have hr := reach_exec P code hc0 rfl (.refl _)
        have hd := regOf_lt_31 (h - 1) hlt
        apply res_outcome P code (v := .i32 (UInt32.ofNat (x.toNat % 2 ^ 32)))
          (w := (UInt32.ofNat (x.toNat % 2 ^ 32)).toUInt64) rfl
          (vs := vs) (by omega) hinv (by omega) (by omega) hst.pop hr
        · show ms.pc + 4 = _
          rw [hpc]; simp [after]
        · rw [State.x_withPc, hvl, State.x_setX_same hd]
          have h31 : ms.x 31 = 0 := by unfold State.x; rw [dite_eq_right (by decide)]
          rw [h31, hx, wrap_val]
        · intro k hk
          rw [State.x_withPc, State.x_setX_ne (fun e => absurd
            (regOf_inj (h - 1) hlt k (by omega) e) (by omega))]
        · rw [State.x_withPc, State.x_setX_ne (regOf_ne_18 _ hlt)]
        · exact State.setX_sp
        · exact State.setX_mem
        · exact State.setX_out
      · exact .inr trivial

end LeanExe.A64
