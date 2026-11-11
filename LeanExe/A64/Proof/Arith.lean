import LeanExe.A64.Proof.Traps
import LeanExe.ProofKit.Exec
import LeanExe.ProofKit.Signed64

/-!
The simulation of the integer comparisons and operations beyond GCD's loop.  `genCmp` compares
the two values on top with `SUBS` and sets the lower one's register to 1 or 0 with `CSINC` and a
condition: `neI64` with `EQ`, `ltUI64` with `HS`, `leUI64` with `HI`, `geUI64` with `LO`,
`ltSI64` with `GE`, and `leSI64` with `GT`, each the inverse of the comparison's.  After `SUBS`,
N equals V exactly when the minuend is at least the subtrahend as `Int64` values.  `genBin`
replaces them by the result of one instruction: `ADD`, `SUB`, `MADD` with `XZR` for `mulI64`,
`AND` for `andI64` and the `i32` `and`, `ORR`, `EOR`, `LSLV`, and `LSRV`.  `shrSI64` is
`sarCode`, the logical shift between two copies of the sign mask in X16, which computes
`Signed64.sar`.  `wrapI64` is a 32-bit `ORR`, whose result the processor zero-extends.
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
      (∀ q, q ≠ r → s'.x q = s.x q) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.io = s.io := by
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
  · show (s1.setX r _).io = s.io
    rw [State.setX_io]; exact State.setX_io

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

theorem condHolds_10 (s : State) : s.condHolds 10 = (s.nFlag == s.vFlag) := rfl
theorem condHolds_12 (s : State) : s.condHolds 12 = (s.nFlag == s.vFlag && !s.zFlag) := rfl

/-- The word `w >>> 63 == 1` is the sign bit of `w`. -/
theorem msb63 (w : UInt64) : (w >>> 63 == 1) = w.toBitVec.msb := by
  rw [ProofKit.Signed64.shr63]
  cases w.toBitVec.msb <;> rfl

/-- After `SUBS` of `x` and `y`, N equals V exactly when `y ≤ x` as `Int64` values. -/
theorem subs_nv (s : State) (x y : UInt64) :
    ((s.subs 31 x y).nFlag == (s.subs 31 x y).vFlag) = decide (y.toInt64 ≤ x.toInt64) := by
  show (((x - y) >>> 63 == 1) == (((x ^^^ y) &&& (x ^^^ (x - y))) >>> 63 == 1)) = _
  rw [msb63, msb63, UInt64.toBitVec_and, UInt64.toBitVec_xor, UInt64.toBitVec_xor,
    BitVec.msb_and, BitVec.msb_xor, BitVec.msb_xor]
  simp only [Int64.le_iff_toInt_le]
  show _ = decide (y.toBitVec.toInt ≤ x.toBitVec.toInt)
  simp only [BitVec.toInt_eq_msb_cond]
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have hr : (x - y).toNat = (2 ^ 64 - y.toNat + x.toNat) % 2 ^ 64 := UInt64.toNat_sub x y
  have ex : x.toBitVec.toNat = x.toNat := rfl
  have ey : y.toBitVec.toNat = y.toNat := rfl
  have er : (x - y).toBitVec.toNat = (x - y).toNat := rfl
  rw [ex, ey]
  cases h1 : x.toBitVec.msb <;> cases h2 : y.toBitVec.msb <;> cases h3 : (x - y).toBitVec.msb <;>
  · first
    | (have a1 := BitVec.msb_eq_true_iff_two_mul_ge.mp h1)
    | (have a1 := BitVec.msb_eq_false_iff_two_mul_lt.mp h1)
    first
    | (have a2 := BitVec.msb_eq_true_iff_two_mul_ge.mp h2)
    | (have a2 := BitVec.msb_eq_false_iff_two_mul_lt.mp h2)
    first
    | (have a3 := BitVec.msb_eq_true_iff_two_mul_ge.mp h3)
    | (have a3 := BitVec.msb_eq_false_iff_two_mul_lt.mp h3)
    rw [ex] at a1
    rw [ey] at a2
    rw [er, hr] at a3
    simp <;> omega

theorem cset_ltS : CsetOk 10 (fun x y => x.toInt64 < y.toInt64) := by
  intro s x y
  rw [condHolds_10, subs_nv]
  by_cases h : y.toInt64 ≤ x.toInt64
  · have : ¬ x.toInt64 < y.toInt64 := by
      rw [Int64.lt_iff_toInt_lt]; rw [Int64.le_iff_toInt_le] at h; omega
    simp [h, this]
  · have : x.toInt64 < y.toInt64 := by
      rw [Int64.lt_iff_toInt_lt]; rw [Int64.le_iff_toInt_le] at h; omega
    simp [h, this]

theorem cset_leS : CsetOk 12 (fun x y => x.toInt64 ≤ y.toInt64) := by
  intro s x y
  rw [condHolds_12, subs_nv, subs_z]
  have heq : x = y ↔ x.toInt64.toInt = y.toInt64.toInt :=
    ⟨fun e => e ▸ rfl, fun e => congrArg Int64.toUInt64 (Int64.toInt_inj.mp e)⟩
  have hle := Int64.le_iff_toInt_le (x := x.toInt64) (y := y.toInt64)
  have hle' := Int64.le_iff_toInt_le (x := y.toInt64) (y := x.toInt64)
  by_cases h2 : x = y
  · subst h2
    simp
  · by_cases h1 : y.toInt64 ≤ x.toInt64
    · have : ¬ x.toInt64 ≤ y.toInt64 := by rw [hle]; rw [hle'] at h1; rw [heq] at h2; omega
      simp [h1, h2, this]
    · have : x.toInt64 ≤ y.toInt64 := by rw [hle]; rw [hle'] at h1; omega
      simp [h1, h2, this]

theorem sim_cmp_of {F : Nat} {inst : Instruction} {c : Fin 16}
    (R : UInt64 → UInt64 → Prop) [DecidableRel R] (hR : CsetOk c R)
    (hgen : ∀ E ctl σ a, genInstr E ctl σ a inst = genCmp ctl σ c)
    (hcase : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals),
      (∃ va vb vs, sl.values = vb :: va :: vs ∧ ∀ wa wb, ValRel va wa → ValRel vb wb →
        execOne (f + 1) m st sl inst =
          .Fallthrough st { sl with values := .i32 (if R wa wb then 1 else 0) :: vs }) ∨
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    InstrSim P code F inst := by
  intro E ctl σ a is fin hg hcode hb hctl α m st sl ms hinv hsr h64 hpc _ _ _ _
  rw [hgen] at hg
  obtain ⟨hhb, hlt, rfl, rfl⟩ := genCmp_ok hg
  have hh := hinv.len
  have hty := hinv.types
  generalize hσl : σ.length = h at *
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
        rw [hvs] at hty
        obtain ⟨ms', hr, hp, hres, hkeep, hsp, hmem, hout⟩ :=
          run_csetc P code (x := ms.x (regOf (h - 2))) (y := ms.x (regOf (h - 1)))
            (regOf_lt_31 (h - 2) (by omega)) (by simpa [after_zero] using hcode 0 (by simp))
            (by simpa using hcode 1 (by simp)) hpc rfl
        apply cmp_outcome P code _ hinv hsr (vs := vs) (hty.drop 2) (by omega) (by omega)
          hst.pop.pop
          hr hp _ _ hsp hmem hout
        · rw [hvl, hres]
          exact hR ms _ _
        · rw [hvl]; exact hkeep
      · rw [hex]; exact .inr trivial

/-! ## Operations -/

theorem genBin_ok {ctl : List Ctl} {σ : List ValueType} {op : Fin 32 → Fin 32 → Fin 32 → Instr}
    {t : ValueType} {is : List Instr} {fin : Option (List ValueType)}
    (hg : genBin ctl σ op t = .ok (is, fin)) :
    curBase ctl + 2 ≤ σ.length ∧ σ.length - 1 < 26 ∧
      is = [op (regOf (σ.length - 2)) (regOf (σ.length - 2)) (regOf (σ.length - 1))] ∧
      fin = some (t :: σ.drop 2) := by
  by_cases hc : σ.length < curBase ctl + 2
  · simp [genBin, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases hlt : σ.length - 1 < 26
  · simp [genBin, hc, opReg_ok hlt, opReg_ok (show σ.length - 2 < 26 by omega), bind,
      Except.bind, pure, Except.pure] at hg
    exact ⟨by omega, hlt, hg.1.symm, hg.2.symm⟩
  · obtain ⟨e, he⟩ := opReg_error hlt
    by_cases hlt2 : σ.length - 2 < 26
    · simp [genBin, hc, he, opReg_ok hlt2, bind, Except.bind] at hg
    · obtain ⟨e2, he2⟩ := opReg_error hlt2
      simp [genBin, hc, he2, bind, Except.bind] at hg

theorem sim_bin_of {F : Nat} {inst : Instruction} {op : Fin 32 → Fin 32 → Fin 32 → Instr}
    {t : ValueType} (g : UInt64 → UInt64 → UInt64)
    (hgen : ∀ E ctl σ a, genInstr E ctl σ a inst = genBin ctl σ op t)
    (hexec : ∀ (s : State) (d n m : Fin 32), LeanExe.A64.exec P (op d n m) s =
      some { s.setX d (g (s.x n) (s.x m)) with pc := s.pc + 4 })
    (hcase : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals),
      (∃ va vb vs, sl.values = vb :: va :: vs ∧ ∀ wa wb, ValRel va wa → ValRel vb wb →
        ∃ vr, ValRel vr (g wa wb) ∧ HasType t vr ∧
          execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := vr :: vs }) ∨
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    InstrSim P code F inst := by
  intro E ctl σ a is fin hg hcode hb hctl α m st sl ms hinv hsr h64 hpc _ _ _ _
  rw [hgen] at hg
  obtain ⟨hhb, hlt, rfl, rfl⟩ := genBin_ok hg
  have hh := hinv.len
  have hty := hinv.types
  generalize hσl : σ.length = h at *
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
        obtain ⟨vr, hvr, htr, hex'⟩ := hex _ _ ha' hb'
        rw [hex']
        rw [hvs] at hty
        have hc0 : code ms.pc = some (encode (op (regOf (h - 2)) (regOf (h - 2))
            (regOf (h - 1)))) := by
          rw [hpc]; simpa [after_zero] using hcode 0 (by simp)
        have hr := reach_exec P code hc0 (hexec ms _ _ _) (.refl _)
        have hd := regOf_lt_31 (h - 2) (by omega)
        apply res_outcome P code hvr (vs := vs) htr (hty.drop 2) hinv hsr (by omega) (by omega)
          hst.pop.pop hr
        · show ms.pc + 4 = _
          rw [hpc]; simp [after]
        · rw [State.x_withPc, hvl, State.x_setX_same hd]
        · intro k hk
          rw [State.x_withPc, State.x_setX_ne (fun e => absurd
            (regOf_inj (h - 2) (by omega) k (by omega) e) (by omega))]
        · rw [State.x_withPc, State.x_setX_ne (regOf_ne_18 _ (by omega))]
        · rw [State.x_withPc, State.x_setX_ne (regOf_ne_17 _ (by omega))]
        · exact State.setX_sp
        · exact State.setX_mem
        · exact State.setX_io
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
      ∃ vr, ValRel vr (g wa wb) ∧ HasType .i64 vr ∧
        execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := vr :: vs }) ∨
    ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg := by
  by_cases h : ∃ a b vs, sl.values = .i64 b :: .i64 a :: vs
  · obtain ⟨a, b, vs, hv⟩ := h
    refine .inl ⟨.i64 a, .i64 b, vs, hv, fun wa wb ha hb =>
      ⟨.i64 (t a b), ?_, trivial, hgood a b vs hv⟩⟩
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

theorem sim_ltSI64 (F : Nat) : InstrSim P code F .ltSI64 :=
  sim_cmp_of P code (inst := .ltSI64)
    (fun x y => x.toInt64 < y.toInt64) cset_ltS (fun _ _ _ _ => by simp only [genInstr])
    fun _ _ _ _ _ => by
      apply i64_cmp_case (fun x y => x.toInt64 < y.toInt64)
      i64_rule_tac

theorem sim_leSI64 (F : Nat) : InstrSim P code F .leSI64 :=
  sim_cmp_of P code (inst := .leSI64)
    (fun x y => x.toInt64 ≤ y.toInt64) cset_leS (fun _ _ _ _ => by simp only [genInstr])
    fun _ _ _ _ _ => by
      apply i64_cmp_case (fun x y => x.toInt64 ≤ y.toInt64)
      i64_rule_tac

theorem sim_addI64 (F : Nat) : InstrSim P code F .addI64 :=
  sim_bin_of P code (inst := .addI64) (t := .i64) (op := Instr.addReg) (fun x y => x + y)
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply i64_bin_case (fun a b => a + b) _ (fun _ _ => rfl)
      i64_rule_tac

theorem sim_subI64 (F : Nat) : InstrSim P code F .subI64 :=
  sim_bin_of P code (inst := .subI64) (t := .i64) (op := Instr.subReg) (fun x y => x - y)
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply i64_bin_case (fun a b => a - b) _ (fun _ _ => rfl)
      i64_rule_tac

theorem sim_mulI64 (F : Nat) : InstrSim P code F .mulI64 :=
  sim_bin_of P code (inst := .mulI64) (t := .i64) (op := (fun d n m => Instr.madd d n m 31))
    (fun x y => 0 + x * y)
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply i64_bin_case (fun a b => a * b) _ (fun _ _ => UInt64.zero_add _)
      i64_rule_tac

theorem sim_andI64 (F : Nat) : InstrSim P code F .andI64 :=
  sim_bin_of P code (inst := .andI64) (t := .i64) (op := Instr.andReg) (fun x y => x &&& y)
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply i64_bin_case (fun a b => a &&& b) _ (fun _ _ => rfl)
      i64_rule_tac

theorem sim_orI64 (F : Nat) : InstrSim P code F .orI64 :=
  sim_bin_of P code (inst := .orI64) (t := .i64) (op := Instr.orrReg) (fun x y => x ||| y)
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply i64_bin_case (fun a b => a ||| b) _ (fun _ _ => rfl)
      i64_rule_tac

theorem sim_xorI64 (F : Nat) : InstrSim P code F .xorI64 :=
  sim_bin_of P code (inst := .xorI64) (t := .i64) (op := Instr.eorReg) (fun x y => x ^^^ y)
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply i64_bin_case (fun a b => a ^^^ b) _ (fun _ _ => rfl)
      i64_rule_tac

theorem sim_shlI64 (F : Nat) : InstrSim P code F .shlI64 :=
  sim_bin_of P code (inst := .shlI64) (t := .i64) (op := Instr.lslv) (fun x y => x <<< (y % 64))
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply i64_bin_case (fun a b => a <<< (b % 64)) _ (fun _ _ => rfl)
      i64_rule_tac

theorem sim_shrUI64 (F : Nat) : InstrSim P code F .shrUI64 :=
  sim_bin_of P code (inst := .shrUI64) (t := .i64) (op := Instr.lsrv) (fun x y => x >>> (y % 64))
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply i64_bin_case (fun a b => a >>> (b % 64)) _ (fun _ _ => rfl)
      i64_rule_tac

/-! ## The arithmetic shift -/

theorem gen_shrS {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {is : List Instr}
    {fin : Option (List ValueType)} (hg : genInstr E ctl σ a .shrSI64 = .ok (is, fin)) :
    curBase ctl + 2 ≤ σ.length ∧ σ.length - 1 < 26 ∧
      is = sarCode (regOf (σ.length - 2)) (regOf (σ.length - 1)) ∧
      fin = some (.i64 :: σ.drop 2) := by
  by_cases hc : σ.length < curBase ctl + 2
  · simp [genInstr, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases hlt : σ.length - 1 < 26
  · simp [genInstr, hc, opReg_ok hlt, opReg_ok (show σ.length - 2 < 26 by omega), bind,
      Except.bind, pure, Except.pure] at hg
    exact ⟨by omega, hlt, hg.1.symm, hg.2.symm⟩
  · obtain ⟨e, he⟩ := opReg_error hlt
    by_cases hlt2 : σ.length - 2 < 26
    · simp [genInstr, hc, he, opReg_ok hlt2, bind, Except.bind] at hg
    · obtain ⟨e2, he2⟩ := opReg_error hlt2
      simp [genInstr, hc, he2, bind, Except.bind] at hg

/-- `sarCode x y`, placed at `a`, leaves `Signed64.sar` of the registers `x` and `y` in `x` and
changes no other register but the scratch register. -/
theorem run_sar {ms : State} {a : UInt64} {x y : Fin 32} (hx : x.val < 31) (hxs : x ≠ scratch)
    (hys : y ≠ scratch) (hxy : x ≠ y) (hcode : CodeAt code a (sarCode x y)) (hpc : ms.pc = a) :
    ∃ ms', Reach P code ms ms' ∧ ms'.pc = after a 5 ∧
      ms'.x x = ProofKit.Signed64.sar (ms.x x) (ms.x y) ∧
      (∀ q, q ≠ x → q ≠ scratch → ms'.x q = ms.x q) ∧
      ms'.sp = ms.sp ∧ ms'.mem = ms.mem ∧ ms'.io = ms.io := by
  have c0 := hcode 0 (by simp [sarCode])
  have c1 := hcode 1 (by simp [sarCode])
  have c2 := hcode 2 (by simp [sarCode])
  have c3 := hcode 3 (by simp [sarCode])
  have c4 := hcode 4 (by simp [sarCode])
  simp only [sarCode, List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3 c4
  have hsc : scratch.val < 31 := by decide
  have h31 : ∀ s : State, s.x 31 = 0 := fun s => by unfold State.x; rw [dite_eq_right (by decide)]
  let s1 : State :=
    { ms.setX scratch (ms.x x >>> UInt64.ofNat (63 : Fin 64).val) with pc := ms.pc + 4 }
  let s2 : State := { s1.setX scratch (s1.x 31 - s1.x scratch) with pc := s1.pc + 4 }
  let s3 : State := { s2.setX x (s2.x x ^^^ s2.x scratch) with pc := s2.pc + 4 }
  let s4 : State := { s3.setX x (s3.x x >>> (s3.x y % 64)) with pc := s3.pc + 4 }
  let s5 : State := { s4.setX x (s4.x x ^^^ s4.x scratch) with pc := s4.pc + 4 }
  have p1 : s1.pc = after a 1 := by simp [s1, hpc, after]
  have p2 : s2.pc = after a 2 := by
    show s1.pc + 4 = _; rw [p1]; exact (after_succ a 1).symm
  have p3 : s3.pc = after a 3 := by
    show s2.pc + 4 = _; rw [p2]; exact (after_succ a 2).symm
  have p4 : s4.pc = after a 4 := by
    show s3.pc + 4 = _; rw [p3]; exact (after_succ a 3).symm
  let S : UInt64 := (0 : UInt64) - (ms.x x >>> 63)
  have k1 : s1.x scratch = ms.x x >>> 63 := State.x_setX_same (s := ms) hsc
  have x1 : s1.x x = ms.x x := State.x_setX_ne (s := ms) (Ne.symm hxs)
  have y1 : s1.x y = ms.x y := State.x_setX_ne (s := ms) (Ne.symm hys)
  have k2 : s2.x scratch = S := by
    have e : s2.x scratch = s1.x 31 - s1.x scratch := State.x_setX_same (s := s1) hsc
    rw [e, h31, k1]
  have x2 : s2.x x = ms.x x := (State.x_setX_ne (s := s1) (Ne.symm hxs)).trans x1
  have y2 : s2.x y = ms.x y := (State.x_setX_ne (s := s1) (Ne.symm hys)).trans y1
  have k3 : s3.x scratch = S := (State.x_setX_ne (s := s2) hxs).trans k2
  have x3 : s3.x x = ms.x x ^^^ S := by
    have e : s3.x x = s2.x x ^^^ s2.x scratch := State.x_setX_same (s := s2) hx
    rw [e, x2, k2]
  have y3 : s3.x y = ms.x y := (State.x_setX_ne (s := s2) hxy).trans y2
  have k4 : s4.x scratch = S := (State.x_setX_ne (s := s3) hxs).trans k3
  have x4 : s4.x x = (ms.x x ^^^ S) >>> (ms.x y % 64) := by
    have e : s4.x x = s3.x x >>> (s3.x y % 64) := State.x_setX_same (s := s3) hx
    rw [e, x3, y3]
  have keep : ∀ q, q ≠ x → q ≠ scratch → s5.x q = ms.x q := fun q hq hqs =>
    (State.x_setX_ne (s := s4) (Ne.symm hq)).trans
      ((State.x_setX_ne (s := s3) (Ne.symm hq)).trans
        ((State.x_setX_ne (s := s2) (Ne.symm hq)).trans
          ((State.x_setX_ne (s := s1) (Ne.symm hqs)).trans
            (State.x_setX_ne (s := ms) (Ne.symm hqs)))))
  refine ⟨s5, reach_exec P code (by rw [hpc]; exact c0) rfl
    (reach_exec P code (by rw [p1]; exact c1) rfl
      (reach_exec P code (by rw [p2]; exact c2) rfl
        (reach_exec P code (by rw [p3]; exact c3) rfl
          (reach_exec P code (by rw [p4]; exact c4) rfl (.refl _))))), ?_, ?_, keep, ?_, ?_, ?_⟩
  · show s4.pc + 4 = _; rw [p4]; exact (after_succ a 4).symm
  · have e : s5.x x = s4.x x ^^^ s4.x scratch := State.x_setX_same (s := s4) hx
    rw [e, x4, k4, ← UInt64.shiftRight_eq_shiftRight_mod]
    rfl
  · show (s4.setX x _).sp = ms.sp
    simp [s4, s3, s2, s1]
  · show (s4.setX x _).mem = ms.mem
    simp [s4, s3, s2, s1]
  · show (s4.setX x _).io = ms.io
    simp [s4, s3, s2, s1]

theorem sim_shrSI64 (F : Nat) : InstrSim P code F .shrSI64 := by
  intro E ctl σ a is fin hg hcode hb hctl α m st sl ms hinv hsr h64 hpc _ _ _ _
  obtain ⟨hhb, hlt, rfl, rfl⟩ := gen_shrS hg
  have hh := hinv.len
  have hty := hinv.types
  generalize hσl : σ.length = h at *
  cases F with
  | zero => rw [ProofKit.execOne_zero]; exact .inr trivial
  | succ f =>
      have hcase : (∃ va vb vs, sl.values = vb :: va :: vs ∧ ∀ wa wb, ValRel va wa →
          ValRel vb wb → ∃ vr, ValRel vr (ProofKit.Signed64.sar wa wb) ∧ HasType .i64 vr ∧
            execOne (f + 1) m st sl .shrSI64 = .Fallthrough st { sl with values := vr :: vs }) ∨
          ∃ msg, execOne (f + 1) m st sl .shrSI64 = .Invalid msg := by
        apply i64_bin_case
          (fun a b => UInt64.ofNat (BitVec.sshiftRight a.toBitVec (b % 64).toNat).toNat) _
          (fun a b => (ProofKit.Signed64.shrS_sar a b).symm)
        i64_rule_tac
      rcases hcase with ⟨va, vb, vs, hvs, hex⟩ | ⟨msg, hex⟩
      · have hvl : vs.length = h - 2 := by rw [hvs] at hh; simp at hh; omega
        have hst := hinv.stack
        rw [hvs] at hst
        have hb' : ValRel vb (ms.x (regOf (h - 1))) := by
          have := hst.top
          rwa [show (va :: vs).length = h - 1 by simp; omega] at this
        have ha' : ValRel va (ms.x (regOf (h - 2))) := by
          have := hst.pop.top
          rwa [hvl] at this
        obtain ⟨vr, hvr, htr, hex'⟩ := hex _ _ ha' hb'
        rw [hex']
        rw [hvs] at hty
        have hne : regOf (h - 2) ≠ regOf (h - 1) := fun e =>
          absurd (regOf_inj (h - 2) (by omega) (h - 1) hlt e) (by omega)
        obtain ⟨ms', hr, hp, hres, hkeep, hsp, hmem, hout⟩ :=
          run_sar P code (regOf_lt_31 _ (by omega)) (regOf_ne_scratch _ (by omega))
            (regOf_ne_scratch _ hlt) hne hcode hpc
        apply res_outcome P code hvr (vs := vs) htr (hty.drop 2) hinv hsr (by omega) (by omega)
          hst.pop.pop hr
        · rw [hp]; rfl
        · rw [hvl, hres]
        · intro k hk
          exact hkeep _ (fun e => absurd (regOf_inj k (by omega) (h - 2) (by omega) e) (by omega))
            (regOf_ne_scratch k (by omega))
        · exact hkeep 18 (Ne.symm (regOf_ne_18 _ (by omega))) (by decide)
        · exact hkeep 17 (Ne.symm (regOf_ne_17 _ (by omega))) (by decide)
        · exact hsp
        · exact hmem
        · exact hout
      · rw [hex]; exact .inr trivial

theorem sim_and (F : Nat) : InstrSim P code F .and :=
  sim_bin_of P code (inst := .and) (t := .i32) (op := Instr.andReg) (fun x y => x &&& y)
    (fun _ _ _ _ => by simp only [genInstr])
    (fun _ _ _ _ => rfl) fun f α m st sl => by
      by_cases h : ∃ a b vs, sl.values = .i32 a :: .i32 b :: vs
      · obtain ⟨a, b, vs, hv⟩ := h
        refine .inl ⟨.i32 b, .i32 a, vs, hv, fun wa wb ha hb => ⟨.i32 (a &&& b), ?_, trivial, ?_⟩⟩
        · simp only [ValRel] at ha hb ⊢
          rw [ha, hb, UInt32.toUInt64_and, UInt64.and_comm]
        · simp only [execOne.eq_def, hv]
      · refine .inr ?_
        simp only [execOne.eq_def]
        split
        · rename_i a b vs hv
          exact absurd ⟨a, b, vs, hv⟩ h
        · exact ⟨_, rfl⟩

theorem gen_wrap {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {is : List Instr}
    {fin : Option (List ValueType)} (hg : genInstr E ctl σ a .wrapI64 = .ok (is, fin)) :
    curBase ctl + 1 ≤ σ.length ∧ σ.length - 1 < 26 ∧
      is = [.orrW (regOf (σ.length - 1)) 31 (regOf (σ.length - 1))] ∧
      fin = some (.i32 :: σ.tail) := by
  by_cases hc : σ.length < curBase ctl + 1
  · simp [genInstr, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases hlt : σ.length - 1 < 26
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
  intro E ctl σ a is fin hg hcode hb hctl α m st sl ms hinv hsr h64 hpc _ _ _ _
  obtain ⟨hhb, hlt, rfl, rfl⟩ := gen_wrap hg
  have hh := hinv.len
  have hty := hinv.types
  generalize hσl : σ.length = h at *
  cases F with
  | zero => rw [ProofKit.execOne_zero]; exact .inr trivial
  | succ f =>
      simp only [execOne.eq_def]
      split
      · rename_i x vs hv
        have hvl : vs.length = h - 1 := by rw [hv] at hh; simp at hh; omega
        have hst := hinv.stack
        rw [hv] at hst
        rw [hv] at hty
        have hx : ms.x (regOf (h - 1)) = x := by
          have := hst.top; rw [hvl] at this; exact this
        have hc0 : code ms.pc = some (encode (.orrW (regOf (h - 1)) 31 (regOf (h - 1)))) := by
          rw [hpc]; simpa [after_zero] using hcode 0 (by simp)
        have hr := reach_exec P code hc0 rfl (.refl _)
        have hd := regOf_lt_31 (h - 1) hlt
        apply res_outcome P code (v := .i32 (UInt32.ofNat (x.toNat % 2 ^ 32)))
          (w := (UInt32.ofNat (x.toNat % 2 ^ 32)).toUInt64) rfl
          (vs := vs) (t := .i32) trivial hty.tail hinv hsr (by omega) (by omega) hst.pop hr
        · show ms.pc + 4 = _
          rw [hpc]; simp [after]
        · rw [State.x_withPc, hvl, State.x_setX_same hd]
          have h31 : ms.x 31 = 0 := by unfold State.x; rw [dite_eq_right (by decide)]
          rw [h31, hx, wrap_val]
        · intro k hk
          rw [State.x_withPc, State.x_setX_ne (fun e => absurd
            (regOf_inj (h - 1) hlt k (by omega) e) (by omega))]
        · rw [State.x_withPc, State.x_setX_ne (regOf_ne_18 _ hlt)]
        · rw [State.x_withPc, State.x_setX_ne (regOf_ne_17 _ hlt)]
        · exact State.setX_sp
        · exact State.setX_mem
        · exact State.setX_io
      · exact .inr trivial

end LeanExe.A64
