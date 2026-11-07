import LeanExe.M7.Proof.Branch

/-!
The code of the area's accesses in the model: the loads and stores at a register plus an offset,
the constants of two halves that address the area, and the bounds test of a 64-bit access.
`run_bounds` states that the test, from a state whose address in the slot at `x` has a high word
of 0 and a low word that `off` leaves within the size word, falls through both branches to the
stub of an access outside memory and leaves the memory's base plus the address in r2.  Code whose
every instruction takes 4 bytes splits at any of its instructions, `CodeAt.split_wide`.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-! ## Code of 4-byte forms -/

/-- The instruction takes 4 bytes. -/
def Instr.wide (i : Instr) : Bool := i.size == 4

theorem codeSize_of_wide : ∀ {is : List Instr}, is.all Instr.wide = true →
    codeSize is = 4 * is.length
  | [], _ => rfl
  | i :: is, h => by
      simp only [List.all_cons, Bool.and_eq_true, Instr.wide, beq_iff_eq] at h
      rw [codeSize_cons, h.1, codeSize_of_wide h.2, List.length_cons]
      omega

/-- The code of `l1 ++ l2`, where every instruction of `l1` takes 4 bytes, places `l2` the
length of `l1` in instructions on. -/
theorem CodeAt.split_wide {a : UInt32} {l1 l2 : List Instr} (h : CodeAt code a (l1 ++ l2))
    (hw : l1.all Instr.wide = true) : CodeAt code a l1 ∧ CodeAt code (after a l1.length) l2 := by
  obtain ⟨h1, h2⟩ := CodeAt.append.mp h
  rw [codeSize_of_wide hw, ← after_eq] at h2
  exact ⟨h1, h2⟩

/-! ## Loads and stores at a register plus an offset -/

theorem exec_ldr {s : State} {t n : Fin 8} {o : Fin 4096}
    (h : WordOk P (s.r n + UInt32.ofNat o.val)) :
    exec P σ (.ldr t n o) s =
      some { s.setR t (load32 s.mem (s.r n + UInt32.ofNat o.val)) with pc := s.pc + 4 } := by
  obtain ⟨h4, hd, hm⟩ := h
  simp only [exec, loadWord, h4, hd, hm, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true,
    Option.map_some]

theorem exec_str {s : State} {t n : Fin 8} {o : Fin 4096}
    (h : WordOk P (s.r n + UInt32.ofNat o.val)) :
    exec P σ (.str t n o) s =
      some { s with
        mem := store32 s.mem (s.r n + UInt32.ofNat o.val) (s.r t), pc := s.pc + 4 } := by
  obtain ⟨h4, hd, hm⟩ := h
  simp only [exec, storeWord, h4, hd, hm, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true,
    Option.map_some]

/-! ## Register code -/

/-- Register code executes as `slotRun` states it. -/
theorem execSeq_reg : ∀ {xs : List Instr} {s : State}, xs.all Instr.regForm = true →
    execSeq P σ xs s = some (slotRun P σ xs s)
  | [], _, _ => rfl
  | i :: xs, s, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      have hi := h.1
      simp only [Instr.regForm, Bool.and_eq_true, Option.isNone_iff_eq_none] at hi
      obtain ⟨he, -⟩ := exec_slotStep (P := P) (σ := σ) (s := s) hi.1
        (fun o ho => by rw [hi.2] at ho; cases ho)
      simp only [execSeq, he, Option.bind_some, slotRun_cons]
      exact execSeq_reg h.2

theorem movWord_regForm (d : Fin 8) (w : UInt32) : (movWord d w).all Instr.regForm = true := rfl

theorem movWord_wide (d : Fin 8) (w : UInt32) : (movWord d w).all Instr.wide = true := rfl

/-- `movWord d w` sets register `d` to `w` and keeps the other registers. -/
theorem slotRun_movWord (d : Fin 8) (w : UInt32) (s : State) :
    (slotRun P σ (movWord d w) s).r d = w ∧
      ∀ e, e ≠ d → (slotRun P σ (movWord d w) s).r e = s.r e := by
  have hw := toNat_lt32 w
  simp only [movWord, Instr.movwOf, Instr.movtOf, slotRun_cons, slotRun_nil, slotStep, exec,
    Option.getD_some]
  refine ⟨?_, fun e he => ?_⟩
  · rw [State.r_withPc, State.r_setR_same, State.r_withPc, State.r_setR_same,
      imm16_field (by omega), imm16_field (by omega), movt_word (by omega) (by omega),
      show w.toNat % 65536 + w.toNat / 65536 * 65536 = w.toNat by omega, UInt32.ofNat_toNat]
  · rw [State.r_withPc, State.r_setR_ne _ _ he, State.r_withPc, State.r_setR_ne _ _ he]

/-! ## Flags of the bounds test -/

/-- The carry of `CMP x, y` is set exactly when `y ≤ x`. -/
theorem carry_cmp (x y : UInt32) :
    (addWithCarry x (~~~y) true).2.1 = decide (y.toNat ≤ x.toNat) := by
  have h := toNat_carry x (~~~y) true
  rw [toNat_not32] at h
  have := toNat_lt32 x
  have := toNat_lt32 y
  simp only [Bool.toNat_true] at h
  by_cases hy : y.toNat ≤ x.toNat
  · rw [decide_eq_true hy]
    exact eq_true_of_toNat (by omega)
  · rw [decide_eq_false hy]
    exact eq_false_of_toNat (by omega)

theorem condHolds_hi (s : State) : s.condHolds 8 = (s.cFlag && !s.zFlag) := by cases s; rfl

/-- `HI` after `CMP x, y` fails when `x` is at most `y`. -/
theorem hi_false {x y : UInt32} (h : x.toNat ≤ y.toNat) :
    (decide (y.toNat ≤ x.toNat) && !(x - y == 0)) = false := by
  by_cases hyx : y.toNat ≤ x.toNat
  · have : x = y := UInt32.toNat_inj.mp (by omega)
    subst this
    simp
  · simp [hyx]

/-! ## The bounds test -/

theorem gen_bounds {trap : UInt32} {x off : Nat} {a : UInt32} {bs : List Instr}
    (hg : boundsCode trap x off a = .ok bs) :
    ∃ (h0 : x < 4096) (h1 : x + 4 < 4096) (o1 o2 : Int),
      o1 % 2 = 0 ∧ -1048576 ≤ o1 ∧ o1 < 1048576 ∧ after a 8 + 4 + UInt32.ofInt o1 = trap ∧
      o2 % 2 = 0 ∧ -1048576 ≤ o2 ∧ o2 < 1048576 ∧ after a 10 + 4 + UInt32.ofInt o2 = trap ∧
      bs = [.ldrSp 0 ⟨x, h0⟩, .ldrSp 1 ⟨x + 4, h1⟩] ++ movWord 2 areaHeader ++
        [.ldr 3 2 0, .movwOf 4 off, .subReg 0 3 3 4, .cmpImm 1 0, .bcondTo condNE o1,
          .cmpReg 0 3, .bcondTo condHI o2] ++ movWord 2 areaMemory ++ [.addLsl 0 2 2 0 0] := by
  unfold boundsCode at hg
  simp only [except_bind_ok, except_pure_ok] at hg
  obtain ⟨l1, hl1, i1, hi1, i2, hi2, rfl⟩ := hg
  obtain ⟨h0, h1, rfl⟩ := ldPair_ok hl1
  obtain ⟨o1, rfl, q1, q2, q3, q4⟩ := bcondAt_ok hi1
  obtain ⟨o2, rfl, r1, r2, r3, r4⟩ := bcondAt_ok hi2
  exact ⟨h0, h1, o1, o2, q1, q2, q3, q4, r1, r2, r3, r4, rfl⟩

/-- The bounds test of an access at the offset `off` from the address whose words lie in the slot
at the offset `x` from SP: when the address's high word is 0 and its low word plus `off` is at
most the size word, which is at least `off`, the model passes both branches to the stub and
reaches the test's end with the memory's base plus the address in r2 and with what `Keeps` names
unchanged. -/
theorem run_bounds {trap : UInt32} {x off : Nat} {a : UInt32} {bs : List Instr}
    (hg : boundsCode trap x off a = .ok bs) (hc : CodeAt code a bs) {s : State} (hpc : s.pc = a)
    (hw0 : WordOk P (s.sp + UInt32.ofNat x)) (hw1 : WordOk P (s.sp + UInt32.ofNat (x + 4)))
    (hwh : WordOk P areaHeader) (hoff : off < 65536)
    (hhi : load32 s.mem (s.sp + UInt32.ofNat (x + 4)) = 0)
    (hin : (load32 s.mem (s.sp + UInt32.ofNat x)).toNat + off ≤
      (load32 s.mem areaHeader).toNat) :
    ∃ t, Reach P σ code s t ∧ t.pc = after a 14 ∧ Keeps s t ∧
      t.r 2 = areaMemory + load32 s.mem (s.sp + UInt32.ofNat x) := by
  obtain ⟨h0, h1, o1, o2, q1, q2, q3, q4, p1, p2, p3, p4, rfl⟩ := gen_bounds hg
  let L1 : List Instr := [.ldrSp 0 ⟨x, h0⟩, .ldrSp 1 ⟨x + 4, h1⟩] ++ movWord 2 areaHeader
  let L2 : List Instr := [.movwOf 4 off, .subReg 0 3 3 4, .cmpImm 1 0]
  let L4 : List Instr := movWord 2 areaMemory ++ [.addLsl 0 2 2 0 0]
  have hc' : CodeAt code a (L1 ++ [Instr.ldr 3 2 0] ++ (L2 ++ [Instr.bcondTo condNE o1]) ++
      ([Instr.cmpReg 0 3] ++ [Instr.bcondTo condHI o2]) ++ L4) := hc
  obtain ⟨c4, cL4⟩ := hc'.split_wide rfl
  obtain ⟨c3, cB2⟩ := c4.split_wide rfl
  obtain ⟨c2, cB1⟩ := c3.split_wide rfl
  obtain ⟨c1, cLd⟩ := c2.split_wide rfl
  rw [show (L1 ++ [Instr.ldr 3 2 0] ++ (L2 ++ [Instr.bcondTo condNE o1]) ++
    ([Instr.cmpReg 0 3] ++ [Instr.bcondTo condHI o2])).length = 11 from rfl] at cL4
  rw [show (L1 ++ [Instr.ldr 3 2 0] ++ (L2 ++ [Instr.bcondTo condNE o1])).length = 9 from rfl]
    at cB2
  rw [show (L1 ++ [Instr.ldr 3 2 0]).length = 5 from rfl] at cB1
  rw [show L1.length = 4 from rfl] at cLd
  -- the address's words and the header's address
  have hok : SlotsOk P s.sp L1 := slotsOk_ld hw0 (slotsOk_ld hw1 (slotsOk_reg rfl _))
  rw [← hpc] at c1
  obtain ⟨r1, pc1, sp1, lr1, tr1, rd1, hi1⟩ := run_slots (σ := σ) hok c1
  generalize hu1 : slotRun P σ L1 s = u1 at r1 pc1 sp1 lr1 tr1 rd1 hi1
  have hm1 : u1.mem = s.mem := by rw [← hu1]; rfl
  have hu1r : u1.r 0 = load32 s.mem (s.sp + UInt32.ofNat x) ∧ u1.r 1 = 0 ∧ u1.r 2 = areaHeader := by
    rw [← hu1]
    obtain ⟨e2, e⟩ := slotRun_movWord (P := P) (σ := σ) 2 areaHeader
      { ({ s.setR 0 (load32 s.mem (s.sp + UInt32.ofNat x)) with pc := s.pc + 4 } : State).setR 1
        (load32 s.mem (s.sp + UInt32.ofNat (x + 4))) with pc := s.pc + 4 + 4 }
    refine ⟨?_, ?_, e2⟩
    · rw [show L1 = [.ldrSp 0 ⟨x, h0⟩, .ldrSp 1 ⟨x + 4, h1⟩] ++ movWord 2 areaHeader from rfl,
        slotRun_append]
      rw [show slotRun P σ [Instr.ldrSp 0 ⟨x, h0⟩, Instr.ldrSp 1 ⟨x + 4, h1⟩] s =
        { ({ s.setR 0 (load32 s.mem (s.sp + UInt32.ofNat x)) with pc := s.pc + 4 } : State).setR 1
          (load32 s.mem (s.sp + UInt32.ofNat (x + 4))) with pc := s.pc + 4 + 4 } from rfl,
        e 0 (by decide)]
      state_simp
    · rw [show L1 = [.ldrSp 0 ⟨x, h0⟩, .ldrSp 1 ⟨x + 4, h1⟩] ++ movWord 2 areaHeader from rfl,
        slotRun_append]
      rw [show slotRun P σ [Instr.ldrSp 0 ⟨x, h0⟩, Instr.ldrSp 1 ⟨x + 4, h1⟩] s =
        { ({ s.setR 0 (load32 s.mem (s.sp + UInt32.ofNat x)) with pc := s.pc + 4 } : State).setR 1
          (load32 s.mem (s.sp + UInt32.ofNat (x + 4))) with pc := s.pc + 4 + 4 } from rfl,
        e 1 (by decide)]
      state_simp
      exact hhi
  obtain ⟨hr0, hr1, hr2⟩ := hu1r
  have hk1 : Keeps s u1 := ⟨sp1, lr1, hi1, hm1, tr1, rd1⟩
  have hpc1 : u1.pc = after a 4 := by rw [pc1, hpc, show L1.length = 4 from rfl, after_eq]
  -- the size word
  rw [← hpc1] at cLd
  have e2 := exec_ldr (P := P) (σ := σ) (s := u1) (t := 3) (n := 2) (o := 0)
    (by rw [hr2]; simpa using hwh)
  generalize hu2 : ({ u1.setR 3 (load32 u1.mem (u1.r 2 + UInt32.ofNat (0 : Fin 4096).val)) with
    pc := u1.pc + 4 } : State) = u2 at e2
  have r2 : Reach P σ code u1 u2 := reach_exec cLd e2 (.refl _)
  have hk2 : Keeps u1 u2 := by rw [← hu2]; exact ((Keeps.refl u1).setR _ _).withPc _
  have hpc2 : u2.pc = after a 5 := by rw [← hu2, State.pc_withPc, hpc1]; addr_after
  have hu2r : u2.r 0 = load32 s.mem (s.sp + UInt32.ofNat x) ∧ u2.r 1 = 0 ∧
      u2.r 3 = load32 s.mem areaHeader := by
    rw [← hu2]
    refine ⟨?_, ?_, ?_⟩
    · rw [State.r_withPc, State.r_setR_ne _ _ (by decide), hr0]
    · rw [State.r_withPc, State.r_setR_ne _ _ (by decide), hr1]
    · rw [State.r_withPc, State.r_setR_same, hr2, hm1]
      simp
  -- `MOVW`, `SUB`, `CMP r1, #0`, and `BNE`
  rw [← hpc2] at cB1
  obtain ⟨u3, r3, hk3, hrg3, hpc3⟩ := run_branch (P := P) (σ := σ) (s := u2)
    (xs := L2) (c := condNE) trap (after a 9) rfl rfl cB1 (execSeq_reg rfl) q1 q2 q3
    (by rw [hpc2, ← q4, show codeSize L2 = 12 from rfl]; addr_after)
    (by rw [hpc2, show codeSize L2 = 12 from rfl]; addr_after)
  have hz3 : (slotRun P σ L2 u2).condHolds condNE = false := by
    simp only [L2, Instr.movwOf, slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some]
    state_simp
    rw [cmp_imm0, hu2r.2.1]
    rfl
  rw [hz3] at hpc3
  have hu3r : u3.r 0 = load32 s.mem (s.sp + UInt32.ofNat x) ∧
      u3.r 3 = load32 s.mem areaHeader - UInt32.ofNat off := by
    rw [State.r_of_regs hrg3, State.r_of_regs hrg3]
    simp only [L2, Instr.movwOf, slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some]
    state_simp
    rw [imm16_field hoff, sub_addWithCarry, hu2r.1, hu2r.2.2]
    exact ⟨rfl, rfl⟩
  -- `CMP r0, r3` and `BHI`
  rw [show cond false trap (after a 9) = after a 9 from rfl] at hpc3
  rw [← hpc3] at cB2
  obtain ⟨u4, r4, hk4, hrg4, hpc4⟩ := run_branch (P := P) (σ := σ) (s := u3)
    (xs := [Instr.cmpReg 0 3]) (c := condHI) trap (after a 11) rfl rfl cB2 (execSeq_reg rfl)
    p1 p2 p3 (by rw [hpc3, ← p4]; addr_after) (by rw [hpc3]; addr_after)
  have hsz : off ≤ (load32 s.mem areaHeader).toNat := by omega
  have hz4 : (slotRun P σ [Instr.cmpReg 0 3] u3).condHolds condHI = false := by
    simp only [slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some]
    rw [show condHI = (8 : Fin 14) from rfl, condHolds_hi, State.cFlag_withPc,
      State.zFlag_withPc, State.cFlag_setNZCV', State.zFlag_setNZCV', carry_cmp,
      sub_addWithCarry, hu3r.1, hu3r.2]
    apply hi_false
    rw [UInt32.toNat_sub_of_le _ _ (by
      rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNat']
      simp only [Nat.reducePow]
      have := toNat_lt32 (load32 s.mem areaHeader)
      omega), UInt32.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  rw [hz4, show cond false trap (after a 11) = after a 11 from rfl] at hpc4
  have hu4r : u4.r 0 = load32 s.mem (s.sp + UInt32.ofNat x) := by
    rw [State.r_of_regs hrg4]
    simp only [slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some]
    state_simp
    exact hu3r.1
  -- the memory's base plus the address
  rw [← hpc4] at cL4
  obtain ⟨r5, pc5, hk5⟩ := run_block (P := P) (σ := σ) (is := L4) (s := u4) rfl rfl cL4
    (execSeq_reg rfl)
  refine ⟨slotRun P σ L4 u4, r1.trans (r2.trans (r3.trans (r4.trans r5))), ?_,
    hk1.trans (hk2.trans (hk3.trans (hk4.trans hk5))), ?_⟩
  · rw [pc5, hpc4, show codeSize L4 = 12 from rfl]
    addr_after
  · rw [show L4 = movWord 2 areaMemory ++ [Instr.addLsl 0 2 2 0 0] from rfl, slotRun_append]
    obtain ⟨e2, e⟩ := slotRun_movWord (P := P) (σ := σ) 2 areaMemory u4
    simp only [Instr.addLsl, slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some]
    state_simp
    rw [e2, e 0 (by decide), hu4r, shl_zero, add_addWithCarry]

end LeanExe.M7
