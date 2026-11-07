import LeanExe.A64.Proof.StartupCode
import LeanExe.A64.Proof.Lift
import LeanExe.A64.Proof.Table
import LeanExe.A64.Proof.Boot
import LeanExe.A64.Proof.Straight
import LeanExe.A64.Proof.Traps

/-!
The run of the startup's exit in the boot model, from its instruction 55 to the `HVC #0` at 65,
with translation on in the covered configuration.  The exit sets X1 to `uartAddr` and stores the
low byte of X0 there, a run of the program model that `bootReach_of_reach` lifts.  `DSB SY` then
completes the store by the rule `sys`, whose fetch succeeds because the TLBs are clean and the
table maps the instruction's address as executable Normal memory.  Last, the exit sets X0 to the
function number of PSCI's `SYSTEM_OFF`, `0x84000008`, in a second lifted run, which writes no
byte to the UART and so keeps `uartDone`.
-/

namespace LeanExe.A64

/-- The exit's instructions as the startup places them: `movImm 1 uartAddr` from instruction 55,
`STRB` and `DSB SY` at 59 and 60, `movImm 0 0x84000008` from 61, `HVC #0` at 65, and the exit
word at 67, a branch to instruction 55. -/
theorem startupCode_exit {L : Layout} {is : List Instr} (hg : startupCode L = .ok is)
    {code : UInt64 → Option UInt32} (hcode : CodeAt code (L.image + 64) is) :
    CodeAt code (after (L.image + 64) 55) (movImm 1 uartAddr) ∧
      CodeAt code (after (L.image + 64) 59) [.strb 0 1 0, .dsbSy] ∧
      CodeAt code (after (L.image + 64) 61) (movImm 0 0x84000008) ∧
      code (after (L.image + 64) 65) = some (encode .hvc0) ∧
      ∃ back, bField L.base (after (L.image + 64) 55) = .ok back ∧
        code (after (L.image + 64) 67) = some (encode (.b back)) := by
  obtain ⟨_, _, vec, tab, clr, fin, stk, ar, _, back, -, -, hv, ht, hc, hf, hs, ha, -, hb, his⟩ :=
    startupCode_ok hg
  rw [his] at hcode
  obtain ⟨c4, cT⟩ := (CodeAt.append (code := code)).mp hcode
  obtain ⟨c3, cM0⟩ := (CodeAt.append (code := code)).mp c4
  obtain ⟨c2, cS⟩ := (CodeAt.append (code := code)).mp c3
  obtain ⟨-, cM1⟩ := (CodeAt.append (code := code)).mp c2
  have hm : ∀ d v, (movImm d v).length = 4 := fun _ _ => rfl
  simp only [List.length_append, List.length_cons, List.length_nil, hm, addrOf_length hv,
    addrOf_length ht, addrOf_length hc, addrOf_length hf, addrOf_length hs, addrOf_length ha,
    show clearLoop.length = 5 from rfl] at cT cM0 cS cM1
  have c67 : code (after (L.image + 64) 67) = some (encode (.b back)) := by
    have := cT 2 (by simp)
    rw [after_after] at this
    exact this
  exact ⟨cM1, cS, cM0, ((CodeAt.cons (code := code)).mp cT).1, back, hb, c67⟩

/-- The run of the exit in the boot model.  From a state after the startup, with the program
counter at the exit's first instruction, SP_EL1 selected, the written system registers in effect,
translation on in the covered configuration with clean TLBs, the table in memory at `TTBR0_EL1`
and protected by `R`, and every address of the code mapped as executable Normal memory, the
machine reaches the `HVC #0` with X0 holding PSCI's `SYSTEM_OFF`, the low byte of X0 appended to
the UART's output, and every store to the UART complete. -/
theorem boot_exit {L : Layout} {is : List Instr} (hg : startupCode L = .ok is)
    {code : UInt64 → Option UInt32} (hcode : CodeAt code (L.image + 64) is)
    {h : Hw} {R : UInt64 → Bool} {b : Boot} (hsp : b.spSel = true)
    (hsync : b.written = b.eff) (hcov : b.eff.covered h = true) (htlb : b.tlb = .clean)
    (hm : ∀ j (hj : j < 32), b.core.mem (b.eff.ttbr0 + UInt64.ofNat j) = tableBytes[j])
    (hR : ∀ j < 32, R (b.eff.ttbr0 + UInt64.ofNat j) = true)
    (hx : ∀ a w, code a = some w → ∃ x, classify h b.eff b.core.mem a = some (.normal x true))
    (hpc : b.core.pc = after (L.image + 64) 55) :
    ∃ b', BootReach h R code b b' ∧ b'.core.pc = after (L.image + 64) 65 ∧
      code b'.core.pc = some (encode .hvc0) ∧ b'.core.x 0 = 0x84000008 ∧
      b'.core.out = b.core.out ++ [(b.core.x 0).toUInt8] ∧ b'.uartDone = true := by
  obtain ⟨c1, cS, c0, cH, -⟩ := startupCode_exit hg hcode
  have hu := classify_uart hcov hm
  obtain ⟨s1, r1, p1, x1, k1, -, m1, o1⟩ :=
    run_movImm (b.platform h R) code (d := 1) (by decide) c1 hpc
  rw [after_after] at p1
  let s2 : State := { s1 with out := s1.out ++ [(s1.x 0).toUInt8], pc := s1.pc + 4 }
  have e2 : exec (b.platform h R) (.strb 0 1 0) s1 = some s2 := by
    have hb : s1.xsp 1 = (b.platform h R).uart := (State.xsp_eq_x (by decide)).trans x1
    simp [exec, hb, State.spAligned, s2]
  have rb2 := bootReach_of_reach hsp hsync hcov htlb hu hR hx
    (r1.trans (reach_exec _ _ (by rw [p1]; exact ((CodeAt.cons (code := code)).mp cS).1) e2
      (.refl _)))
  let b3 : Boot := { b with core := { s2 with pc := s2.pc + 4 }, uartDone := true }
  have hm3 : b3.core.mem = b.core.mem := m1
  have st3 : BootStep h R code
      { b with core := s2, uartDone := b.uartDone && s2.out == b.core.out } b3 := by
    have hc : code s2.pc = some (encode .dsbSy) := by
      have := ((CodeAt.cons (code := code)).mp ((CodeAt.cons (code := code)).mp cS).2).1
      rw [after_after] at this
      show code (s1.pc + 4) = _
      rw [p1, ← after_succ]
      exact this
    have hf : ∃ x, classify h b.eff s2.mem s2.pc = some (.normal x true) := by
      show ∃ x, classify h b.eff s1.mem s2.pc = some (.normal x true)
      rw [m1]
      exact hx _ _ hc
    refine .sys hc (decode_encode _) (.inl hsp) (.inr ⟨htlb, hf⟩)
      (.inr ⟨htlb, by rw [hsync]; exact hf⟩) ?_
    simp [sysExec, b3, htlb]
  have hp3 : b3.core.pc = after (L.image + 64) 61 := by
    show s1.pc + 4 + 4 = _
    rw [p1, ← after_succ, ← after_succ]
  obtain ⟨s4, r4, p4, x4, -, -, -, o4⟩ :=
    run_movImm (b3.platform h R) code (d := 0) (by decide) c0 hp3
  have rb4 := bootReach_of_reach (b := b3) hsp hsync hcov htlb (by rw [hm3]; exact hu) hR
    (by rw [hm3]; exact hx) r4
  rw [after_after] at p4
  refine ⟨_, rb2.trans (.next st3 rb4), p4, by show code s4.pc = _; rw [p4]; exact cH,
    x4, ?_, ?_⟩
  · show s4.out = _
    rw [o4]
    show s1.out ++ [(s1.x 0).toUInt8] = _
    rw [o1, k1 0 (by decide)]
  · show (true && s4.out == b3.core.out) = true
    rw [o4, beq_self_eq_true, Bool.and_true]

/-- The exit word, which the trap stubs reach, branches to the exit, instruction 55. -/
theorem run_exitWord {P : Platform} {code : UInt64 → Option UInt32} {L : Layout}
    {is : List Instr} (hs : startupCode L = .ok is) (hc : CodeAt code (L.image + 64) is)
    (hbase : L.base = after (L.image + 64) 67) {s : State} (hpc : s.pc = L.base) :
    Reach P code s { s with pc := after (L.image + 64) 55 } := by
  obtain ⟨-, -, -, -, back, hb, cb⟩ := startupCode_exit hs hc
  have he : LeanExe.A64.exec P (.b back) s = some { s with pc := after (L.image + 64) 55 } := by
    show some { s with pc := s.pc + sext 26 back.val * 4 } = _
    rw [hpc, bField_target hb]
  exact reach_exec P code (by rw [hpc, hbase]; exact cb) he (.refl _)

end LeanExe.A64
