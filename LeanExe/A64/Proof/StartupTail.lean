import LeanExe.A64.Proof.ImageRun
import LeanExe.A64.Proof.Addr
import LeanExe.A64.Proof.Clear

/-!
The run of the startup's tail, from instruction 40, after the `ISB` that puts translation in
effect, to `main`.  With the MMU on, the tail sets X0 and X1 to the first byte that it clears and
the area's end, clears them with `clearLoop`, sets SP to the stack's top through X1, sets X17 to
the area, and calls `main` with `BL`, which leaves the exit's address in X30.  The run is one of
the program model under the boot state's platform, which `bootReach_of_reach` lifts.
-/

namespace LeanExe.A64

/-- The tail's instructions as the startup places them. -/
theorem startupCode_tail {L : Layout} {is : List Instr} (hg : startupCode L = .ok is)
    {code : UInt64 → Option UInt32} (hcode : CodeAt code (L.image + 64) is) :
    ∃ clr fin stk ar call,
      addrOf 0 (after (L.image + 64) 40) L.clear = .ok clr ∧
      CodeAt code (after (L.image + 64) 40) clr ∧
      addrOf 1 (after (L.image + 64) 42) L.areaEnd = .ok fin ∧
      CodeAt code (after (L.image + 64) 42) fin ∧
      CodeAt code (after (L.image + 64) 44) clearLoop ∧
      addrOf 1 (after (L.image + 64) 49) L.stackTop = .ok stk ∧
      CodeAt code (after (L.image + 64) 49) stk ∧
      code (after (L.image + 64) 51) = some (encode (.addImm 31 1 0)) ∧
      addrOf 17 (after (L.image + 64) 52) L.area = .ok ar ∧
      CodeAt code (after (L.image + 64) 52) ar ∧
      bField (after (L.image + 64) 54) (after L.base 1) = .ok call ∧
      code (after (L.image + 64) 54) = some (encode (.bl call)) := by
  obtain ⟨_, _, vec, tab, clr, fin, stk, ar, call, _, -, -, hv, ht, hc, hf, hs, ha, hcall, -,
    his⟩ := startupCode_ok hg
  rw [his] at hcode
  obtain ⟨c1, -⟩ := (CodeAt.append (code := code)).mp hcode
  obtain ⟨c2, -⟩ := (CodeAt.append (code := code)).mp c1
  obtain ⟨c3, -⟩ := (CodeAt.append (code := code)).mp c2
  obtain ⟨c4, -⟩ := (CodeAt.append (code := code)).mp c3
  obtain ⟨c5, cBl⟩ := (CodeAt.append (code := code)).mp c4
  obtain ⟨c6, cAr⟩ := (CodeAt.append (code := code)).mp c5
  obtain ⟨c7, cAdd⟩ := (CodeAt.append (code := code)).mp c6
  obtain ⟨c8, cStk⟩ := (CodeAt.append (code := code)).mp c7
  obtain ⟨c9, cLoop⟩ := (CodeAt.append (code := code)).mp c8
  obtain ⟨c10, cFin⟩ := (CodeAt.append (code := code)).mp c9
  obtain ⟨-, cClr⟩ := (CodeAt.append (code := code)).mp c10
  have hm : ∀ d v, (movImm d v).length = 4 := fun _ _ => rfl
  simp only [List.length_append, List.length_cons, List.length_nil, hm, addrOf_length hv,
    addrOf_length ht, addrOf_length hc, addrOf_length hf, addrOf_length hs, addrOf_length ha,
    show clearLoop.length = 5 from rfl] at cBl cAr cAdd cStk cLoop cFin cClr
  exact ⟨clr, fin, stk, ar, call, hc, cClr, hf, cFin, cLoop, hs, cStk,
    ((CodeAt.cons (code := code)).mp cAdd).1, ha, cAr, hcall,
    ((CodeAt.cons (code := code)).mp cBl).1⟩

/-- The run of the tail in the program model under any platform `P` whose Normal memory covers the
bytes that the loop clears: the machine reaches `main` with X30 at the exit, X17 at the area, SP
at the stack's top, the cleared bytes 0, every other byte kept, and the output kept. -/
theorem run_startup_tail (P : Platform) {L : Layout} {is : List Instr}
    (hs : startupCode L = .ok is) {code : UInt64 → Option UInt32}
    (hc : CodeAt code (L.image + 64) is) {s : State} (hpc : s.pc = after (L.image + 64) 40)
    (hcl : L.clear.toNat ≤ L.areaEnd.toNat) (h8 : (L.areaEnd.toNat - L.clear.toNat) % 8 = 0)
    (hnorm : ∀ j < L.areaEnd.toNat - L.clear.toNat,
      P.normal (L.clear + UInt64.ofNat j) = true) :
    ∃ s', Reach P code s s' ∧ s'.pc = after L.base 1 ∧ s'.x 30 = after (L.image + 64) 55 ∧
      s'.x 17 = L.area ∧ s'.sp = L.stackTop ∧ s'.out = s.out ∧
      (∀ a, (a - L.clear).toNat < (L.areaEnd - L.clear).toNat → s'.mem a = 0) ∧
      (∀ a, ¬ (a - L.clear).toNat < (L.areaEnd - L.clear).toNat → s'.mem a = s.mem a) := by
  obtain ⟨clr, fin, stk, ar, call, hclr, cclr, hfin, cfin, cloop, hstk, cstk, cadd, har, car,
    hcall, cbl⟩ := startupCode_tail hs hc
  obtain ⟨s1, r1, p1, x1, k1, sp1, m1, o1⟩ := run_addrOf P code hclr (by decide) cclr hpc
  rw [after_after] at p1
  obtain ⟨s2, r2, p2, x2, k2, sp2, m2, o2⟩ := run_addrOf P code hfin (by decide) cfin p1
  rw [after_after] at p2
  obtain ⟨s3, r3, p3, hz, hk, -, k3, sp3, o3⟩ := run_clearLoop P code cloop p2
    (by rw [k2 0 (by decide), x1]) x2 hcl h8 hnorm
  rw [after_after] at p3
  obtain ⟨s4, r4, p4, x4, k4, sp4, m4, o4⟩ := run_addrOf P code hstk (by decide) cstk p3
  rw [after_after] at p4
  let s5 : State := { s4 with sp := s4.x 1 + UInt64.ofNat 0, pc := s4.pc + 4 }
  have e5 : LeanExe.A64.exec P (.addImm 31 1 0) s4 = some s5 := by
    simp only [exec, State.xsp_eq_x (show (1 : Fin 32).val < 31 by decide), State.setXsp]
    rfl
  have p5 : s5.pc = after (L.image + 64) 52 := by
    show s4.pc + 4 = _
    rw [p4, ← after_succ]
  obtain ⟨s6, r6, p6, x6, k6, sp6, m6, o6⟩ := run_addrOf P code har (by decide) car p5
  rw [after_after] at p6
  let s7 : State := { s6.setX 30 (s6.pc + 4) with pc := s6.pc + sext 26 call.val * 4 }
  have e7 : LeanExe.A64.exec P (.bl call) s6 = some s7 := rfl
  refine ⟨s7, r1.trans (r2.trans (r3.trans (r4.trans (reach_exec P code (by rw [p4]; exact cadd)
      e5 (r6.trans (reach_exec P code (by rw [p6]; exact cbl) e7 (.refl _))))))), ?_, ?_, ?_, ?_,
    ?_, fun a ha => ?_, fun a ha => ?_⟩
  · show s6.pc + sext 26 call.val * 4 = _
    rw [p6, bField_target hcall]
  · rw [State.x_withPc, State.x_setX_same (by decide), p6, ← after_succ]
  · rw [State.x_withPc, State.x_setX_ne (by decide)]
    exact x6
  · show (s6.setX 30 (s6.pc + 4)).sp = _
    rw [State.setX_sp, sp6]
    show s4.x 1 + UInt64.ofNat 0 = _
    rw [x4, add_ofNat_zero]
  · show (s6.setX 30 (s6.pc + 4)).out = _
    rw [State.setX_out, o6]
    show s4.out = _
    rw [o4, o3, o2, o1]
  · show (s6.setX 30 (s6.pc + 4)).mem a = _
    rw [State.setX_mem, m6]
    show s4.mem a = _
    rw [m4, hz a ha]
  · show (s6.setX 30 (s6.pc + 4)).mem a = _
    rw [State.setX_mem, m6]
    show s4.mem a = _
    rw [m4, hk a ha, m2, m1]

end LeanExe.A64
