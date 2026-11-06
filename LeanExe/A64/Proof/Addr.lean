import LeanExe.A64.Proof.StartupCode
import LeanExe.A64.Proof.Straight
import LeanExe.A64.Proof.Memory

/-!
The run of the `ADRP` and `ADD` that `addrOf` emits.  `ADRP` adds to the program counter's page the
signed difference of the target's page and the program counter's page, which `addrOf` encodes
in 21 bits, and `ADD` adds the target's offset in its page, so the register holds the target.
-/

namespace LeanExe.A64

/-- The value of `addrOf`'s `ADRP` at `here` plus its `ADD`'s offset is the target. -/
theorem addrOf_value {here target : UInt64} {pages : Int} (hlo : -(2 ^ 20) ≤ pages)
    (hhi : pages < 2 ^ 20)
    (hp : pages = Int.ofNat (target.toNat / 4096) - Int.ofNat (here.toNat / 4096)) :
    here - here % 4096 + sext 21 (4 * ((pages % (2 ^ 21 : Int)).toNat / 4 % 524288) +
      (pages % (2 ^ 21 : Int)).toNat % 4) * 4096 + UInt64.ofNat (target.toNat % 4096) =
      target := by
  simp only [Int.ofNat_eq_coe] at hp
  apply UInt64.toNat_inj.mp
  have ht := target.toNat_lt
  have hh := here.toNat_lt
  have hfI : (((pages % (2 ^ 21 : Int)).toNat : Nat) : Int) = pages % (2 ^ 21 : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  generalize (pages % (2 ^ 21 : Int)).toNat = f at *
  have hf : f < 2 ^ 21 := by omega
  rw [show 4 * (f / 4 % 524288) + f % 4 = f by omega]
  have hm : (here % 4096).toNat = here.toNat % 4096 := UInt64.toNat_mod _ _
  have hs : (here - here % 4096).toNat = here.toNat - here.toNat % 4096 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hm]; omega), hm]
  have e4 : (4096 : UInt64).toNat = 4096 := rfl
  unfold sext
  split
  · rename_i hlt
    simp only [UInt64.toNat_add, UInt64.toNat_mul, hs, e4, UInt64.toNat_ofNat'] at *
    simp only [Nat.reducePow] at *
    omega
  · rename_i hlt
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_sub, hs, e4,
      UInt64.toNat_ofNat'] at *
    simp only [Nat.reducePow] at *
    omega

/-- `addrOf`'s two instructions at `here` set register `d`, below 31, to the target and keep the
other registers, SP, the memory, and the output. -/
theorem run_addrOf (P : Platform) (code : UInt64 → Option UInt32) {d : Fin 32}
    {here target : UInt64} {is : List Instr} (hg : addrOf d here target = .ok is) (hd : d.val < 31)
    (hc : CodeAt code here is) {s : State} (hpc : s.pc = here) :
    ∃ s', Reach P code s s' ∧ s'.pc = after here 2 ∧ s'.x d = target ∧
      (∀ q, q ≠ d → s'.x q = s.x q) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.out = s.out := by
  obtain ⟨pages, hlo, hhi, hp, rfl⟩ := addrOf_ok hg
  have c0 := hc 0 (by simp)
  have c1 := hc 1 (by simp)
  rw [after_zero] at c0
  let v := s.pc - s.pc % 4096 + sext 21 (4 * ((pages % (2 ^ 21 : Int)).toNat / 4 % 524288) +
    (pages % (2 ^ 21 : Int)).toNat % 4) * 4096
  let s1 : State := { s.setX d v with pc := s.pc + 4 }
  have e1 : LeanExe.A64.exec P (.adrp d ⟨(pages % (2 ^ 21 : Int)).toNat % 4,
      Nat.mod_lt _ (by decide)⟩ ⟨(pages % (2 ^ 21 : Int)).toNat / 4 % 524288,
      Nat.mod_lt _ (by decide)⟩) s = some s1 := rfl
  let s2 : State := { s1.setX d (s1.x d + UInt64.ofNat (target.toNat % 4096)) with
    pc := s1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.addImm d d ⟨target.toNat % 4096, Nat.mod_lt _ (by decide)⟩) s1 =
      some s2 := by
    simp only [exec, State.xsp_eq_x hd, State.setXsp_eq_setX hd]
    rfl
  have p1 : s1.pc = after here 1 := by simp [s1, hpc, after]
  refine ⟨s2, reach_exec P code (by rw [hpc]; exact c0) e1
    (reach_exec P code (by rw [p1]; exact c1) e2 (.refl _)), ?_, ?_, fun q hq => ?_, ?_, ?_, ?_⟩
  · show s1.pc + 4 = _
    rw [p1, ← after_succ]
  · rw [State.x_withPc, State.x_setX_same hd]
    show (s.setX d v).x d + _ = _
    rw [State.x_setX_same hd]
    show s.pc - s.pc % 4096 + _ + _ = _
    rw [hpc]
    exact addrOf_value hlo hhi hp
  · rw [State.x_withPc, State.x_setX_ne (Ne.symm hq)]
    show (s.setX d v).x q = _
    rw [State.x_setX_ne (Ne.symm hq)]
  · show (s1.setX d _).sp = _
    rw [State.setX_sp]
    exact State.setX_sp
  · show (s1.setX d _).mem = _
    rw [State.setX_mem]
    exact State.setX_mem
  · show (s1.setX d _).out = _
    rw [State.setX_out]
    exact State.setX_out

end LeanExe.A64
