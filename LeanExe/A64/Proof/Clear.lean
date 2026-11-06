import LeanExe.A64.Clear
import LeanExe.A64.Proof.Memory

/-!
`run_clearCheck` runs the comparison and the conditional branch of `clearLoop`, `run_clearPass`
runs a pass that stores a zero word at X0, and `run_clearLoop` runs the whole loop by induction on
the number of words from X0 to X1.  X0 starts at or below X1 and reaches it in steps of 8, so no
addition wraps around and the unsigned comparison leaves the loop exactly at X1.  No premise
bounds X1 further, since every address that the loop forms lies at or below it.
-/

namespace LeanExe.A64

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- The target of the `B.HS` of `clearLoop` at `a`: the word after the loop. -/
theorem clear_exit (a : UInt64) : after a 1 + sext 19 (4 : Fin 524288).val * 4 = after a 5 := by
  have h : 4 * UInt64.ofNat 1 + sext 19 (4 : Fin 524288).val * 4 = 4 * UInt64.ofNat 5 := by
    decide
  rw [after, after, UInt64.add_assoc, h]

/-- The target of the `B` of `clearLoop` at `a`: the `CMP` at `a`. -/
theorem clear_back (a : UInt64) : after a 4 + sext 26 (67108860 : Fin 67108864).val * 4 = a := by
  have h : 4 * UInt64.ofNat 4 + sext 26 (67108860 : Fin 67108864).val * 4 = 0 := by decide
  rw [after, UInt64.add_assoc, h, UInt64.add_zero]

/-- The comparison and the conditional branch of `clearLoop` at `a`, from `u` at `a`: the machine
reaches the word after the loop when X1 is at or below X0 and the `STR` otherwise, and it keeps
the registers, SP, the memory, and the output. -/
theorem run_clearCheck {a : UInt64} {u : State} (hcode : CodeAt code a clearLoop)
    (hpc : u.pc = a) :
    ∃ u', Reach P code u u' ∧ u'.pc = (if u.x 1 ≤ u.x 0 then after a 5 else after a 2) ∧
      (∀ q, u'.x q = u.x q) ∧ u'.sp = u.sp ∧ u'.mem = u.mem ∧ u'.out = u.out := by
  have c0 : code (after a 0) = some (encode (.subsReg 31 0 1)) := hcode 0 (by decide)
  have c1 : code (after a 1) = some (encode (.bcond 2 4)) := hcode 1 (by decide)
  rw [after_zero] at c0
  let u1 : State := { u.subs 31 (u.x 0) (u.x 1) with pc := u.pc + 4 }
  have e1 : LeanExe.A64.exec P (.subsReg 31 0 1) u = some u1 := rfl
  let u2 : State := { u1 with
    pc := if u1.condHolds 2 then u1.pc + sext 19 (4 : Fin 524288).val * 4 else u1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.bcond 2 4) u1 = some u2 := rfl
  have p1 : u1.pc = after a 1 := by simp [u1, hpc, after]
  have hx1 : ∀ q, u1.x q = u.x q := by
    intro q
    show (u.setX 31 (u.x 0 - u.x 1)).x q = u.x q
    unfold State.setX; rw [ite_eq_right (by decide)]
  have hc : u1.condHolds 2 = decide (u.x 1 ≤ u.x 0) := by
    rw [condHolds_2]; exact subs_c u (u.x 0) (u.x 1)
  refine ⟨u2, reach_exec P code (by rw [hpc]; exact c0) e1
    (reach_exec P code (by rw [p1]; exact c1) e2 (.refl _)), ?_, hx1, ?_, ?_, ?_⟩
  · show (if u1.condHolds 2 then u1.pc + sext 19 (4 : Fin 524288).val * 4 else u1.pc + 4) = _
    rw [hc, p1]
    by_cases h : u.x 1 ≤ u.x 0
    · rw [ite_eq_left (decide_eq_true h), ite_eq_left h]
      exact clear_exit a
    · rw [ite_eq_right (show ¬ decide (u.x 1 ≤ u.x 0) = true by simpa using h), ite_eq_right h]
      exact (after_succ a 1).symm
  · simp [u2, u1, State.subs]
  · simp [u2, u1, State.subs]
  · simp [u2, u1, State.subs]

/-- A pass of `clearLoop` at `a`, from `u` at `a` with X0 below X1 and the 8 bytes from X0 in
Normal memory: the machine stores a zero word at X0, adds 8 to X0, and returns to `a`, and it
keeps the other registers, SP, and the output. -/
theorem run_clearPass {a : UInt64} {u : State} (hcode : CodeAt code a clearLoop)
    (hpc : u.pc = a) (hlt : ¬ u.x 1 ≤ u.x 0)
    (hmap : ∀ k < 8, P.normal (u.x 0 + UInt64.ofNat k) = true) :
    ∃ u', Reach P code u u' ∧ u'.pc = a ∧ u'.x 0 = u.x 0 + 8 ∧
      (∀ q, q ≠ 0 → u'.x q = u.x q) ∧ u'.sp = u.sp ∧ u'.mem = store64 u.mem (u.x 0) 0 ∧
      u'.out = u.out := by
  obtain ⟨u2, r2, p2, x2, sp2, mem2, out2⟩ := run_clearCheck P code hcode hpc
  rw [ite_eq_right hlt] at p2
  have c2 : code (after a 2) = some (encode (.str 31 0 0)) := hcode 2 (by decide)
  have c3 : code (after a 3) = some (encode (.addImm 0 0 8)) := hcode 3 (by decide)
  have c4 : code (after a 4) = some (encode (.b 67108860)) := hcode 4 (by decide)
  have hd : (0 : Fin 32).val < 31 := by decide
  let u3 : State := { u2 with
    mem := store64 u2.mem (u2.x 0 + UInt64.ofNat (8 * 0)) (u2.x 31), pc := u2.pc + 4 }
  have e3 : LeanExe.A64.exec P (.str 31 0 0) u2 = some u3 :=
    exec_str_base P (t := 31) (i := 0) (by decide) hd fun k hk => by
      rw [x2, Nat.mul_zero, Nat.zero_add]
      exact hmap k hk
  let u4 : State := { u3.setX 0 (u3.x 0 + UInt64.ofNat 8) with pc := u3.pc + 4 }
  have e4 : LeanExe.A64.exec P (.addImm 0 0 8) u3 = some u4 := by
    simp only [exec, State.xsp_eq_x hd, State.setXsp_eq_setX hd]
    rfl
  have p3 : u3.pc = after a 3 := by
    show u2.pc + 4 = _
    rw [p2, ← after_succ]
  have p4 : u4.pc = after a 4 := by
    show u3.pc + 4 = _
    rw [p3, ← after_succ]
  have e5 : LeanExe.A64.exec P (.b 67108860) u4 = some { u4 with pc := a } := by
    show some { u4 with pc := u4.pc + sext 26 (67108860 : Fin 67108864).val * 4 } = _
    rw [p4, clear_back]
  refine ⟨{ u4 with pc := a }, r2.trans (reach_exec P code (by rw [p2]; exact c2) e3
      (reach_exec P code (by rw [p3]; exact c3) e4
        (reach_exec P code (by rw [p4]; exact c4) e5 (.refl _)))), rfl, ?_, fun q hq => ?_, ?_,
    ?_, ?_⟩
  · rw [State.x_withPc]
    show (u3.setX 0 (u3.x 0 + UInt64.ofNat 8)).x 0 = _
    rw [State.x_setX_same hd]
    show u2.x 0 + UInt64.ofNat 8 = u.x 0 + UInt64.ofNat 8
    rw [x2]
  · rw [State.x_withPc]
    show (u3.setX 0 (u3.x 0 + UInt64.ofNat 8)).x q = _
    rw [State.x_setX_ne (Ne.symm hq)]
    exact x2 q
  · show (u3.setX 0 (u3.x 0 + UInt64.ofNat 8)).sp = _
    rw [State.setX_sp]
    exact sp2
  · show (u3.setX 0 (u3.x 0 + UInt64.ofNat 8)).mem = _
    rw [State.setX_mem]
    show store64 u2.mem (u2.x 0 + UInt64.ofNat (8 * 0)) (u2.x 31) = _
    rw [mem2, x2, x2, Nat.mul_zero, add_ofNat_zero]
    rfl
  · show (u3.setX 0 (u3.x 0 + UInt64.ofNat 8)).out = _
    rw [State.setX_out]
    exact out2

/-- The run of `clearLoop` at `a` from `s` at `a` with `lo` in X0 and `hi` in X1, where `lo` is
at or below `hi` as natural numbers, `hi - lo` is a multiple of 8, and every byte from `lo` below
`hi` is Normal memory: the machine reaches the word after the loop with every byte from `lo` below
`hi` zero, every other byte kept, `hi` in X0, and the other registers, SP, and the output kept. -/
theorem run_clearLoop {a lo hi : UInt64} {s : State} (hcode : CodeAt code a clearLoop)
    (hpc : s.pc = a) (h0 : s.x 0 = lo) (h1 : s.x 1 = hi) (hle : lo.toNat ≤ hi.toNat)
    (h8 : (hi.toNat - lo.toNat) % 8 = 0)
    (hmap : ∀ j < hi.toNat - lo.toNat, P.normal (lo + UInt64.ofNat j) = true) :
    ∃ s', Reach P code s s' ∧ s'.pc = after a 5 ∧
      (∀ b, (b - lo).toNat < (hi - lo).toNat → s'.mem b = 0) ∧
      (∀ b, ¬ (b - lo).toNat < (hi - lo).toNat → s'.mem b = s.mem b) ∧
      s'.x 0 = hi ∧ (∀ q, q ≠ 0 → s'.x q = s.x q) ∧ s'.sp = s.sp ∧ s'.out = s.out := by
  obtain ⟨m, hm⟩ : ∃ m, hi.toNat = lo.toNat + 8 * m :=
    ⟨(hi.toNat - lo.toNat) / 8, by omega⟩
  clear hle h8
  have hhi := hi.toNat_lt
  induction m generalizing s lo with
  | zero =>
      have hlh : lo = hi := UInt64.toNat_inj.mp (by omega)
      subst hlh
      obtain ⟨u, r, p, hx, hsp, hmem, hout⟩ := run_clearCheck P code hcode hpc
      rw [h0, h1, ite_eq_left (UInt64.le_refl _)] at p
      refine ⟨u, r, p, fun b hb => ?_, fun b _ => by rw [hmem], by rw [hx, h0],
        fun q _ => hx q, hsp, hout⟩
      simp at hb
  | succ m ih =>
      have hlo8 : (lo + 8).toNat = lo.toNat + 8 := by
        rw [UInt64.toNat_add, show (8 : UInt64).toNat = 8 from rfl]
        simp only [Nat.reducePow] at *
        omega
      have hlt : ¬ s.x 1 ≤ s.x 0 := by
        rw [h0, h1, UInt64.le_iff_toNat_le]
        omega
      obtain ⟨u, r, p, hx0, hxq, hsp, hmem, hout⟩ := run_clearPass P code hcode hpc hlt
        fun k hk => by
          rw [h0]
          exact hmap k (by omega)
      obtain ⟨s', r', p', hz, hk, hx', hxq', hsp', hout'⟩ := ih (s := u) (lo := lo + 8) p
        (by rw [hx0, h0]) (by rw [hxq 1 (by decide), h1])
        (fun j hj => by
          rw [show (8 : UInt64) = UInt64.ofNat 8 from rfl, add_ofNat_add]
          exact hmap (8 + j) (by omega))
        (by omega)
      have hin : ∀ b : UInt64, (b - lo).toNat < (hi - lo).toNat ↔
          b - lo < 8 ∨ (b - (lo + 8)).toNat < (hi - (lo + 8)).toNat := by
        intro b
        have hb := b.toNat_lt
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub b lo, UInt64.toNat_sub hi lo,
          UInt64.toNat_sub b (lo + 8), UInt64.toNat_sub hi (lo + 8), hlo8,
          show (8 : UInt64).toNat = 8 from rfl]
        simp only [Nat.reducePow] at *
        constructor <;> intro h <;> omega
      refine ⟨s', r.trans r', p', fun b hb => ?_, fun b hb => ?_, hx', fun q hq => ?_,
        by rw [hsp', hsp], by rw [hout', hout]⟩
      · by_cases hb' : (b - (lo + 8)).toNat < (hi - (lo + 8)).toNat
        · exact hz b hb'
        · rw [hk b hb', hmem, h0]
          simp [store64, ((hin b).mp hb).resolve_right hb']
      · rw [hk b fun h => hb ((hin b).mpr (.inr h)), hmem, h0]
        exact store64_other _ _ _ _ fun h => hb ((hin b).mpr (.inl h))
      · rw [hxq' q hq, hxq q hq]

end LeanExe.A64
