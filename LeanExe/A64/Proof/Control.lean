import LeanExe.A64.Proof.Traps

/-!
The simulation of the branches `br`, `br_if`, and `ret`.  A branch to a construct moves the
value that it carries, if any, from the top of the stack to the register of the construct's base
height with `ORR` and branches with `B` to the construct's target, so the machine reaches the
target with the carried value where the construct's code after the target expects it and with the
registers below the base unchanged.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

theorem gen_branchTo {t : Ctl} {h : Nat} {a : UInt64} {is : List Instr}
    (hg : branchTo t h a = .ok is) :
    t.base + t.arity ≤ h ∧ t.arity ≤ 1 ∧ (t.arity = 1 → h - 1 < 26 ∧ t.base < 26) ∧
      ∃ f, bField (after a t.arity) t.target = .ok f ∧
        is = (if t.arity = 1 then [mov (regOf t.base) (regOf (h - 1))] else []) ++ [.b f] := by
  obtain ⟨tg, ar, bs⟩ := t
  unfold branchTo at hg
  simp only at hg ⊢
  by_cases hc : h < bs + ar ∨ ar > 1
  · simp [hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  refine ⟨by omega, by omega, ?_⟩
  by_cases h1 : ar = 1
  · subst h1
    have hlt : ¬ h < bs + 1 := by omega
    by_cases hb : bs < 26
    · by_cases hh : h - 1 < 26
      · cases hf : bField (after a 1) tg with
        | error e =>
            simp [hlt, opReg_ok hb, opReg_ok hh, hf, bind, Except.bind, pure, Except.pure] at hg
        | ok f =>
            simp [hlt, opReg_ok hb, opReg_ok hh, hf, bind, Except.bind, pure, Except.pure] at hg
            subst hg
            exact ⟨fun _ => ⟨hh, hb⟩, f, rfl, by simp⟩
      · obtain ⟨e, he⟩ := opReg_error hh
        simp [hlt, opReg_ok hb, he, bind, Except.bind] at hg
    · obtain ⟨e, he⟩ := opReg_error hb
      simp [hlt, he, bind, Except.bind] at hg
  · have h0 : ar = 0 := by omega
    subst h0
    have hlt : ¬ h < bs := by omega
    cases hf : bField (after a 0) tg with
    | error e => simp [hlt, hf, bind, Except.bind, pure, Except.pure] at hg
    | ok f =>
        simp [hlt, hf, bind, Except.bind, pure, Except.pure] at hg
        subst hg
        exact ⟨fun e => absurd e (by decide), f, rfl, by simp⟩

/-- The run of a branch to `t` from a related state whose stack `vs` has its height `h`: the
machine reaches `t.target` with the value that the branch carries in the register of `t.base`
and the registers below `t.base`, `SP`, the memory, and the UART's output unchanged. -/
theorem run_branchTo {t : Ctl} {h : Nat} {a : UInt64} {is : List Instr} {ms : State}
    {vs : List Value} (hg : branchTo t h a = .ok is) (hcode : CodeAt code a is)
    (hpc : ms.pc = a) (hst : StackRel ms vs) (hh : vs.length = h) :
    ∃ ms', Reach P code ms ms' ∧ ms'.pc = t.target ∧ Kept t vs ms' ∧ Frame t.base ms ms' ∧
      ms'.sp = ms.sp ∧ ms'.mem = ms.mem ∧ ms'.out = ms.out := by
  obtain ⟨hle, ha1, hregs, f, hf, rfl⟩ := gen_branchTo hg
  have h26 := hst.1
  by_cases h1 : t.arity = 1
  · obtain ⟨hh1, hb⟩ := hregs h1
    simp only [h1, ite_true, List.singleton_append] at hcode
    have c0 := (CodeAt.cons.mp hcode).1
    have c1 := (CodeAt.cons.mp (CodeAt.cons.mp hcode).2).1
    let s1 : State := { ms.setX (regOf t.base) (ms.x 31 ||| ms.x (regOf (h - 1))) with
      pc := ms.pc + 4 }
    have p1 : s1.pc = after a 1 := by simp [s1, hpc, after]
    have hx31 : ms.x 31 = 0 := by unfold State.x; rw [dite_eq_right (by decide)]
    refine ⟨{ s1 with pc := s1.pc + sext 26 f.val * 4 },
      reach_exec P code (by rw [hpc]; exact c0) rfl
        (reach_exec P code (by rw [p1]; exact c1) rfl (.refl _)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show s1.pc + sext 26 f.val * 4 = t.target
      rw [p1, ← bField_target hf, h1]
    · refine ⟨by omega, by omega, fun j hj => ?_⟩
      have hj0 : j = 0 := by omega
      subst hj0
      show ValRel _ ((ms.setX (regOf t.base) (ms.x 31 ||| ms.x (regOf (h - 1)))).x
        (regOf (t.base + 0)))
      rw [Nat.add_zero, State.x_setX_same (regOf_lt_31 _ hb), hx31, UInt64.zero_or]
      have htop := hst.2 (h - 1) (by omega)
      have : vs.reverse[h - 1]'(by simp; omega) = vs[0]'(by omega) := by
        rw [List.getElem_reverse]; congr 1; omega
      rw [this] at htop
      simpa [h1] using htop
    · intro k hk
      show (ms.setX (regOf t.base) _).x (regOf k) = ms.x (regOf k)
      exact State.x_setX_ne (fun e => absurd (regOf_inj t.base hb k (by omega) e) (by omega))
    · show (ms.setX (regOf t.base) _).sp = ms.sp; exact State.setX_sp
    · show (ms.setX (regOf t.base) _).mem = ms.mem; exact State.setX_mem
    · show (ms.setX (regOf t.base) _).out = ms.out; exact State.setX_out
  · have h0 : t.arity = 0 := by omega
    simp only [h1, ite_false, List.nil_append] at hcode
    have c0 := (CodeAt.cons.mp hcode).1
    refine ⟨{ ms with pc := ms.pc + sext 26 f.val * 4 },
      reach_exec P code (by rw [hpc]; exact c0) rfl (.refl _), ?_, ?_, fun _ _ => rfl, rfl, rfl,
      rfl⟩
    · show ms.pc + sext 26 f.val * 4 = t.target
      rw [hpc, ← bField_target hf, h0, after_zero]
    · exact ⟨by omega, by omega, fun j hj => absurd hj (by omega)⟩

end LeanExe.A64
