import LeanExe.A64.Proof.Arith

/-!
The simulation of the f64 forms.  An f64 value lies in the register of its height as its word, as
an `i64` does, so `i64ReinterpretF64` and `f64ReinterpretI64` emit nothing and change only the
type.  `genFBin` moves the words of the two values on top into D0 and D1 with `FMOV`, computes
`FADD`, `FSUB`, `FMUL`, or `FDIV` into D0, and moves D0's word into the register of the lower
value; the model's meaning of each form is Talos's function, so the register then holds Talos's
result.  `f64Sqrt` goes through D0 in the same way, `f64ConvertI64U` converts the register's word
into D0 with `UCVTF`, and `f64Abs` adds the register to itself, which drops the sign bit, and
shifts the sum right by 1, which gives Talos's `IEEE64.abs`.  `genFCmp` moves the two words into
D0 and D1, compares them with `FCMP`, and sets the lower value's register with `CSINC XZR, XZR`
and a condition: `f64Eq` with `NE`, `f64Lt` with `PL`, and `f64Le` with `HI`, each the inverse of
the condition that holds after `FCMP` when the comparison gives 1, `EQ`, `MI`, or `LS`.  No f64
form changes a general register but the one of its result, SP, the memory, or the UART's output,
and the D registers and the flags lie outside the relation.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-! ## Runs of the f64 code -/

/-- The code `fBin op x y`, for an `op` that sets its destination D register to `g` of the words
of its operand D registers, sets `x`, below 31, to `g` of the words of `x` and `y`, and keeps the
other general registers, SP, the memory, and the output. -/
theorem run_fBin {op : Fin 32 → Fin 32 → Fin 32 → Instr} (g : UInt64 → UInt64 → UInt64)
    (hexec : ∀ (s : State) (d n m : Fin 32), LeanExe.A64.exec P (op d n m) s =
      some { s.setD d (g (s.dregs n) (s.dregs m)) with pc := s.pc + 4 })
    {s : State} {a : UInt64} {x y : Fin 32} (hx : x.val < 31)
    (hcode : CodeAt code a (fBin op x y)) (hpc : s.pc = a) :
    ∃ s', Reach P code s s' ∧ s'.pc = after a 4 ∧ s'.x x = g (s.x x) (s.x y) ∧
      (∀ q, q ≠ x → s'.x q = s.x q) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.out = s.out := by
  have c0 := hcode 0 (by simp [fBin])
  have c1 := hcode 1 (by simp [fBin])
  have c2 := hcode 2 (by simp [fBin])
  have c3 := hcode 3 (by simp [fBin])
  simp only [fBin, List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3
  let s1 : State := { s.setD 0 (s.x x) with pc := s.pc + 4 }
  let s2 : State := { s1.setD 1 (s1.x y) with pc := s1.pc + 4 }
  let s3 : State := { s2.setD 0 (g (s2.dregs 0) (s2.dregs 1)) with pc := s2.pc + 4 }
  let s4 : State := { s3.setX x (s3.dregs 0) with pc := s3.pc + 4 }
  have p1 : s1.pc = after a 1 := by
    show s.pc + 4 = _
    rw [hpc, after_succ, after_zero]
  have p2 : s2.pc = after a 2 := by
    show s1.pc + 4 = _
    rw [p1, ← after_succ]
  have p3 : s3.pc = after a 3 := by
    show s2.pc + 4 = _
    rw [p2, ← after_succ]
  refine ⟨s4, reach_exec P code (by rw [hpc]; exact c0) rfl
      (reach_exec P code (by rw [p1]; exact c1) rfl
        (reach_exec P code (by rw [p2]; exact c2) (hexec s2 0 0 1)
          (reach_exec P code (by rw [p3]; exact c3) rfl (.refl _)))), ?_, ?_, fun q hq => ?_,
    ?_, ?_, ?_⟩
  · show s3.pc + 4 = _
    rw [p3, ← after_succ]
  · show (s3.setX x (s3.dregs 0)).x x = _
    rw [State.x_setX_same hx]
    show (s2.setD 0 (g (s2.dregs 0) (s2.dregs 1))).dregs 0 = _
    rw [State.dregs_setD_same]
    show g ((s1.setD 1 (s1.x y)).dregs 0) ((s1.setD 1 (s1.x y)).dregs 1) = _
    rw [State.dregs_setD_ne s1 (r := 1) (q := 0) _ (by decide), State.dregs_setD_same]
    show g ((s.setD 0 (s.x x)).dregs 0) (s.x y) = _
    rw [State.dregs_setD_same]
  · show (s3.setX x (s3.dregs 0)).x q = s3.x q
    exact State.x_setX_ne (Ne.symm hq)
  · show (s3.setX x (s3.dregs 0)).sp = s3.sp
    exact State.setX_sp
  · show (s3.setX x (s3.dregs 0)).mem = s3.mem
    exact State.setX_mem
  · show (s3.setX x (s3.dregs 0)).out = s3.out
    exact State.setX_out

/-- What the code `ops r` of a unary operation does: from every state at its start, with `r` below
31, it reaches its end with `g` of `r`'s word in `r` and the other general registers, SP, the
memory, and the output unchanged. -/
def UnRuns (ops : Fin 32 → List Instr) (g : UInt64 → UInt64) : Prop :=
  ∀ (s : State) (a : UInt64) (r : Fin 32), r.val < 31 → CodeAt code a (ops r) → s.pc = a →
    ∃ s', Reach P code s s' ∧ s'.pc = after a (ops r).length ∧ s'.x r = g (s.x r) ∧
      (∀ q, q ≠ r → s'.x q = s.x q) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.out = s.out

theorem runs_none : UnRuns P code (fun _ => []) fun w => w :=
  fun s a _ _ _ hpc => ⟨s, .refl _, by rw [hpc]; exact (after_zero a).symm, rfl,
    fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The code `FMOV D0, Xr`, `op D0, D0`, `FMOV Xr, D0`, for an `op` that sets its destination D
register to `g` of the word of its operand D register, computes `g` on the word of `r`. -/
theorem run_viaD {op : Fin 32 → Fin 32 → Instr} (g : UInt64 → UInt64)
    (hexec : ∀ (s : State) (d n : Fin 32), LeanExe.A64.exec P (op d n) s =
      some { s.setD d (g (s.dregs n)) with pc := s.pc + 4 }) :
    UnRuns P code (fun r => [.fmovDX 0 r, op 0 0, .fmovXD r 0]) g := by
  intro s a r hr hcode hpc
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  have c2 := hcode 2 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2
  let s1 : State := { s.setD 0 (s.x r) with pc := s.pc + 4 }
  let s2 : State := { s1.setD 0 (g (s1.dregs 0)) with pc := s1.pc + 4 }
  let s3 : State := { s2.setX r (s2.dregs 0) with pc := s2.pc + 4 }
  have p1 : s1.pc = after a 1 := by
    show s.pc + 4 = _
    rw [hpc, after_succ, after_zero]
  have p2 : s2.pc = after a 2 := by
    show s1.pc + 4 = _
    rw [p1, ← after_succ]
  refine ⟨s3, reach_exec P code (by rw [hpc]; exact c0) rfl
      (reach_exec P code (by rw [p1]; exact c1) (hexec s1 0 0)
        (reach_exec P code (by rw [p2]; exact c2) rfl (.refl _))), ?_, ?_, fun q hq => ?_,
    ?_, ?_, ?_⟩
  · show s2.pc + 4 = after a 3
    rw [p2, ← after_succ]
  · show (s2.setX r (s2.dregs 0)).x r = _
    rw [State.x_setX_same hr]
    show (s1.setD 0 (g (s1.dregs 0))).dregs 0 = _
    rw [State.dregs_setD_same]
    show g ((s.setD 0 (s.x r)).dregs 0) = _
    rw [State.dregs_setD_same]
  · show (s2.setX r (s2.dregs 0)).x q = s2.x q
    exact State.x_setX_ne (Ne.symm hq)
  · show (s2.setX r (s2.dregs 0)).sp = s2.sp
    exact State.setX_sp
  · show (s2.setX r (s2.dregs 0)).mem = s2.mem
    exact State.setX_mem
  · show (s2.setX r (s2.dregs 0)).out = s2.out
    exact State.setX_out

/-- The code `op D0, Xr`, `FMOV Xr, D0`, for an `op` that sets its destination D register to `g` of
the word of its operand general register, computes `g` on the word of `r`. -/
theorem run_viaX {op : Fin 32 → Fin 32 → Instr} (g : UInt64 → UInt64)
    (hexec : ∀ (s : State) (d n : Fin 32), LeanExe.A64.exec P (op d n) s =
      some { s.setD d (g (s.x n)) with pc := s.pc + 4 }) :
    UnRuns P code (fun r => [op 0 r, .fmovXD r 0]) g := by
  intro s a r hr hcode hpc
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  let s1 : State := { s.setD 0 (g (s.x r)) with pc := s.pc + 4 }
  let s2 : State := { s1.setX r (s1.dregs 0) with pc := s1.pc + 4 }
  have p1 : s1.pc = after a 1 := by
    show s.pc + 4 = _
    rw [hpc, after_succ, after_zero]
  refine ⟨s2, reach_exec P code (by rw [hpc]; exact c0) (hexec s 0 r)
      (reach_exec P code (by rw [p1]; exact c1) rfl (.refl _)), ?_, ?_, fun q hq => ?_,
    ?_, ?_, ?_⟩
  · show s1.pc + 4 = after a 2
    rw [p1, ← after_succ]
  · show (s1.setX r (s1.dregs 0)).x r = _
    rw [State.x_setX_same hr]
    show (s.setD 0 (g (s.x r))).dregs 0 = _
    rw [State.dregs_setD_same]
  · show (s1.setX r (s1.dregs 0)).x q = s1.x q
    exact State.x_setX_ne (Ne.symm hq)
  · show (s1.setX r (s1.dregs 0)).sp = s1.sp
    exact State.setX_sp
  · show (s1.setX r (s1.dregs 0)).mem = s1.mem
    exact State.setX_mem
  · show (s1.setX r (s1.dregs 0)).out = s1.out
    exact State.setX_out

theorem runs_sqrt : UnRuns P code sqrtCode Wasm.f64Sqrt :=
  run_viaD P code Wasm.f64Sqrt (op := Instr.fsqrt) fun _ _ _ => rfl

theorem runs_convert : UnRuns P code convertCode Wasm.f64ConvertI64U :=
  run_viaX P code Wasm.f64ConvertI64U (op := Instr.ucvtf) fun _ _ _ => rfl

/-- A word added to itself and shifted right by 1 has its sign bit clear and its other bits kept,
which is Talos's absolute value of a double. -/
theorem abs_word (w : UInt64) : (w + w) >>> UInt64.ofNat 1 = Wasm.f64Abs w := by
  apply UInt64.toNat_inj.mp
  have hw := w.toNat_lt
  simp only [Wasm.f64Abs, Wasm.IEEE64.abs, Wasm.IEEE64.encodeFinite, Wasm.IEEE64.exponent,
    Wasm.IEEE64.fraction, Bool.false_eq_true, ↓reduceIte, UInt64.toNat_shiftRight,
    UInt64.toNat_add, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow, Nat.reducePow,
    Nat.reduceMod, Nat.zero_add] at hw ⊢
  omega

theorem runs_abs : UnRuns P code absCode Wasm.f64Abs := by
  intro s a r hr hcode hpc
  have c0 := hcode 0 (by simp [absCode])
  have c1 := hcode 1 (by simp [absCode])
  simp only [absCode, List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  let s1 : State := { s.setX r (s.x r + s.x r) with pc := s.pc + 4 }
  let s2 : State := { s1.setX r (s1.x r >>> UInt64.ofNat 1) with pc := s1.pc + 4 }
  have p1 : s1.pc = after a 1 := by
    show s.pc + 4 = _
    rw [hpc, after_succ, after_zero]
  refine ⟨s2, reach_exec P code (by rw [hpc]; exact c0) rfl
      (reach_exec P code (by rw [p1]; exact c1) rfl (.refl _)), ?_, ?_, fun q hq => ?_,
    ?_, ?_, ?_⟩
  · show s1.pc + 4 = after a 2
    rw [p1, ← after_succ]
  · show (s1.setX r (s1.x r >>> UInt64.ofNat 1)).x r = _
    rw [State.x_setX_same hr]
    show (s.setX r (s.x r + s.x r)).x r >>> UInt64.ofNat 1 = _
    rw [State.x_setX_same hr, abs_word]
  · show (s1.setX r (s1.x r >>> UInt64.ofNat 1)).x q = _
    rw [State.x_setX_ne (Ne.symm hq)]
    show (s.setX r (s.x r + s.x r)).x q = _
    rw [State.x_setX_ne (Ne.symm hq)]
  · show (s1.setX r (s1.x r >>> UInt64.ofNat 1)).sp = _
    rw [State.setX_sp]
    show (s.setX r (s.x r + s.x r)).sp = _
    rw [State.setX_sp]
  · show (s1.setX r (s1.x r >>> UInt64.ofNat 1)).mem = _
    rw [State.setX_mem]
    show (s.setX r (s.x r + s.x r)).mem = _
    rw [State.setX_mem]
  · show (s1.setX r (s1.x r >>> UInt64.ofNat 1)).out = _
    rw [State.setX_out]
    show (s.setX r (s.x r + s.x r)).out = _
    rw [State.setX_out]

/-- The code `fCmp c x y` sets `x`, below 31, to 0 when the condition `c` holds of the flags of
`FCMP` of the words of `x` and `y`, and to 1 otherwise, and keeps the other general registers, SP,
the memory, and the output. -/
theorem run_fCmp {s : State} {a : UInt64} {c : Fin 16} {x y : Fin 32} (hx : x.val < 31)
    (hcode : CodeAt code a (fCmp c x y)) (hpc : s.pc = a) :
    ∃ s', Reach P code s s' ∧ s'.pc = after a 4 ∧
      s'.x x = (if (s.fcmp (s.x x) (s.x y)).condHolds c then 0 else 1) ∧
      (∀ q, q ≠ x → s'.x q = s.x q) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.out = s.out := by
  have c0 := hcode 0 (by simp [fCmp])
  have c1 := hcode 1 (by simp [fCmp])
  have c2 := hcode 2 (by simp [fCmp])
  have c3 := hcode 3 (by simp [fCmp])
  simp only [fCmp, List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3
  let s1 : State := { s.setD 0 (s.x x) with pc := s.pc + 4 }
  let s2 : State := { s1.setD 1 (s1.x y) with pc := s1.pc + 4 }
  let s3 : State := { s2.fcmp (s2.dregs 0) (s2.dregs 1) with pc := s2.pc + 4 }
  let s4 : State :=
    { s3.setX x (if s3.condHolds c then s3.x 31 else s3.x 31 + 1) with pc := s3.pc + 4 }
  have p1 : s1.pc = after a 1 := by
    show s.pc + 4 = _
    rw [hpc, after_succ, after_zero]
  have p2 : s2.pc = after a 2 := by
    show s1.pc + 4 = _
    rw [p1, ← after_succ]
  have p3 : s3.pc = after a 3 := by
    show s2.pc + 4 = _
    rw [p2, ← after_succ]
  have hd0 : s2.dregs 0 = s.x x := by
    show (s1.setD 1 (s1.x y)).dregs 0 = _
    rw [State.dregs_setD_ne s1 (r := 1) (q := 0) _ (by decide)]
    show (s.setD 0 (s.x x)).dregs 0 = _
    rw [State.dregs_setD_same]
  have hd1 : s2.dregs 1 = s.x y := by
    show (s1.setD 1 (s1.x y)).dregs 1 = _
    rw [State.dregs_setD_same]
    rfl
  have hc : s3.condHolds c = (s.fcmp (s.x x) (s.x y)).condHolds c := by
    show (s2.fcmp (s2.dregs 0) (s2.dregs 1)).condHolds c = _
    rw [hd0, hd1]
    rfl
  have h31 : s3.x 31 = 0 := by unfold State.x; rw [dite_eq_right (by decide)]
  refine ⟨s4, reach_exec P code (by rw [hpc]; exact c0) rfl
      (reach_exec P code (by rw [p1]; exact c1) rfl
        (reach_exec P code (by rw [p2]; exact c2) rfl
          (reach_exec P code (by rw [p3]; exact c3) rfl (.refl _)))), ?_, ?_, fun q hq => ?_,
    ?_, ?_, ?_⟩
  · show s3.pc + 4 = _
    rw [p3, ← after_succ]
  · show (s3.setX x (if s3.condHolds c then s3.x 31 else s3.x 31 + 1)).x x = _
    rw [State.x_setX_same hx, hc, h31]
    rfl
  · show (s3.setX x _).x q = s3.x q
    exact State.x_setX_ne (Ne.symm hq)
  · show (s3.setX x _).sp = s3.sp
    exact State.setX_sp
  · show (s3.setX x _).mem = s3.mem
    exact State.setX_mem
  · show (s3.setX x _).out = s3.out
    exact State.setX_out

/-- Talos's `le` holds exactly when `lt` or `eq` does. -/
theorem le_eq_lt_or_eq (a b : UInt64) :
    Wasm.IEEE64.le a b = (Wasm.IEEE64.lt a b || Wasm.IEEE64.eq a b) := by
  unfold Wasm.IEEE64.le Wasm.IEEE64.lt Wasm.IEEE64.eq
  by_cases hn : (Wasm.IEEE64.isNaN a || Wasm.IEEE64.isNaN b) = true
  · rw [if_pos hn, if_pos hn, if_pos hn]
    rfl
  · rw [if_neg hn, if_neg hn, if_neg hn]
    generalize Wasm.IEEE64.scaledValue a = u
    generalize Wasm.IEEE64.scaledValue b = v
    by_cases h : u < v
    · have : u ≤ v := Int.le_of_lt h
      simp [h, this]
    · by_cases he : u = v
      · subst he
        simp
      · have : ¬ u ≤ v := by omega
        simp [h, he, this]

/-- The condition `NE` holds after `FCMP` exactly when `eq` does not. -/
theorem fcmp_ne (s : State) (a b : UInt64) : (s.fcmp a b).condHolds 1 = !Wasm.f64Eq a b := rfl

/-- The condition `PL` holds after `FCMP` exactly when `lt` does not. -/
theorem fcmp_pl (s : State) (a b : UInt64) : (s.fcmp a b).condHolds 5 = !Wasm.f64Lt a b := rfl

/-- The condition `HI` holds after `FCMP` exactly when `le` does not. -/
theorem fcmp_hi (s : State) (a b : UInt64) : (s.fcmp a b).condHolds 8 = !Wasm.f64Le a b := by
  show (!Wasm.IEEE64.lt a b && !Wasm.IEEE64.eq a b) = !Wasm.IEEE64.le a b
  rw [le_eq_lt_or_eq, Bool.not_or]

/-- The register of `CSINC` after `FCMP` holds the comparison `R` as an `i32`, for the condition
`c` that holds exactly when `R` does not. -/
theorem fcset_val {c : Fin 16} {R : UInt64 → UInt64 → Bool}
    (h : ∀ (s : State) (a b : UInt64), (s.fcmp a b).condHolds c = !R a b) (s : State)
    (a b : UInt64) :
    (if (s.fcmp a b).condHolds c then (0 : UInt64) else 1) =
      (if R a b then (1 : UInt32) else 0).toUInt64 := by
  rw [h]
  cases R a b <;> rfl

/-! ## The generator's code -/

theorem genFBin_ok {ctl : List Ctl} {σ : List ValueType} {op : Fin 32 → Fin 32 → Fin 32 → Instr}
    {is : List Instr} {fin : Option (List ValueType)} (hg : genFBin ctl σ op = .ok (is, fin)) :
    curBase ctl + 2 ≤ σ.length ∧ σ.length - 1 < 26 ∧
      is = fBin op (regOf (σ.length - 2)) (regOf (σ.length - 1)) ∧
      fin = some (.f64 :: σ.drop 2) := by
  by_cases hc : σ.length < curBase ctl + 2
  · simp [genFBin, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases hlt : σ.length - 1 < 26
  · simp [genFBin, hc, opReg_ok hlt, opReg_ok (show σ.length - 2 < 26 by omega), bind,
      Except.bind, pure, Except.pure] at hg
    exact ⟨by omega, hlt, hg.1.symm, hg.2.symm⟩
  · obtain ⟨e, he⟩ := opReg_error hlt
    by_cases hlt2 : σ.length - 2 < 26
    · simp [genFBin, hc, he, opReg_ok hlt2, bind, Except.bind] at hg
    · obtain ⟨e2, he2⟩ := opReg_error hlt2
      simp [genFBin, hc, he2, bind, Except.bind] at hg

theorem genUn_ok {ctl : List Ctl} {σ : List ValueType} {ops : Fin 32 → List Instr}
    {t : ValueType} {is : List Instr} {fin : Option (List ValueType)}
    (hg : genUn ctl σ ops t = .ok (is, fin)) :
    curBase ctl + 1 ≤ σ.length ∧ σ.length - 1 < 26 ∧ is = ops (regOf (σ.length - 1)) ∧
      fin = some (t :: σ.tail) := by
  by_cases hc : σ.length < curBase ctl + 1
  · simp [genUn, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases hlt : σ.length - 1 < 26
  · simp [genUn, hc, opReg_ok hlt, bind, Except.bind, pure, Except.pure] at hg
    exact ⟨by omega, hlt, hg.1.symm, hg.2.symm⟩
  · obtain ⟨e, he⟩ := opReg_error hlt
    simp [genUn, hc, he, bind, Except.bind] at hg

theorem genFCmp_ok {ctl : List Ctl} {σ : List ValueType} {c : Fin 16} {is : List Instr}
    {fin : Option (List ValueType)} (hg : genFCmp ctl σ c = .ok (is, fin)) :
    curBase ctl + 2 ≤ σ.length ∧ σ.length - 1 < 26 ∧
      is = fCmp c (regOf (σ.length - 2)) (regOf (σ.length - 1)) ∧
      fin = some (.i32 :: σ.drop 2) := by
  by_cases hc : σ.length < curBase ctl + 2
  · simp [genFCmp, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases hlt : σ.length - 1 < 26
  · simp [genFCmp, hc, opReg_ok hlt, opReg_ok (show σ.length - 2 < 26 by omega), bind,
      Except.bind, pure, Except.pure] at hg
    exact ⟨by omega, hlt, hg.1.symm, hg.2.symm⟩
  · obtain ⟨e, he⟩ := opReg_error hlt
    by_cases hlt2 : σ.length - 2 < 26
    · simp [genFCmp, hc, he, opReg_ok hlt2, bind, Except.bind] at hg
    · obtain ⟨e2, he2⟩ := opReg_error hlt2
      simp [genFCmp, hc, he2, bind, Except.bind] at hg

/-! ## The simulations -/

/-- The simulation of an f64 operation on the two values on top, whose code is `fBin op` for an
`op` that computes `g`, and whose rule in Talos replaces `.f64 b :: .f64 a` by `.f64 (g a b)`. -/
theorem sim_fbin_of {F : Nat} {inst : Instruction} {op : Fin 32 → Fin 32 → Fin 32 → Instr}
    (g : UInt64 → UInt64 → UInt64)
    (hgen : ∀ E ctl σ a, genInstr E ctl σ a inst = genFBin ctl σ op)
    (hexec : ∀ (s : State) (d n m : Fin 32), LeanExe.A64.exec P (op d n m) s =
      some { s.setD d (g (s.dregs n) (s.dregs m)) with pc := s.pc + 4 })
    (hcase : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals),
      (∃ a b vs, sl.values = .f64 b :: .f64 a :: vs ∧
        execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := .f64 (g a b) :: vs }) ∨
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    InstrSim P code F inst := by
  intro E ctl σ a is fin hg hcode hb hctl α m st sl ms hinv hsr h64 hpc _ _ _ _
  rw [hgen] at hg
  obtain ⟨hhb, hlt, rfl, rfl⟩ := genFBin_ok hg
  have hh := hinv.len
  have hty := hinv.types
  generalize hσl : σ.length = h at *
  cases F with
  | zero => rw [ProofKit.execOne_zero]; exact .inr trivial
  | succ f =>
      rcases hcase f m st sl with ⟨x, y, vs, hvs, hex⟩ | ⟨msg, hex⟩
      · have hvl : vs.length = h - 2 := by rw [hvs] at hh; simp at hh; omega
        have hst := hinv.stack
        rw [hvs] at hst
        have hy : ms.x (regOf (h - 1)) = y := by
          have := hst.top
          rw [show (Value.f64 x :: vs).length = h - 1 by simp; omega] at this
          exact this
        have hx : ms.x (regOf (h - 2)) = x := by
          have := hst.pop.top
          rw [hvl] at this
          exact this
        rw [hex]
        rw [hvs] at hty
        obtain ⟨ms', hr, hp, hres, hkeep, hsp, hmem, hout⟩ :=
          run_fBin P code g hexec (regOf_lt_31 (h - 2) (by omega)) hcode hpc
        apply res_outcome P code (v := .f64 (g x y)) (w := g x y) rfl (vs := vs) (t := .f64)
          trivial (hty.drop 2) hinv hsr (by omega) (by omega) hst.pop.pop hr
        · exact hp
        · rw [hvl, hres, hx, hy]
        · intro k hk
          exact hkeep _ (fun e => absurd (regOf_inj k (by omega) (h - 2) (by omega) e) (by omega))
        · exact hkeep 18 (Ne.symm (regOf_ne_18 _ (by omega)))
        · exact hkeep 17 (Ne.symm (regOf_ne_17 _ (by omega)))
        · exact hsp
        · exact hmem
        · exact hout
      · rw [hex]; exact .inr trivial

/-- The simulation of an f64 comparison of the two values on top, whose code is `fCmp c` for a
condition `c` that holds after `FCMP` exactly when `R` does not, and whose rule in Talos replaces
`.f64 b :: .f64 a` by the `i32` of `R a b`. -/
theorem sim_fcmp_of {F : Nat} {inst : Instruction} {c : Fin 16} (R : UInt64 → UInt64 → Bool)
    (hR : ∀ (s : State) (a b : UInt64), (s.fcmp a b).condHolds c = !R a b)
    (hgen : ∀ E ctl σ a, genInstr E ctl σ a inst = genFCmp ctl σ c)
    (hcase : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals),
      (∃ a b vs, sl.values = .f64 b :: .f64 a :: vs ∧
        execOne (f + 1) m st sl inst =
          .Fallthrough st { sl with values := .i32 (if R a b then 1 else 0) :: vs }) ∨
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    InstrSim P code F inst := by
  intro E ctl σ a is fin hg hcode hb hctl α m st sl ms hinv hsr h64 hpc _ _ _ _
  rw [hgen] at hg
  obtain ⟨hhb, hlt, rfl, rfl⟩ := genFCmp_ok hg
  have hh := hinv.len
  have hty := hinv.types
  generalize hσl : σ.length = h at *
  cases F with
  | zero => rw [ProofKit.execOne_zero]; exact .inr trivial
  | succ f =>
      rcases hcase f m st sl with ⟨x, y, vs, hvs, hex⟩ | ⟨msg, hex⟩
      · have hvl : vs.length = h - 2 := by rw [hvs] at hh; simp at hh; omega
        have hst := hinv.stack
        rw [hvs] at hst
        have hy : ms.x (regOf (h - 1)) = y := by
          have := hst.top
          rw [show (Value.f64 x :: vs).length = h - 1 by simp; omega] at this
          exact this
        have hx : ms.x (regOf (h - 2)) = x := by
          have := hst.pop.top
          rw [hvl] at this
          exact this
        rw [hex]
        rw [hvs] at hty
        obtain ⟨ms', hr, hp, hres, hkeep, hsp, hmem, hout⟩ :=
          run_fCmp P code (regOf_lt_31 (h - 2) (by omega)) hcode hpc
        apply res_outcome P code (v := .i32 (if R x y then 1 else 0))
          (w := (if R x y then (1 : UInt32) else 0).toUInt64) rfl (vs := vs) (t := .i32)
          trivial (hty.drop 2) hinv hsr (by omega) (by omega) hst.pop.pop hr
        · exact hp
        · rw [hvl, hres, hx, hy]
          exact fcset_val hR ms x y
        · intro k hk
          exact hkeep _ (fun e => absurd (regOf_inj k (by omega) (h - 2) (by omega) e) (by omega))
        · exact hkeep 18 (Ne.symm (regOf_ne_18 _ (by omega)))
        · exact hkeep 17 (Ne.symm (regOf_ne_17 _ (by omega)))
        · exact hsp
        · exact hmem
        · exact hout
      · rw [hex]; exact .inr trivial

/-- The simulation of an operation on the value on top, whose code `ops` computes `g` on the word
of its register. -/
theorem sim_un_of {F : Nat} {inst : Instruction} {ops : Fin 32 → List Instr} {t : ValueType}
    (g : UInt64 → UInt64)
    (hgen : ∀ E ctl σ a, genInstr E ctl σ a inst = genUn ctl σ ops t)
    (hrun : UnRuns P code ops g)
    (hcase : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals),
      (∃ va vs, sl.values = va :: vs ∧ ∀ w, ValRel va w → ∃ vr, ValRel vr (g w) ∧ HasType t vr ∧
        execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := vr :: vs }) ∨
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    InstrSim P code F inst := by
  intro E ctl σ a is fin hg hcode hb hctl α m st sl ms hinv hsr h64 hpc _ _ _ _
  rw [hgen] at hg
  obtain ⟨hhb, hlt, rfl, rfl⟩ := genUn_ok hg
  have hh := hinv.len
  have hty := hinv.types
  generalize hσl : σ.length = h at *
  cases F with
  | zero => rw [ProofKit.execOne_zero]; exact .inr trivial
  | succ f =>
      rcases hcase f m st sl with ⟨va, vs, hvs, hex⟩ | ⟨msg, hex⟩
      · have hvl : vs.length = h - 1 := by rw [hvs] at hh; simp at hh; omega
        have hst := hinv.stack
        rw [hvs] at hst
        have ha : ValRel va (ms.x (regOf (h - 1))) := by
          have := hst.top
          rwa [hvl] at this
        obtain ⟨vr, hvr, htr, hex'⟩ := hex _ ha
        rw [hex']
        rw [hvs] at hty
        obtain ⟨ms', hr, hp, hres, hkeep, hsp, hmem, hout⟩ :=
          hrun ms a _ (regOf_lt_31 (h - 1) hlt) hcode hpc
        apply res_outcome P code hvr (vs := vs) htr hty.tail hinv hsr (by omega) (by omega)
          hst.pop hr hp
        · rw [hvl, hres]
        · intro k hk
          exact hkeep _ (fun e => absurd (regOf_inj k (by omega) (h - 1) hlt e) (by omega))
        · exact hkeep 18 (Ne.symm (regOf_ne_18 _ hlt))
        · exact hkeep 17 (Ne.symm (regOf_ne_17 _ hlt))
        · exact hsp
        · exact hmem
        · exact hout
      · rw [hex]; exact .inr trivial

/-! ## Talos's rules -/

/-- Talos's cases of an f64 operation whose rule replaces `.f64 b :: .f64 a` by `.f64 (g a b)`. -/
theorem f64_bin_case {inst : Instruction} (g : UInt64 → UInt64 → UInt64) {f : Nat} {α : Type}
    {m : Module} {st : Store α} {sl : Locals}
    (hgood : ∀ a b vs, sl.values = .f64 b :: .f64 a :: vs →
      execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := .f64 (g a b) :: vs })
    (hbad : (∀ a b vs, sl.values ≠ .f64 b :: .f64 a :: vs) →
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    (∃ a b vs, sl.values = .f64 b :: .f64 a :: vs ∧
      execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := .f64 (g a b) :: vs }) ∨
    ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg := by
  by_cases h : ∃ a b vs, sl.values = .f64 b :: .f64 a :: vs
  · obtain ⟨a, b, vs, hv⟩ := h
    exact .inl ⟨a, b, vs, hv, hgood a b vs hv⟩
  · exact .inr (hbad fun a b vs hv => h ⟨a, b, vs, hv⟩)

/-- Talos's cases of an f64 comparison whose rule replaces `.f64 b :: .f64 a` by the `i32` of
`R a b`. -/
theorem f64_cmp_case {inst : Instruction} (R : UInt64 → UInt64 → Bool) {f : Nat} {α : Type}
    {m : Module} {st : Store α} {sl : Locals}
    (hgood : ∀ a b vs, sl.values = .f64 b :: .f64 a :: vs →
      execOne (f + 1) m st sl inst =
        .Fallthrough st { sl with values := .i32 (if R a b then 1 else 0) :: vs })
    (hbad : (∀ a b vs, sl.values ≠ .f64 b :: .f64 a :: vs) →
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    (∃ a b vs, sl.values = .f64 b :: .f64 a :: vs ∧
      execOne (f + 1) m st sl inst =
        .Fallthrough st { sl with values := .i32 (if R a b then 1 else 0) :: vs }) ∨
    ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg := by
  by_cases h : ∃ a b vs, sl.values = .f64 b :: .f64 a :: vs
  · obtain ⟨a, b, vs, hv⟩ := h
    exact .inl ⟨a, b, vs, hv, hgood a b vs hv⟩
  · exact .inr (hbad fun a b vs hv => h ⟨a, b, vs, hv⟩)

/-- Talos's cases of an operation whose rule replaces `inp a` by `out (g a)`, where `inp` and `out`
are `.i64` or `.f64`, whose register word is the value's word. -/
theorem word_un_case {inst : Instruction} (inp out : UInt64 → Value) {t : ValueType}
    (g : UInt64 → UInt64) (hin : ∀ a w, ValRel (inp a) w → w = a) (hout : ∀ a, ValRel (out a) a)
    (ht : ∀ a, HasType t (out a)) {f : Nat} {α : Type} {m : Module} {st : Store α} {sl : Locals}
    (hgood : ∀ a vs, sl.values = inp a :: vs →
      execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := out (g a) :: vs })
    (hbad : (∀ a vs, sl.values ≠ inp a :: vs) →
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    (∃ va vs, sl.values = va :: vs ∧ ∀ w, ValRel va w → ∃ vr, ValRel vr (g w) ∧ HasType t vr ∧
      execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := vr :: vs }) ∨
    ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg := by
  by_cases h : ∃ a vs, sl.values = inp a :: vs
  · obtain ⟨a, vs, hv⟩ := h
    refine .inl ⟨inp a, vs, hv, fun w hw => ⟨out (g a), ?_, ht (g a), hgood a vs hv⟩⟩
    rw [hin a w hw]
    exact hout _
  · exact .inr (hbad fun a vs hv => h ⟨a, vs, hv⟩)

/-- Proves the premises of `word_un_case` from Talos's rule. -/
syntax "un_rule_tac" : tactic
macro_rules
  | `(tactic| un_rule_tac) => `(tactic| (
      · intro a vs hv
        simp only [execOne.eq_def, hv]
      · intro hne
        simp only [execOne.eq_def]
        first
          | exact ⟨_, rfl⟩
          | split
            · rename_i a vs hv
              exact absurd hv (hne a vs)
            · exact ⟨_, rfl⟩))

theorem f64_in (a w : UInt64) (h : ValRel (.f64 a) w) : w = a := h
theorem i64_in (a w : UInt64) (h : ValRel (.i64 a) w) : w = a := h

/-! ## The forms -/

theorem sim_f64Const (F : Nat) (w : UInt64) : InstrSim P code F (.f64Const w) :=
  sim_const_of P code (v := .f64 w) (.inr (.inr ⟨rfl, rfl⟩)) rfl trivial
    (fun _ _ _ _ _ => by simp only [execOne.eq_def])

theorem sim_f64Add (F : Nat) : InstrSim P code F .f64Add :=
  sim_fbin_of P code (inst := .f64Add) (op := Instr.fadd) Wasm.f64Add
    (fun _ _ _ _ => by simp only [genInstr]) (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply f64_bin_case Wasm.f64Add
      i64_rule_tac

theorem sim_f64Sub (F : Nat) : InstrSim P code F .f64Sub :=
  sim_fbin_of P code (inst := .f64Sub) (op := Instr.fsub) Wasm.f64Sub
    (fun _ _ _ _ => by simp only [genInstr]) (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply f64_bin_case Wasm.f64Sub
      i64_rule_tac

theorem sim_f64Mul (F : Nat) : InstrSim P code F .f64Mul :=
  sim_fbin_of P code (inst := .f64Mul) (op := Instr.fmul) Wasm.f64Mul
    (fun _ _ _ _ => by simp only [genInstr]) (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply f64_bin_case Wasm.f64Mul
      i64_rule_tac

theorem sim_f64Div (F : Nat) : InstrSim P code F .f64Div :=
  sim_fbin_of P code (inst := .f64Div) (op := Instr.fdiv) Wasm.f64Div
    (fun _ _ _ _ => by simp only [genInstr]) (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply f64_bin_case Wasm.f64Div
      i64_rule_tac

theorem sim_f64Eq (F : Nat) : InstrSim P code F .f64Eq :=
  sim_fcmp_of P code (inst := .f64Eq) (c := 1) Wasm.f64Eq fcmp_ne
    (fun _ _ _ _ => by simp only [genInstr]) fun _ _ _ _ _ => by
      apply f64_cmp_case Wasm.f64Eq
      i64_rule_tac

theorem sim_f64Lt (F : Nat) : InstrSim P code F .f64Lt :=
  sim_fcmp_of P code (inst := .f64Lt) (c := 5) Wasm.f64Lt fcmp_pl
    (fun _ _ _ _ => by simp only [genInstr]) fun _ _ _ _ _ => by
      apply f64_cmp_case Wasm.f64Lt
      i64_rule_tac

theorem sim_f64Le (F : Nat) : InstrSim P code F .f64Le :=
  sim_fcmp_of P code (inst := .f64Le) (c := 8) Wasm.f64Le fcmp_hi
    (fun _ _ _ _ => by simp only [genInstr]) fun _ _ _ _ _ => by
      apply f64_cmp_case Wasm.f64Le
      i64_rule_tac

theorem sim_f64Sqrt (F : Nat) : InstrSim P code F .f64Sqrt :=
  sim_un_of P code (inst := .f64Sqrt) (ops := sqrtCode) (t := .f64) Wasm.f64Sqrt
    (fun _ _ _ _ => by simp only [genInstr]) (runs_sqrt P code) fun _ _ _ _ _ => by
      apply word_un_case (t := .f64) Value.f64 Value.f64 Wasm.f64Sqrt f64_in (fun _ => rfl)
        (fun _ => trivial)
      un_rule_tac

theorem sim_f64Abs (F : Nat) : InstrSim P code F .f64Abs :=
  sim_un_of P code (inst := .f64Abs) (ops := absCode) (t := .f64) Wasm.f64Abs
    (fun _ _ _ _ => by simp only [genInstr]) (runs_abs P code) fun _ _ _ _ _ => by
      apply word_un_case (t := .f64) Value.f64 Value.f64 Wasm.f64Abs f64_in (fun _ => rfl)
        (fun _ => trivial)
      un_rule_tac

theorem sim_f64ConvertI64U (F : Nat) : InstrSim P code F .f64ConvertI64U :=
  sim_un_of P code (inst := .f64ConvertI64U) (ops := convertCode) (t := .f64)
    Wasm.f64ConvertI64U (fun _ _ _ _ => by simp only [genInstr]) (runs_convert P code)
    fun _ _ _ _ _ => by
      apply word_un_case (t := .f64) Value.i64 Value.f64 Wasm.f64ConvertI64U i64_in (fun _ => rfl)
        (fun _ => trivial)
      un_rule_tac

theorem sim_i64ReinterpretF64 (F : Nat) : InstrSim P code F .i64ReinterpretF64 :=
  sim_un_of P code (inst := .i64ReinterpretF64) (ops := fun _ => []) (t := .i64) (fun w => w)
    (fun _ _ _ _ => by simp only [genInstr]) (runs_none P code) fun _ _ _ _ _ => by
      apply word_un_case (t := .i64) Value.f64 Value.i64 (fun w => w) f64_in (fun _ => rfl)
        (fun _ => trivial)
      un_rule_tac

theorem sim_f64ReinterpretI64 (F : Nat) : InstrSim P code F .f64ReinterpretI64 :=
  sim_un_of P code (inst := .f64ReinterpretI64) (ops := fun _ => []) (t := .f64) (fun w => w)
    (fun _ _ _ _ => by simp only [genInstr]) (runs_none P code) fun _ _ _ _ _ => by
      apply word_un_case (t := .f64) Value.i64 Value.f64 (fun w => w) i64_in (fun _ => rfl)
        (fun _ => trivial)
      un_rule_tac

end LeanExe.A64
