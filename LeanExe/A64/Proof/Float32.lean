import LeanExe.A64.Proof.Float

/-!
The simulation of the f32 forms.  An f32 value lies in the register of its height as its 32-bit
word, zero-extended, as an `i32` does, so `f32ReinterpretI32` and `i32ReinterpretF32` emit nothing
and change only the type.  `genFBin32` moves the words of the two values on top into S0 and S1
with `FMOV Sd, Wn`, computes `FADD`, `FSUB`, `FMUL`, or `FDIV` into S0, and moves S0's word into the
register of the lower value with `FMOV Wd, Sn`, which zero-extends it.  The model's meaning of each
S form is Talos's function of the low 32 bits of its operand D registers, written zero-extended
into the destination, so the register then holds Talos's result.  `f32Sqrt` and `f32Nearest` go
through S0 in the same way with `FSQRT` and `FRINTN`, `f32ConvertI64U` and `f32ConvertI32S`
convert the register into S0 with `UCVTF` and `SCVTF`, `i64TruncSatF32U` and `i32TruncSatF32S`
move the word into S0 and convert it back with `FCVTZU` and `FCVTZS`, and `f32Abs` doubles the
word, keeps its low 32 bits, which drops the sign bit, and shifts it right by 1.  `genFCmp32`
compares S0 with S1 by `FCMP` and sets the lower value's register with `CSINC` and the conditions
of the f64 comparisons.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-! ## Runs of the f32 code -/

/-- The code `fBin32 op x y`, for an `op` that sets its destination D register to `g` of the low
32 bits of its operand D registers, zero-extended, sets `x`, below 31, to `g` of the low 32 bits
of `x` and `y`, zero-extended, and keeps the other general registers, SP, the memory, and the
output. -/
theorem run_fBin32 {op : Fin 32 → Fin 32 → Fin 32 → Instr} (g : UInt32 → UInt32 → UInt32)
    (hexec : ∀ (s : State) (d n m : Fin 32), LeanExe.A64.exec P (op d n m) s =
      some { s.setD d (g (s.dregs n).toUInt32 (s.dregs m).toUInt32).toUInt64 with pc := s.pc + 4 })
    {s : State} {a : UInt64} {x y : Fin 32} (hx : x.val < 31)
    (hcode : CodeAt code a (fBin32 op x y)) (hpc : s.pc = a) :
    ∃ s', Reach P code s s' ∧ s'.pc = after a 4 ∧
      s'.x x = (g (s.x x).toUInt32 (s.x y).toUInt32).toUInt64 ∧
      (∀ q, q ≠ x → s'.x q = s.x q) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.out = s.out := by
  have c0 := hcode 0 (by simp [fBin32])
  have c1 := hcode 1 (by simp [fBin32])
  have c2 := hcode 2 (by simp [fBin32])
  have c3 := hcode 3 (by simp [fBin32])
  simp only [fBin32, List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3
  let s1 : State := { s.setD 0 (s.x x).toUInt32.toUInt64 with pc := s.pc + 4 }
  let s2 : State := { s1.setD 1 (s1.x y).toUInt32.toUInt64 with pc := s1.pc + 4 }
  let s3 : State :=
    { s2.setD 0 (g (s2.dregs 0).toUInt32 (s2.dregs 1).toUInt32).toUInt64 with pc := s2.pc + 4 }
  let s4 : State := { s3.setX x (s3.dregs 0).toUInt32.toUInt64 with pc := s3.pc + 4 }
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
  · show (s3.setX x (s3.dregs 0).toUInt32.toUInt64).x x = _
    rw [State.x_setX_same hx]
    show (((s2.setD 0 (g (s2.dregs 0).toUInt32
      (s2.dregs 1).toUInt32).toUInt64).dregs 0).toUInt32).toUInt64 = _
    rw [State.dregs_setD_same, UInt32.toUInt32_toUInt64]
    show (g ((s1.setD 1 (s1.x y).toUInt32.toUInt64).dregs 0).toUInt32
      ((s1.setD 1 (s1.x y).toUInt32.toUInt64).dregs 1).toUInt32).toUInt64 = _
    rw [State.dregs_setD_ne s1 (r := 1) (q := 0) _ (by decide), State.dregs_setD_same,
      UInt32.toUInt32_toUInt64, State.dregs_setD_same, UInt32.toUInt32_toUInt64]
    rfl
  · show (s3.setX x (s3.dregs 0).toUInt32.toUInt64).x q = s3.x q
    exact State.x_setX_ne (Ne.symm hq)
  · show (s3.setX x (s3.dregs 0).toUInt32.toUInt64).sp = s3.sp
    exact State.setX_sp
  · show (s3.setX x (s3.dregs 0).toUInt32.toUInt64).mem = s3.mem
    exact State.setX_mem
  · show (s3.setX x (s3.dregs 0).toUInt32.toUInt64).out = s3.out
    exact State.setX_out

/-- The code `FMOV S0, Wr`, `op S0, S0`, `FMOV Wr, S0`, for an `op` that sets its destination D
register to `g` of the low 32 bits of its operand D register, zero-extended, computes `g` on the
low 32 bits of `r`. -/
theorem run_viaS {op : Fin 32 → Fin 32 → Instr} (g : UInt32 → UInt32)
    (hexec : ∀ (s : State) (d n : Fin 32), LeanExe.A64.exec P (op d n) s =
      some { s.setD d (g (s.dregs n).toUInt32).toUInt64 with pc := s.pc + 4 }) :
    UnRuns P code (unCode32 op) fun w => (g w.toUInt32).toUInt64 := by
  intro s a r hr hcode hpc
  have c0 := hcode 0 (by simp [unCode32])
  have c1 := hcode 1 (by simp [unCode32])
  have c2 := hcode 2 (by simp [unCode32])
  simp only [unCode32, List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2
  let s1 : State := { s.setD 0 (s.x r).toUInt32.toUInt64 with pc := s.pc + 4 }
  let s2 : State := { s1.setD 0 (g (s1.dregs 0).toUInt32).toUInt64 with pc := s1.pc + 4 }
  let s3 : State := { s2.setX r (s2.dregs 0).toUInt32.toUInt64 with pc := s2.pc + 4 }
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
  · show s2.pc + 4 = after a (unCode32 op r).length
    rw [p2, ← after_succ]
    rfl
  · show (s2.setX r (s2.dregs 0).toUInt32.toUInt64).x r = _
    rw [State.x_setX_same hr]
    show ((s1.setD 0 (g (s1.dregs 0).toUInt32).toUInt64).dregs 0).toUInt32.toUInt64 = _
    rw [State.dregs_setD_same, UInt32.toUInt32_toUInt64]
    show (g ((s.setD 0 (s.x r).toUInt32.toUInt64).dregs 0).toUInt32).toUInt64 = _
    rw [State.dregs_setD_same, UInt32.toUInt32_toUInt64]
  · show (s2.setX r (s2.dregs 0).toUInt32.toUInt64).x q = s2.x q
    exact State.x_setX_ne (Ne.symm hq)
  · show (s2.setX r (s2.dregs 0).toUInt32.toUInt64).sp = s2.sp
    exact State.setX_sp
  · show (s2.setX r (s2.dregs 0).toUInt32.toUInt64).mem = s2.mem
    exact State.setX_mem
  · show (s2.setX r (s2.dregs 0).toUInt32.toUInt64).out = s2.out
    exact State.setX_out

/-- The code `op S0, Xr`, `FMOV Wr, S0`, for an `op` that sets its destination D register to `g` of
the word of its operand general register, zero-extended, computes `g` on the word of `r`. -/
theorem run_toS {op : Fin 32 → Fin 32 → Instr} (g : UInt64 → UInt32)
    (hexec : ∀ (s : State) (d n : Fin 32), LeanExe.A64.exec P (op d n) s =
      some { s.setD d (g (s.x n)).toUInt64 with pc := s.pc + 4 }) :
    UnRuns P code (toS32 op) fun w => (g w).toUInt64 := by
  intro s a r hr hcode hpc
  have c0 := hcode 0 (by simp [toS32])
  have c1 := hcode 1 (by simp [toS32])
  simp only [toS32, List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  let s1 : State := { s.setD 0 (g (s.x r)).toUInt64 with pc := s.pc + 4 }
  let s2 : State := { s1.setX r (s1.dregs 0).toUInt32.toUInt64 with pc := s1.pc + 4 }
  have p1 : s1.pc = after a 1 := by
    show s.pc + 4 = _
    rw [hpc, after_succ, after_zero]
  refine ⟨s2, reach_exec P code (by rw [hpc]; exact c0) (hexec s 0 r)
      (reach_exec P code (by rw [p1]; exact c1) rfl (.refl _)), ?_, ?_, fun q hq => ?_,
    ?_, ?_, ?_⟩
  · show s1.pc + 4 = after a (toS32 op r).length
    rw [p1, ← after_succ]
    rfl
  · show (s1.setX r (s1.dregs 0).toUInt32.toUInt64).x r = _
    rw [State.x_setX_same hr]
    show ((s.setD 0 (g (s.x r)).toUInt64).dregs 0).toUInt32.toUInt64 = _
    rw [State.dregs_setD_same, UInt32.toUInt32_toUInt64]
  · show (s1.setX r (s1.dregs 0).toUInt32.toUInt64).x q = s1.x q
    exact State.x_setX_ne (Ne.symm hq)
  · show (s1.setX r (s1.dregs 0).toUInt32.toUInt64).sp = s1.sp
    exact State.setX_sp
  · show (s1.setX r (s1.dregs 0).toUInt32.toUInt64).mem = s1.mem
    exact State.setX_mem
  · show (s1.setX r (s1.dregs 0).toUInt32.toUInt64).out = s1.out
    exact State.setX_out

/-- The code `FMOV S0, Wr`, `op Xr, S0`, for an `op` that sets its destination general register to
`g` of the low 32 bits of its operand D register, computes `g` on the low 32 bits of `r`. -/
theorem run_ofS {op : Fin 32 → Fin 32 → Instr} (g : UInt32 → UInt64)
    (hexec : ∀ (s : State) (d n : Fin 32), LeanExe.A64.exec P (op d n) s =
      some { s.setX d (g (s.dregs n).toUInt32) with pc := s.pc + 4 }) :
    UnRuns P code (ofS32 op) fun w => g w.toUInt32 := by
  intro s a r hr hcode hpc
  have c0 := hcode 0 (by simp [ofS32])
  have c1 := hcode 1 (by simp [ofS32])
  simp only [ofS32, List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  let s1 : State := { s.setD 0 (s.x r).toUInt32.toUInt64 with pc := s.pc + 4 }
  let s2 : State := { s1.setX r (g (s1.dregs 0).toUInt32) with pc := s1.pc + 4 }
  have p1 : s1.pc = after a 1 := by
    show s.pc + 4 = _
    rw [hpc, after_succ, after_zero]
  refine ⟨s2, reach_exec P code (by rw [hpc]; exact c0) rfl
      (reach_exec P code (by rw [p1]; exact c1) (hexec s1 r 0) (.refl _)), ?_, ?_, fun q hq => ?_,
    ?_, ?_, ?_⟩
  · show s1.pc + 4 = after a (ofS32 op r).length
    rw [p1, ← after_succ]
    rfl
  · show (s1.setX r (g (s1.dregs 0).toUInt32)).x r = _
    rw [State.x_setX_same hr]
    show g ((s.setD 0 (s.x r).toUInt32.toUInt64).dregs 0).toUInt32 = _
    rw [State.dregs_setD_same, UInt32.toUInt32_toUInt64]
  · show (s1.setX r (g (s1.dregs 0).toUInt32)).x q = s1.x q
    exact State.x_setX_ne (Ne.symm hq)
  · show (s1.setX r (g (s1.dregs 0).toUInt32)).sp = s1.sp
    exact State.setX_sp
  · show (s1.setX r (g (s1.dregs 0).toUInt32)).mem = s1.mem
    exact State.setX_mem
  · show (s1.setX r (g (s1.dregs 0).toUInt32)).out = s1.out
    exact State.setX_out

theorem runs_sqrt32 : UnRuns P code (unCode32 .fsqrtS) fun w => (Wasm.f32Sqrt w.toUInt32).toUInt64 :=
  run_viaS P code Wasm.f32Sqrt (op := Instr.fsqrtS) fun _ _ _ => rfl

theorem runs_nearest32 :
    UnRuns P code (unCode32 .frintnS) fun w => (Wasm.f32Nearest w.toUInt32).toUInt64 :=
  run_viaS P code Wasm.f32Nearest (op := Instr.frintnS) fun _ _ _ => rfl

theorem runs_convert32 :
    UnRuns P code (toS32 .ucvtfSX) fun w => (Wasm.f32ConvertI64U w).toUInt64 :=
  run_toS P code Wasm.f32ConvertI64U (op := Instr.ucvtfSX) fun _ _ _ => rfl

theorem runs_convertS32 :
    UnRuns P code (toS32 .scvtfSW) fun w => (Wasm.f32ConvertI32S w.toUInt32).toUInt64 :=
  run_toS P code (fun w => Wasm.f32ConvertI32S w.toUInt32) (op := Instr.scvtfSW) fun _ _ _ => rfl

theorem runs_trunc32 : UnRuns P code (ofS32 .fcvtzuXS) fun w => Wasm.i64TruncSatF32U w.toUInt32 :=
  run_ofS P code Wasm.i64TruncSatF32U (op := Instr.fcvtzuXS) fun _ _ _ => rfl

theorem runs_truncS32 :
    UnRuns P code (ofS32 .fcvtzsWS) fun w => (Wasm.i32TruncSatF32S w.toUInt32).toUInt64 :=
  run_ofS P code (fun a => (Wasm.i32TruncSatF32S a).toUInt64) (op := Instr.fcvtzsWS)
    fun _ _ _ => rfl

/-- A word doubled, cut to its low 32 bits, and shifted right by 1 is the low 32 bits of the word
with bit 31 clear, which is Talos's absolute value of a single. -/
theorem abs_word32 (w : UInt64) :
    (0 ||| (w + w)).toUInt32.toUInt64 >>> UInt64.ofNat 1 = (Wasm.f32Abs w.toUInt32).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have hw := w.toNat_lt
  simp only [Wasm.f32Abs, Wasm.IEEE32.abs, Wasm.IEEE32.encodeFinite, Wasm.IEEE32.exponent,
    Wasm.IEEE32.fraction, Bool.false_eq_true, ↓reduceIte, UInt64.toNat_shiftRight,
    UInt64.zero_or, UInt64.toNat_add, UInt64.toNat_ofNat', UInt32.toNat_toUInt64,
    UInt64.toNat_toUInt32, UInt32.toNat_ofNat', Nat.shiftRight_eq_div_pow, Nat.reducePow,
    Nat.reduceMod, Nat.zero_add] at hw ⊢
  omega

theorem runs_abs32 : UnRuns P code absCode32 fun w => (Wasm.f32Abs w.toUInt32).toUInt64 := by
  intro s a r hr hcode hpc
  have c0 := hcode 0 (by simp [absCode32])
  have c1 := hcode 1 (by simp [absCode32])
  have c2 := hcode 2 (by simp [absCode32])
  simp only [absCode32, List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2
  let s1 : State := { s.setX r (s.x r + s.x r) with pc := s.pc + 4 }
  let s2 : State := { s1.setX r (s1.x 31 ||| s1.x r).toUInt32.toUInt64 with pc := s1.pc + 4 }
  let s3 : State := { s2.setX r (s2.x r >>> UInt64.ofNat 1) with pc := s2.pc + 4 }
  have p1 : s1.pc = after a 1 := by
    show s.pc + 4 = _
    rw [hpc, after_succ, after_zero]
  have p2 : s2.pc = after a 2 := by
    show s1.pc + 4 = _
    rw [p1, ← after_succ]
  have h31 : s1.x 31 = 0 := by unfold State.x; rw [dite_eq_right (by decide)]
  refine ⟨s3, reach_exec P code (by rw [hpc]; exact c0) rfl
      (reach_exec P code (by rw [p1]; exact c1) rfl
        (reach_exec P code (by rw [p2]; exact c2) rfl (.refl _))), ?_, ?_, fun q hq => ?_,
    ?_, ?_, ?_⟩
  · show s2.pc + 4 = after a 3
    rw [p2, ← after_succ]
  · show (s2.setX r (s2.x r >>> UInt64.ofNat 1)).x r = _
    rw [State.x_setX_same hr]
    show (s1.setX r (s1.x 31 ||| s1.x r).toUInt32.toUInt64).x r >>> UInt64.ofNat 1 = _
    rw [State.x_setX_same hr, h31]
    show (0 ||| (s.setX r (s.x r + s.x r)).x r).toUInt32.toUInt64 >>> UInt64.ofNat 1 = _
    rw [State.x_setX_same hr, abs_word32]
  · show (s2.setX r (s2.x r >>> UInt64.ofNat 1)).x q = _
    rw [State.x_setX_ne (Ne.symm hq)]
    show (s1.setX r (s1.x 31 ||| s1.x r).toUInt32.toUInt64).x q = _
    rw [State.x_setX_ne (Ne.symm hq)]
    show (s.setX r (s.x r + s.x r)).x q = _
    rw [State.x_setX_ne (Ne.symm hq)]
  · show (s2.setX r (s2.x r >>> UInt64.ofNat 1)).sp = _
    rw [State.setX_sp]
    show (s1.setX r (s1.x 31 ||| s1.x r).toUInt32.toUInt64).sp = _
    rw [State.setX_sp]
    show (s.setX r (s.x r + s.x r)).sp = _
    rw [State.setX_sp]
  · show (s2.setX r (s2.x r >>> UInt64.ofNat 1)).mem = _
    rw [State.setX_mem]
    show (s1.setX r (s1.x 31 ||| s1.x r).toUInt32.toUInt64).mem = _
    rw [State.setX_mem]
    show (s.setX r (s.x r + s.x r)).mem = _
    rw [State.setX_mem]
  · show (s2.setX r (s2.x r >>> UInt64.ofNat 1)).out = _
    rw [State.setX_out]
    show (s1.setX r (s1.x 31 ||| s1.x r).toUInt32.toUInt64).out = _
    rw [State.setX_out]
    show (s.setX r (s.x r + s.x r)).out = _
    rw [State.setX_out]

/-- The code `fCmp32 c x y` sets `x`, below 31, to 0 when the condition `c` holds of the flags of
`FCMP` of the low 32 bits of `x` and `y`, and to 1 otherwise, and keeps the other general
registers, SP, the memory, and the output. -/
theorem run_fCmp32 {s : State} {a : UInt64} {c : Fin 16} {x y : Fin 32} (hx : x.val < 31)
    (hcode : CodeAt code a (fCmp32 c x y)) (hpc : s.pc = a) :
    ∃ s', Reach P code s s' ∧ s'.pc = after a 4 ∧
      s'.x x = (if (s.fcmpS (s.x x).toUInt32 (s.x y).toUInt32).condHolds c then 0 else 1) ∧
      (∀ q, q ≠ x → s'.x q = s.x q) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.out = s.out := by
  have c0 := hcode 0 (by simp [fCmp32])
  have c1 := hcode 1 (by simp [fCmp32])
  have c2 := hcode 2 (by simp [fCmp32])
  have c3 := hcode 3 (by simp [fCmp32])
  simp only [fCmp32, List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3
  let s1 : State := { s.setD 0 (s.x x).toUInt32.toUInt64 with pc := s.pc + 4 }
  let s2 : State := { s1.setD 1 (s1.x y).toUInt32.toUInt64 with pc := s1.pc + 4 }
  let s3 : State := { s2.fcmpS (s2.dregs 0).toUInt32 (s2.dregs 1).toUInt32 with pc := s2.pc + 4 }
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
  have hd0 : (s2.dregs 0).toUInt32 = (s.x x).toUInt32 := by
    show ((s1.setD 1 (s1.x y).toUInt32.toUInt64).dregs 0).toUInt32 = _
    rw [State.dregs_setD_ne s1 (r := 1) (q := 0) _ (by decide)]
    show ((s.setD 0 (s.x x).toUInt32.toUInt64).dregs 0).toUInt32 = _
    rw [State.dregs_setD_same, UInt32.toUInt32_toUInt64]
  have hd1 : (s2.dregs 1).toUInt32 = (s.x y).toUInt32 := by
    show ((s1.setD 1 (s1.x y).toUInt32.toUInt64).dregs 1).toUInt32 = _
    rw [State.dregs_setD_same, UInt32.toUInt32_toUInt64]
    rfl
  have hc : s3.condHolds c = (s.fcmpS (s.x x).toUInt32 (s.x y).toUInt32).condHolds c := by
    show (s2.fcmpS (s2.dregs 0).toUInt32 (s2.dregs 1).toUInt32).condHolds c = _
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

/-- Talos's `le` of singles holds exactly when `lt` or `eq` does. -/
theorem le_eq_lt_or_eq32 (a b : UInt32) :
    Wasm.IEEE32.le a b = (Wasm.IEEE32.lt a b || Wasm.IEEE32.eq a b) := by
  unfold Wasm.IEEE32.le Wasm.IEEE32.lt Wasm.IEEE32.eq
  by_cases hn : (Wasm.IEEE32.isNaN a || Wasm.IEEE32.isNaN b) = true
  · rw [if_pos hn, if_pos hn, if_pos hn]
    rfl
  · rw [if_neg hn, if_neg hn, if_neg hn]
    generalize Wasm.IEEE32.scaledValue a = u
    generalize Wasm.IEEE32.scaledValue b = v
    by_cases h : u < v
    · have : u ≤ v := Int.le_of_lt h
      simp [h, this]
    · by_cases he : u = v
      · subst he
        simp
      · have : ¬ u ≤ v := by omega
        simp [h, he, this]

/-- The condition `NE` holds after `FCMP` of singles exactly when `eq` does not. -/
theorem fcmpS_ne (s : State) (a b : UInt32) : (s.fcmpS a b).condHolds 1 = !Wasm.f32Eq a b := rfl

/-- The condition `PL` holds after `FCMP` of singles exactly when `lt` does not. -/
theorem fcmpS_pl (s : State) (a b : UInt32) : (s.fcmpS a b).condHolds 5 = !Wasm.f32Lt a b := rfl

/-- The condition `HI` holds after `FCMP` of singles exactly when `le` does not. -/
theorem fcmpS_hi (s : State) (a b : UInt32) : (s.fcmpS a b).condHolds 8 = !Wasm.f32Le a b := by
  show (!Wasm.IEEE32.lt a b && !Wasm.IEEE32.eq a b) = !Wasm.IEEE32.le a b
  rw [le_eq_lt_or_eq32, Bool.not_or]

/-- The register of `CSINC` after `FCMP` of singles holds the comparison `R` as an `i32`, for the
condition `c` that holds exactly when `R` does not. -/
theorem fcset_val32 {c : Fin 16} {R : UInt32 → UInt32 → Bool}
    (h : ∀ (s : State) (a b : UInt32), (s.fcmpS a b).condHolds c = !R a b) (s : State)
    (a b : UInt32) :
    (if (s.fcmpS a b).condHolds c then (0 : UInt64) else 1) =
      (if R a b then (1 : UInt32) else 0).toUInt64 := by
  rw [h]
  cases R a b <;> rfl

/-! ## The generator's code -/

theorem genFBin32_ok {ctl : List Ctl} {σ : List ValueType} {op : Fin 32 → Fin 32 → Fin 32 → Instr}
    {is : List Instr} {fin : Option (List ValueType)} (hg : genFBin32 ctl σ op = .ok (is, fin)) :
    curBase ctl + 2 ≤ σ.length ∧ σ.length - 1 < 26 ∧
      is = fBin32 op (regOf (σ.length - 2)) (regOf (σ.length - 1)) ∧
      fin = some (.f32 :: σ.drop 2) := by
  by_cases hc : σ.length < curBase ctl + 2
  · simp [genFBin32, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases hlt : σ.length - 1 < 26
  · simp [genFBin32, hc, opReg_ok hlt, opReg_ok (show σ.length - 2 < 26 by omega), bind,
      Except.bind, pure, Except.pure] at hg
    exact ⟨by omega, hlt, hg.1.symm, hg.2.symm⟩
  · obtain ⟨e, he⟩ := opReg_error hlt
    by_cases hlt2 : σ.length - 2 < 26
    · simp [genFBin32, hc, he, opReg_ok hlt2, bind, Except.bind] at hg
    · obtain ⟨e2, he2⟩ := opReg_error hlt2
      simp [genFBin32, hc, he2, bind, Except.bind] at hg

theorem genFCmp32_ok {ctl : List Ctl} {σ : List ValueType} {c : Fin 16} {is : List Instr}
    {fin : Option (List ValueType)} (hg : genFCmp32 ctl σ c = .ok (is, fin)) :
    curBase ctl + 2 ≤ σ.length ∧ σ.length - 1 < 26 ∧
      is = fCmp32 c (regOf (σ.length - 2)) (regOf (σ.length - 1)) ∧
      fin = some (.i32 :: σ.drop 2) := by
  by_cases hc : σ.length < curBase ctl + 2
  · simp [genFCmp32, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases hlt : σ.length - 1 < 26
  · simp [genFCmp32, hc, opReg_ok hlt, opReg_ok (show σ.length - 2 < 26 by omega), bind,
      Except.bind, pure, Except.pure] at hg
    exact ⟨by omega, hlt, hg.1.symm, hg.2.symm⟩
  · obtain ⟨e, he⟩ := opReg_error hlt
    by_cases hlt2 : σ.length - 2 < 26
    · simp [genFCmp32, hc, he, opReg_ok hlt2, bind, Except.bind] at hg
    · obtain ⟨e2, he2⟩ := opReg_error hlt2
      simp [genFCmp32, hc, he2, bind, Except.bind] at hg

/-! ## The simulations -/

/-- The simulation of an f32 operation on the two values on top, whose code is `fBin32 op` for an
`op` that computes `g`, and whose rule in Talos replaces `.f32 b :: .f32 a` by `.f32 (g a b)`. -/
theorem sim_fbin32_of {F : Nat} {inst : Instruction} {op : Fin 32 → Fin 32 → Fin 32 → Instr}
    (g : UInt32 → UInt32 → UInt32)
    (hgen : ∀ E ctl σ a, genInstr E ctl σ a inst = genFBin32 ctl σ op)
    (hexec : ∀ (s : State) (d n m : Fin 32), LeanExe.A64.exec P (op d n m) s =
      some { s.setD d (g (s.dregs n).toUInt32 (s.dregs m).toUInt32).toUInt64 with pc := s.pc + 4 })
    (hcase : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals),
      (∃ a b vs, sl.values = .f32 b :: .f32 a :: vs ∧
        execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := .f32 (g a b) :: vs }) ∨
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    InstrSim P code F inst := by
  intro E ctl σ a is fin hg hcode hb hctl α m st sl ms hinv hsr h64 hpc _ _ _ _
  rw [hgen] at hg
  obtain ⟨hhb, hlt, rfl, rfl⟩ := genFBin32_ok hg
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
        have hy : ms.x (regOf (h - 1)) = y.toUInt64 := by
          have := hst.top
          rw [show (Value.f32 x :: vs).length = h - 1 by simp; omega] at this
          exact this
        have hx : ms.x (regOf (h - 2)) = x.toUInt64 := by
          have := hst.pop.top
          rw [hvl] at this
          exact this
        rw [hex]
        rw [hvs] at hty
        obtain ⟨ms', hr, hp, hres, hkeep, hsp, hmem, hout⟩ :=
          run_fBin32 P code g hexec (regOf_lt_31 (h - 2) (by omega)) hcode hpc
        apply res_outcome P code (v := .f32 (g x y)) (w := (g x y).toUInt64) rfl (vs := vs)
          (t := .f32) trivial (hty.drop 2) hinv hsr (by omega) (by omega) hst.pop.pop hr
        · exact hp
        · rw [hvl, hres, hx, hy, UInt32.toUInt32_toUInt64, UInt32.toUInt32_toUInt64]
        · intro k hk
          exact hkeep _ (fun e => absurd (regOf_inj k (by omega) (h - 2) (by omega) e) (by omega))
        · exact hkeep 18 (Ne.symm (regOf_ne_18 _ (by omega)))
        · exact hkeep 17 (Ne.symm (regOf_ne_17 _ (by omega)))
        · exact hsp
        · exact hmem
        · exact hout
      · rw [hex]; exact .inr trivial

/-- The simulation of an f32 comparison of the two values on top, whose code is `fCmp32 c` for a
condition `c` that holds after `FCMP` exactly when `R` does not, and whose rule in Talos replaces
`.f32 b :: .f32 a` by the `i32` of `R a b`. -/
theorem sim_fcmp32_of {F : Nat} {inst : Instruction} {c : Fin 16} (R : UInt32 → UInt32 → Bool)
    (hR : ∀ (s : State) (a b : UInt32), (s.fcmpS a b).condHolds c = !R a b)
    (hgen : ∀ E ctl σ a, genInstr E ctl σ a inst = genFCmp32 ctl σ c)
    (hcase : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals),
      (∃ a b vs, sl.values = .f32 b :: .f32 a :: vs ∧
        execOne (f + 1) m st sl inst =
          .Fallthrough st { sl with values := .i32 (if R a b then 1 else 0) :: vs }) ∨
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    InstrSim P code F inst := by
  intro E ctl σ a is fin hg hcode hb hctl α m st sl ms hinv hsr h64 hpc _ _ _ _
  rw [hgen] at hg
  obtain ⟨hhb, hlt, rfl, rfl⟩ := genFCmp32_ok hg
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
        have hy : ms.x (regOf (h - 1)) = y.toUInt64 := by
          have := hst.top
          rw [show (Value.f32 x :: vs).length = h - 1 by simp; omega] at this
          exact this
        have hx : ms.x (regOf (h - 2)) = x.toUInt64 := by
          have := hst.pop.top
          rw [hvl] at this
          exact this
        rw [hex]
        rw [hvs] at hty
        obtain ⟨ms', hr, hp, hres, hkeep, hsp, hmem, hout⟩ :=
          run_fCmp32 P code (regOf_lt_31 (h - 2) (by omega)) hcode hpc
        apply res_outcome P code (v := .i32 (if R x y then 1 else 0))
          (w := (if R x y then (1 : UInt32) else 0).toUInt64) rfl (vs := vs) (t := .i32)
          trivial (hty.drop 2) hinv hsr (by omega) (by omega) hst.pop.pop hr
        · exact hp
        · rw [hvl, hres, hx, hy, UInt32.toUInt32_toUInt64, UInt32.toUInt32_toUInt64]
          exact fcset_val32 hR ms x y
        · intro k hk
          exact hkeep _ (fun e => absurd (regOf_inj k (by omega) (h - 2) (by omega) e) (by omega))
        · exact hkeep 18 (Ne.symm (regOf_ne_18 _ (by omega)))
        · exact hkeep 17 (Ne.symm (regOf_ne_17 _ (by omega)))
        · exact hsp
        · exact hmem
        · exact hout
      · rw [hex]; exact .inr trivial

/-! ## Talos's rules -/

/-- Talos's cases of an f32 operation whose rule replaces `.f32 b :: .f32 a` by `.f32 (g a b)`. -/
theorem f32_bin_case {inst : Instruction} (g : UInt32 → UInt32 → UInt32) {f : Nat} {α : Type}
    {m : Module} {st : Store α} {sl : Locals}
    (hgood : ∀ a b vs, sl.values = .f32 b :: .f32 a :: vs →
      execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := .f32 (g a b) :: vs })
    (hbad : (∀ a b vs, sl.values ≠ .f32 b :: .f32 a :: vs) →
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    (∃ a b vs, sl.values = .f32 b :: .f32 a :: vs ∧
      execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := .f32 (g a b) :: vs }) ∨
    ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg := by
  by_cases h : ∃ a b vs, sl.values = .f32 b :: .f32 a :: vs
  · obtain ⟨a, b, vs, hv⟩ := h
    exact .inl ⟨a, b, vs, hv, hgood a b vs hv⟩
  · exact .inr (hbad fun a b vs hv => h ⟨a, b, vs, hv⟩)

/-- Talos's cases of an f32 comparison whose rule replaces `.f32 b :: .f32 a` by the `i32` of
`R a b`. -/
theorem f32_cmp_case {inst : Instruction} (R : UInt32 → UInt32 → Bool) {f : Nat} {α : Type}
    {m : Module} {st : Store α} {sl : Locals}
    (hgood : ∀ a b vs, sl.values = .f32 b :: .f32 a :: vs →
      execOne (f + 1) m st sl inst =
        .Fallthrough st { sl with values := .i32 (if R a b then 1 else 0) :: vs })
    (hbad : (∀ a b vs, sl.values ≠ .f32 b :: .f32 a :: vs) →
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    (∃ a b vs, sl.values = .f32 b :: .f32 a :: vs ∧
      execOne (f + 1) m st sl inst =
        .Fallthrough st { sl with values := .i32 (if R a b then 1 else 0) :: vs }) ∨
    ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg := by
  by_cases h : ∃ a b vs, sl.values = .f32 b :: .f32 a :: vs
  · obtain ⟨a, b, vs, hv⟩ := h
    exact .inl ⟨a, b, vs, hv, hgood a b vs hv⟩
  · exact .inr (hbad fun a b vs hv => h ⟨a, b, vs, hv⟩)

/-- Talos's cases of an operation whose rule replaces `inp a` by `out a`, for a word function `g`
that carries every register word of `inp a` to a register word of `out a`. -/
theorem val_un_case {inst : Instruction} {β : Type} (inp out : β → Value) {t : ValueType}
    (g : UInt64 → UInt64) (hio : ∀ a w, ValRel (inp a) w → ValRel (out a) (g w))
    (ht : ∀ a, HasType t (out a)) {f : Nat} {α : Type} {m : Module} {st : Store α} {sl : Locals}
    (hgood : ∀ a vs, sl.values = inp a :: vs →
      execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := out a :: vs })
    (hbad : (∀ a vs, sl.values ≠ inp a :: vs) →
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    (∃ va vs, sl.values = va :: vs ∧ ∀ w, ValRel va w → ∃ vr, ValRel vr (g w) ∧ HasType t vr ∧
      execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := vr :: vs }) ∨
    ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg := by
  by_cases h : ∃ a vs, sl.values = inp a :: vs
  · obtain ⟨a, vs, hv⟩ := h
    exact .inl ⟨inp a, vs, hv, fun w hw => ⟨out a, hio a w hw, ht a, hgood a vs hv⟩⟩
  · exact .inr (hbad fun a vs hv => h ⟨a, vs, hv⟩)

/-- A function of a single's word carries the register word of `.f32 a` to that of
`.f32 (f a)`. -/
theorem f32_io (f : UInt32 → UInt32) (a : UInt32) (w : UInt64) (h : ValRel (.f32 a) w) :
    ValRel (.f32 (f a)) ((f w.toUInt32).toUInt64) := by
  show (f w.toUInt32).toUInt64 = (f a).toUInt64
  rw [show w = a.toUInt64 from h, UInt32.toUInt32_toUInt64]

/-! ## The forms -/

theorem sim_f32Const (F : Nat) (c : UInt32) : InstrSim P code F (.f32Const c) :=
  sim_const_of P code (w := c.toUInt64) (v := .f32 c) (.inr (.inr (.inr ⟨c, rfl, rfl, rfl⟩)))
    rfl trivial (fun _ _ _ _ _ => by simp only [execOne.eq_def])

theorem sim_f32Add (F : Nat) : InstrSim P code F .f32Add :=
  sim_fbin32_of P code (inst := .f32Add) (op := Instr.faddS) Wasm.f32Add
    (fun _ _ _ _ => by simp only [genInstr]) (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply f32_bin_case Wasm.f32Add
      i64_rule_tac

theorem sim_f32Sub (F : Nat) : InstrSim P code F .f32Sub :=
  sim_fbin32_of P code (inst := .f32Sub) (op := Instr.fsubS) Wasm.f32Sub
    (fun _ _ _ _ => by simp only [genInstr]) (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply f32_bin_case Wasm.f32Sub
      i64_rule_tac

theorem sim_f32Mul (F : Nat) : InstrSim P code F .f32Mul :=
  sim_fbin32_of P code (inst := .f32Mul) (op := Instr.fmulS) Wasm.f32Mul
    (fun _ _ _ _ => by simp only [genInstr]) (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply f32_bin_case Wasm.f32Mul
      i64_rule_tac

theorem sim_f32Div (F : Nat) : InstrSim P code F .f32Div :=
  sim_fbin32_of P code (inst := .f32Div) (op := Instr.fdivS) Wasm.f32Div
    (fun _ _ _ _ => by simp only [genInstr]) (fun _ _ _ _ => rfl) fun _ _ _ _ _ => by
      apply f32_bin_case Wasm.f32Div
      i64_rule_tac

theorem sim_f32Eq (F : Nat) : InstrSim P code F .f32Eq :=
  sim_fcmp32_of P code (inst := .f32Eq) (c := 1) Wasm.f32Eq fcmpS_ne
    (fun _ _ _ _ => by simp only [genInstr]) fun _ _ _ _ _ => by
      apply f32_cmp_case Wasm.f32Eq
      i64_rule_tac

theorem sim_f32Lt (F : Nat) : InstrSim P code F .f32Lt :=
  sim_fcmp32_of P code (inst := .f32Lt) (c := 5) Wasm.f32Lt fcmpS_pl
    (fun _ _ _ _ => by simp only [genInstr]) fun _ _ _ _ _ => by
      apply f32_cmp_case Wasm.f32Lt
      i64_rule_tac

theorem sim_f32Le (F : Nat) : InstrSim P code F .f32Le :=
  sim_fcmp32_of P code (inst := .f32Le) (c := 8) Wasm.f32Le fcmpS_hi
    (fun _ _ _ _ => by simp only [genInstr]) fun _ _ _ _ _ => by
      apply f32_cmp_case Wasm.f32Le
      i64_rule_tac

theorem sim_f32Sqrt (F : Nat) : InstrSim P code F .f32Sqrt :=
  sim_un_of P code (inst := .f32Sqrt) (ops := unCode32 .fsqrtS) (t := .f32) _
    (fun _ _ _ _ => by simp only [genInstr]) (runs_sqrt32 P code) fun _ _ _ _ _ => by
      apply val_un_case (t := .f32) Value.f32 (fun a => .f32 (Wasm.f32Sqrt a)) _
        (f32_io Wasm.f32Sqrt) (fun _ => trivial)
      un_rule_tac

theorem sim_f32Nearest (F : Nat) : InstrSim P code F .f32Nearest :=
  sim_un_of P code (inst := .f32Nearest) (ops := unCode32 .frintnS) (t := .f32) _
    (fun _ _ _ _ => by simp only [genInstr]) (runs_nearest32 P code) fun _ _ _ _ _ => by
      apply val_un_case (t := .f32) Value.f32 (fun a => .f32 (Wasm.f32Nearest a)) _
        (f32_io Wasm.f32Nearest) (fun _ => trivial)
      un_rule_tac

theorem sim_f32Abs (F : Nat) : InstrSim P code F .f32Abs :=
  sim_un_of P code (inst := .f32Abs) (ops := absCode32) (t := .f32) _
    (fun _ _ _ _ => by simp only [genInstr]) (runs_abs32 P code) fun _ _ _ _ _ => by
      apply val_un_case (t := .f32) Value.f32 (fun a => .f32 (Wasm.f32Abs a)) _
        (f32_io Wasm.f32Abs) (fun _ => trivial)
      un_rule_tac

theorem sim_f32ConvertI64U (F : Nat) : InstrSim P code F .f32ConvertI64U :=
  sim_un_of P code (inst := .f32ConvertI64U) (ops := toS32 .ucvtfSX) (t := .f32) _
    (fun _ _ _ _ => by simp only [genInstr]) (runs_convert32 P code) fun _ _ _ _ _ => by
      apply val_un_case (t := .f32) Value.i64 (fun a => .f32 (Wasm.f32ConvertI64U a)) _
        (fun a w (h : w = a) => by show _ = _; rw [h]) (fun _ => trivial)
      un_rule_tac

theorem sim_f32ConvertI32S (F : Nat) : InstrSim P code F .f32ConvertI32S :=
  sim_un_of P code (inst := .f32ConvertI32S) (ops := toS32 .scvtfSW) (t := .f32) _
    (fun _ _ _ _ => by simp only [genInstr]) (runs_convertS32 P code) fun _ _ _ _ _ => by
      apply val_un_case (t := .f32) Value.i32 (fun a => .f32 (Wasm.f32ConvertI32S a)) _
        (fun a w (h : w = a.toUInt64) => by
          show _ = _
          rw [h, UInt32.toUInt32_toUInt64]) (fun _ => trivial)
      un_rule_tac

theorem sim_i64TruncSatF32U (F : Nat) : InstrSim P code F .i64TruncSatF32U :=
  sim_un_of P code (inst := .i64TruncSatF32U) (ops := ofS32 .fcvtzuXS) (t := .i64) _
    (fun _ _ _ _ => by simp only [genInstr]) (runs_trunc32 P code) fun _ _ _ _ _ => by
      apply val_un_case (t := .i64) Value.f32 (fun a => .i64 (Wasm.i64TruncSatF32U a)) _
        (fun a w (h : w = a.toUInt64) => by
          show _ = _
          rw [h, UInt32.toUInt32_toUInt64]) (fun _ => trivial)
      un_rule_tac

theorem sim_i32TruncSatF32S (F : Nat) : InstrSim P code F .i32TruncSatF32S :=
  sim_un_of P code (inst := .i32TruncSatF32S) (ops := ofS32 .fcvtzsWS) (t := .i32) _
    (fun _ _ _ _ => by simp only [genInstr]) (runs_truncS32 P code) fun _ _ _ _ _ => by
      apply val_un_case (t := .i32) Value.f32 (fun a => .i32 (Wasm.i32TruncSatF32S a)) _
        (fun a w (h : w = a.toUInt64) => by
          show _ = _
          rw [h, UInt32.toUInt32_toUInt64]) (fun _ => trivial)
      un_rule_tac

theorem sim_f32ReinterpretI32 (F : Nat) : InstrSim P code F .f32ReinterpretI32 :=
  sim_un_of P code (inst := .f32ReinterpretI32) (ops := fun _ => []) (t := .f32) (fun w => w)
    (fun _ _ _ _ => by simp only [genInstr]) (runs_none P code) fun _ _ _ _ _ => by
      apply val_un_case (t := .f32) Value.i32 Value.f32 (fun w => w) (fun _ _ h => h)
        (fun _ => trivial)
      un_rule_tac

theorem sim_i32ReinterpretF32 (F : Nat) : InstrSim P code F .i32ReinterpretF32 :=
  sim_un_of P code (inst := .i32ReinterpretF32) (ops := fun _ => []) (t := .i32) (fun w => w)
    (fun _ _ _ _ => by simp only [genInstr]) (runs_none P code) fun _ _ _ _ _ => by
      apply val_un_case (t := .i32) Value.f32 Value.i32 (fun w => w) (fun _ _ h => h)
        (fun _ => trivial)
      un_rule_tac

end LeanExe.A64
