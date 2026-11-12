import LeanExe.A64.Proof.LinuxMain
import LeanExe.A64.Proof.BytesProgram

/-!
The run of a program of `genSysProgram`, a Linux executable's program, from `main`: the call of
the allocator with `inMax + 1`, the read loop of `run_readLoop` into the block that it returns,
the call of the function over bytes on the bytes read, and the write loop of `run_writeLoop'`.
`sysProgram_run` follows the run at one fuel of Talos's runs of the two calls, as
`bytesProgram_run` does for the UART's entry routine.  A read that fails ends the run at the exit
word with status 65 and nothing written.  Otherwise an input longer than `inMax` ends the run at
the exit word with status 64 and nothing written, and a shorter one leads the process to do what
`SysResult` states for Talos's run of the function on the buffer of the input, where a write that
fails ends the run with status 66, or to reach the stub of an overflow of the stack.  The trace of
each run holds at most one failure, its last event.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- `genSysMain`'s code: the frame and X18, the allocation, the read loop, the call of the
function, the write loop, the return, and the stubs of statuses 64, 65, and 66. -/
theorem gen_sysMain {a e a0 rd wr inMax room base : UInt64} {main : List Instr}
    (hg : genSysMain a e a0 rd wr inMax room base = .ok main) :
    ∃ ga gr fe fl fr go gk fd gw fz fw gb x64 x65 x66,
      bField (after a 12) a0 = .ok ga ∧ bField (after a 22) rd = .ok gr ∧
      cbField (after a 23) (after a 30) = .ok fe ∧ cbField (after a 25) (after a 62) = .ok fl ∧
      cbField (after a 28) (after a 21) = .ok fr ∧ bField (after a 29) (after a 57) = .ok go ∧
      bField (after a 36) e = .ok gk ∧ cbField (after a 41) (after a 50) = .ok fd ∧
      bField (after a 43) wr = .ok gw ∧ cbField (after a 44) (after a 67) = .ok fz ∧
      cbField (after a 46) (after a 67) = .ok fw ∧ bField (after a 49) (after a 41) = .ok gb ∧
      bField (after (after a 57) 4) base = .ok x64 ∧
      bField (after (after a 62) 4) base = .ok x65 ∧
      bField (after (after a 67) 4) base = .ok x66 ∧
      main = ([.subImm 31 31 16, .str 30 31 0, .addImm 18 31 0] ++ movImm 16 room ++
          [.subReg 18 18 16]) ++
        (movImm 0 (inMax + 1) ++ ([.bl ga, .str 0 31 1, .addReg 1 17 0, .addImm 1 1 2048,
          .addImm 1 1 2048] ++ (movImm 2 (inMax + 1) ++ ([.movz 0 0 0, .bl gr, .cbz 0 fe,
          .subsReg 31 0 2, .bcond 8 fl, .addReg 1 1 0, .subReg 2 2 0, .cbnz 2 fr, .b go] ++
          (movImm 16 (inMax + 1) ++ ([.subReg 1 16 2, .ldr 0 31 1, .bl gk, mov 2 1,
          .addReg 1 17 0, .addImm 1 1 2048, .addImm 1 1 2048] ++ ([.cbz 2 fd, .movz 0 1 0,
          .bl gw, .cbz 0 fz, .subsReg 31 0 2, .bcond 8 fw, .addReg 1 1 0, .subReg 2 2 0,
          .b gb] ++ (movImm 0 0 ++ ([.ldr 30 31 0, .addImm 31 31 16, .ret 30] ++
          ((movImm 0 64 ++ [.b x64]) ++ ((movImm 0 65 ++ [.b x65]) ++
          (movImm 0 66 ++ [.b x66])))))))))))) := by
  unfold genSysMain at hg
  obtain ⟨ga, h1⟩ : ∃ v, bField (after a 12) a0 = .ok v := by
    cases h : bField (after a 12) a0 with
    | error e => simp [h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨gr, h2⟩ : ∃ v, bField (after a 22) rd = .ok v := by
    cases h : bField (after a 22) rd with
    | error e => simp [h1, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨fe, h3⟩ : ∃ v, cbField (after a 23) (after a 30) = .ok v := by
    cases h : cbField (after a 23) (after a 30) with
    | error e => simp [h1, h2, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨fl, h4⟩ : ∃ v, cbField (after a 25) (after a 62) = .ok v := by
    cases h : cbField (after a 25) (after a 62) with
    | error e => simp [h1, h2, h3, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨fr, h5⟩ : ∃ v, cbField (after a 28) (after a 21) = .ok v := by
    cases h : cbField (after a 28) (after a 21) with
    | error e => simp [h1, h2, h3, h4, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨go, h6⟩ : ∃ v, bField (after a 29) (after a 57) = .ok v := by
    cases h : bField (after a 29) (after a 57) with
    | error e => simp [h1, h2, h3, h4, h5, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨gk, h7⟩ : ∃ v, bField (after a 36) e = .ok v := by
    cases h : bField (after a 36) e with
    | error e => simp [h1, h2, h3, h4, h5, h6, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨fd, h8⟩ : ∃ v, cbField (after a 41) (after a 50) = .ok v := by
    cases h : cbField (after a 41) (after a 50) with
    | error e => simp [h1, h2, h3, h4, h5, h6, h7, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨gw, h9⟩ : ∃ v, bField (after a 43) wr = .ok v := by
    cases h : bField (after a 43) wr with
    | error e => simp [h1, h2, h3, h4, h5, h6, h7, h8, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨fz, h10⟩ : ∃ v, cbField (after a 44) (after a 67) = .ok v := by
    cases h : cbField (after a 44) (after a 67) with
    | error e => simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨fw, h11⟩ : ∃ v, cbField (after a 46) (after a 67) = .ok v := by
    cases h : cbField (after a 46) (after a 67) with
    | error e => simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨gb, h12⟩ : ∃ v, bField (after a 49) (after a 41) = .ok v := by
    cases h : bField (after a 49) (after a 41) with
    | error e => simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨x64, h13⟩ : ∃ v, bField (after (after a 57) 4) base = .ok v := by
    cases h : bField (after (after a 57) 4) base with
    | error e =>
      simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨x65, h14⟩ : ∃ v, bField (after (after a 62) 4) base = .ok v := by
    cases h : bField (after (after a 62) 4) base with
    | error e =>
      simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨x66, h15⟩ : ∃ v, bField (after (after a 67) 4) base = .ok v := by
    cases h : bField (after (after a 67) 4) base with
    | error e =>
      simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h, bind,
        Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, bind,
    Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  refine ⟨ga, gr, fe, fl, fr, go, gk, fd, gw, fz, fw, gb, x64, x65, x66, h1, h2, h3, h4, h5, h6,
    h7, h8, h9, h10, h11, h12, h13, h14, h15, ?_⟩
  rw [← hg]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem genSysMain_length {a e a0 rd wr inMax room base : UInt64} {main : List Instr}
    (hg : genSysMain a e a0 rd wr inMax room base = .ok main) : main.length = sysMainSize := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, rfl⟩ := gen_sysMain hg
  simp only [List.length_append, movImm_length, List.length_cons, List.length_nil, sysMainSize]

/-- The program of `genSysProgram`: `genProgramWith` with the functions that may store bytes,
whose `main` is `genSysMain` with the entries of function `k` and of the allocator, function 0
among the functions that calls reach from function `k`. -/
theorem gen_sysProgram {m : Module} {k : Nat} {inMax rd wr base room : UInt64} {cap : Nat}
    {is : List Instr} (hg : genSysProgram m k inMax rd wr base room cap = .ok is) :
    ∃ gts fs first T main fns e pk rk a0 p0 r0 g1 g2 g3 g4,
      areaOk m cap = true ∧ globalTypesOf m = some gts ∧ gts.length ≤ 511 ∧
      (reachFrom m k).mapM (funcOf m) = .ok fs ∧
      first = after (after base 1) sysMainSize ∧
      T = endOf (sigIn (callTargets m k) fs) first fs ∧
      entryIn (sigIn (callTargets m k) fs) first fs k = some (e, pk, rk) ∧
      entryIn (sigIn (callTargets m k) fs) first fs 0 = some (a0, p0, r0) ∧
      genSysMain (after base 1) e a0 rd wr inMax room base = .ok main ∧
      genFunctions (tableOf (callTargets m k) first fs)
        ⟨T, after T 5, after T 10, after T 15, cap, gts, true⟩ first fs = .ok fns ∧
      is = main ++ fns ++ (movImm 0 (UInt64.ofNat 1) ++ [.b g1] ++
        (movImm 0 (UInt64.ofNat 2) ++ [.b g2]) ++ (movImm 0 (UInt64.ofNat 3) ++ [.b g3]) ++
        (movImm 0 (UInt64.ofNat 4) ++ [.b g4])) ∧
      bField (after T 4) base = .ok g1 ∧ bField (after (after T 5) 4) base = .ok g2 ∧
      bField (after (after T 10) 4) base = .ok g3 ∧
      bField (after (after T 15) 4) base = .ok g4 := by
  obtain ⟨gts, fs, first, T, main, fns, e, pk, rk, g1, g2, g3, g4, hok, hgt, hgl, hfs, hfirst,
    hT, hen, hps, hmg, hfg, his, hb1, hb2, hb3, hb4⟩ := gen_programWith hg
  simp only [hfs, bind, Except.bind] at hmg
  rw [← hfirst] at hmg
  cases h0 : entryIn (sigIn (callTargets m k) fs) first fs 0 with
  | none => simp [h0, throw, throwThe, MonadExceptOf.throw] at hmg
  | some c =>
      obtain ⟨a0, p0, r0⟩ := c
      simp only [h0] at hmg
      exact ⟨gts, fs, first, T, main, fns, e, pk, rk, a0, p0, r0, g1, g2, g3, g4, hok, hgt, hgl,
        hfs, hfirst, hT, hen, h0, hmg, hfg, his, hb1, hb2, hb3, hb4⟩

/-- The first eight instructions of `genSysMain`: the frame of 16 bytes with X30 in its first
slot and the stack's limit in X18. -/
theorem run_sysFront {A room : UInt64} {ms : State}
    (hc : CodeAt code A ([.subImm 31 31 16, .str 30 31 0, .addImm 18 31 0] ++ movImm 16 room ++
      [.subReg 18 18 16]))
    (hpc : ms.pc = A) (hal : ms.sp % 16 = 0)
    (hmain : ∀ j < 16, P.normal (ms.sp - 16 + UInt64.ofNat j) = true) :
    ∃ t, Reach P code ms t ∧ t.pc = after A 8 ∧ t.sp = ms.sp - 16 ∧
      t.x 18 = ms.sp - 16 - room ∧ (∀ q : Fin 32, q ≠ 16 → q ≠ 18 → t.x q = ms.x q) ∧
      t.io = ms.io ∧ t.mem = store64 ms.mem (slotAddr (ms.sp - 16) 0) (ms.x 30) := by
  have s2 := CodeAt.split code hc (n := 7) (by simp [movImm])
  have s1 := CodeAt.split code s2.1 (n := 3) rfl
  have c0 := (CodeAt.cons.mp s1.1).1
  have c1 := (CodeAt.cons.mp (CodeAt.cons.mp s1.1).2).1
  have c2 := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp s1.1).2).2).1
  rw [after_after] at c2
  have halm : (ms.sp - 16) % 16 = 0 := sub_aligned (k := 16) hal (by decide)
  let t1 : State := { ms with sp := ms.sp - 16, pc := ms.pc + 4 }
  have e1 : LeanExe.A64.exec P (.subImm 31 31 16) ms = some t1 := rfl
  let t2 : State :=
    { t1 with mem := store64 t1.mem (slotAddr t1.sp 0) (t1.x 30), pc := t1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.str 30 31 0) t1 = some t2 :=
    exec_str_sp P (i := 0) (by decide) halm fun j hj => by
      simpa using hmain j (by omega)
  let t2a : State := { t2.setX 18 (t2.sp + UInt64.ofNat 0) with pc := t2.pc + 4 }
  have e2a : LeanExe.A64.exec P (.addImm 18 31 0) t2 = some t2a := rfl
  have p2 : t2.pc = after A 2 := by
    show ms.pc + 4 + 4 = A + 4 * UInt64.ofNat 2
    rw [hpc, UInt64.add_assoc]
    congr 1
  have p2a : t2a.pc = after A 3 := by
    show t2.pc + 4 = _
    rw [p2, ← after_succ]
  have h18a : t2a.x 18 = ms.sp - 16 := by
    rw [State.x_withPc, State.x_setX_same (by decide)]
    exact add_ofNat_zero _
  have r2 : Reach P code ms t2a :=
    reach_exec P code (by rw [hpc]; exact c0) e1
      (reach_exec P code (by show code (ms.pc + 4) = _; rw [hpc]; simpa [after] using c1) e2
        (reach_exec P code (by rw [p2]; exact c2) e2a (.refl _)))
  have hk2a : ∀ q : Fin 32, q ≠ 18 → t2a.x q = ms.x q := fun q hq => by
    rw [State.x_withPc, State.x_setX_ne (Ne.symm hq)]
    rfl
  obtain ⟨t3a, r3a, p3a, hx16, hk3a, sp3a, mem3a, out3a⟩ :=
    run_movImm P code (d := 16) (v := room) (by decide) s1.2 p2a
  have csub : code (after A 7) = some (encode (.subReg 18 18 16)) := (CodeAt.cons.mp s2.2).1
  let t3b : State := { t3a.setX 18 (t3a.x 18 - t3a.x 16) with pc := t3a.pc + 4 }
  have e3b : LeanExe.A64.exec P (.subReg 18 18 16) t3a = some t3b := rfl
  refine ⟨t3b, r2.trans (r3a.trans (reach_exec P code (by rw [p3a, after_after]; exact csub)
    e3b (.refl _))), by show t3a.pc + 4 = _; rw [p3a, ← after_succ, after_after], ?_, ?_,
    fun q h16 h18 => ?_, ?_, ?_⟩
  · show (t3a.setX 18 (t3a.x 18 - t3a.x 16)).sp = _
    rw [State.setX_sp, sp3a]
    rfl
  · rw [State.x_withPc, State.x_setX_same (by decide), hx16, hk3a 18 (by decide), h18a]
  · rw [State.x_withPc, State.x_setX_ne (Ne.symm h18), hk3a q h16, hk2a q h18]
  · show (t3a.setX 18 (t3a.x 18 - t3a.x 16)).io = _
    rw [State.setX_io, out3a]
    rfl
  · show (t3a.setX 18 (t3a.x 18 - t3a.x 16)).mem = _
    rw [State.setX_mem, mem3a]
    rfl

/-- What the process does from `main` at `p` when Talos's run of the program's function over
bytes gives `res`: a success with the root and the length of a buffer whose bytes lie in the
memory writes them to standard output and returns 0 to `p.core.x 30`, or, when a write fails,
reaches the exit word with status 66 after writing a prefix of them, with the failure as the
trace's last event; a trap reaches the exit word with its code, nothing written.  Every trace but
the last holds no failure. -/
def SysResult (K : Kernel) (base : UInt64) (res : Result Unit) (p : Proc) : Prop :=
  match res with
  | .Success vs st' => ∀ (root len : UInt64) (bs : List UInt8), vs = [.i64 len, .i64 root] →
      len.toNat = bs.length → root.toNat + bs.length ≤ st'.mem.pages * 65536 →
      (∀ i (h : i < bs.length), st'.mem.bytes (root.toNat + i) = bs[i]) →
      (∃ p', ProcReach K P code p p' ∧ p'.core.pc = p.core.x 30 ∧ p'.core.x 0 = 0 ∧
        stdoutOf p'.trace = bs ∧ p'.core.io = p.core.io ∧
        ∀ nr e, Event.fail nr e ∉ p'.trace) ∨
      (∃ p', ProcReach K P code p p' ∧ p'.core.pc = base ∧ p'.core.x 0 = 66 ∧
        p'.core.io = p.core.io ∧ (∃ k e, K.fail k = some e) ∧
        ∃ tr e, p'.trace = tr ++ [.fail 64 e] ∧ stdoutOf tr <+: bs ∧
          ∀ nr e', Event.fail nr e' ∉ tr)
  | .Trap _ msg => ∃ p', ProcReach K P code p p' ∧ p'.core.pc = base ∧ stdoutOf p'.trace = [] ∧
      p'.core.io = p.core.io ∧ (∀ nr e, Event.fail nr e ∉ p'.trace) ∧
      ((msg = "unreachable" ∧ p'.core.x 0 = 1) ∨ (msg = "out of bounds memory access" ∧
        p'.core.x 0 = 2) ∨ (msg = "integer divide by zero" ∧ p'.core.x 0 = 3))
  | _ => True

/-- The run of a program of `genSysProgram`, whose function `k` of `m` takes and returns the two
words of a buffer and whose function 0 is the allocator, from `main` at `after base 1` with
`FPCR` at `fpcrValue` and no event in the trace, on a platform whose UART lies outside Normal
memory, for Talos's runs at fuel `F`, when the allocator's run on `inMax + 1` gives the root
`root` and the store `st1`, for every kernel.  When a read fails, the process reaches the exit word
with status 65 and nothing written, and the failure is the trace's last event.  Otherwise, when
the input has more than `inMax` bytes, the process reaches the exit word with status 64 and
nothing written, and when it has at most `inMax`, it reaches the stub of an overflow of the stack
when `room` lies below `stackBound m k`, or does what `SysResult` states for Talos's run of the
function on the root and the input's length in the store with the input written from the root.
Every trace but those of the failures holds no failure. -/
theorem sysProgram_run {K : Kernel} {m : Module} {k : Nat} {fk : Function}
    {inMax rd wr base room area : UInt64} {cap : Nat} {is : List Instr}
    (hg : genSysProgram m k inMax rd wr base room cap = .ok is)
    (hcode : CodeAt code (after base 1) is)
    (hrd : OpsAt code rd [.ins (.movz 8 63 0), .svc, .ins (.ret 30)])
    (hwr : OpsAt code wr [.ins (.movz 8 64 0), .svc, .ins (.ret 30)])
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) (hbase : (base).toNat < 2 ^ 55)
    (hm : m.imports = []) (hk : m.funcs[k]? = some fk) (hpk : fk.params = [.i64, .i64])
    (hrk : fk.results = [.i64, .i64]) {typeIdx : Nat}
    (h0 : m.funcs[0]? = some (LeanExe.Runtime.allocFunction typeIdx))
    (h0room : stackBound m 0 ≤ room.toNat) (F : Nat)
    (p : Proc) (hpc : p.core.pc = after base 1) (hf : p.fpcr = fpcrValue) (htr : p.trace = [])
    (h30 : (p.core.x 30).toNat < 2 ^ 55)
    (hal : p.core.sp % 16 = 0) (hroom : 4096 ≤ room.toNat) (htop : p.core.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (p.core.sp - 16 - room + UInt64.ofNat j) = true)
    (h17 : p.core.x 17 = area)
    (harea : ∀ j < areaSize cap, p.core.mem (area + UInt64.ofNat j) = areaByte m.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true)
    (habove : area.toNat + areaSize cap + room.toNat + 16 ≤ p.core.sp.toNat)
    (hU : P.normal P.uart = false)
    (hin : inMax.toNat < 2 ^ 32) (root : UInt64) (st1 : Store Unit)
    (hrun : Wasm.run F m 0 (initStore m cap) [.i64 (inMax + 1)] = .Success [.i64 root] st1)
    (hfit : root.toNat + (inMax.toNat + 1) ≤ st1.mem.pages * 65536) :
    (∃ p', ProcReach K P code p p' ∧ p'.core.pc = base ∧ p'.core.x 0 = 65 ∧
        p'.core.io = p.core.io ∧ (∃ k e, K.fail k = some e) ∧
        ∃ tr e, p'.trace = tr ++ [.fail 63 e] ∧ stdoutOf tr = [] ∧
          ∀ nr e', Event.fail nr e' ∉ tr) ∨
    ((inMax.toNat < K.input.length → ∃ p', ProcReach K P code p p' ∧ p'.core.pc = base ∧
        p'.core.x 0 = 64 ∧ stdoutOf p'.trace = [] ∧ p'.core.io = p.core.io ∧
        ∀ nr e, Event.fail nr e ∉ p'.trace) ∧
    (K.input.length ≤ inMax.toNat →
      (∃ p', ProcReach K P code p p' ∧ p'.core.pc = base ∧ p'.core.x 0 = 4 ∧
          stdoutOf p'.trace = [] ∧ p'.core.io = p.core.io ∧ room.toNat < stackBound m k ∧
          ∀ nr e, Event.fail nr e ∉ p'.trace) ∨
      SysResult P code K base (Wasm.run F m k (storeBytes st1 root.toNat K.input)
        [.i64 (UInt64.ofNat K.input.length), .i64 root]) p)) := by
  obtain ⟨gts, fs, first, T, main, fns, e, pk, rk, a0, p0, r0, g1, g2, g3, g4, hok', hgt, hgl,
    hfs, hfirst, hT, hen, hen0, hmg, hfg, his, hb1, hb2, hb3, hb4⟩ := gen_sysProgram hg
  subst his
  have hsp : 4096 + room.toNat + 16 ≤ p.core.sp.toNat := by unfold areaSize at habove; omega
  have h64 : m.memIs64 = false := memIs64_of_areaOk hok'
  have hfm := mapM_funcOf hfs
  have hsig := sigOf_tableOf (callTargets m k) first fs
  have hend := (genFunctions_length hsig hfg).2
  have hml := genSysMain_length hmg
  obtain ⟨ga, gr, fe, fl, fr, go, gk, fd, gw, fz, fw, gb, x64, x65, x66, hga, hgr, hfe, hfl, hfr,
    hgo, hgk, hfd, hgw, hfz, hfw, hgb, hx64, hx65, hx66, hmeq⟩ := gen_sysMain hmg
  have hmain : ∀ j < 16, P.normal (p.core.sp - 16 + UInt64.ofNat j) = true := fun j hj => by
    rw [stack_main]
    exact hstack _ (by omega)
  generalize hA : after base 1 = A at *
  -- the code's parts
  have hc := (CodeAt.append (code := code)).mp hcode
  have hc2 := CodeAt.split code hc.1 hml
  have cfns : CodeAt code first fns := by rw [hfirst]; exact hc2.2
  have cst : CodeAt code T (movImm 0 (UInt64.ofNat 1) ++ [.b g1] ++
      (movImm 0 (UInt64.ofNat 2) ++ [.b g2]) ++ (movImm 0 (UInt64.ofNat 3) ++ [.b g3]) ++
      (movImm 0 (UInt64.ofNat 4) ++ [.b g4])) := by
    have := hc.2
    rw [List.length_append, hml, ← after_after, ← hfirst, ← hend, ← hT] at this
    exact this
  have cs4 := CodeAt.split code cst (n := 15) (by simp [movImm])
  have cs3 := CodeAt.split code cs4.1 (n := 10) (by simp [movImm])
  have cs1 := CodeAt.split code cs3.1 (n := 5) (by simp [movImm])
  have hAi : ∀ i < sysMainSize, (after A i).toNat < 2 ^ 55 := fun i hi =>
    hdom _ _ (hc2.1 i (by rw [hml]; exact hi))
  have cmain := hc2.1
  rw [hmeq, ← after_zero A] at cmain
  have q1 := CodeAt.peel code cmain (k := 8) (by simp [movImm])
  have q2 := CodeAt.peel code q1.2 (k := 4) (movImm_length _ _)
  have q3 := CodeAt.peel code q2.2 (k := 5) rfl
  have q4 := CodeAt.peel code q3.2 (k := 4) (movImm_length _ _)
  have q5 := CodeAt.peel code q4.2 (k := 9) rfl
  have q6 := CodeAt.peel code q5.2 (k := 4) (movImm_length _ _)
  have q7 := CodeAt.peel code q6.2 (k := 7) rfl
  have q8 := CodeAt.peel code q7.2 (k := 9) rfl
  have q9 := CodeAt.peel code q8.2 (k := 4) (movImm_length _ _)
  have q10 := CodeAt.peel code q9.2 (k := 3) rfl
  have q11 := CodeAt.peel code q10.2 (k := 5) (by simp [movImm])
  have q12 := CodeAt.peel code q11.2 (k := 5) (by simp [movImm])
  simp only [Nat.zero_add, Nat.reduceAdd] at q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  rw [after_zero] at q1
  -- the frame and X18
  obtain ⟨t1, r1, p1, sp1, x181, k1, io1, mem1⟩ :=
    run_sysFront P code q1.1 hpc hal hmain
  have halm : (p.core.sp - 16) % 16 = 0 := sub_aligned (k := 16) hal (by decide)
  have e16 : (p.core.sp - 16).toNat = p.core.sp.toNat - 16 := toNat_sub_le (by
    show 16 ≤ p.core.sp.toNat
    omega)
  have e16r : (p.core.sp - 16 - room).toNat = p.core.sp.toNat - 16 - room.toNat := by
    rw [toNat_sub_le (by omega), e16]
  have ht16 : (p.core.sp - 16).toNat < 2 ^ 63 := by
    rw [e16]
    simp only [Nat.reducePow] at *
    omega
  -- X0 at inMax + 1 and the call of the allocator
  obtain ⟨t2, r2, p2, x02, k2, sp2, mem2, io2⟩ :=
    run_movImm P code (d := 0) (v := inMax + 1) (by decide) q2.1 p1
  have cbl : code (after A 12) = some (encode (.bl ga)) := (CodeAt.cons.mp q3.1).1
  let t3 : State := { t2.setX 30 (t2.pc + 4) with pc := t2.pc + sext 26 ga.val * 4 }
  have r3 : Reach P code p.core t3 := r1.trans (r2.trans
    (reach_exec P code (by rw [p2, after_after]; exact cbl) rfl (.refl _)))
  have p3 : t3.pc = a0 := by
    show t2.pc + sext 26 ga.val * 4 = _
    rw [p2, after_after]
    exact bField_target hga
  have h303 : t3.x 30 = after A 13 := by
    rw [State.x_withPc, State.x_setX_same (by decide), p2, after_after, ← after_succ]
  have hk3 : ∀ q : Fin 32, q ≠ 30 → q ≠ 0 → q ≠ 16 → q ≠ 18 → t3.x q = p.core.x q :=
    fun q h30' h0' h16 h18 => by
      rw [State.x_withPc, State.x_setX_ne (Ne.symm h30'), k2 q h0', k1 q h16 h18]
  have hsp3 : t3.sp = p.core.sp - 16 := by
    show (t2.setX 30 (t2.pc + 4)).sp = _
    rw [State.setX_sp, sp2, sp1]
  have h183 : t3.x 18 = p.core.sp - 16 - room := by
    rw [State.x_withPc, State.x_setX_ne (by decide), k2 18 (by decide), x181]
  have h173 : t3.x 17 = area := by
    rw [hk3 17 (by decide) (by decide) (by decide) (by decide), h17]
  have hmem3 : t3.mem = store64 p.core.mem (slotAddr (p.core.sp - 16) 0) (p.core.x 30) := by
    show (t2.setX 30 (t2.pc + 4)).mem = _
    rw [State.setX_mem, mem2, mem1]
  have hio3 : t3.io = p.core.io := by
    show (t2.setX 30 (t2.pc + 4)).io = _
    rw [State.setX_io, io2, io1]
  have hd3 : (t3.sp - t3.x 18).toNat = room.toNat := by
    rw [hsp3, h183, toNat_sub_le (by omega), e16, e16r]
    omega
  have hstk3 : StackOk P t3 := by
    refine ⟨by rw [hsp3]; exact halm, ?_, ?_⟩
    · rw [hsp3, h183, e16, e16r]
      simp only [Nat.reducePow] at *
      omega
    · intro j hj
      rw [hd3] at hj
      rw [h183]
      exact hstack j (by omega)
  have hsr3 : StoreRel P cap gts (initStore m cap) t3 := by
    refine storeRel_init P hok' hgt hgl (fun j hj => ?_) (fun j hj => by rw [h173]; exact hamap j hj)
      (by rw [h173, h183, e16r]; unfold areaSize at habove ⊢; omega)
    have := area.toNat_lt
    unfold areaSize at habove hj
    have hjl : (area + UInt64.ofNat j).toNat < (p.core.sp - 16 - room).toNat := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat', e16r]
      simp only [Nat.reducePow] at *
      omega
    rw [hmem3, h173, store64_other _ _ _ _ (below_slot (by rw [e16r, e16]; omega) ht16
      (by decide) hjl)]
    exact harea j hj
  -- the functions
  have hfuns : ∀ {j : Nat} {c : UInt64 × List ValueType × List ValueType},
      entryIn (sigIn (callTargets m k) fs) first fs j = some c → ∃ f fis, (j, f) ∈ fs ∧
        c.2 = (f.params, f.results) ∧
        genFunction (tableOf (callTargets m k) first fs)
          ⟨T, after T 5, after T 10, after T 15, cap, gts, true⟩ c.1 f = .ok fis ∧
        CodeAt code c.1 fis :=
    fun h => gen_functions code hsig hfg cfns _ (entryIn_mem h)
  have htab : ∀ j c, tableOf (callTargets m k) first fs j = some c → ∃ f is,
      m.funcs[j]? = some f ∧ c.2 = (f.params, f.results) ∧
      genFunction (tableOf (callTargets m k) first fs)
        ⟨T, after T 5, after T 10, after T 15, cap, gts, true⟩ c.1 f = .ok is ∧
        CodeAt code c.1 is := by
    intro j c hj
    unfold tableOf at hj
    split at hj
    · obtain ⟨f', fis, hmem, hpr, hgen, hcd⟩ := hfuns hj
      exact ⟨f', fis, hfm _ hmem, hpr, hgen, hcd⟩
    · cases hj
  have hcl := calls_ok P code hm h64 (fun _ => hU) htab (need := stackNeed m m.funcs.length)
    (fun _ _ hj => stackNeed_ok hj _) F
  obtain ⟨f0', fis0, hm0, hp0, hg0, cf0⟩ := hfuns hen0
  have hf0 := hfm _ hm0
  simp only at hf0
  rw [h0] at hf0
  cases hf0
  simp only [Prod.mk.injEq] at hp0
  -- the allocator's run
  have hvt0 : Typed (LeanExe.Runtime.allocFunction typeIdx).params.reverse
      ([Value.i64 (inMax + 1)].take (LeanExe.Runtime.allocFunction typeIdx).params.length) :=
    by simp [LeanExe.Runtime.allocFunction, Typed, HasType]
  rcases run_outcome P code hm h64 h0 hg0 cf0 hcl (stackNeed_ok h0 _) (initStore m cap)
      [.i64 (inMax + 1)] t3 (by simp [LeanExe.Runtime.allocFunction]) hvt0 p3 hstk3 hsr3
      (by
        refine ⟨by simp [LeanExe.Runtime.allocFunction], fun i hi => ?_⟩
        simp only [LeanExe.Runtime.allocFunction, List.length_cons, List.length_nil,
          List.take_succ_cons, List.take_zero, List.reverse_cons, List.reverse_nil,
          List.nil_append] at hi ⊢
        obtain rfl : i = 0 := by omega
        show t3.x (regOf 0) = inMax + 1
        rw [show regOf 0 = 0 by decide, State.x_withPc, State.x_setX_ne (by decide)]
        exact x02) with ⟨hov, -⟩ | hro0
  · rw [hd3] at hov
    exact absurd h0room (by unfold stackBound; omega)
  rw [hrun] at hro0
  obtain ⟨t4, r4, p4, sp4, h184, io4, mf4, -, -, hres4, -, hsr4⟩ := hro0
  have hx04 : t4.x 0 = root := by
    have := hres4.2 0 (by simp [LeanExe.Runtime.allocFunction])
    simpa [show regOf 0 = 0 by decide, LeanExe.Runtime.allocFunction, ValRel] using this
  have p4' : t4.pc = after A 13 := by rw [p4, h303]
  have hsp4 : t4.sp = p.core.sp - 16 := by rw [sp4, hsp3]
  have h184' : t4.x 18 = p.core.sp - 16 - room := by rw [h184, h183]
  have hfr4 : ∀ a : UInt64, (p.core.sp - 16).toNat ≤ a.toNat → t4.mem a = t3.mem a :=
    fun a ha => mf4 a (by rw [hsp3]; omega)
  -- the root into the frame's second slot and X1 at the block
  have cstr : code (after A 13) = some (encode (.str 0 31 1)) := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp q3.1).2).1
    rwa [after_after] at this
  have halm4 : t4.sp % 16 = 0 := by rw [hsp4]; exact halm
  let t5 : State := { t4 with mem := store64 t4.mem (slotAddr t4.sp 1) (t4.x 0), pc := t4.pc + 4 }
  have e5 : LeanExe.A64.exec P (.str 0 31 1) t4 = some t5 :=
    exec_str_sp P (i := 1) (by decide) halm4 fun j hj => by
      rw [hsp4]
      simpa using hmain (8 + j) (by omega)
  have hsr5 : StoreRel P cap gts st1 t5 := hsr4.congr rfl rfl fun a ha => by
    show store64 t4.mem (slotAddr t4.sp 1) (t4.x 0) a = t4.mem a
    rw [hsp4]
    exact store64_other _ _ _ _ (below_slot (lim := t4.x 18)
      (by rw [h184', e16r, e16]; omega) ht16 (by decide) ha)
  have c14 : code (after A 14) = some (encode (.addReg 1 17 0)) := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp q3.1).2).2).1
    rwa [after_after, after_after] at this
  have c15 : code (after A 15) = some (encode (.addImm 1 1 2048)) := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp q3.1).2).2).2).1
    rwa [after_after, after_after, after_after] at this
  have c16 : code (after A 16) = some (encode (.addImm 1 1 2048)) := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp
      (CodeAt.cons.mp q3.1).2).2).2).2).1
    rwa [after_after, after_after, after_after, after_after] at this
  have p5 : t5.pc = after A 14 := by show t4.pc + 4 = _; rw [p4', ← after_succ]
  obtain ⟨t6, r6, p6, x16, k6, sp6, mem6, io6⟩ := run_setX P code (d := 1) (by decide)
    (by rw [p5]; exact c14) (rfl : LeanExe.A64.exec P (.addReg 1 17 0) t5 = _)
  obtain ⟨t7, r7, p7, x17', k7, sp7, mem7, io7⟩ := run_setX P code (d := 1) (by decide)
    (by rw [p6, p5, ← after_succ]; exact c15)
    (exec_addImm_x P (s := t6) (d := 1) (n := 1) (imm := 2048) (by decide) (by decide))
  obtain ⟨t8, r8, p8, x18', k8, sp8, mem8, io8⟩ := run_setX P code (d := 1) (by decide)
    (by rw [p7, p6, p5, ← after_succ, ← after_succ]; exact c16)
    (exec_addImm_x P (s := t7) (d := 1) (n := 1) (imm := 2048) (by decide) (by decide))
  have p8' : t8.pc = after A 17 := by rw [p8, p7, p6, p5, ← after_succ, ← after_succ, ← after_succ]
  obtain ⟨t9, r9, p9, x29, k9, sp9, mem9, io9⟩ :=
    run_movImm P code (d := 2) (v := inMax + 1) (by decide) q4.1 p8'
  have p9' : t9.pc = after A 21 := by rw [p9, after_after]
  have hk9 : ∀ q : Fin 32, q ≠ 1 → q ≠ 2 → t9.x q = t4.x q := fun q h1 h2 => by
    rw [k9 q h2, k8 q h1, k7 q h1, k6 q h1]
    rfl
  have hx19 : t9.x 1 = t9.x 17 + UInt64.ofNat (4096 + (root.toNat + 0)) := by
    rw [hk9 17 (by decide) (by decide), k9 1 (by decide), x18', x17', x16]
    show t5.x 17 + t5.x 0 + UInt64.ofNat 2048 + UInt64.ofNat 2048 = _
    show t4.x 17 + t4.x 0 + UInt64.ofNat 2048 + UInt64.ofNat 2048 = _
    rw [hx04, add_ofNat_add, show 2048 + 2048 = 4096 by rfl, Nat.add_zero]
    rw [show t4.x 17 + root + UInt64.ofNat 4096 = t4.x 17 + UInt64.ofNat 4096 +
      UInt64.ofNat root.toNat by rw [UInt64.ofNat_toNat]; ac_rfl, add_ofNat_add]
  have hmem9 : t9.mem = t5.mem := by rw [mem9, mem8, mem7, mem6]
  have hsp9 : t9.sp = p.core.sp - 16 := by rw [sp9, sp8, sp7, sp6]; exact hsp4
  have hsr9 : StoreRel P cap gts (storeBytes st1 root.toNat (K.input.take 0)) t9 :=
    hsr5.regs (hk9 17 (by decide) (by decide)) (hk9 18 (by decide) (by decide)) hmem9
  have hio9 : t9.io = p.core.io := by rw [io9, io8, io7, io6]; exact io4.trans hio3
  have r9' : Reach P code p.core t9 := r3.trans (r4.trans (reach_exec P code
    (by rw [p4']; exact cstr) e5 (r6.trans (r7.trans (r8.trans r9)))))
  have hN : inMax.toNat + 1 < 2 ^ 64 := by omega
  have hN' : (inMax + 1).toNat = inMax.toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
    simp only [Nat.reducePow] at *
    omega
  have qt9 : ProcReach K P code p { p with core := t9 } :=
    ProcReach.of_reach' hdom hf r9' (by rw [p9']; exact hAi 21 (by decide))
  -- the read loop
  have cread : CodeAt code (after A 21) [.movz 0 0 0, .bl gr, .cbz 0 fe, .subsReg 31 0 2,
      .bcond 8 fl, .addReg 1 1 0, .subReg 2 2 0, .cbnz 2 fr, .b go] := q5.1
  have hgr' : bField (after (after A 21) 1) rd = .ok gr := by rw [after_after]; exact hgr
  have hfe' : cbField (after (after A 21) 2) (after (after A 21) 9) = .ok fe := by
    rw [after_after, after_after]; exact hfe
  have hfl' : cbField (after (after A 21) 4) (after A 62) = .ok fl := by
    rw [after_after]; exact hfl
  have hfr' : cbField (after (after A 21) 7) (after A 21) = .ok fr := by
    rw [after_after]; exact hfr
  have hgo' : bField (after (after A 21) 8) (after A 57) = .ok go := by
    rw [after_after]; exact hgo
  have hread := run_readLoop P code (K := K) (H := after A 21) (e64 := after A 57)
    (e65 := after A 62) cread hgr' hfe' hfl' hfr' hgo' hrd hdom
    (by rw [after_after]; exact hAi 30 (by decide)) (hAi 57 (by decide)) (hAi 62 (by decide))
    st1 root.toNat
    (inMax.toNat + 1) hfit (inMax.toNat + 1) { p with core := t9 } 0 (by omega) (by omega)
    p9' (by exact hf) (by show t9.x 2 = _; rw [x29, ← hN', UInt64.ofNat_toNat])
    hx19 (by rw [htr]; rfl) (Nat.zero_le _) (by rw [htr]; rfl)
    (fun nr e h => by
      change Event.fail nr e ∈ p.trace at h
      rw [htr] at h
      cases h) hsr9
  -- the stubs of statuses 64 and 4 and of a trap
  have stub : ∀ (c : Nat) (a : UInt64) (g : Fin 67108864),
      CodeAt code a (movImm 0 (UInt64.ofNat c) ++ [.b g]) → bField (after a 4) base = .ok g →
      ∀ q : Proc, ProcReach K P code p q → q.core.pc = a → q.fpcr = fpcrValue →
        ∃ q', ProcReach K P code p q' ∧ q'.core.pc = base ∧ q'.core.x 0 = UInt64.ofNat c ∧
          q'.trace = q.trace ∧ q'.core.io = q.core.io := by
    intro c a g hca hga q hq hqa hqf
    obtain ⟨u, ru, pu, xu, iou⟩ := run_stub P code (c := c) hca hga hqa
    exact ⟨{ q with core := u }, hq.trans (ProcReach.of_reach' hdom hqf ru (by rw [pu]; exact
      hbase)), pu, xu, rfl, iou⟩
  rcases hread with ⟨q, rq, pq, fq, ioq, hk, tr, e, htrq, outq, nfq⟩ | ⟨hread1, hread2⟩
  · -- a failed read: the stub of status 65
    obtain ⟨q', rq', pq', xq', trq', ioq'⟩ := stub 65 (after A 62) x65 q12.1 hx65 q
      (qt9.trans rq) pq fq
    exact .inl ⟨q', rq', pq', xq', by rw [ioq', ioq]; exact hio9, hk, tr, e, by rw [trq', htrq],
      outq, nfq⟩
  refine .inr ⟨fun hlong => ?_, fun hshort => ?_⟩
  · obtain ⟨q, rq, pq, outq, fq, ioq, nfq⟩ := hread2 (by omega)
    obtain ⟨q', rq', pq', xq', trq', ioq'⟩ := stub 64 (after A 57) x64 q11.1 hx64 q
      (qt9.trans rq) pq fq
    exact ⟨q', rq', pq', xq', by rw [trq', outq], by rw [ioq', ioq]; exact hio9,
      by rw [trq']; exact nfq⟩
  obtain ⟨q, rq, pq, x2q, hsrq, inq, outq, fq, kq, spq, frq, ioq, nfq⟩ := hread1 (by omega)
  -- the frame's slots: X30 and the root
  have hslot5 : load64 t5.mem (slotAddr (p.core.sp - 16) 0) = p.core.x 30 ∧
      load64 t5.mem (slotAddr (p.core.sp - 16) 1) = root := by
    show load64 (store64 t4.mem (slotAddr t4.sp 1) (t4.x 0)) _ = _ ∧
      load64 (store64 t4.mem (slotAddr t4.sp 1) (t4.x 0)) _ = _
    rw [hsp4, load64_store64_other _ _ _ _ (slot_apart (by decide) (by decide) (by decide)),
      load64_store64_same, hx04, load64_congr (m' := t3.mem) fun j hj =>
        hfr4 _ (le_slot hj ht16 (by decide) (Nat.zero_le _)), hmem3, load64_store64_same]
    exact ⟨rfl, rfl⟩
  have h18q : q.core.x 18 = p.core.sp - 16 - room := by
    rw [kq 18 (by decide) (by decide) (by decide) (by decide) (by decide)]
    show t9.x 18 = _
    rw [hk9 18 (by decide) (by decide), h184']
  have hslots : ∀ s : State,
      (∀ a : UInt64, (p.core.sp - 16).toNat ≤ a.toNat → s.mem a = t5.mem a) →
      load64 s.mem (slotAddr (p.core.sp - 16) 0) = p.core.x 30 ∧
        load64 s.mem (slotAddr (p.core.sp - 16) 1) = root := by
    intro s hs
    rw [load64_congr (m' := t5.mem) fun j hj => hs _ (le_slot hj ht16 (by decide)
        (Nat.zero_le _)),
      load64_congr (m' := t5.mem) (a := slotAddr (p.core.sp - 16) 1) fun j hj =>
        hs _ (by have := le_slot (m := 0) hj ht16 (i := 1) (by decide) (Nat.zero_le _); omega)]
    exact hslot5
  have hfrq : ∀ a : UInt64, (p.core.sp - 16).toNat ≤ a.toNat → q.core.mem a = t5.mem a :=
    fun a ha => by
      rw [frq a (by
        show (t9.x 18).toNat ≤ _
        rw [hk9 18 (by decide) (by decide), h184', e16r]
        rw [e16] at ha
        omega), hmem9]
  -- the length into X1, the root into X0, and the call of the function
  have pq' : q.core.pc = after A 30 := by rw [pq, after_after]
  obtain ⟨u1, ru1, pu1, x16u1, ku1, spu1, memu1, iou1⟩ :=
    run_movImm P code (d := 16) (v := inMax + 1) (by decide) q6.1 pq'
  have c34 : code (after A 34) = some (encode (.subReg 1 16 2)) := (CodeAt.cons.mp q7.1).1
  have q7a := (CodeAt.cons.mp q7.1).2
  have c35 : code (after A 35) = some (encode (.ldr 0 31 1)) := by
    have := (CodeAt.cons.mp q7a).1
    rwa [after_after] at this
  have q7b := (CodeAt.cons.mp q7a).2
  have c36 : code (after A 36) = some (encode (.bl gk)) := by
    have := (CodeAt.cons.mp q7b).1
    rwa [after_after, after_after] at this
  have q7c := (CodeAt.cons.mp q7b).2
  have c37 : code (after A 37) = some (encode (mov 2 1)) := by
    have := (CodeAt.cons.mp q7c).1
    rwa [after_after, after_after, after_after] at this
  have q7d := (CodeAt.cons.mp q7c).2
  have c38 : code (after A 38) = some (encode (.addReg 1 17 0)) := by
    have := (CodeAt.cons.mp q7d).1
    rwa [after_after, after_after, after_after, after_after] at this
  have q7e := (CodeAt.cons.mp q7d).2
  have c39 : code (after A 39) = some (encode (.addImm 1 1 2048)) := by
    have := (CodeAt.cons.mp q7e).1
    rwa [after_after, after_after, after_after, after_after, after_after] at this
  have q7f := (CodeAt.cons.mp q7e).2
  have c40 : code (after A 40) = some (encode (.addImm 1 1 2048)) := by
    have := (CodeAt.cons.mp q7f).1
    rwa [after_after, after_after, after_after, after_after, after_after, after_after] at this
  have pu1' : u1.pc = after A 34 := by rw [pu1, after_after]
  obtain ⟨u2, ru2, pu2, x1u2, ku2, spu2, memu2, iou2⟩ := run_setX P code (d := 1) (by decide)
    (by rw [pu1']; exact c34) (rfl : LeanExe.A64.exec P (.subReg 1 16 2) u1 = _)
  have hspu1 : u1.sp = p.core.sp - 16 := by rw [spu1, spq]; exact hsp9
  have hlen64 : K.input.length < 2 ^ 64 := by omega
  have e1 : (inMax + 1) = UInt64.ofNat (inMax.toNat + 1) := by
    rw [← hN', UInt64.ofNat_toNat]
  have hx1u2 : u2.x 1 = UInt64.ofNat K.input.length := by
    rw [x1u2, x16u1, ku1 2 (by decide), x2q, e1, ofNat_sub_ofNat (by omega) hN]
    congr 1
    omega
  have pu2' : u2.pc = after A 35 := by rw [pu2, pu1', ← after_succ]
  have hspu2 : u2.sp = p.core.sp - 16 := by rw [spu2, hspu1]
  have hmemu2 : u2.mem = q.core.mem := by rw [memu2, memu1]
  obtain ⟨u3, ru3, pu3, x0u3, ku3, spu3, memu3, iou3⟩ := run_setX P code (d := 0) (by decide)
    (by rw [pu2']; exact c35)
    (exec_ldr_sp P (s := u2) (r := 0) (i := 1) _ (by rw [hspu2]; exact halm)
      fun j hj => by rw [hspu2]; simpa using hmain (8 + j) (by omega))
  have hx0u3 : u3.x 0 = root := by
    rw [x0u3, hspu2, hmemu2]
    exact (hslots q.core hfrq).2
  have pu3' : u3.pc = after A 36 := by rw [pu3, pu2', ← after_succ]
  let u4 : State := { u3.setX 30 (u3.pc + 4) with pc := u3.pc + sext 26 gk.val * 4 }
  have ru4 : Reach P code q.core u4 := ru1.trans (ru2.trans (ru3.trans
    (reach_exec P code (by rw [pu3']; exact c36) rfl (.refl _))))
  have pu4 : u4.pc = e := by
    show u3.pc + sext 26 gk.val * 4 = _
    rw [pu3']
    exact bField_target hgk
  have h30u4 : u4.x 30 = after A 37 := by
    rw [State.x_withPc, State.x_setX_same (by decide), pu3', ← after_succ]
  have hku4 : ∀ r : Fin 32, r ≠ 30 → r ≠ 0 → r ≠ 1 → r ≠ 16 → u4.x r = q.core.x r :=
    fun r h30' h0' h1' h16' => by
      rw [State.x_withPc, State.x_setX_ne (Ne.symm h30'), ku3 r h0', ku2 r h1', ku1 r h16']
  have hspu4 : u4.sp = p.core.sp - 16 := by
    show (u3.setX 30 (u3.pc + 4)).sp = _
    rw [State.setX_sp, spu3, hspu2]
  have h18u4 : u4.x 18 = p.core.sp - 16 - room := by
    rw [hku4 18 (by decide) (by decide) (by decide) (by decide), h18q]
  have hx0u4 : u4.x 0 = root := by rw [State.x_withPc, State.x_setX_ne (by decide), hx0u3]
  have hx1u4 : u4.x 1 = UInt64.ofNat K.input.length := by
    rw [State.x_withPc, State.x_setX_ne (by decide), ku3 1 (by decide), hx1u2]
  have hmemu4 : u4.mem = q.core.mem := by
    show (u3.setX 30 (u3.pc + 4)).mem = _
    rw [State.setX_mem, memu3, hmemu2]
  have hiou4 : u4.io = p.core.io := by
    show (u3.setX 30 (u3.pc + 4)).io = _
    rw [State.setX_io, iou3, iou2, iou1, ioq]
    exact hio9
  have hdu4 : (u4.sp - u4.x 18).toNat = room.toNat := by
    rw [hspu4, h18u4, toNat_sub_le (by omega), e16, e16r]
    omega
  have hstku4 : StackOk P u4 := by
    refine ⟨by rw [hspu4]; exact halm, ?_, ?_⟩
    · rw [hspu4, h18u4, e16, e16r]
      simp only [Nat.reducePow] at *
      omega
    · intro j hj
      rw [hdu4] at hj
      rw [h18u4]
      exact hstack j (by omega)
  have hsru4 : StoreRel P cap gts (storeBytes st1 root.toNat K.input) u4 :=
    hsrq.regs (hku4 17 (by decide) (by decide) (by decide) (by decide))
      (hku4 18 (by decide) (by decide) (by decide) (by decide)) hmemu4
  have qq : ProcReach K P code p q := qt9.trans rq
  -- a run of the program's model from `u4` that ends at a word of the code
  have lift : ∀ v : State, Reach P code u4 v → v.pc.toNat < 2 ^ 55 →
      ProcReach K P code p { q with core := v } := fun v rv hv =>
    qq.trans (ProcReach.of_reach' hdom fq (ru4.trans rv) hv)
  obtain ⟨fk', fisk, hmk, hpk', hgk', cfk⟩ := hfuns hen
  have hfk := hfm _ hmk
  simp only at hfk
  rw [hk] at hfk
  cases hfk
  rcases run_outcome P code hm h64 hk hgk' cfk hcl (stackNeed_ok hk _)
      (storeBytes st1 root.toNat K.input) [.i64 (UInt64.ofNat K.input.length), .i64 root] u4
      (by rw [hpk]; simp) (by rw [hpk]; simp [Typed, HasType]) pu4 hstku4 hsru4 (by
        rw [hpk]
        refine ⟨by simp, fun i hi => ?_⟩
        simp only [List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero,
          List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hi ⊢
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
        · show u4.x (regOf 0) = root
          rw [show regOf 0 = 0 by decide]
          exact hx0u4
        · show u4.x (regOf 1) = UInt64.ofNat K.input.length
          rw [show regOf 1 = 1 by decide]
          exact hx1u4) with ⟨hov, hovr⟩ | hro
  · rw [hdu4] at hov
    obtain ⟨v, rv, pv, iov⟩ := hovr
    obtain ⟨v2, rv2, pv2, xv2, iov2⟩ := run_stub P code cs4.2 hb4 pv
    exact .inl ⟨{ q with core := v2 }, lift v2 (rv.trans rv2) (by rw [pv2]; exact hbase), pv2,
      xv2, outq, by show v2.io = _; rw [iov2, iov, hiou4], by unfold stackBound; omega, nfq⟩
  refine .inr ?_
  revert hro
  cases Wasm.run F m k (storeBytes st1 root.toNat K.input)
      [.i64 (UInt64.ofNat K.input.length), .i64 root] with
  | Trap st' tmsg =>
      intro hro
      obtain ⟨v, rv, iov, hmsg'⟩ := hro
      rcases hmsg' with ⟨hm1, pv⟩ | ⟨hm2, pv⟩ | ⟨hm3, pv⟩
      · obtain ⟨v2, rv2, pv2, xv2, iov2⟩ := run_stub P code cs1.1 hb1 pv
        exact ⟨{ q with core := v2 }, lift v2 (rv.trans rv2) (by rw [pv2]; exact hbase), pv2,
          outq, by show v2.io = _; rw [iov2, iov, hiou4], nfq, .inl ⟨hm1, xv2⟩⟩
      · obtain ⟨v2, rv2, pv2, xv2, iov2⟩ := run_stub P code cs1.2 hb2 pv
        exact ⟨{ q with core := v2 }, lift v2 (rv.trans rv2) (by rw [pv2]; exact hbase), pv2,
          outq, by show v2.io = _; rw [iov2, iov, hiou4], nfq, .inr (.inl ⟨hm2, xv2⟩)⟩
      · obtain ⟨v2, rv2, pv2, xv2, iov2⟩ := run_stub P code cs3.2 hb3 pv
        exact ⟨{ q with core := v2 }, lift v2 (rv.trans rv2) (by rw [pv2]; exact hbase), pv2,
          outq, by show v2.io = _; rw [iov2, iov, hiou4], nfq, .inr (.inr ⟨hm3, xv2⟩)⟩
  | Invalid _ => intro _; trivial
  | OutOfFuel => intro _; trivial
  | Thrown _ _ _ => intro _; trivial
  | Success vs' st3 =>
  intro hro root' len bs hvs hlenbs hfitbs hbytes
  subst hvs
  obtain ⟨v5, rv5, pv5, spv5, h18v5, iov5, mfv5, -, -, hresv5, -, hsrv5⟩ := hro
  rw [hrk] at hresv5
  have hx0v5 : v5.x 0 = root' := by
    have := hresv5.2 0 (by simp)
    simpa [show regOf 0 = 0 by decide, ValRel] using this
  have hx1v5 : v5.x 1 = UInt64.ofNat bs.length := by
    have := hresv5.2 1 (by simp)
    have e : v5.x 1 = len := by simpa [show regOf 1 = 1 by decide, ValRel] using this
    rw [e, ← hlenbs, UInt64.ofNat_toNat]
  have pv5' : v5.pc = after A 37 := by rw [pv5, h30u4]
  have hspv5 : v5.sp = p.core.sp - 16 := by rw [spv5, hspu4]
  have hfrv5 : ∀ a : UInt64, (p.core.sp - 16).toNat ≤ a.toNat → v5.mem a = t5.mem a :=
    fun a ha => by rw [mfv5 a (by rw [hspu4]; omega), hmemu4, hfrq a ha]
  -- the count into X2 and the result's address into X1
  obtain ⟨v6, rv6, pv6, x2v6, kv6, spv6, memv6, iov6⟩ := run_setX P code (d := 2) (by decide)
    (by rw [pv5']; exact c37) (rfl : LeanExe.A64.exec P (mov 2 1) v5 = _)
  obtain ⟨v7, rv7, pv7, x1v7, kv7, spv7, memv7, iov7⟩ := run_setX P code (d := 1) (by decide)
    (by rw [pv6, pv5', ← after_succ]; exact c38)
    (rfl : LeanExe.A64.exec P (.addReg 1 17 0) v6 = _)
  obtain ⟨v8, rv8, pv8, x1v8, kv8, spv8, memv8, iov8⟩ := run_setX P code (d := 1) (by decide)
    (by rw [pv7, pv6, pv5', ← after_succ, ← after_succ]; exact c39)
    (exec_addImm_x P (s := v7) (d := 1) (n := 1) (imm := 2048) (by decide) (by decide))
  obtain ⟨v9, rv9, pv9, x1v9, kv9, spv9, memv9, iov9⟩ := run_setX P code (d := 1) (by decide)
    (by rw [pv8, pv7, pv6, pv5', ← after_succ, ← after_succ, ← after_succ]; exact c40)
    (exec_addImm_x P (s := v8) (d := 1) (n := 1) (imm := 2048) (by decide) (by decide))
  have pv9' : v9.pc = after A 41 := by
    rw [pv9, pv8, pv7, pv6, pv5', ← after_succ, ← after_succ, ← after_succ, ← after_succ]
  have hkv9 : ∀ r : Fin 32, r ≠ 1 → r ≠ 2 → v9.x r = v5.x r := fun r h1 h2 => by
    rw [kv9 r h1, kv8 r h1, kv7 r h1, kv6 r h2]
  have hx1v9 : v9.x 1 = v9.x 17 + UInt64.ofNat (4096 + root'.toNat) := by
    rw [hkv9 17 (by decide) (by decide), x1v9, x1v8, x1v7, kv6 17 (by decide),
      kv6 0 (by decide), hx0v5, add_ofNat_add]
    show v5.x 17 + root' + UInt64.ofNat 4096 = _
    rw [show v5.x 17 + root' + UInt64.ofNat 4096 = v5.x 17 + UInt64.ofNat 4096 +
      UInt64.ofNat root'.toNat by rw [UInt64.ofNat_toNat]; ac_rfl, add_ofNat_add]
  have hx2v9 : v9.x 2 = UInt64.ofNat bs.length := by
    rw [kv9 2 (by decide), kv8 2 (by decide), kv7 2 (by decide), x2v6]
    show v5.x 31 ||| v5.x 1 = _
    rw [x31_or, hx1v5]
  have hmemv9 : v9.mem = v5.mem := by rw [memv9, memv8, memv7, memv6]
  have hsrv9 : StoreRel P cap gts st3 v9 :=
    hsrv5.regs (hkv9 17 (by decide) (by decide)) (hkv9 18 (by decide) (by decide)) hmemv9
  have hpg3 := hsrv5.pages
  have rv9' : Reach P code u4 v9 := rv5.trans (rv6.trans (rv7.trans (rv8.trans rv9)))
  have qv9 := lift v9 rv9' (by rw [pv9']; exact hAi 41 (by decide))
  -- the write loop
  have hfd' : cbField (after A 41) (after (after A 41) 9) = .ok fd := by
    rw [after_after]; exact hfd
  have hgw' : bField (after (after A 41) 2) wr = .ok gw := by rw [after_after]; exact hgw
  have hfw' : cbField (after (after A 41) 5) (after A 67) = .ok fw := by
    rw [after_after]; exact hfw
  have hgb' : bField (after (after A 41) 8) (after A 41) = .ok gb := by
    rw [after_after]; exact hgb
  have hbs64 : bs.length + 4095 < 2 ^ 64 := by
    have : st3.mem.pages * 65536 ≤ cap * 65536 := Nat.mul_le_mul_right _ hpg3.2
    have := hsrv5.cap_lt
    simp only [Nat.reducePow]
    omega
  have hrlbs : readList v9.mem (v9.x 1) bs.length = bs := by
    have hcp : st3.mem.pages * 65536 ≤ cap * 65536 := Nat.mul_le_mul_right _ hpg3.2
    have hrl := readList_bytes P hsrv9 bs.length root'.toNat (Nat.le_trans hfitbs hcp)
    rw [hx1v9, hrl, memBytes_eq st3.mem bs root'.toNat hbytes]
  rcases run_writeLoop' P code (K := K) q8.1
    hfd' hgw' hfw' hgb' hwr hdom (by rw [after_after]; exact hAi 50 (by decide))
    (hAi 67 (by decide)) bs.length { q with core := v9 } pv9' fq hx2v9 hbs64 (fun i hi => by
      show P.normal (v9.x 1 + UInt64.ofNat i) = true
      rw [hx1v9, add_ofNat_add]
      have : st3.mem.pages * 65536 ≤ cap * 65536 := Nat.mul_le_mul_right _ hpg3.2
      exact hsrv9.mapped _ (by unfold areaSize; omega)) nfq with
    ⟨w, rw', pw, fw', iow, hk, tr, e, htrw, ⟨j, hj, houtj⟩, nfw⟩ |
    ⟨w, rw', pw, fw', outw, memw, spw, iow, kw, nfw⟩
  · -- a failed write: the stub of status 66, after a prefix of the result
    obtain ⟨w', rw'', pw', xw', trw', iow'⟩ := stub 66 (after A 67) x66 q12.2 hx66 w
      (qv9.trans rw') pw fw'
    refine .inr ⟨w', rw'', pw', xw', ?_, hk, tr, e, by rw [trw', htrw], ?_, nfw⟩
    · rw [iow', iow]
      show v9.io = _
      rw [iov9, iov8, iov7, iov6, iov5, hiou4]
    · rw [houtj]
      show stdoutOf q.trace ++ readList v9.mem (v9.x 1) j <+: bs
      rw [outq, List.nil_append]
      refine ⟨readList v9.mem (v9.x 1 + UInt64.ofNat j) (bs.length - j), ?_⟩
      rw [← readList_add, Nat.add_sub_cancel' hj, hrlbs]
  have houtw : stdoutOf w.trace = bs := by
    rw [outw]
    show stdoutOf q.trace ++ readList v9.mem (v9.x 1) bs.length = bs
    rw [outq, hrlbs]
    rfl
  -- the return
  have pw' : w.core.pc = after A 50 := by rw [pw, after_after]
  obtain ⟨y1, ry1, py1, x0y1, ky1, spy1, memy1, ioy1⟩ :=
    run_movImm P code (d := 0) (v := 0) (by decide) q9.1 pw'
  have hspw : w.core.sp = p.core.sp - 16 := by rw [spw]; exact hspv5.symm ▸ (by
    show v9.sp = _
    rw [spv9, spv8, spv7, spv6, hspv5])
  obtain ⟨y2, ry2, py2, spy2, ioy2, memy2, ky2⟩ :=
    run_epilogue P code (n := 0) (fs := 16) (by decide) (by decide) q10.1
      (by rw [py1, after_after]) (by rw [spy1, hspw]; exact halm)
      (fun j hj => by rw [spy1, hspw]; simpa using hmain j (by omega))
  have hy2pc : y2.pc = p.core.x 30 := by
    rw [py2, spy1, hspw, memy1, memw]
    show load64 v9.mem _ = _
    rw [hmemv9]
    exact (hslots v5 hfrv5).1
  refine .inl ⟨{ w with core := y2 }, qv9.trans (rw'.trans (ProcReach.of_reach' hdom fw'
    (ry1.trans ry2) (by rw [hy2pc]; exact h30))), hy2pc, by
      show y2.x 0 = 0
      rw [ky2 0 (by decide), x0y1], houtw, ?_, nfw⟩
  show y2.io = _
  rw [ioy2, ioy1, iow]
  show v9.io = _
  rw [iov9, iov8, iov7, iov6, iov5, hiou4]

end LeanExe.A64
