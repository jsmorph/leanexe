import LeanExe.A64.Proof.BytesMain
import LeanExe.Runtime.Defs

/-!
The run of a program of `genBytesProgram`, which reads a length and a message from the UART,
calls the module's allocator, reads the message into the block that it returns, calls a function
over bytes, and writes the bytes of the buffer that the function returns.  `bytesProgram_run`
follows the run from `main` at one fuel of Talos's runs of the two calls.  A byte with an error
flag among the first eight ends it with status 65, as does one among the message's bytes after the
allocator's run, and a length above `inMax` ends it with status 64.  Otherwise the machine does
what `BytesResult` states for Talos's run of the function on the buffer of the message, or reaches
the stub of an overflow of the stack.  The program's functions may store bytes, so the theorem
assumes that the UART lies outside Normal memory.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- What the machine does from `main` at `ms` when Talos's run of the program's function over
bytes gives `res`: a success with the root and the length of a buffer whose bytes lie in the
memory writes them and returns 0 to `ms.x 30`, and a trap reaches the exit word with its code,
the output kept. -/
def BytesResult (base : UInt64) (res : Result Unit) (ms : State) : Prop :=
  match res with
  | .Success vs st' => ∀ (root len : UInt64) (bs : List UInt8), vs = [.i64 len, .i64 root] →
      len.toNat = bs.length → root.toNat + bs.length ≤ st'.mem.pages * 65536 →
      (∀ i (h : i < bs.length), st'.mem.bytes (root.toNat + i) = bs[i]) →
      ∃ ms', Reach P code ms ms' ∧ ms'.pc = ms.x 30 ∧ ms'.x 0 = 0 ∧ ms'.io.out = ms.io.out ++ bs
  | .Trap _ msg => ∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧ ms'.io.out = ms.io.out ∧
      ((msg = "unreachable" ∧ ms'.x 0 = 1) ∨ (msg = "out of bounds memory access" ∧ ms'.x 0 = 2) ∨
        (msg = "integer divide by zero" ∧ ms'.x 0 = 3))
  | _ => True

/-- The program of `genBytesProgram`: `genProgramWith` with the functions that may store bytes,
whose `main` is `genBytesMain` with the entries of function `k` and of the allocator, function 0
among the functions that calls reach from function `k`. -/
theorem gen_bytesProgram {m : Module} {k : Nat} {inMax uart base room : UInt64} {cap : Nat}
    {is : List Instr} (hg : genBytesProgram m k inMax uart base room cap = .ok is) :
    ∃ gts fs first T main fns e pk rk a0 p0 r0 g1 g2 g3 g4,
      areaOk m cap = true ∧ globalTypesOf m = some gts ∧ gts.length ≤ 511 ∧
      (reachFrom m k).mapM (funcOf m) = .ok fs ∧
      first = after (after base 1) bytesMainSize ∧
      T = endOf (sigIn (callTargets m k) fs) first fs ∧
      entryIn (sigIn (callTargets m k) fs) first fs k = some (e, pk, rk) ∧
      entryIn (sigIn (callTargets m k) fs) first fs 0 = some (a0, p0, r0) ∧
      genBytesMain (after base 1) e a0 inMax uart room base = .ok main ∧
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

theorem genBytesMain_length {a e a0 inMax uart room base : UInt64} {main : List Instr}
    (hg : genBytesMain a e a0 inMax uart room base = .ok main) : main.length = bytesMainSize := by
  obtain ⟨len, ov, ga, msg, gk, out, x65, x64, hl, -, -, hm, -, ho, -, -, rfl⟩ := gen_bytesMain hg
  obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := readMessage_ok hm
  obtain ⟨-, -, -, -, rfl⟩ := writeBytes_ok ho
  simp only [List.length_append, movImm_length, List.length_cons, List.length_nil,
    readBytes_length 8 0 hl, bytesMainSize]

/-- The first sixteen instructions of `genBytesMain`: the frame of 16 bytes with X30 in its first
slot, the stack's limit in X18, the address of UARTDR in X8, the masks of the reads in X11, X12,
and X13, and 0 in X7. -/
theorem run_bytesFront {A uart room : UInt64} {ms : State}
    (hc : CodeAt code A ([.subImm 31 31 16, .str 30 31 0, .addImm 18 31 0] ++ movImm 16 room ++
      [.subReg 18 18 16] ++ movImm 8 uart ++
      [.movz 11 0x10 0, .movz 12 0xF00 0, .movz 13 0xFF 0, .movz 7 0 0]))
    (hpc : ms.pc = A) (hal : ms.sp % 16 = 0)
    (hmain : ∀ j < 16, P.normal (ms.sp - 16 + UInt64.ofNat j) = true) :
    ∃ t, Reach P code ms t ∧ t.pc = after A 16 ∧ t.sp = ms.sp - 16 ∧
      t.x 18 = ms.sp - 16 - room ∧ t.x 8 = uart ∧ t.x 11 = 0x10 ∧ t.x 12 = 0xF00 ∧
      t.x 13 = 0xFF ∧ t.x 7 = 0 ∧ t.x 17 = ms.x 17 ∧ t.x 30 = ms.x 30 ∧ t.io = ms.io ∧
      t.mem = store64 ms.mem (slotAddr (ms.sp - 16) 0) (ms.x 30) := by
  have s4 := CodeAt.split code hc (n := 12) (by simp [movImm])
  have s3 := CodeAt.split code s4.1 (n := 8) (by simp [movImm])
  have s2 := CodeAt.split code s3.1 (n := 7) (by simp [movImm])
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
  have p3b : t3b.pc = after A 8 := by
    show t3a.pc + 4 = _
    rw [p3a, ← after_succ, after_after]
  have r3b : Reach P code ms t3b :=
    r2.trans (r3a.trans (reach_exec P code (by rw [p3a, after_after]; exact csub) e3b (.refl _)))
  have hk3b : ∀ q : Fin 32, q ≠ 16 → q ≠ 18 → t3b.x q = ms.x q := fun q h16 h18 => by
    rw [State.x_withPc, State.x_setX_ne (Ne.symm h18), hk3a q h16, hk2a q h18]
  -- the UART's registers
  obtain ⟨t4, r4, p4, x84, k4, sp4, mem4, io4⟩ :=
    run_movImm P code (d := 8) (v := uart) (by decide) s3.2 p3b
  have c11 : code (after A 12) = some (encode (.movz 11 0x10 0)) := by
    have := s4.2 0 (by simp)
    rwa [after_zero] at this
  have c12 : code (after A 13) = some (encode (.movz 12 0xF00 0)) := by
    have := s4.2 1 (by simp)
    rwa [after_after] at this
  have c13 : code (after A 14) = some (encode (.movz 13 0xFF 0)) := by
    have := s4.2 2 (by simp)
    rwa [after_after] at this
  have c7 : code (after A 15) = some (encode (.movz 7 0 0)) := by
    have := s4.2 3 (by simp)
    rwa [after_after] at this
  have p4' : t4.pc = after A 12 := by rw [p4, after_after]
  obtain ⟨t5, r5, p5, x115, k5, sp5, mem5, io5⟩ :=
    run_movz P code (d := 11) (v := 0x10) (by decide) (by rw [p4']; exact c11)
  have p5' : t5.pc = after A 13 := by rw [p5, p4', ← after_succ]
  obtain ⟨t6, r6, p6, x126, k6, sp6, mem6, io6⟩ :=
    run_movz P code (d := 12) (v := 0xF00) (by decide) (by rw [p5']; exact c12)
  have p6' : t6.pc = after A 14 := by rw [p6, p5', ← after_succ]
  obtain ⟨t7, r7, p7, x137, k7, sp7, mem7, io7⟩ :=
    run_movz P code (d := 13) (v := 0xFF) (by decide) (by rw [p6']; exact c13)
  have p7' : t7.pc = after A 15 := by rw [p7, p6', ← after_succ]
  obtain ⟨t8, r8, p8, x78, k8, sp8, mem8, io8⟩ :=
    run_movz P code (d := 7) (v := 0) (by decide) (by rw [p7']; exact c7)
  have hk8 : ∀ q : Fin 32, q ≠ 7 → q ≠ 13 → q ≠ 12 → q ≠ 11 → q ≠ 8 → t8.x q = t3b.x q :=
    fun q h7 h13 h12 h11 h8 => by rw [k8 q h7, k7 q h13, k6 q h12, k5 q h11, k4 q h8]
  refine ⟨t8, r3b.trans (r4.trans (r5.trans (r6.trans (r7.trans r8)))),
    by rw [p8, p7', ← after_succ], ?_, ?_, ?_, ?_, ?_, ?_, x78, ?_, ?_, ?_, ?_⟩
  · rw [sp8, sp7, sp6, sp5, sp4]
    show (t3a.setX 18 (t3a.x 18 - t3a.x 16)).sp = _
    rw [State.setX_sp, sp3a]
    rfl
  · rw [hk8 18 (by decide) (by decide) (by decide) (by decide) (by decide), State.x_withPc,
      State.x_setX_same (by decide), hx16, hk3a 18 (by decide), h18a]
  · rw [k8 8 (by decide), k7 8 (by decide), k6 8 (by decide), k5 8 (by decide)]
    exact x84
  · rw [k8 11 (by decide), k7 11 (by decide), k6 11 (by decide)]
    exact x115
  · rw [k8 12 (by decide), k7 12 (by decide)]
    exact x126
  · rw [k8 13 (by decide)]
    exact x137
  · rw [hk8 17 (by decide) (by decide) (by decide) (by decide) (by decide),
      hk3b 17 (by decide) (by decide)]
  · rw [hk8 30 (by decide) (by decide) (by decide) (by decide) (by decide),
      hk3b 30 (by decide) (by decide)]
  · rw [io8, io7, io6, io5, io4]
    show (t3a.setX 18 (t3a.x 18 - t3a.x 16)).io = _
    rw [State.setX_io, out3a]
    rfl
  · rw [mem8, mem7, mem6, mem5, mem4]
    show (t3a.setX 18 (t3a.x 18 - t3a.x 16)).mem = _
    rw [State.setX_mem, mem3a]
    rfl

theorem x31_or (s : State) (v : UInt64) : s.x 31 ||| v = v := by
  show (0 : UInt64) ||| v = v
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_or]

theorem add_root_one (g r : UInt64) : g + r + UInt64.ofNat 1 = g + UInt64.ofNat (r.toNat + 1) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
  have := r.toNat_lt
  simp only [Nat.reducePow] at *
  omega

theorem memBytes_eq (m : Mem) : ∀ (bs : List UInt8) (p : Nat),
    (∀ i (h : i < bs.length), m.bytes (p + i) = bs[i]) → memBytes m p bs.length = bs
  | [], _, _ => rfl
  | b :: bs, p, h => by
      rw [List.length_cons, memBytes, memBytes_eq m bs (p + 1) fun i hi => by
        have := h (i + 1) (by simp; omega)
        rwa [show p + (i + 1) = p + 1 + i by omega] at this]
      have := h 0 (by simp)
      rw [Nat.add_zero] at this
      rw [this]
      rfl

/-- The `SUBS XZR, X7, X16` and `B.HI` of the bound at `a`: the run reaches the stub `tB` when X7
lies above X16 and the next instruction otherwise, changing the flags alone. -/
theorem run_hi {a tB : UInt64} {g : Fin 524288}
    (hcode : CodeAt code a [.subsReg 31 7 16, .bcond 8 g]) (hg : cbField (after a 1) tB = .ok g)
    {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ (t.pc = if s.x 16 < s.x 7 then tB else after a 2) ∧
      (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  let s1 : State := { s.subs 31 (s.x 7) (s.x 16) with pc := s.pc + 4 }
  have e1 : LeanExe.A64.exec P (.subsReg 31 7 16) s = some s1 := rfl
  let s2 : State :=
    { s1 with pc := if s1.condHolds 8 then s1.pc + sext 19 g.val * 4 else s1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.bcond 8 g) s1 = some s2 := rfl
  have p1 : s1.pc = after a 1 := by show s.pc + 4 = _; rw [hpc, after_succ, after_zero]
  have hx1 : ∀ q : Fin 32, s1.x q = s.x q := fun q => by
    show (s.setX 31 (s.x 7 - s.x 16)).x q = _
    unfold State.setX
    rw [ite_eq_right (by decide)]
  have hcond : s1.condHolds 8 = decide (s.x 16 < s.x 7) := by
    rw [condHolds_8]
    show (decide (s.x 16 ≤ s.x 7) && !(s.x 7 - s.x 16 == 0)) = _
    exact cond_hi _ _
  refine ⟨s2, reach_exec P code (by rw [hpc]; exact c0) e1
      (reach_exec P code (by rw [p1]; exact c1) e2 (.refl _)), ?_, hx1, ?_, ?_, ?_⟩
  · show (if s1.condHolds 8 then s1.pc + sext 19 g.val * 4 else s1.pc + 4) = _
    rw [hcond, p1]
    by_cases h : s.x 16 < s.x 7
    · rw [if_pos (by simpa using h), if_pos h]
      exact cbField_target hg
    · rw [if_neg (by simpa using h), if_neg h, ← after_succ]
  · show (s.setX 31 (s.x 7 - s.x 16)).sp = _
    exact State.setX_sp
  · show (s.setX 31 (s.x 7 - s.x 16)).mem = _
    exact State.setX_mem
  · show (s.setX 31 (s.x 7 - s.x 16)).io = _
    exact State.setX_io

/-- The run of a program of `genBytesProgram`, whose function `k` of `m` takes and returns the two
words of a buffer and whose function 0 is the allocator, from `main` at `after base 1` with the
receiver at its first read and no poll done, on a platform whose UART lies outside Normal memory,
for Talos's runs at fuel `F`.  A byte with an error flag among the first eight ends the run at the
exit word with status 65.  When the first eight carry none, their bytes give a length L,
`rxSum P.rx 0 8`.  Above `inMax` the run ends with status 64.  Within it, after the allocator's
run gives the root `root` and the store `st1`, a byte with an error flag among the next L ends the
run with status 65, and otherwise the machine reaches the stub of an overflow of the stack when
`room` lies below `stackBound m k`, or does what `BytesResult` states for Talos's run of the
function on the root and L in the store with the bytes of the reads written from the root. -/
theorem bytesProgram_run {m : Module} {k : Nat} {fk : Function} {inMax base room area : UInt64}
    {cap : Nat} {is : List Instr}
    (hg : genBytesProgram m k inMax P.uart base room cap = .ok is)
    (hcode : CodeAt code (after base 1) is) (hm : m.imports = [])
    (hk : m.funcs[k]? = some fk) (hpk : fk.params = [.i64, .i64])
    (hrk : fk.results = [.i64, .i64]) {typeIdx : Nat}
    (h0 : m.funcs[0]? = some (LeanExe.Runtime.allocFunction typeIdx))
    (h0room : stackBound m 0 ≤ room.toNat) (F : Nat)
    (ms : State) (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0)
    (hroom : 4096 ≤ room.toNat) (htop : ms.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true)
    (h17 : ms.x 17 = area)
    (harea : ∀ j < areaSize cap, ms.mem (area + UInt64.ofNat j) = areaByte m.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true)
    (habove : area.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat)
    (hU : P.normal P.uart = false) (hrx : ms.io.rxNext = 0) (hpo : ms.io.rxPolls = 0) :
    (∀ j < 8, (∀ i < j, ¬ P.rx.Flagged i) → P.rx.Flagged j →
      ∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧ ms'.x 0 = 65 ∧ ms'.io.out = ms.io.out) ∧
    ((∀ j < 8, ¬ P.rx.Flagged j) →
      (inMax.toNat < rxSum P.rx 0 8 →
        ∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧ ms'.x 0 = 64 ∧ ms'.io.out = ms.io.out) ∧
      (rxSum P.rx 0 8 ≤ inMax.toNat → ∀ (root : UInt64) (st1 : Store Unit),
        Wasm.run F m 0 (initStore m cap) [.i64 (UInt64.ofNat (rxSum P.rx 0 8))] =
          .Success [.i64 root] st1 →
        root.toNat + rxSum P.rx 0 8 ≤ st1.mem.pages * 65536 →
        (∀ t < rxSum P.rx 0 8, (∀ i < t, ¬ P.rx.Flagged (8 + i)) → P.rx.Flagged (8 + t) →
          ∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧ ms'.x 0 = 65 ∧
            ms'.io.out = ms.io.out) ∧
        ((∀ t < rxSum P.rx 0 8, ¬ P.rx.Flagged (8 + t)) →
          (∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧ ms'.x 0 = 4 ∧
            ms'.io.out = ms.io.out ∧ room.toNat < stackBound m k) ∨
          BytesResult P code base (Wasm.run F m k
            (storeBytes st1 root.toNat (rxBytes P.rx 8 (rxSum P.rx 0 8)))
            [.i64 (UInt64.ofNat (rxSum P.rx 0 8)), .i64 root]) ms))) := by
  obtain ⟨gts, fs, first, T, main, fns, e, pk, rk, a0, p0, r0, g1, g2, g3, g4, hok, hgt, hgl,
    hfs, hfirst, hT, hen, hen0, hmg, hfg, his, hb1, hb2, hb3, hb4⟩ := gen_bytesProgram hg
  subst his
  have hsp : 4096 + room.toNat + 16 ≤ ms.sp.toNat := by unfold areaSize at habove; omega
  have h64 : m.memIs64 = false := memIs64_of_areaOk hok
  have hfm := mapM_funcOf hfs
  have hsig := sigOf_tableOf (callTargets m k) first fs
  have hend := (genFunctions_length hsig hfg).2
  have hml := genBytesMain_length hmg
  obtain ⟨len, ov, ga, msg, gk, out, x65, x64, hlen, hov, hga, hmsg, hgk, hout, hx65, hx64,
    hmeq⟩ := gen_bytesMain hmg
  have hmain : ∀ j < 16, P.normal (ms.sp - 16 + UInt64.ofNat j) = true := fun j hj => by
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
  have cmain := hc2.1
  rw [hmeq, ← after_zero A] at cmain
  obtain ⟨done, back, fail, loop, -, hback, hfail, hloop, hmsgeq⟩ := readMessage_ok hmsg
  obtain ⟨odone, oback, hodone, hoback, houteq⟩ := writeBytes_ok hout
  have q1 := CodeAt.peel code cmain (k := 16) (by simp [movImm])
  have q2 := CodeAt.peel code q1.2 (k := 80) (readBytes_length 8 0 hlen)
  have q3 := CodeAt.peel code q2.2 (k := 4) (movImm_length _ _)
  have q4 := CodeAt.peel code q3.2 (k := 5) rfl
  have q5 := CodeAt.peel code q4.2 (k := 4) (movImm_length _ _)
  have q6 := CodeAt.peel code q5.2 (k := 5) rfl
  have q7 := CodeAt.peel code q6.2 (k := 11) (by rw [hmsgeq]; rfl)
  have q8 := CodeAt.peel code q7.2 (k := 2) rfl
  have q9 := CodeAt.peel code q8.2 (k := 4) (movImm_length _ _)
  have q10 := CodeAt.peel code q9.2 (k := 8) (by rw [houteq]; rfl)
  have q11 := CodeAt.peel code q10.2 (k := 4) (movImm_length _ _)
  have q12 := CodeAt.peel code q11.2 (k := 3) rfl
  have q13 := CodeAt.peel code q12.2 (k := 5) (by simp [movImm])
  simp only [Nat.zero_add, Nat.reduceAdd] at q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  rw [after_zero] at q1
  -- the frame, X18, and the UART's registers
  obtain ⟨t1, r1, p1, sp1, x181, x81, x111, x121, x131, x71, x171, x301, io1, mem1⟩ :=
    run_bytesFront P code q1.1 hpc hal hmain
  have halm : (ms.sp - 16) % 16 = 0 := sub_aligned (k := 16) hal (by decide)
  have e16 : (ms.sp - 16).toNat = ms.sp.toNat - 16 := toNat_sub_le (by
    show 16 ≤ ms.sp.toNat
    omega)
  have e16r : (ms.sp - 16 - room).toNat = ms.sp.toNat - 16 - room.toNat := by
    rw [toNat_sub_le (by omega), e16]
  have ht16 : (ms.sp - 16).toNat < 2 ^ 63 := by
    rw [e16]
    simp only [Nat.reducePow] at *
    omega
  -- the stubs of statuses 65 and 64
  have stub65 : ∀ u : State, Reach P code ms u → u.pc = after A 146 → u.io.out = ms.io.out →
      ∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧ ms'.x 0 = 65 ∧ ms'.io.out = ms.io.out := by
    intro u ru pu ou
    obtain ⟨u2, ru2, pu2, xu2, ou2⟩ := run_stub P code (c := 65) q13.1 hx65 pu
    exact ⟨u2, ru.trans ru2, pu2, xu2, by rw [ou2, ou]⟩
  have stub64 : ∀ u : State, Reach P code ms u → u.pc = after A 151 → u.io.out = ms.io.out →
      ∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧ ms'.x 0 = 64 ∧ ms'.io.out = ms.io.out := by
    intro u ru pu ou
    obtain ⟨u2, ru2, pu2, xu2, ou2⟩ := run_stub P code (c := 64) q13.2 hx64 pu
    exact ⟨u2, ru.trans ru2, pu2, xu2, by rw [ou2, ou]⟩
  -- the length
  obtain ⟨hlenok, hlenflag⟩ := run_readBytes P code (r := 7) (by decide) 0 8 0 (by omega) hlen
    q2.1 p1 x81 x111 x121 x131 (by rw [io1, hrx]) (by rw [io1, hpo])
    (by rw [x71]; rfl)
  refine ⟨fun j hj hpre hf => ?_, fun hclean => ?_⟩
  · obtain ⟨u, ru, pu, ou⟩ := hlenflag j hj (by simpa using hpre) (by simpa using hf)
    exact stub65 u (r1.trans ru) pu (by rw [ou, io1])
  obtain ⟨t2, r2, p2, x72, k2, sp2, mem2, io2⟩ := hlenok (by simpa using hclean)
  simp only [Nat.zero_add] at x72 io2
  generalize hL : rxSum P.rx 0 8 = L at x72 ⊢
  have hL64 : L < 2 ^ 64 := by rw [← hL]; exact rxSum_lt P.rx 0 8
  have hx7 : t2.x 7 = UInt64.ofNat L := by rw [← x72, UInt64.ofNat_toNat]
  have hk2 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 14 → q ≠ 7 → t2.x q = t1.x q := k2
  -- the bound
  obtain ⟨t3, r3, p3, x163, k3, sp3, mem3, io3⟩ :=
    run_movImm P code (d := 16) (v := inMax) (by decide) q3.1 (by rw [p2, after_after])
  have q4' := CodeAt.peel code (n := 100) q4.1 (l1 := [.subsReg 31 7 16, .bcond 8 ov])
    (l2 := [.str 7 31 1, mov 0 7, .bl ga]) rfl
  obtain ⟨t4, r4, p4, k4, sp4, mem4, io4⟩ := run_hi P code (a := after A 100) (tB := after A 151)
    q4'.1 (by rw [after_after]; exact hov) (by rw [p3, after_after])
  have hx73 : t3.x 7 = UInt64.ofNat L := by
    rw [k3 7 (by decide)]
    exact hx7
  have hx74 : t4.x 7 = UInt64.ofNat L := by rw [k4]; exact hx73
  have hout4 : t4.io.out = ms.io.out := by rw [io4, io3, io2, io1]
  have r4' : Reach P code ms t4 := r1.trans (r2.trans (r3.trans r4))
  refine ⟨fun hov' => ?_, fun hle root st1 hrun hfit => ?_⟩
  · have hlt : t3.x 16 < t3.x 7 := by
      rw [hx73, x163, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
      simp only [Nat.reducePow] at *
      omega
    rw [if_pos hlt] at p4
    exact stub64 t4 r4' p4 hout4
  have hnlt : ¬ t3.x 16 < t3.x 7 := by
    rw [hx73, x163, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
    simp only [Nat.reducePow] at *
    omega
  rw [if_neg hnlt, after_after] at p4
  -- the facts of t4 that the rest needs
  have hsp4 : t4.sp = ms.sp - 16 := by rw [sp4, sp3, sp2, sp1]
  have h184 : t4.x 18 = ms.sp - 16 - room := by
    rw [k4, k3 18 (by decide), hk2 18 (by decide) (by decide) (by decide) (by decide), x181]
  have h174 : t4.x 17 = area := by
    rw [k4, k3 17 (by decide), hk2 17 (by decide) (by decide) (by decide) (by decide), x171,
      h17]
  have hmem4 : t4.mem = store64 ms.mem (slotAddr (ms.sp - 16) 0) (ms.x 30) := by
    rw [mem4, mem3, mem2, mem1]
  have hio4 : t4.io.rxNext = 8 ∧ t4.io.rxPolls = 0 := by
    rw [io4, io3, io2]
    exact ⟨rfl, rfl⟩
  -- the length into the frame's second slot, X0, and the call of the allocator
  have q5' := CodeAt.peel code (n := 102) q4'.2 (l1 := [.str 7 31 1, mov 0 7])
    (l2 := [.bl ga]) rfl
  have cstr : code (after A 102) = some (encode (.str 7 31 1)) := (CodeAt.cons.mp q5'.1).1
  have cmov : code (after A 103) = some (encode (mov 0 7)) := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp q5'.1).2).1
    rwa [after_after] at this
  have cbl : code (after A 104) = some (encode (.bl ga)) := (CodeAt.cons.mp q5'.2).1
  have halm4 : t4.sp % 16 = 0 := by rw [hsp4]; exact halm
  let t5 : State :=
    { t4 with mem := store64 t4.mem (slotAddr t4.sp 1) (t4.x 7), pc := t4.pc + 4 }
  have e5 : LeanExe.A64.exec P (.str 7 31 1) t4 = some t5 :=
    exec_str_sp P (i := 1) (by decide) halm4 fun j hj => by
      rw [hsp4]
      simpa using hmain (8 + j) (by omega)
  have p5 : t5.pc = after A 103 := by show t4.pc + 4 = _; rw [p4, ← after_succ]
  obtain ⟨t6, r6, p6, x06, k6, sp6, mem6, io6⟩ := run_setX P code (d := 0) (by decide)
    (by rw [p5]; exact cmov) (rfl : LeanExe.A64.exec P (mov 0 7) t5 = _)
  have hx06 : t6.x 0 = UInt64.ofNat L := by
    rw [x06, x31_or]
    exact hx74
  let t7 : State := { t6.setX 30 (t6.pc + 4) with pc := t6.pc + sext 26 ga.val * 4 }
  have e7 : LeanExe.A64.exec P (.bl ga) t6 = some t7 := rfl
  have p6' : t6.pc = after A 104 := by rw [p6, p5, ← after_succ]
  have r7 : Reach P code ms t7 := r4'.trans (reach_exec P code (by rw [p4]; exact cstr) e5
    (r6.trans (reach_exec P code (by rw [p6']; exact cbl) e7 (.refl _))))
  have p7 : t7.pc = a0 := by
    show t6.pc + sext 26 ga.val * 4 = _
    rw [p6', bField_target hga]
  have h307 : t7.x 30 = after A 105 := by
    rw [State.x_withPc, State.x_setX_same (by decide), p6', ← after_succ]
  have hk7 : ∀ q : Fin 32, q ≠ 30 → q ≠ 0 → t7.x q = t4.x q := fun q h30 h0' => by
    rw [State.x_withPc, State.x_setX_ne (Ne.symm h30), k6 q h0']
    rfl
  have hsp7 : t7.sp = ms.sp - 16 := by
    show (t6.setX 30 (t6.pc + 4)).sp = _
    rw [State.setX_sp, sp6]
    exact hsp4
  have hmem7 : t7.mem = store64 (store64 ms.mem (slotAddr (ms.sp - 16) 0) (ms.x 30))
      (slotAddr (ms.sp - 16) 1) (UInt64.ofNat L) := by
    show (t6.setX 30 (t6.pc + 4)).mem = _
    rw [State.setX_mem, mem6]
    show store64 t4.mem (slotAddr t4.sp 1) (t4.x 7) = _
    rw [hmem4, hsp4, hx74]
  have hio7 : t7.io = t4.io := by
    show (t6.setX 30 (t6.pc + 4)).io = _
    rw [State.setX_io, io6]
  have h187 : t7.x 18 = ms.sp - 16 - room := by
    rw [hk7 18 (by decide) (by decide), h184]
  have h177 : t7.x 17 = area := by rw [hk7 17 (by decide) (by decide), h174]
  have hd7 : (t7.sp - t7.x 18).toNat = room.toNat := by
    rw [hsp7, h187, toNat_sub_le (by omega), e16, e16r]
    omega
  have hstk7 : StackOk P t7 := by
    refine ⟨by rw [hsp7]; exact halm, ?_, ?_⟩
    · rw [hsp7, h187, e16, e16r]
      simp only [Nat.reducePow] at *
      omega
    · intro j hj
      rw [hd7] at hj
      rw [h187]
      exact hstack j (by omega)
  have hsr7 : StoreRel P cap gts (initStore m cap) t7 := by
    refine storeRel_init P hok hgt hgl (fun j hj => ?_) (fun j hj => by rw [h177]; exact hamap j hj)
      (by rw [h177, h187, e16r]; unfold areaSize at habove ⊢; omega)
    have := area.toNat_lt
    unfold areaSize at habove hj
    have hjl : (area + UInt64.ofNat j).toNat < (ms.sp - 16 - room).toNat := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat', e16r]
      simp only [Nat.reducePow] at *
      omega
    rw [hmem7, h177, store64_other _ _ _ _ (below_slot (by rw [e16r, e16]; omega) ht16
      (by decide) hjl), store64_other _ _ _ _ (below_slot (by rw [e16r, e16]; omega) ht16
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
      ([Value.i64 (UInt64.ofNat L)].take (LeanExe.Runtime.allocFunction typeIdx).params.length) :=
    by simp [LeanExe.Runtime.allocFunction, Typed, HasType]
  rcases run_outcome P code hm h64 h0 hg0 cf0 hcl (stackNeed_ok h0 _) (initStore m cap)
      [.i64 (UInt64.ofNat L)] t7 (by simp [LeanExe.Runtime.allocFunction]) hvt0 p7 hstk7 hsr7
      (by
        refine ⟨by simp [LeanExe.Runtime.allocFunction], fun i hi => ?_⟩
        simp only [LeanExe.Runtime.allocFunction, List.length_cons, List.length_nil,
          List.take_succ_cons, List.take_zero, List.reverse_cons, List.reverse_nil,
          List.nil_append] at hi ⊢
        obtain rfl : i = 0 := by omega
        show t7.x (regOf 0) = UInt64.ofNat L
        rw [show regOf 0 = 0 by decide, State.x_withPc, State.x_setX_ne (by decide)]
        exact hx06) with ⟨hov, -⟩ | hro0
  · rw [hd7] at hov
    exact absurd h0room (by unfold stackBound; omega)
  rw [hrun] at hro0
  obtain ⟨t8, r8, p8, sp8, h188, io8, mf8, -, -, hres8, -, hsr8⟩ := hro0
  have hx08 : t8.x 0 = root := by
    have := hres8.2 0 (by simp [LeanExe.Runtime.allocFunction])
    simpa [show regOf 0 = 0 by decide, LeanExe.Runtime.allocFunction, ValRel] using this
  have p8' : t8.pc = after A 105 := by rw [p8, h307]
  have hsp8 : t8.sp = ms.sp - 16 := by rw [sp8, hsp7]
  have h188' : t8.x 18 = ms.sp - 16 - room := by rw [h188, h187]
  -- the bytes of the frame's slots
  have hslot7 : load64 t7.mem (slotAddr (ms.sp - 16) 0) = ms.x 30 ∧
      load64 t7.mem (slotAddr (ms.sp - 16) 1) = UInt64.ofNat L := by
    rw [hmem7, load64_store64_same, load64_store64_other _ _ _ _
      (slot_apart (by decide) (by decide) (by decide)), load64_store64_same]
    exact ⟨rfl, rfl⟩
  have hslots : ∀ s : State,
      (∀ a : UInt64, (ms.sp - 16).toNat ≤ a.toNat → s.mem a = t7.mem a) →
      load64 s.mem (slotAddr (ms.sp - 16) 0) = ms.x 30 ∧
        load64 s.mem (slotAddr (ms.sp - 16) 1) = UInt64.ofNat L := by
    intro s hs
    rw [load64_congr (m' := t7.mem) fun j hj => hs _ (le_slot hj ht16 (by decide)
        (Nat.zero_le _)),
      load64_congr (m' := t7.mem) (a := slotAddr (ms.sp - 16) 1) fun j hj =>
        hs _ (by have := le_slot (m := 0) hj ht16 (i := 1) (by decide) (Nat.zero_le _); omega)]
    exact hslot7
  have hfr8 : ∀ a : UInt64, (ms.sp - 16).toNat ≤ a.toNat → t8.mem a = t7.mem a :=
    fun a ha => mf8 a (by rw [hsp7]; omega)
  -- the UART's registers and the block's address
  obtain ⟨t9, r9, p9, x89, k9, sp9, mem9, io9⟩ :=
    run_movImm P code (d := 8) (v := P.uart) (by decide) q5.1 p8'
  have c11 : code (after A 109) = some (encode (.movz 11 0x10 0)) := (CodeAt.cons.mp q6.1).1
  have q6a := (CodeAt.cons.mp q6.1).2
  have c12 : code (after A 110) = some (encode (.movz 12 0xF00 0)) := by
    have := (CodeAt.cons.mp q6a).1
    rwa [after_after] at this
  have q6b := (CodeAt.cons.mp q6a).2
  have c15 : code (after A 111) = some (encode (.addReg 15 17 0)) := by
    have := (CodeAt.cons.mp q6b).1
    rwa [after_after, after_after] at this
  have q6c := (CodeAt.cons.mp q6b).2
  have c15' : code (after A 112) = some (encode (.addImm 15 15 1)) := by
    have := (CodeAt.cons.mp q6c).1
    rwa [after_after, after_after, after_after] at this
  have q6d := (CodeAt.cons.mp q6c).2
  have c7l : code (after A 113) = some (encode (.ldr 7 31 1)) := by
    have := (CodeAt.cons.mp q6d).1
    rwa [after_after, after_after, after_after, after_after] at this
  have p9' : t9.pc = after A 109 := by rw [p9, after_after]
  obtain ⟨t10, r10, p10, x1110, k10, sp10, mem10, io10⟩ :=
    run_movz P code (d := 11) (v := 0x10) (by decide) (by rw [p9']; exact c11)
  have p10' : t10.pc = after A 110 := by rw [p10, p9', ← after_succ]
  obtain ⟨t11, r11, p11, x1211, k11, sp11, mem11, io11⟩ :=
    run_movz P code (d := 12) (v := 0xF00) (by decide) (by rw [p10']; exact c12)
  have p11' : t11.pc = after A 111 := by rw [p11, p10', ← after_succ]
  obtain ⟨t12, r12, p12, x1512, k12, sp12, mem12, io12⟩ := run_setX P code (d := 15)
    (by decide) (by rw [p11']; exact c15)
    (rfl : LeanExe.A64.exec P (.addReg 15 17 0) t11 = _)
  have p12' : t12.pc = after A 112 := by rw [p12, p11', ← after_succ]
  obtain ⟨t13, r13, p13, x1513, k13, sp13, mem13, io13⟩ := run_setX P code (d := 15)
    (by decide) (by rw [p12']; exact c15')
    (exec_addImm_x P (s := t12) (d := 15) (n := 15) (imm := 1) (by decide) (by decide))
  have p13' : t13.pc = after A 113 := by rw [p13, p12', ← after_succ]
  have hsp13 : t13.sp = ms.sp - 16 := by rw [sp13, sp12, sp11, sp10, sp9, hsp8]
  have hmem13 : t13.mem = t8.mem := by rw [mem13, mem12, mem11, mem10, mem9]
  obtain ⟨t14, r14, p14, x714, k14, sp14, mem14, io14⟩ := run_setX P code (d := 7)
    (by decide) (by rw [p13']; exact c7l)
    (exec_ldr_sp P (s := t13) (r := 7) (i := 1) _ (by rw [hsp13]; exact halm)
      fun j hj => by rw [hsp13]; simpa using hmain (8 + j) (by omega))
  have p14' : t14.pc = after A 114 := by rw [p14, p13', ← after_succ]
  have hk14 : ∀ q : Fin 32, q ≠ 7 → q ≠ 15 → q ≠ 12 → q ≠ 11 → q ≠ 8 → t14.x q = t8.x q :=
    fun q h7' h15' h12' h11' h8' => by
      rw [k14 q h7', k13 q h15', k12 q h15', k11 q h12', k10 q h11', k9 q h8']
  have hsp14 : t14.sp = ms.sp - 16 := by rw [sp14, hsp13]
  have hmem14 : t14.mem = t8.mem := by rw [mem14, hmem13]
  have hio14 : t14.io = t8.io := by rw [io14, io13, io12, io11, io10, io9]
  have hx714 : t14.x 7 = UInt64.ofNat L := by
    rw [x714, hsp13, hmem13]
    exact (hslots t8 hfr8).2
  have hx1514 : t14.x 15 = t14.x 17 + UInt64.ofNat (root.toNat + 1) := by
    have e15 : t14.x 15 = t8.x 17 + t8.x 0 + UInt64.ofNat 1 := by
      rw [k14 15 (by decide), x1513, x1512, k11 17 (by decide), k10 17 (by decide),
        k9 17 (by decide), k11 0 (by decide), k10 0 (by decide), k9 0 (by decide)]
      try rfl
    rw [e15, hk14 17 (by decide) (by decide) (by decide) (by decide) (by decide), hx08,
      add_root_one]
  have hsr14 : StoreRel P cap gts st1 t14 :=
    hsr8.regs (hk14 17 (by decide) (by decide) (by decide) (by decide) (by decide))
      (hk14 18 (by decide) (by decide) (by decide) (by decide) (by decide)) hmem14
  have r14 : Reach P code ms t14 :=
    r7.trans (r8.trans (r9.trans (r10.trans (r11.trans (r12.trans (r13.trans r14))))))
  have hout14 : t14.io.out = ms.io.out := by rw [hio14, io8, hio7, hout4]
  -- the reads of the message
  obtain ⟨hmok, hmflag⟩ := run_readMessage P code hmsg q7.1 (cap := cap) (gts := gts) hU L t14
    st1 root.toNat 8 p14' hx714
    (by rw [k14 8 (by decide), k13 8 (by decide), k12 8 (by decide), k11 8 (by decide),
        k10 8 (by decide)]; exact x89)
    (by rw [k14 11 (by decide), k13 11 (by decide), k12 11 (by decide), k11 11 (by decide)];
        exact x1110)
    (by rw [k14 12 (by decide), k13 12 (by decide), k12 12 (by decide)]; exact x1211)
    hx1514 (by rw [hio14, io8, hio7]; exact hio4.1) (by rw [hio14, io8, hio7]; exact hio4.2)
    hsr14 hfit
  refine ⟨fun t ht hpre hf => ?_, fun hclean' => ?_⟩
  · obtain ⟨u, ru, pu, ou⟩ := hmflag t ht hpre hf
    exact stub65 u (r14.trans ru) pu (by rw [ou, hout14])
  obtain ⟨t15, r15, p15, hsr15, k15, sp15, mf15, out15, -, -⟩ := hmok hclean'
  have p15' : t15.pc = after A 125 := by rw [p15, after_after]
  have hsp15 : t15.sp = ms.sp - 16 := by rw [sp15, hsp14]
  have h1814 : t14.x 18 = ms.sp - 16 - room := by
    rw [hk14 18 (by decide) (by decide) (by decide) (by decide) (by decide), h188']
  have h1815 : t15.x 18 = ms.sp - 16 - room := by
    rw [k15 18 (by decide) (by decide) (by decide) (by decide), h1814]
  have hfr15 : ∀ a : UInt64, (ms.sp - 16).toNat ≤ a.toNat → t15.mem a = t7.mem a :=
    fun a ha => by
      rw [mf15 a (by rw [h1814, e16r]; rw [e16] at ha; omega), hmem14, hfr8 a ha]
  -- the length into X1 and the call of the function
  have c1l : code (after A 125) = some (encode (.ldr 1 31 1)) := (CodeAt.cons.mp q8.1).1
  have cblk : code (after A 126) = some (encode (.bl gk)) := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp q8.1).2).1
    rwa [after_after] at this
  obtain ⟨t16, r16, p16, x116, k16, sp16, mem16, io16⟩ := run_setX P code (d := 1) (by decide)
    (by rw [p15']; exact c1l)
    (exec_ldr_sp P (s := t15) (r := 1) (i := 1) _ (by rw [hsp15]; exact halm)
      fun j hj => by rw [hsp15]; simpa using hmain (8 + j) (by omega))
  have hx116 : t16.x 1 = UInt64.ofNat L := by
    rw [x116, hsp15]
    exact (hslots t15 hfr15).2
  let t17 : State := { t16.setX 30 (t16.pc + 4) with pc := t16.pc + sext 26 gk.val * 4 }
  have e17 : LeanExe.A64.exec P (.bl gk) t16 = some t17 := rfl
  have p16' : t16.pc = after A 126 := by rw [p16, p15', ← after_succ]
  have r17 : Reach P code ms t17 := r14.trans (r15.trans (r16.trans
    (reach_exec P code (by rw [p16']; exact cblk) e17 (.refl _))))
  have p17 : t17.pc = e := by
    show t16.pc + sext 26 gk.val * 4 = _
    rw [p16', bField_target hgk]
  have h3017 : t17.x 30 = after A 127 := by
    rw [State.x_withPc, State.x_setX_same (by decide), p16', ← after_succ]
  have hk17 : ∀ q : Fin 32, q ≠ 30 → q ≠ 1 → t17.x q = t15.x q := fun q h30 h1 => by
    rw [State.x_withPc, State.x_setX_ne (Ne.symm h30), k16 q h1]
  have hsp17 : t17.sp = ms.sp - 16 := by
    show (t16.setX 30 (t16.pc + 4)).sp = _
    rw [State.setX_sp, sp16, hsp15]
  have h1817 : t17.x 18 = ms.sp - 16 - room := by
    rw [hk17 18 (by decide) (by decide), h1815]
  have hx017 : t17.x 0 = root := by
    rw [hk17 0 (by decide) (by decide), k15 0 (by decide) (by decide) (by decide) (by decide),
      hk14 0 (by decide) (by decide) (by decide) (by decide) (by decide), hx08]
  have hx117 : t17.x 1 = UInt64.ofNat L := by
    rw [State.x_withPc, State.x_setX_ne (by decide), hx116]
  have hmem17 : t17.mem = t15.mem := by
    show (t16.setX 30 (t16.pc + 4)).mem = _
    rw [State.setX_mem, mem16]
  have hio17 : t17.io.out = ms.io.out := by
    show (t16.setX 30 (t16.pc + 4)).io.out = _
    rw [State.setX_io, io16, out15, hout14]
  have hd17 : (t17.sp - t17.x 18).toNat = room.toNat := by
    rw [hsp17, h1817, toNat_sub_le (by omega), e16, e16r]
    omega
  have hstk17 : StackOk P t17 := by
    refine ⟨by rw [hsp17]; exact halm, ?_, ?_⟩
    · rw [hsp17, h1817, e16, e16r]
      simp only [Nat.reducePow] at *
      omega
    · intro j hj
      rw [hd17] at hj
      rw [h1817]
      exact hstack j (by omega)
  have hsr17 : StoreRel P cap gts (storeBytes st1 root.toNat (rxBytes P.rx 8 L)) t17 :=
    hsr15.regs (hk17 17 (by decide) (by decide)) (by rw [h1817, h1815]) hmem17
  obtain ⟨fk', fisk, hmk, hpk', hgk', cfk⟩ := hfuns hen
  have hfk := hfm _ hmk
  simp only at hfk
  rw [hk] at hfk
  cases hfk
  rcases run_outcome P code hm h64 hk hgk' cfk hcl (stackNeed_ok hk _)
      (storeBytes st1 root.toNat (rxBytes P.rx 8 L)) [.i64 (UInt64.ofNat L), .i64 root] t17
      (by rw [hpk]; simp) (by rw [hpk]; simp [Typed, HasType]) p17 hstk17 hsr17 (by
        rw [hpk]
        refine ⟨by simp, fun i hi => ?_⟩
        simp only [List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero,
          List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hi ⊢
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
        · show t17.x (regOf 0) = root
          rw [show regOf 0 = 0 by decide]
          exact hx017
        · show t17.x (regOf 1) = UInt64.ofNat L
          rw [show regOf 1 = 1 by decide]
          exact hx117) with ⟨hov, hovr⟩ | hro
  · rw [hd17] at hov
    obtain ⟨u, ru, pu, ou⟩ := hovr
    obtain ⟨u2, ru2, pu2, xu2, ou2⟩ := run_stub P code cs4.2 hb4 pu
    exact .inl ⟨u2, r17.trans (ru.trans ru2), pu2, xu2, by rw [ou2, ou]; exact hio17,
      by unfold stackBound; omega⟩
  refine .inr ?_
  revert hro
  cases Wasm.run F m k (storeBytes st1 root.toNat (rxBytes P.rx 8 L))
      [.i64 (UInt64.ofNat L), .i64 root] with
  | Trap st' tmsg =>
      intro hro
      obtain ⟨u, ru, outu, hmsg'⟩ := hro
      rcases hmsg' with ⟨hm1, pu⟩ | ⟨hm2, pu⟩ | ⟨hm3, pu⟩
      · obtain ⟨u2, ru2, pu2, xu2, outu2⟩ := run_stub P code cs1.1 hb1 pu
        exact ⟨u2, r17.trans (ru.trans ru2), pu2, by rw [outu2, outu]; exact hio17,
          .inl ⟨hm1, xu2⟩⟩
      · obtain ⟨u2, ru2, pu2, xu2, outu2⟩ := run_stub P code cs1.2 hb2 pu
        exact ⟨u2, r17.trans (ru.trans ru2), pu2, by rw [outu2, outu]; exact hio17,
          .inr (.inl ⟨hm2, xu2⟩)⟩
      · obtain ⟨u2, ru2, pu2, xu2, outu2⟩ := run_stub P code cs3.2 hb3 pu
        exact ⟨u2, r17.trans (ru.trans ru2), pu2, by rw [outu2, outu]; exact hio17,
          .inr (.inr ⟨hm3, xu2⟩)⟩
  | Invalid _ => intro _; trivial
  | OutOfFuel => intro _; trivial
  | Thrown _ _ _ => intro _; trivial
  | Success vs' st3 =>
  intro hro root' len bs hvs hlenbs hfitbs hbytes
  subst hvs
  obtain ⟨t18, r18, p18, sp18, h1818, io18, mf18, -, -, hres18, -, hsr18⟩ := hro
  rw [hrk] at hres18
  have hx018 : t18.x 0 = root' := by
    have := hres18.2 0 (by simp)
    simpa [show regOf 0 = 0 by decide, ValRel] using this
  have hx118 : t18.x 1 = UInt64.ofNat bs.length := by
    have := hres18.2 1 (by simp)
    have e : t18.x 1 = len := by simpa [show regOf 1 = 1 by decide, ValRel] using this
    rw [e, ← hlenbs, UInt64.ofNat_toNat]
  have p18' : t18.pc = after A 127 := by rw [p18, h3017]
  have hfr18 : ∀ a : UInt64, (ms.sp - 16).toNat ≤ a.toNat → t18.mem a = t7.mem a :=
    fun a ha => by rw [mf18 a (by rw [hsp17]; omega), hmem17, hfr15 a ha]
  -- the UART's address and the writes of the result
  obtain ⟨t19, r19, p19, x819, k19, sp19, mem19, io19⟩ :=
    run_movImm P code (d := 8) (v := P.uart) (by decide) q9.1 p18'
  have cW := q10.1
  rw [houteq] at cW
  have cw0 : code (after A 131) = some (encode (.addReg 3 17 0)) := (CodeAt.cons.mp cW).1
  have cw1 : code (after A 132) = some (encode (.addImm 3 3 1)) := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp cW).2).1
    rwa [after_after] at this
  have cWl : CodeAt code (after (after A 131) 2) [.cbz 1 odone, .ldrb 6 3 4095, .strb 6 8 0,
      .addImm 3 3 1, .subImm 1 1 1, .b oback] := by
    simpa only [after_after] using (CodeAt.cons.mp (CodeAt.cons.mp cW).2).2
  have p19' : t19.pc = after A 131 := by rw [p19, after_after]
  obtain ⟨t20, r20, p20, x320, k20, sp20, mem20, io20⟩ := run_setX P code (d := 3) (by decide)
    (by rw [p19']; exact cw0) (rfl : LeanExe.A64.exec P (.addReg 3 17 0) t19 = _)
  obtain ⟨t21, r21, p21, x321, k21, sp21, mem21, io21⟩ := run_setX P code (d := 3) (by decide)
    (by rw [p20, p19', ← after_succ]; exact cw1)
    (exec_addImm_x P (s := t20) (d := 3) (n := 3) (imm := 1) (by decide) (by decide))
  have hk21 : ∀ q : Fin 32, q ≠ 3 → q ≠ 8 → t21.x q = t18.x q := fun q h3 h8 => by
    rw [k21 q h3, k20 q h3, k19 q h8]
  have hx321 : t21.x 3 = t21.x 17 + UInt64.ofNat (root'.toNat + 1) := by
    have e3 : t21.x 3 = t18.x 17 + t18.x 0 + UInt64.ofNat 1 := by
      rw [x321, x320, k19 17 (by decide), k19 0 (by decide)]
      try rfl
    rw [e3, hk21 17 (by decide) (by decide), hx018, add_root_one]
  have hmem21 : t21.mem = t18.mem := by rw [mem21, mem20, mem19]
  have hsr21 : StoreRel P cap gts st3 t21 :=
    hsr18.regs (hk21 17 (by decide) (by decide)) (hk21 18 (by decide) (by decide)) hmem21
  have hpg3 := hsr18.pages
  obtain ⟨t22, r22, p22, out22, sp22, mem22, -, -, k22⟩ :=
    run_writeLoop P code (a := after A 131) cWl hodone hoback bs.length t21 root'.toNat
      (by rw [p21, p20, p19', ← after_succ, ← after_succ, after_after])
      (by rw [hk21 1 (by decide) (by decide)]; exact hx118)
      (by rw [k21 8 (by decide), k20 8 (by decide)]; exact x819) hx321 hsr21 hfitbs
  -- the return
  obtain ⟨t23, r23, p23, x023, k23, sp23, mem23, io23⟩ :=
    run_movImm P code (d := 0) (v := 0) (by decide) q11.1 (by rw [p22, after_after])
  have hsp23 : t23.sp = ms.sp - 16 := by
    rw [sp23, sp22, sp21, sp20, sp19, sp18, hsp17]
  have hmem23 : t23.mem = t18.mem := by rw [mem23, mem22, hmem21]
  obtain ⟨t24, r24, p24, sp24, io24, mem24, k24⟩ :=
    run_epilogue P code (n := 0) (fs := 16) (by decide) (by decide) q12.1
      (by rw [p23, after_after]) (by rw [hsp23]; exact halm)
      (fun j hj => by rw [hsp23]; simpa using hmain j (by omega))
  refine ⟨t24, r17.trans (r18.trans (r19.trans (r20.trans (r21.trans (r22.trans
    (r23.trans r24)))))), ?_, ?_, ?_⟩
  · rw [p24, hsp23, hmem23]
    exact (hslots t18 hfr18).1
  · rw [k24 0 (by decide), x023]
  · rw [io24, io23, out22, io21, io20, io19, io18, hio17, memBytes_eq st3.mem bs root'.toNat hbytes]

end LeanExe.A64
