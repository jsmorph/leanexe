import LeanExe.A64.Proof.Function

/-!
The run of a program that `genProgram` generates.  `main` saves X30 in its frame, loads the
arguments into X0 up, calls the function, writes the eight bytes of the function's result to the
UART, the lowest first, sets X0 to 0, restores X30, and returns.  `program_sim` states that the
machine does so from `main` when Talos's run of the function on the arguments returns a word.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-! ## Code that `flatMap` lays out -/

theorem length_flatMap_const {β : Type} {g : β → List Instr} {c : Nat}
    (hg : ∀ x, (g x).length = c) : ∀ l : List β, (l.flatMap g).length = c * l.length
  | [] => by simp
  | x :: xs => by
      rw [List.flatMap_cons, List.length_append, hg, length_flatMap_const hg xs,
        List.length_cons, Nat.mul_succ, Nat.add_comm]

theorem CodeAt.flatMap {β : Type} {g : β → List Instr} {c : Nat}
    (hg : ∀ x, (g x).length = c) :
    ∀ {l : List β} {a : UInt64}, CodeAt code a (l.flatMap g) →
      ∀ i (hi : i < l.length), CodeAt code (after a (c * i)) (g l[i])
  | [], _, _, i, hi => absurd hi (by simp)
  | x :: xs, a, h, i, hi => by
      rw [List.flatMap_cons] at h
      have h2 := (CodeAt.append (code := code)).mp h
      cases i with
      | zero => simpa [after_zero] using h2.1
      | succ i =>
          have := CodeAt.flatMap hg (l := xs) h2.2 i (by simp at hi; omega)
          rw [after_after, hg, show c + c * i = c * (i + 1) by rw [Nat.mul_succ, Nat.add_comm]]
            at this
          simpa using this

/-! ## The generator's program -/

theorem gen_main {a entry uart : UInt64} {args : List UInt64} {is : List Instr}
    (hg : genMain a entry args uart = .ok is) :
    args.length ≤ 8 ∧ ∃ g, bField (after a (2 + 4 * args.length)) entry = .ok g ∧
      is = [.subImm 31 31 16, .str 30 31 0] ++
        args.zipIdx.flatMap (fun (v, i) => movImm ⟨i % 32, Nat.mod_lt _ (by decide)⟩ v) ++
        [.bl g] ++ movImm 1 uart ++
        (List.range 8).flatMap (fun i =>
          [Instr.lsrImm 2 0 ⟨8 * i % 64, Nat.mod_lt _ (by decide)⟩, .strb 2 1 0]) ++
        movImm 0 0 ++ [.ldr 30 31 0, .addImm 31 31 16, .ret 30] := by
  by_cases hc : args.length > 8
  · simp [genMain, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  cases hb : bField (after a (2 + 4 * args.length)) entry with
  | error e => simp [genMain, hc, hb, bind, Except.bind] at hg
  | ok g =>
      simp [genMain, hc, hb, bind, Except.bind, pure, Except.pure] at hg
      subst hg
      exact ⟨by omega, g, rfl, by simp⟩

theorem loads_length (args : List UInt64) :
    (args.zipIdx.flatMap fun (v, i) =>
      movImm ⟨i % 32, Nat.mod_lt _ (by decide)⟩ v).length = 4 * args.length := by
  rw [length_flatMap_const (c := 4) ?_, List.length_zipIdx]
  rintro ⟨v, i⟩
  rfl

theorem writes_length :
    ((List.range 8).flatMap fun i =>
      [Instr.lsrImm 2 0 ⟨8 * i % 64, Nat.mod_lt _ (by decide)⟩, .strb 2 1 0]).length = 16 := by
  rw [length_flatMap_const (c := 2) (fun _ => rfl), List.length_range]

theorem genMain_length {a entry uart : UInt64} {args : List UInt64} {is : List Instr}
    (hg : genMain a entry args uart = .ok is) : is.length = mainSize args.length := by
  obtain ⟨-, g, -, rfl⟩ := gen_main hg
  simp only [List.length_append, loads_length, writes_length]
  simp only [List.length_cons, List.length_nil, mainSize, movImm]

theorem movImm_length (d : Fin 32) (v : UInt64) : (movImm d v).length = 4 := rfl

theorem CodeAt.split {a : UInt64} {l1 l2 : List Instr} {n : Nat}
    (h : CodeAt code a (l1 ++ l2)) (hn : l1.length = n) :
    CodeAt code a l1 ∧ CodeAt code (after a n) l2 := by
  have := (CodeAt.append (code := code)).mp h
  rwa [hn] at this

theorem gen_program {m : Module} {k : Nat} {args : List UInt64} {uart base : UInt64}
    {is : List Instr} (hg : genProgram m k args uart base = .ok is) :
    ∃ f main fn stubs, m.funcs[k]? = some f ∧
      genMain (after base 1) (after (after base 1) (mainSize args.length)) args uart =
        .ok main ∧
      genFunction (after (after (after base 1) (mainSize args.length)) (functionSize f))
        (after (after (after (after base 1) (mainSize args.length)) (functionSize f)) 10)
        (after (after base 1) (mainSize args.length)) f = .ok fn ∧
      is = main ++ fn ++ stubs := by
  cases hk : m.funcs[k]? with
  | none =>
      simp [genProgram, hk, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  | some f =>
      simp [genProgram, hk, bind, Except.bind, pure, Except.pure] at hg
      split at hg
      · cases hg
      rename_i main hmain
      split at hg
      · cases hg
      rename_i fn hfn
      split at hg
      · cases hg
      rename_i b1 _
      split at hg
      · cases hg
      rename_i b2 _
      split at hg
      · cases hg
      rename_i b3 _
      cases hg
      exact ⟨f, main, fn, b1 ++ b2 ++ b3, rfl, hmain, hfn, by simp⟩

/-! ## Runs of `main`'s parts -/

/-- The loads of `args` into X0 up. -/
theorem run_loads {args : List UInt64} (h8 : args.length ≤ 8) {a : UInt64} {s : State}
    (hcode : CodeAt code a
      (args.zipIdx.flatMap fun (v, i) => movImm ⟨i % 32, Nat.mod_lt _ (by decide)⟩ v))
    (hpc : s.pc = a) :
    ∃ s', Reach P code s s' ∧ s'.pc = after a (4 * args.length) ∧
      (∀ i (hi : i < args.length), s'.x ⟨i % 32, Nat.mod_lt _ (by decide)⟩ = args[i]) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.out = s.out := by
  have key : ∀ j ≤ args.length, ∃ s', Reach P code s s' ∧ s'.pc = after a (4 * j) ∧
      (∀ i (hi : i < j) (hi' : i < args.length),
        s'.x ⟨i % 32, Nat.mod_lt _ (by decide)⟩ = args[i]) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.out = s.out := by
    intro j
    induction j with
    | zero =>
        exact fun _ => ⟨s, .refl _, by rw [hpc, Nat.mul_zero, after_zero],
          fun i hi => absurd hi (by omega), rfl, rfl, rfl⟩
    | succ j ih =>
        intro hj
        obtain ⟨s', hr, hp, hx, hsp, hmem, hout⟩ := ih (by omega)
        have cj := CodeAt.flatMap code (c := 4) ?_ hcode j (by simp; omega)
        rotate_left
        · rintro ⟨v, i⟩
          rfl
        simp only [List.getElem_zipIdx, Nat.zero_add] at cj
        obtain ⟨s'', hr', hp', hd, hk, hsp', hmem', hout'⟩ :=
          run_movImm P code (show j % 32 < 31 by omega) cj hp
        refine ⟨s'', hr.trans hr', by rw [hp', after_after, Nat.mul_succ], fun i hi hi' => ?_,
          by rw [hsp', hsp], by rw [hmem', hmem], by rw [hout', hout]⟩
        by_cases hij : i = j
        · subst hij
          exact hd
        · rw [hk _ fun e => hij (by have : i % 32 = j % 32 := congrArg Fin.val e; omega)]
          exact hx i (by omega) hi'
  obtain ⟨s', hr, hp, hx, hsp, hmem, hout⟩ := key _ (Nat.le_refl _)
  exact ⟨s', hr, hp, fun i hi => hx i hi hi, hsp, hmem, hout⟩

/-- The writes of the eight bytes of X0 to the UART at X1. -/
theorem run_writes {a : UInt64} {s : State}
    (hcode : CodeAt code a ((List.range 8).flatMap fun i =>
      [Instr.lsrImm 2 0 ⟨8 * i % 64, Nat.mod_lt _ (by decide)⟩, .strb 2 1 0]))
    (hpc : s.pc = a) (h1 : s.x 1 = P.uart) :
    ∃ s', Reach P code s s' ∧ s'.pc = after a 16 ∧
      s'.out = s.out ++ (List.range 8).map (fun j => (s.x 0 >>> UInt64.ofNat (8 * j)).toUInt8) ∧
      s'.x 0 = s.x 0 ∧ s'.sp = s.sp ∧ s'.mem = s.mem := by
  have key : ∀ j ≤ 8, ∃ s', Reach P code s s' ∧ s'.pc = after a (2 * j) ∧
      s'.out = s.out ++ (List.range j).map (fun j => (s.x 0 >>> UInt64.ofNat (8 * j)).toUInt8) ∧
      s'.x 0 = s.x 0 ∧ s'.x 1 = s.x 1 ∧ s'.sp = s.sp ∧ s'.mem = s.mem := by
    intro j
    induction j with
    | zero =>
        exact fun _ => ⟨s, .refl _, by rw [hpc, Nat.mul_zero, after_zero], by simp, rfl, rfl,
          rfl, rfl⟩
    | succ j ih =>
        intro hj
        obtain ⟨s', hr, hp, hout, hx0, hx1, hsp, hmem⟩ := ih (by omega)
        have cj := CodeAt.flatMap code (c := 2) (fun _ => rfl) hcode j (by simp; omega)
        simp only [List.getElem_range] at cj
        have c0 := (CodeAt.cons.mp cj).1
        have c1 := (CodeAt.cons.mp (CodeAt.cons.mp cj).2).1
        let w : UInt64 := s'.x 0 >>> UInt64.ofNat (8 * j % 64)
        let s1 : State := { s'.setX 2 w with pc := s'.pc + 4 }
        have e1 : LeanExe.A64.exec P (.lsrImm 2 0 ⟨8 * j % 64, Nat.mod_lt _ (by decide)⟩) s' =
            some s1 := rfl
        have hx1' : s1.x 1 = P.uart := by
          show (s'.setX 2 w).x 1 = P.uart
          rw [State.x_setX_ne (by decide), hx1, h1]
        let s2 : State := { s1 with out := s1.out ++ [(s1.x 2).toUInt8], pc := s1.pc + 4 }
        have hxsp : s1.xsp 1 = P.uart := by rw [State.xsp_eq_x (by decide), hx1']
        have e2 : LeanExe.A64.exec P (.strb 2 1 0) s1 = some s2 := by
          simp [exec, hxsp, State.spAligned, s2]
        have p1 : s1.pc = after (after a (2 * j)) 1 := by
          rw [after_succ, after_zero]
          show s'.pc + 4 = _
          rw [hp]
        have hw : s1.x 2 = s.x 0 >>> UInt64.ofNat (8 * j) := by
          show (s'.setX 2 w).x 2 = _
          rw [State.x_setX_same (by decide)]
          show s'.x 0 >>> UInt64.ofNat (8 * j % 64) = _
          rw [hx0, Nat.mod_eq_of_lt (by omega)]
        refine ⟨s2, hr.trans (reach_exec P code (by rw [hp]; exact c0) e1
          (reach_exec P code (by rw [p1]; exact c1) e2 (.refl _))), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show s1.pc + 4 = _
          rw [p1, ← after_succ, after_after, Nat.mul_succ]
        · show s1.out ++ [(s1.x 2).toUInt8] = _
          rw [hw, List.range_succ, List.map_append, ← List.append_assoc, ← hout]
          rfl
        · show (s'.setX 2 w).x 0 = _
          rw [State.x_setX_ne (by decide), hx0]
        · show (s'.setX 2 w).x 1 = _
          rw [State.x_setX_ne (by decide), hx1]
        · show (s'.setX 2 w).sp = _
          rw [State.setX_sp, hsp]
        · show (s'.setX 2 w).mem = _
          rw [State.setX_mem, hmem]
  obtain ⟨s', hr, hp, hout, hx0, -, hsp, hmem⟩ := key 8 (Nat.le_refl _)
  exact ⟨s', hr, hp, hout, hx0, hsp, hmem⟩

/-! ## The program -/

/-- The bytes of the slot at `sp` lie outside the frame of `fs` bytes below `sp`. -/
theorem above_frame {sp : UInt64} {fs k : Nat} (hfs : fs < 4096) (hk : k < 8) :
    ¬ slotAddr sp 0 + UInt64.ofNat k - (sp - UInt64.ofNat fs) < UInt64.ofNat fs := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, UInt64.toNat_add, toNat_slot sp 0,
    UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  have := sp.toNat_lt
  simp only [Nat.reducePow] at *
  omega

theorem stack_main {sp : UInt64} {j : Nat} (hj : j < 16) :
    sp - 16 + UInt64.ofNat j = sp - 4112 + UInt64.ofNat (4096 + j) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat']
  have := sp.toNat_lt
  have h16 : (16 : UInt64).toNat = 16 := rfl
  have h4112 : (4112 : UInt64).toNat = 4112 := rfl
  rw [h16, h4112]
  simp only [Nat.reducePow] at *
  omega

theorem stack_fn {sp : UInt64} {fs j : Nat} (hfs : fs < 4096) (hj : j < fs) :
    sp - 16 - UInt64.ofNat fs + UInt64.ofNat j = sp - 4112 + UInt64.ofNat (4096 - fs + j) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat']
  have := sp.toNat_lt
  have h16 : (16 : UInt64).toNat = 16 := rfl
  have h4112 : (4112 : UInt64).toNat = 4112 := rfl
  rw [h16, h4112]
  simp only [Nat.reducePow] at *
  omega

/-- The run of the program that runs function `k` of `m`, which imports nothing, on the words
`args`, from `main` at `after base 1`: when Talos's run of the function on the arguments returns
the word `y`, the machine returns to the address in X30 with SP as it was, X0 = 0, and the eight
bytes of `y`, the lowest first, appended to the UART's output.  The 4112 bytes below SP, the 16
of `main`'s frame and at most 4096 of the function's, must be Normal memory. -/
theorem program_sim {m : Module} {k : Nat} {f : Function} {args : List UInt64} {base : UInt64}
    {is : List Instr} (hg : genProgram m k args P.uart base = .ok is)
    (hcode : CodeAt code (after base 1) is) (hm : m.imports = []) (hk : m.funcs[k]? = some f)
    (hloc : ∀ t ∈ f.locals, ValRel t.zero 0) (hp : args.length = f.params.length)
    {F : Nat} {α : Type} {st st' : Store α} {y : UInt64}
    (hrun : Wasm.run F m k st (args.map .i64).reverse = .Success [.i64 y] st')
    (ms : State) (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0)
    (hstack : ∀ j < 4112, P.normal (ms.sp - 4112 + UInt64.ofNat j) = true) :
    ∃ ms', Reach P code ms ms' ∧ ms'.pc = ms.x 30 ∧ ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧
      ms'.out = ms.out ++ (List.range 8).map fun j => (y >>> UInt64.ofNat (8 * j)).toUInt8 := by
  obtain ⟨f', main, fn, stubs, hk', hmg, hfg, rfl⟩ := gen_program hg
  rw [hk] at hk'
  cases hk'
  obtain ⟨h8, g, hbl, hmeq⟩ := gen_main hmg
  obtain ⟨-, -, hff, -⟩ := gen_function hfg
  have hmain : ∀ j < 16, P.normal (ms.sp - 16 + UInt64.ofNat j) = true := fun j hj => by
    rw [stack_main hj]
    exact hstack _ (by omega)
  have hfn : ∀ j < frameSize (f.params.length + f.locals.length),
      P.normal (ms.sp - 16 - UInt64.ofNat (frameSize (f.params.length + f.locals.length)) +
        UInt64.ofNat j) = true := fun j hj => by
    rw [stack_fn hff hj]
    exact hstack _ (by omega)
  have hc := (CodeAt.append (code := code)).mp hcode
  have hc2 := CodeAt.split code hc.1 (genMain_length hmg)
  have cfn := hc2.2
  have cmain := hc2.1
  rw [hmeq] at cmain
  generalize hA : after base 1 = A at *
  generalize hn : args.length = n at *
  have hL := loads_length args
  rw [hn] at hL
  have s6 := CodeAt.split code cmain (n := 4 * n + 27) (by
    simp only [List.length_append, hL, writes_length, movImm_length, List.length_cons,
      List.length_nil]
    all_goals omega)
  have s5 := CodeAt.split code s6.1 (n := 4 * n + 23) (by
    simp only [List.length_append, hL, writes_length, movImm_length, List.length_cons,
      List.length_nil]
    all_goals omega)
  have s4 := CodeAt.split code s5.1 (n := 4 * n + 7) (by
    simp only [List.length_append, hL, movImm_length, List.length_cons, List.length_nil]
    all_goals omega)
  have s3 := CodeAt.split code s4.1 (n := 4 * n + 3) (by
    simp only [List.length_append, hL, List.length_cons, List.length_nil]
    all_goals omega)
  have s2 := CodeAt.split code s3.1 (n := 2 + 4 * n) (by
    simp only [List.length_append, hL, List.length_cons, List.length_nil]
    all_goals omega)
  have s1 := CodeAt.split code s2.1 (n := 2) rfl
  -- `sub` and `str` of X30
  have c0 := (CodeAt.cons.mp s1.1).1
  have c1 := (CodeAt.cons.mp (CodeAt.cons.mp s1.1).2).1
  have halm : (ms.sp - 16) % 16 = 0 := sub_aligned (k := 16) hal (by decide)
  let t1 : State := { ms with sp := ms.sp - 16, pc := ms.pc + 4 }
  have e1 : LeanExe.A64.exec P (.subImm 31 31 16) ms = some t1 := rfl
  let t2 : State :=
    { t1 with mem := store64 t1.mem (slotAddr t1.sp 0) (t1.x 30), pc := t1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.str 30 31 0) t1 = some t2 :=
    exec_str_sp P (i := 0) (by decide) halm fun j hj => by
      simpa using hmain j (by omega)
  have p2 : t2.pc = after A 2 := by
    show ms.pc + 4 + 4 = A + 4 * UInt64.ofNat 2
    rw [hpc, UInt64.add_assoc]
    congr 1
  have r2 : Reach P code ms t2 :=
    reach_exec P code (by rw [hpc]; exact c0) e1
      (reach_exec P code (by show code (ms.pc + 4) = _; rw [hpc]; simpa [after] using c1) e2
        (.refl _))
  -- the loads
  obtain ⟨t3, r3, p3, hx3, sp3, mem3, out3⟩ :=
    run_loads P code (args := args) (by omega) s1.2 p2
  rw [hn, after_after] at p3
  -- the call
  have cbl : code (after A (2 + 4 * n)) = some (encode (.bl g)) := (CodeAt.cons.mp s2.2).1
  let t4 : State := { t3.setX 30 (t3.pc + 4) with pc := t3.pc + sext 26 g.val * 4 }
  have e4 : LeanExe.A64.exec P (.bl g) t3 = some t4 := rfl
  have p4 : t4.pc = after A (mainSize n) := by
    show t3.pc + sext 26 g.val * 4 = _
    rw [p3, bField_target hbl]
  have sp4 : t4.sp = ms.sp - 16 := by
    show (t3.setX 30 (t3.pc + 4)).sp = _
    rw [State.setX_sp, sp3]
  have h30 : t4.x 30 = after A (4 * n + 3) := by
    show (t3.setX 30 (t3.pc + 4)).x 30 = _
    rw [State.x_setX_same (by decide), p3, ← after_succ]
    congr 1
    omega
  obtain ⟨t5, r5, hret⟩ := run_sim P code hm hk hfg cfn hloc
    (args := args.map .i64) (by simp [hn, hp]) hrun t4 p4 (by rw [sp4]; exact halm)
    (by rw [sp4]; exact hfn) (fun i hi => by
      simp only [List.getElem_map, ValRel]
      show (t3.setX 30 (t3.pc + 4)).x ⟨i % 32, Nat.mod_lt _ (by decide)⟩ = _
      rw [State.x_setX_ne (fun e => by
        have : 30 = i % 32 := congrArg Fin.val e
        simp at hi
        omega)]
      exact hx3 i (by simpa using hi))
  have hy : t5.x 0 = y := hret.res (.i64 y) (by simp)
  -- the result's bytes
  obtain ⟨t6, r6, p6, hx6, hk6, sp6, mem6, out6⟩ :=
    run_movImm P code (d := 1) (v := P.uart) (by decide) s3.2 (by rw [hret.pc, h30])
  obtain ⟨t7, r7, p7, out7, hx7, sp7, mem7⟩ :=
    run_writes P code (s := t6) s4.2
      (by rw [p6, after_after, show 4 * n + 3 + 4 = 4 * n + 7 by omega]) hx6
  obtain ⟨t8, r8, p8, hx8, hk8, sp8, mem8, out8⟩ :=
    run_movImm P code (d := 0) (v := 0) (by decide) s5.2
      (by rw [p7, after_after, show 4 * n + 7 + 16 = 4 * n + 23 by omega])
  have sp8' : t8.sp = ms.sp - 16 := by rw [sp8, sp7, sp6, hret.sp, sp4]
  have p8' : t8.pc = after A (4 * n + 27) := by
    rw [p8, after_after, show 4 * n + 23 + 4 = 4 * n + 27 by omega]
  have al8 : t8.sp % 16 = 0 := by rw [sp8']; exact halm
  have mp8 : ∀ j < 8, P.normal (t8.sp + UInt64.ofNat (8 * 0 + j)) = true := fun j hj => by
    rw [sp8']
    simpa using hmain j (by omega)
  obtain ⟨t9, r9, p9, sp9, out9, mem9, hx9⟩ :=
    run_epilogue P code (n := 0) (fs := 16) (by decide) (by decide) s6.2 p8' al8 mp8
  refine ⟨t9, r2.trans (r3.trans (reach_exec P code (by rw [p3]; exact cbl) e4
    (r5.trans (r6.trans (r7.trans (r8.trans r9)))))), ?_, ?_, ?_, ?_⟩
  · have hab : ∀ k < 8, ¬ slotAddr (ms.sp - 16) 0 + UInt64.ofNat k -
        (t4.sp - UInt64.ofNat (frameSize (f.params.length + f.locals.length))) <
        UInt64.ofNat (frameSize (f.params.length + f.locals.length)) := fun k hk => by
      rw [sp4]
      exact above_frame hff hk
    rw [p9, sp8', mem8, mem7, mem6, load64_congr (m' := t4.mem) fun k hk => hret.mem _ (hab k hk)]
    show load64 t3.mem _ = _
    rw [mem3]
    exact load64_store64_same _ _ _
  · rw [sp9, sp8', show UInt64.ofNat 16 = 16 from rfl, UInt64.sub_add_cancel]
  · rw [hx9, hx8]
  · rw [out9, out8, out7, hk6 0 (by decide), hy, out6, hret.out]
    show (t3.setX 30 (t3.pc + 4)).out ++ _ = _
    rw [State.setX_out, out3]

end LeanExe.A64
