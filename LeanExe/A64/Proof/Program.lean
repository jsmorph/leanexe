import LeanExe.A64.Proof.Function

/-!
The run of a program that `genProgram` generates.  `main` saves X30 in its frame, sets the
stack's limit in X18 a given number of bytes below that frame, loads the arguments into X0 up,
calls the function, writes the eight bytes of the function's result to the
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

theorem gen_main {a entry uart room : UInt64} {args : List UInt64} {is : List Instr}
    (hg : genMain a entry args uart room = .ok is) :
    args.length ≤ 8 ∧ ∃ g, bField (after a (8 + 4 * args.length)) entry = .ok g ∧
      is = [.subImm 31 31 16, .str 30 31 0, .addImm 18 31 0] ++ movImm 16 room ++
        [.subReg 18 18 16] ++
        args.zipIdx.flatMap (fun (v, i) => movImm ⟨i % 32, Nat.mod_lt _ (by decide)⟩ v) ++
        [.bl g] ++ movImm 1 uart ++
        (List.range 8).flatMap (fun i =>
          [Instr.lsrImm 2 0 ⟨8 * i % 64, Nat.mod_lt _ (by decide)⟩, .strb 2 1 0]) ++
        movImm 0 0 ++ [.ldr 30 31 0, .addImm 31 31 16, .ret 30] := by
  by_cases hc : args.length > 8
  · simp [genMain, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  cases hb : bField (after a (8 + 4 * args.length)) entry with
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

theorem genMain_length {a entry uart room : UInt64} {args : List UInt64} {is : List Instr}
    (hg : genMain a entry args uart room = .ok is) : is.length = mainSize args.length := by
  obtain ⟨-, g, -, rfl⟩ := gen_main hg
  simp only [List.length_append, loads_length, writes_length]
  simp only [List.length_cons, List.length_nil, mainSize, movImm]

theorem movImm_length (d : Fin 32) (v : UInt64) : (movImm d v).length = 4 := rfl

theorem CodeAt.split {a : UInt64} {l1 l2 : List Instr} {n : Nat}
    (h : CodeAt code a (l1 ++ l2)) (hn : l1.length = n) :
    CodeAt code a l1 ∧ CodeAt code (after a n) l2 := by
  have := (CodeAt.append (code := code)).mp h
  rwa [hn] at this

theorem genFunction_length {callee : Table}
    {tU tB tD tS entry : UInt64} {f : Function} {is : List Instr}
    (hg : genFunction callee tU tB tD tS entry f = .ok is) :
    is.length = functionSize (sigOf callee) f := by
  obtain ⟨-, -, -, hf, hn, stores, body, fin, g, hsl, -, hl, -, -, rfl⟩ := gen_function hg
  have hs := (genList_size _ _ _ f.body body fin hl).1
  simp only [List.map_cons, List.map_nil, List.length_nil, Ctl.arity_mk,
    List.length_reverse] at hs
  simp only [List.length_append, List.length_cons, List.length_nil, hsl, hs, functionSize]

/-! ## The layout of the functions -/

theorem mapM_funcOf {m : Module} : ∀ {ks : List Nat} {fs : List (Nat × Function)},
    ks.mapM (funcOf m) = .ok fs → ∀ x ∈ fs, m.funcs[x.1]? = some x.2
  | [], fs, h => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp
  | j :: ks, fs, h => by
      rw [List.mapM_cons] at h
      cases h1 : funcOf m j with
      | error e => simp [h1, bind, Except.bind] at h
      | ok y =>
          cases h2 : ks.mapM (funcOf m) with
          | error e => simp [h1, h2, bind, Except.bind] at h
          | ok ys =>
              simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
              subst h
              intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · unfold funcOf at h1
                split at h1
                · rename_i f hf
                  simp only [pure, Except.pure, Except.ok.injEq] at h1
                  subst h1
                  exact hf
                · simp [throw, throwThe, MonadExceptOf.throw] at h1
              · exact mapM_funcOf h2 x hx

theorem find_entriesFrom (sig : Nat → Option (Nat × Nat)) (j : Nat) :
    ∀ (a : UInt64) (fs : List (Nat × Function)),
      ((entriesFrom sig a fs).find? (·.1 = j)).map (fun x => (x.2.2.1.length, x.2.2.2.length)) =
        (fs.find? (·.1 = j)).map (fun x => (x.2.params.length, x.2.results.length))
  | _, [] => rfl
  | a, (j', f) :: rest => by
      by_cases h : j' = j
      · simp [entriesFrom, List.find?_cons, h]
      · simp only [entriesFrom, List.find?_cons, h, decide_false]
        exact find_entriesFrom sig j _ rest

theorem sigOf_tableOf (targets : List Nat) (a : UInt64) (fs : List (Nat × Function)) :
    sigOf (tableOf targets a fs) = sigIn targets fs := by
  funext j
  simp only [sigOf, tableOf, sigIn]
  split
  · simp only [entryIn, Option.map_map]
    exact find_entriesFrom _ j a fs
  · rfl

theorem entryIn_mem {sig : Nat → Option (Nat × Nat)} {a : UInt64} {fs : List (Nat × Function)}
    {j : Nat} {c : UInt64 × List ValueType × List ValueType} (h : entryIn sig a fs j = some c) :
    (j, c) ∈ entriesFrom sig a fs := by
  unfold entryIn at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  have h1 := List.mem_of_find?_eq_some hx
  have h2 := List.find?_some hx
  simp only [decide_eq_true_eq] at h2
  rw [← h2]
  exact h1

/-- The number of instructions of the functions of `fs` that `genFunctions` lays out from `a`,
and the address after them. -/
theorem genFunctions_length {callee : Table} {tU tB tD tS : UInt64}
    {sig : Nat → Option (Nat × Nat)} (hsig : sigOf callee = sig) :
    ∀ {a : UInt64} {fs : List (Nat × Function)} {is : List Instr},
      genFunctions callee tU tB tD tS a fs = .ok is →
      is.length = (fs.map fun x => functionSize sig x.2).sum ∧ endOf sig a fs = after a is.length
  | a, [], is, hg => by
      simp only [genFunctions, pure, Except.pure, Except.ok.injEq] at hg
      subst hg
      exact ⟨rfl, by rw [List.length_nil, after_zero]; rfl⟩
  | a, (j, f) :: rest, is, hg => by
      simp only [genFunctions, bind, Except.bind] at hg
      cases h1 : genFunction callee tU tB tD tS a f with
      | error e => simp [h1] at hg
      | ok is1 =>
          cases h2 : genFunctions callee tU tB tD tS (after a is1.length) rest with
          | error e => simp [h1, h2] at hg
          | ok is2 =>
              simp [h1, h2, pure, Except.pure] at hg
              subst hg
              have hl1 : is1.length = functionSize sig f := by rw [genFunction_length h1, hsig]
              obtain ⟨hl2, he2⟩ := genFunctions_length hsig h2
              refine ⟨?_, ?_⟩
              · simp only [List.map_cons, List.sum_cons, List.length_append, hl1, hl2]
              · simp only [endOf]
                rw [← hl1, he2, after_after, List.length_append]

/-- The code of each function of `fs` that `genFunctions` lays out from `a`, at its entry. -/
theorem gen_functions {callee : Table} {tU tB tD tS : UInt64}
    {sig : Nat → Option (Nat × Nat)} (hsig : sigOf callee = sig) :
    ∀ {a : UInt64} {fs : List (Nat × Function)} {is : List Instr},
      genFunctions callee tU tB tD tS a fs = .ok is → CodeAt code a is →
      ∀ x ∈ entriesFrom sig a fs, ∃ f fis, (x.1, f) ∈ fs ∧ x.2.2 = (f.params, f.results) ∧
        genFunction callee tU tB tD tS x.2.1 f = .ok fis ∧ CodeAt code x.2.1 fis
  | a, [], is, _, _ => fun x hx => by simp [entriesFrom] at hx
  | a, (j, f) :: rest, is, hg, hcode => by
      simp only [genFunctions, bind, Except.bind] at hg
      cases h1 : genFunction callee tU tB tD tS a f with
      | error e => simp [h1] at hg
      | ok is1 =>
          cases h2 : genFunctions callee tU tB tD tS (after a is1.length) rest with
          | error e => simp [h1, h2] at hg
          | ok is2 =>
              simp [h1, h2, pure, Except.pure] at hg
              subst hg
              have hc := (CodeAt.append (code := code)).mp hcode
              have hl1 : is1.length = functionSize sig f := by rw [genFunction_length h1, hsig]
              have ht2 := gen_functions hsig h2 hc.2
              intro x hx
              simp only [entriesFrom, List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact ⟨f, is1, by simp, rfl, h1, hc.1⟩
              · rw [← hl1] at hx
                obtain ⟨f', fis, hm, hp, hgen, hcd⟩ := ht2 x hx
                exact ⟨f', fis, List.mem_cons_of_mem _ hm, hp, hgen, hcd⟩

/-! ## The generator's program -/

theorem gen_program {m : Module} {k : Nat} {args : List UInt64} {uart base room : UInt64}
    {is : List Instr} (hg : genProgram m k args uart base room = .ok is) :
    ∃ fs first T main fns e pk rk g1 g2 g3 g4,
      (reachFrom m k).mapM (funcOf m) = .ok fs ∧
      first = after (after base 1) (mainSize args.length) ∧
      T = endOf (sigIn (callTargets m k) fs) first fs ∧
      entryIn (sigIn (callTargets m k) fs) first fs k = some (e, pk, rk) ∧
      pk.all (· == .i64) = true ∧
      genMain (after base 1) e args uart room = .ok main ∧
      genFunctions (tableOf (callTargets m k) first fs) T (after T 5) (after T 10) (after T 15)
        first fs = .ok fns ∧
      is = main ++ fns ++ (movImm 0 (UInt64.ofNat 1) ++ [.b g1] ++
        (movImm 0 (UInt64.ofNat 2) ++ [.b g2]) ++ (movImm 0 (UInt64.ofNat 3) ++ [.b g3]) ++
        (movImm 0 (UInt64.ofNat 4) ++ [.b g4])) ∧
      bField (after T 4) base = .ok g1 ∧ bField (after (after T 5) 4) base = .ok g2 ∧
      bField (after (after T 10) 4) base = .ok g3 ∧
      bField (after (after T 15) 4) base = .ok g4 := by
  simp only [genProgram] at hg
  cases hfs : (reachFrom m k).mapM (funcOf m) with
  | error e => simp [hfs, bind, Except.bind] at hg
  | ok fs =>
      simp only [hfs, bind, Except.bind] at hg
      generalize hfirst : after (after base 1) (mainSize args.length) = first at hg
      generalize hT : endOf (sigIn (callTargets m k) fs) first fs = T at hg
      cases hen : entryIn (sigIn (callTargets m k) fs) first fs k with
      | none => simp [hen, throw, throwThe, MonadExceptOf.throw] at hg
      | some c =>
          obtain ⟨e, pk, rk⟩ := c
          have hps : pk.all (· == .i64) = true := by
            cases h : pk.all (· == .i64) with
            | true => rfl
            | false => simp [hen, h, throw, throwThe, MonadExceptOf.throw] at hg
          simp only [hen, hps, if_true, pure, Except.pure] at hg
          cases hmn : genMain (after base 1) e args uart room with
          | error err => simp [hmn] at hg
          | ok main =>
              simp only [hmn] at hg
              cases hfn : genFunctions (tableOf (callTargets m k) first fs) T (after T 5)
                  (after T 10) (after T 15) first fs with
              | error err => simp [hfn] at hg
              | ok fns =>
                  simp only [hfn] at hg
                  cases hb1 : bField (after T 4) base with
                  | error err => simp [hb1] at hg
                  | ok g1 =>
                  cases hb2 : bField (after (after T 5) 4) base with
                  | error err => simp [hb1, hb2] at hg
                  | ok g2 =>
                  cases hb3 : bField (after (after T 10) 4) base with
                  | error err => simp [hb1, hb2, hb3] at hg
                  | ok g3 =>
                  cases hb4 : bField (after (after T 15) 4) base with
                  | error err => simp [hb1, hb2, hb3, hb4] at hg
                  | ok g4 =>
                  simp [hb1, hb2, hb3, hb4] at hg
                  refine ⟨fs, first, T, main, fns, e, pk, rk, g1, g2, g3, g4, rfl, rfl, hT.symm,
                    hen, hps, hmn, hfn, ?_, hb1, hb2, hb3, hb4⟩
                  rw [← hg]
                  simp [List.append_assoc]

theorem genProgram_length {m : Module} {k : Nat} {args : List UInt64}
    {uart base room : UInt64} {is : List Instr} (hg : genProgram m k args uart base room = .ok is)
    {fs : List (Nat × Function)} (hfs : (reachFrom m k).mapM (funcOf m) = .ok fs) :
    is.length = mainSize args.length +
      (fs.map fun x => functionSize (sigIn (callTargets m k) fs) x.2).sum + 20 := by
  obtain ⟨fs', first, T, main, fns, e, pk, rk, g1, g2, g3, g4, hfs', -, -, -, -, hmg, hfg, rfl,
    -⟩ := gen_program hg
  rw [hfs] at hfs'
  cases hfs'
  have hl := (genFunctions_length (sigOf_tableOf _ _ _) hfg).1
  simp only [List.length_append, genMain_length hmg, hl, movImm_length, List.length_singleton]

/-! ## Runs of `main`'s parts -/

/-- The loads of `args` into X0 up. -/
theorem run_loads {args : List UInt64} (h8 : args.length ≤ 8) {a : UInt64} {s : State}
    (hcode : CodeAt code a
      (args.zipIdx.flatMap fun (v, i) => movImm ⟨i % 32, Nat.mod_lt _ (by decide)⟩ v))
    (hpc : s.pc = a) :
    ∃ s', Reach P code s s' ∧ s'.pc = after a (4 * args.length) ∧
      (∀ i (hi : i < args.length), s'.x ⟨i % 32, Nat.mod_lt _ (by decide)⟩ = args[i]) ∧
      (∀ q : Fin 32, 8 ≤ q.val → s'.x q = s.x q) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.out = s.out := by
  have key : ∀ j ≤ args.length, ∃ s', Reach P code s s' ∧ s'.pc = after a (4 * j) ∧
      (∀ i (hi : i < j) (hi' : i < args.length),
        s'.x ⟨i % 32, Nat.mod_lt _ (by decide)⟩ = args[i]) ∧
      (∀ q : Fin 32, 8 ≤ q.val → s'.x q = s.x q) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.out = s.out := by
    intro j
    induction j with
    | zero =>
        exact fun _ => ⟨s, .refl _, by rw [hpc, Nat.mul_zero, after_zero],
          fun i hi => absurd hi (by omega), fun _ _ => rfl, rfl, rfl, rfl⟩
    | succ j ih =>
        intro hj
        obtain ⟨s', hr, hp, hx, hhi, hsp, hmem, hout⟩ := ih (by omega)
        have cj := CodeAt.flatMap code (c := 4) ?_ hcode j (by simp; omega)
        rotate_left
        · rintro ⟨v, i⟩
          rfl
        simp only [List.getElem_zipIdx, Nat.zero_add] at cj
        obtain ⟨s'', hr', hp', hd, hk, hsp', hmem', hout'⟩ :=
          run_movImm P code (show j % 32 < 31 by omega) cj hp
        refine ⟨s'', hr.trans hr', by rw [hp', after_after, Nat.mul_succ], fun i hi hi' => ?_,
          fun q hq => ?_, by rw [hsp', hsp], by rw [hmem', hmem], by rw [hout', hout]⟩
        rotate_left
        · rw [hk _ fun e => by have : q.val = j % 32 := congrArg Fin.val e; omega]
          exact hhi q hq
        by_cases hij : i = j
        · subst hij
          exact hd
        · rw [hk _ fun e => hij (by have : i % 32 = j % 32 := congrArg Fin.val e; omega)]
          exact hx i (by omega) hi'
  obtain ⟨s', hr, hp, hx, hhi, hsp, hmem, hout⟩ := key _ (Nat.le_refl _)
  exact ⟨s', hr, hp, fun i hi => hx i hi hi, hhi, hsp, hmem, hout⟩

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

/-- The address of byte `j` of `main`'s frame of 16 bytes below `sp` as an address above the
stack's limit `room` bytes below that frame. -/
theorem stack_main (sp room : UInt64) (j : Nat) :
    sp - 16 + UInt64.ofNat j = sp - 16 - room + UInt64.ofNat (room.toNat + j) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat']
  have := sp.toNat_lt
  have := room.toNat_lt
  have h16 : (16 : UInt64).toNat = 16 := rfl
  rw [h16]
  simp only [Nat.reducePow] at *
  omega

theorem toNat_sub_le {a b : UInt64} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  UInt64.toNat_sub_of_le a b (UInt64.le_iff_toNat_le.mpr h)

theorem typed_i64 : ∀ {ts : List ValueType} {ws : List UInt64}, ts.all (· == .i64) = true →
    ts.length = ws.length → Typed ts (ws.map .i64)
  | [], [], _, _ => trivial
  | t :: ts, w :: ws, h, hl => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      cases t <;> first
        | exact ⟨trivial, typed_i64 h.2 (by simpa using hl)⟩
        | exact absurd h.1 (by intro e; cases e)
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

/-- The run of a trap stub at `a`: X0 set to the trap's code `c`, then a branch to the exit word
at `base`. -/
theorem run_stub {a base : UInt64} {c : Nat} {g : Fin 67108864} {s : State}
    (hcode : CodeAt code a (movImm 0 (UInt64.ofNat c) ++ [.b g]))
    (hb : bField (after a 4) base = .ok g) (hpc : s.pc = a) :
    ∃ s', Reach P code s s' ∧ s'.pc = base ∧ s'.x 0 = UInt64.ofNat c ∧ s'.out = s.out := by
  have h := CodeAt.split code hcode (movImm_length 0 (UInt64.ofNat c))
  obtain ⟨s1, r1, p1, x1, -, -, -, out1⟩ := run_movImm P code (d := 0) (by decide) h.1 hpc
  have cb : code (after a 4) = some (encode (.b g)) := (CodeAt.cons.mp h.2).1
  let s2 : State := { s1 with pc := s1.pc + sext 26 g.val * 4 }
  have e2 : LeanExe.A64.exec P (.b g) s1 = some s2 := rfl
  refine ⟨s2, r1.trans (reach_exec P code (by rw [p1]; exact cb) e2 (.refl _)), ?_, x1, out1⟩
  show s1.pc + sext 26 g.val * 4 = base
  rw [p1]
  exact bField_target hb

/-- What the machine does from `main` at `ms` when Talos's run of the program's function gives
`res`: a return of one value writes the eight bytes of its word to the UART, the lowest first,
and returns 0 to the address in X30 with SP as it was, and a trap at `unreachable`, an access
outside the memory, or a division by zero reaches the exit word at `base` with the trap's code in
X0 and the UART's output as it was.  When `calls` holds, the machine may instead reach the exit
word with the status 4 of an overflow of the stack. -/
def ProgramOutcome (base : UInt64) (calls : Prop) {α : Type} (res : Result α) (ms : State) :
    Prop :=
  (calls ∧ ∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧ ms'.x 0 = 4 ∧ ms'.out = ms.out) ∨
  match res with
  | .Success [v] _ => ∃ w ms', ValRel v w ∧ Reach P code ms ms' ∧ ms'.pc = ms.x 30 ∧
      ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧
      ms'.out = ms.out ++ (List.range 8).map fun j => (w >>> UInt64.ofNat (8 * j)).toUInt8
  | .Trap _ msg => ∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧ ms'.out = ms.out ∧
      ((msg = "unreachable" ∧ ms'.x 0 = 1) ∨ (msg = "out of bounds memory access" ∧ ms'.x 0 = 2) ∨
        (msg = "integer divide by zero" ∧ ms'.x 0 = 3))
  | _ => True

theorem ProgramOutcome.success {base : UInt64} {calls : Prop} {α : Type} {res : Result α}
    {v : Value} {st' : Store α} {ms : State} (h : ProgramOutcome P code base calls res ms)
    (hres : res = .Success [v] st') :
    (calls ∧ ∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧ ms'.x 0 = 4 ∧ ms'.out = ms.out) ∨
      ∃ w ms', ValRel v w ∧ Reach P code ms ms' ∧ ms'.pc = ms.x 30 ∧ ms'.sp = ms.sp ∧
        ms'.x 0 = 0 ∧
        ms'.out = ms.out ++ (List.range 8).map fun j => (w >>> UInt64.ofNat (8 * j)).toUInt8 := by
  subst hres
  exact h

theorem ProgramOutcome.unreachable {base : UInt64} {calls : Prop} {α : Type} {res : Result α}
    {st' : Store α} {ms : State} (h : ProgramOutcome P code base calls res ms)
    (hres : res = .Trap st' "unreachable") :
    (calls ∧ ∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧ ms'.x 0 = 4 ∧ ms'.out = ms.out) ∨
      ∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧ ms'.x 0 = 1 ∧ ms'.out = ms.out := by
  subst hres
  rcases h with h | ⟨ms', hr, hp, ho, ⟨-, hx⟩ | ⟨habs, -⟩ | ⟨habs, -⟩⟩
  · exact .inl h
  · exact .inr ⟨ms', hr, hp, hx, ho⟩
  · exact absurd habs (by decide)
  · exact absurd habs (by decide)

/-- The run of the program that runs function `k` of `m`, which imports nothing, on the words
`args`, from `main` at `after base 1`, for Talos's run of the function on the arguments at any
fuel.  The machine may reach the exit word with the status of an overflow of the stack only when
the functions that calls reach from function `k` call others.  `main` sets the stack's limit
`room` bytes below its frame of 16 bytes, and those `room + 16` bytes below SP must be Normal
memory above address 4096. -/
theorem program_sim {m : Module} {k : Nat} {f : Function} {args : List UInt64}
    {base room : UInt64} {is : List Instr} (hg : genProgram m k args P.uart base room = .ok is)
    (hcode : CodeAt code (after base 1) is) (hm : m.imports = []) (hk : m.funcs[k]? = some f)
    (hp : args.length = f.params.length) (F : Nat) {α : Type} (st : Store α)
    (ms : State) (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0)
    (hroom : 4096 ≤ room.toNat) (hsp : 4096 + room.toNat + 16 ≤ ms.sp.toNat)
    (htop : ms.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true) :
    ProgramOutcome P code base (callTargets m k ≠ []) (Wasm.run F m k st (args.map .i64).reverse)
      ms := by
  obtain ⟨fs, first, T, main, fns, e, pk, rk, g1, g2, g3, g4, hfs, hfirst, hT, hen, hps, hmg,
    hfg, his, hb1, hb2, hb3, hb4⟩ := gen_program hg
  subst his
  have hfm := mapM_funcOf hfs
  have hsig := sigOf_tableOf (callTargets m k) first fs
  have hend := (genFunctions_length hsig hfg).2
  obtain ⟨h8, g, hbl, hmeq⟩ := gen_main hmg
  have hmain : ∀ j < 16, P.normal (ms.sp - 16 + UInt64.ofNat j) = true := fun j hj => by
    rw [stack_main]
    exact hstack _ (by omega)
  -- the code's parts
  have hc := (CodeAt.append (code := code)).mp hcode
  have hc2 := CodeAt.split code hc.1 (genMain_length hmg)
  have cfns : CodeAt code first fns := by rw [hfirst]; exact hc2.2
  have cst : CodeAt code T (movImm 0 (UInt64.ofNat 1) ++ [.b g1] ++
      (movImm 0 (UInt64.ofNat 2) ++ [.b g2]) ++ (movImm 0 (UInt64.ofNat 3) ++ [.b g3]) ++
      (movImm 0 (UInt64.ofNat 4) ++ [.b g4])) := by
    have := hc.2
    rw [List.length_append, genMain_length hmg, ← after_after, ← hfirst, ← hend, ← hT] at this
    exact this
  have cs4 := CodeAt.split code cst (n := 15) (by simp [movImm])
  have cs3 := CodeAt.split code cs4.1 (n := 10) (by simp [movImm])
  have cs1 := CodeAt.split code cs3.1 (n := 5) (by simp [movImm])
  -- the functions
  obtain ⟨f', fis, hkm, hpk, hgk, cfk⟩ := gen_functions code hsig hfg cfns _ (entryIn_mem hen)
  have hf' := hfm _ hkm
  simp only at hf'
  rw [hk] at hf'
  cases hf'
  simp only [Prod.mk.injEq] at hpk
  rw [hpk.1] at hps
  obtain ⟨-, -, -, hff, -⟩ := gen_function hgk
  have htab : ∀ j c, tableOf (callTargets m k) first fs j = some c → ∃ f is,
      m.funcs[j]? = some f ∧ c.2 = (f.params, f.results) ∧
      genFunction (tableOf (callTargets m k) first fs) T (after T 5) (after T 10) (after T 15)
        c.1 f = .ok is ∧ CodeAt code c.1 is := by
    intro j c hj
    unfold tableOf at hj
    split at hj
    · obtain ⟨f', fis, hmem, hpr, hgen, hcd⟩ := gen_functions code hsig hfg cfns _ (entryIn_mem hj)
      exact ⟨f', fis, hfm _ hmem, hpr, hgen, hcd⟩
    · cases hj
  have hcl := calls_ok P code hm htab F
  have cmain := hc2.1
  rw [hmeq] at cmain
  generalize hA : after base 1 = A at *
  generalize hn : args.length = n at *
  have hL := loads_length args
  rw [hn] at hL
  have s8 := CodeAt.split code cmain (n := 4 * n + 33) (by
    simp only [List.length_append, hL, writes_length, movImm_length, List.length_cons,
      List.length_nil]
    all_goals omega)
  have s7 := CodeAt.split code s8.1 (n := 4 * n + 29) (by
    simp only [List.length_append, hL, writes_length, movImm_length, List.length_cons,
      List.length_nil]
    all_goals omega)
  have s6 := CodeAt.split code s7.1 (n := 4 * n + 13) (by
    simp only [List.length_append, hL, movImm_length, List.length_cons, List.length_nil]
    all_goals omega)
  have s5 := CodeAt.split code s6.1 (n := 4 * n + 9) (by
    simp only [List.length_append, hL, movImm_length, List.length_cons, List.length_nil]
    all_goals omega)
  have s4 := CodeAt.split code s5.1 (n := 8 + 4 * n) (by
    simp only [List.length_append, hL, movImm_length, List.length_cons, List.length_nil]
    all_goals omega)
  have s3 := CodeAt.split code s4.1 (n := 8) (by
    simp only [List.length_append, movImm_length, List.length_cons, List.length_nil]
    all_goals omega)
  have s2 := CodeAt.split code s3.1 (n := 7) (by
    simp only [List.length_append, movImm_length, List.length_cons, List.length_nil]
    all_goals omega)
  have s1 := CodeAt.split code s2.1 (n := 3) rfl
  -- `main`'s frame and X18
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
  obtain ⟨t3a, r3a, p3a, hx16, hk3a, sp3a, mem3a, out3a⟩ :=
    run_movImm P code (d := 16) (v := room) (by decide) s1.2 p2a
  have csub : code (after A 7) = some (encode (.subReg 18 18 16)) := (CodeAt.cons.mp s2.2).1
  let t3b : State := { t3a.setX 18 (t3a.x 18 - t3a.x 16) with pc := t3a.pc + 4 }
  have e3b : LeanExe.A64.exec P (.subReg 18 18 16) t3a = some t3b := rfl
  have p3b : t3b.pc = after A 8 := by
    show t3a.pc + 4 = _
    rw [p3a, ← after_succ, after_after]
  have h18b : t3b.x 18 = ms.sp - 16 - room := by
    rw [State.x_withPc, State.x_setX_same (by decide), hx16, hk3a 18 (by decide), h18a]
  have sp3b : t3b.sp = ms.sp - 16 := by
    show (t3a.setX 18 (t3a.x 18 - t3a.x 16)).sp = _
    rw [State.setX_sp, sp3a]
    rfl
  -- the loads
  obtain ⟨t3, r3, p3, hx3, hhi3, sp3, mem3, out3⟩ :=
    run_loads P code (args := args) (by omega) s3.2 p3b
  rw [hn, after_after] at p3
  -- the call
  have cbl : code (after A (8 + 4 * n)) = some (encode (.bl g)) := (CodeAt.cons.mp s4.2).1
  let t4 : State := { t3.setX 30 (t3.pc + 4) with pc := t3.pc + sext 26 g.val * 4 }
  have e4 : LeanExe.A64.exec P (.bl g) t3 = some t4 := rfl
  have p4 : t4.pc = e := by
    show t3.pc + sext 26 g.val * 4 = _
    rw [p3, bField_target hbl]
  have sp4 : t4.sp = ms.sp - 16 := by
    show (t3.setX 30 (t3.pc + 4)).sp = _
    rw [State.setX_sp, sp3, sp3b]
  have h30 : t4.x 30 = after A (4 * n + 9) := by
    show (t3.setX 30 (t3.pc + 4)).x 30 = _
    rw [State.x_setX_same (by decide), p3, ← after_succ]
    congr 1
    omega
  have h184 : t4.x 18 = ms.sp - 16 - room := by
    show (t3.setX 30 (t3.pc + 4)).x 18 = _
    rw [State.x_setX_ne (by decide), hhi3 18 (by decide), h18b]
  have e16 : (ms.sp - 16).toNat = ms.sp.toNat - 16 := toNat_sub_le (by
    show 16 ≤ ms.sp.toNat
    omega)
  have e16r : (ms.sp - 16 - room).toNat = ms.sp.toNat - 16 - room.toNat := by
    rw [toNat_sub_le (by omega), e16]
  have hd4 : (t4.sp - t4.x 18).toNat = room.toNat := by
    rw [sp4, h184, toNat_sub_le (by omega), e16, e16r]
    omega
  have hstk : StackOk P t4 := by
    refine ⟨by rw [sp4]; exact halm, ?_, ?_⟩
    · rw [sp4, h184, e16, e16r]
      simp only [Nat.reducePow] at *
      omega
    · intro j hj
      rw [hd4] at hj
      rw [h184]
      exact hstack j (by omega)
  have out4 : t4.out = ms.out := by
    show (t3.setX 30 (t3.pc + 4)).out = _
    rw [State.setX_out, out3]
    show (t3a.setX 18 (t3a.x 18 - t3a.x 16)).out = _
    have ho2 : t2a.out = ms.out := rfl
    rw [State.setX_out, out3a, ho2]
  have r4 : Reach P code ms t4 :=
    r2.trans (r3a.trans (reach_exec P code (by rw [p3a, after_after]; exact csub) e3b
      (r3.trans (reach_exec P code (by rw [p3]; exact cbl) e4 (.refl _)))))
  have hvs : ((args.map Value.i64).reverse).length = f.params.length := by simp [hn, hp]
  have hvt : Typed f.params.reverse
      (((args.map Value.i64).reverse).take f.params.length) := by
    rw [List.take_of_length_le (by omega)]
    exact Typed.reverse (typed_i64 hps (by simp [hn, hp]))
  rcases run_outcome P code hm hk hgk cfk hcl st (args.map Value.i64).reverse t4 (by omega) hvt
    p4 hstk (fun i hi => by
      have hi' : i < n := by omega
      have e1 : f.params.length - 1 - i < (args.map Value.i64).reverse.length := by omega
      rw [List.getElem_reverse]
      simp only [List.getElem_map, List.length_map, ValRel]
      show (t3.setX 30 (t3.pc + 4)).x ⟨i % 32, Nat.mod_lt _ (by decide)⟩ = _
      rw [State.x_setX_ne (fun e => by
        have : 30 = i % 32 := congrArg Fin.val e
        omega)]
      rw [hx3 i (by omega)]
      congr 1
      omega) with ⟨hov, hovr⟩ | hro
  · rcases hov with hov | ⟨j, c, hj⟩
    · rw [hd4] at hov
      omega
    have htj : j ∈ callTargets m k := by
      unfold tableOf at hj
      split at hj
      · assumption
      · cases hj
    obtain ⟨u, ru, pu, outu⟩ := hovr
    obtain ⟨u2, ru2, pu2, xu2, outu2⟩ := run_stub P code cs4.2 hb4 pu
    exact .inl ⟨fun he => by rw [he] at htj; exact List.not_mem_nil htj, u2,
      r4.trans (ru.trans ru2), pu2, xu2, by rw [outu2, outu, out4]⟩
  refine .inr ?_
  revert hro
  cases Wasm.run F m k st (args.map Value.i64).reverse with
  | Trap st' msg =>
      intro hro
      obtain ⟨u, ru, outu, hmsg⟩ := hro
      rcases hmsg with ⟨hm1, pu⟩ | ⟨hm2, pu⟩ | ⟨hm3, pu⟩
      · obtain ⟨u2, ru2, pu2, xu2, outu2⟩ := run_stub P code cs1.1 hb1 pu
        exact ⟨u2, r4.trans (ru.trans ru2), pu2, by rw [outu2, outu, out4], .inl ⟨hm1, xu2⟩⟩
      · obtain ⟨u2, ru2, pu2, xu2, outu2⟩ := run_stub P code cs1.2 hb2 pu
        exact ⟨u2, r4.trans (ru.trans ru2), pu2, by rw [outu2, outu, out4],
          .inr (.inl ⟨hm2, xu2⟩)⟩
      · obtain ⟨u2, ru2, pu2, xu2, outu2⟩ := run_stub P code cs3.2 hb3 pu
        exact ⟨u2, r4.trans (ru.trans ru2), pu2, by rw [outu2, outu, out4],
          .inr (.inr ⟨hm3, xu2⟩)⟩
  | Invalid _ => intro _; trivial
  | OutOfFuel => intro _; trivial
  | Thrown _ _ _ => intro _; trivial
  | Success vs' st' =>
  intro hro
  obtain ⟨t5, r5, p5, sp5, -, out5, mf5, hlen5, -, hres5, -⟩ := hro
  rcases vs' with _ | ⟨v, _ | ⟨v2, rest⟩⟩
  · trivial
  rotate_left
  · trivial
  have hr1 : f.results.length = 1 := by simp [hvs] at hlen5; omega
  rw [hr1] at hres5
  have hy : ValRel v (t5.x 0) := hres5 v (by simp)
  -- the result's bytes
  obtain ⟨t6, r6, p6, hx6, hk6, sp6, mem6, out6⟩ :=
    run_movImm P code (d := 1) (v := P.uart) (by decide) s5.2 (by rw [p5, h30])
  obtain ⟨t7, r7, p7, out7, hx7, sp7, mem7⟩ :=
    run_writes P code (s := t6) s6.2
      (by rw [p6, after_after, show 4 * n + 9 + 4 = 4 * n + 13 by omega]) hx6
  obtain ⟨t8, r8, p8, hx8, hk8, sp8, mem8, out8⟩ :=
    run_movImm P code (d := 0) (v := 0) (by decide) s7.2
      (by rw [p7, after_after, show 4 * n + 13 + 16 = 4 * n + 29 by omega])
  have sp8' : t8.sp = ms.sp - 16 := by rw [sp8, sp7, sp6, sp5, sp4]
  have p8' : t8.pc = after A (4 * n + 33) := by
    rw [p8, after_after, show 4 * n + 29 + 4 = 4 * n + 33 by omega]
  have al8 : t8.sp % 16 = 0 := by rw [sp8']; exact halm
  have mp8 : ∀ j < 8, P.normal (t8.sp + UInt64.ofNat (8 * 0 + j)) = true := fun j hj => by
    rw [sp8']
    simpa using hmain j (by omega)
  obtain ⟨t9, r9, p9, sp9, out9, mem9, hx9⟩ :=
    run_epilogue P code (n := 0) (fs := 16) (by decide) (by decide) s8.2 p8' al8 mp8
  refine ⟨t5.x 0, t9, hy, r4.trans (r5.trans (r6.trans (r7.trans (r8.trans r9)))), ?_, ?_, ?_,
    ?_⟩
  · have hl4 : (t4.x 18).toNat ≤ t4.sp.toNat := by
      rw [sp4, h184, e16, e16r]
      omega
    have ht4 : t4.sp.toNat < 2 ^ 63 := by
      rw [sp4, e16]
      simp only [Nat.reducePow] at *
      omega
    have hab : ∀ k < 8, ¬ slotAddr (ms.sp - 16) 0 + UInt64.ofNat k - t4.x 18 <
        t4.sp - t4.x 18 + UInt64.ofNat (8 * 0) := fun k hk => by
      rw [← sp4]
      exact slot_above hk hl4 ht4 (by decide)
    rw [p9, sp8', mem8, mem7, mem6, load64_congr (m' := t4.mem) fun k hk => mf5 _ (hab k hk)]
    show load64 t3.mem _ = _
    rw [mem3]
    show load64 t3a.mem _ = _
    rw [mem3a]
    exact load64_store64_same _ _ _
  · rw [sp9, sp8', show UInt64.ofNat 16 = 16 from rfl, UInt64.sub_add_cancel]
  · rw [hx9 0 (by decide), hx8]
  · rw [out9, out8, out7, hk6 0 (by decide), out6, out5, out4]

end LeanExe.A64
