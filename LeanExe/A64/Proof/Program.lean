import LeanExe.A64.Proof.Function
import LeanExe.ProofKit.Array

/-!
The run of a program that `genProgram` generates.  `main` saves X30 in its frame, sets the
stack's limit in X18 a given number of bytes below that frame, loads the arguments into X0 up,
calls the function, writes the eight bytes of the function's result to the
UART, the lowest first, sets X0 to 0, restores X30, and returns.  `program_sim` states that the
machine does so from `main` when Talos's run of the function on the arguments returns a word.
-/

namespace LeanExe.A64

open Wasm

export LeanExe.CallGraph (mapM_funcOf mem_reachable mem_reachFrom callsIn_callTargets)

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

theorem gen_main {a entry uart room : UInt64} {args : List UInt64} {o : Output}
    {is : List Instr} (hg : genMain a entry args uart room o = .ok is) :
    args.length ≤ 8 ∧ ∃ g out, bField (after a (8 + 4 * args.length)) entry = .ok g ∧
      genOut (after a (13 + 4 * args.length)) o = .ok out ∧
      is = [.subImm 31 31 16, .str 30 31 0, .addImm 18 31 0] ++ movImm 16 room ++
        [.subReg 18 18 16] ++
        args.zipIdx.flatMap (fun (v, i) => movImm ⟨i % 32, Nat.mod_lt _ (by decide)⟩ v) ++
        [.bl g] ++ movImm 1 uart ++ out ++ movImm 0 0 ++
        [.ldr 30 31 0, .addImm 31 31 16, .ret 30] := by
  by_cases hc : args.length > 8
  · simp [genMain, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  cases hb : bField (after a (8 + 4 * args.length)) entry with
  | error e => simp [genMain, hc, hb, bind, Except.bind] at hg
  | ok g =>
      cases ho : genOut (after a (13 + 4 * args.length)) o with
      | error e => simp [genMain, hc, hb, ho, bind, Except.bind] at hg
      | ok out =>
          simp [genMain, hc, hb, ho, bind, Except.bind, pure, Except.pure] at hg
          subst hg
          exact ⟨by omega, g, out, rfl, rfl, by simp⟩

theorem loads_length (args : List UInt64) :
    (args.zipIdx.flatMap fun (v, i) =>
      movImm ⟨i % 32, Nat.mod_lt _ (by decide)⟩ v).length = 4 * args.length := by
  rw [length_flatMap_const (c := 4) ?_, List.length_zipIdx]
  rintro ⟨v, i⟩
  rfl

theorem writesOf_length (r : Fin 32) : (writesOf r).length = 16 := by
  unfold writesOf
  rw [length_flatMap_const (c := 2) (fun _ => rfl), List.length_range]

/-- The code of an output of an array. -/
theorem gen_out_array {a : UInt64} {out : List Instr} (hg : genOut a .array = .ok out) :
    ∃ cz back, cbField (after a 18) (after a 39) = .ok cz ∧
      bField (after a 38) (after a 18) = .ok back ∧
      out = [.addReg 3 17 0, .ldr 4 3 512] ++ writesOf 4 ++ [.cbz 4 cz, .addImm 3 3 8,
        .ldr 6 3 512] ++ writesOf 6 ++ [.subImm 4 4 1, .b back] := by
  simp only [genOut] at hg
  cases h1 : cbField (after a 18) (after a 39) with
  | error e => simp [h1, bind, Except.bind] at hg
  | ok cz =>
      cases h2 : bField (after a 38) (after a 18) with
      | error e => simp [h1, h2, bind, Except.bind] at hg
      | ok back =>
          simp [h1, h2, bind, Except.bind, pure, Except.pure] at hg
          exact ⟨cz, back, rfl, rfl, hg.symm⟩

theorem genOut_length {a : UInt64} {o : Output} {out : List Instr} (hg : genOut a o = .ok out) :
    out.length = outSize o := by
  cases o with
  | word =>
      simp only [genOut, pure, Except.pure, Except.ok.injEq] at hg
      subst hg
      exact writesOf_length 0
  | array =>
      obtain ⟨cz, back, -, -, rfl⟩ := gen_out_array hg
      simp only [List.length_append, writesOf_length, List.length_cons, List.length_nil, outSize]

theorem genMain_length {a entry uart room : UInt64} {args : List UInt64} {o : Output}
    {is : List Instr} (hg : genMain a entry args uart room o = .ok is) :
    is.length = mainSize args.length o := by
  obtain ⟨-, g, out, -, ho, rfl⟩ := gen_main hg
  simp only [List.length_append, loads_length, genOut_length ho]
  simp only [List.length_cons, List.length_nil, mainSize, movImm]

theorem movImm_length (d : Fin 32) (v : UInt64) : (movImm d v).length = 4 := rfl

theorem CodeAt.split {a : UInt64} {l1 l2 : List Instr} {n : Nat}
    (h : CodeAt code a (l1 ++ l2)) (hn : l1.length = n) :
    CodeAt code a l1 ∧ CodeAt code (after a n) l2 := by
  have := (CodeAt.append (code := code)).mp h
  rwa [hn] at this

theorem genFunction_length {callee : Table}
    {S : Shared} {entry : UInt64} {f : Function} {is : List Instr}
    (hg : genFunction callee S entry f = .ok is) :
    is.length = functionSize (sigOf callee) f := by
  obtain ⟨-, -, -, hf, hn, stores, body, fin, g, hsl, -, hl, -, -, rfl⟩ := gen_function hg
  have hs := (genList_size _ _ _ f.body body fin hl).1
  simp only [List.map_cons, List.map_nil, List.length_nil, Ctl.arity_mk,
    List.length_reverse] at hs
  simp only [List.length_append, List.length_cons, List.length_nil, hsl, hs, functionSize]

/-! ## The layout of the functions -/

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
theorem genFunctions_length {callee : Table} {S : Shared}
    {sig : Nat → Option (Nat × Nat)} (hsig : sigOf callee = sig) :
    ∀ {a : UInt64} {fs : List (Nat × Function)} {is : List Instr},
      genFunctions callee S a fs = .ok is →
      is.length = (fs.map fun x => functionSize sig x.2).sum ∧ endOf sig a fs = after a is.length
  | a, [], is, hg => by
      simp only [genFunctions, pure, Except.pure, Except.ok.injEq] at hg
      subst hg
      exact ⟨rfl, by rw [List.length_nil, after_zero]; rfl⟩
  | a, (j, f) :: rest, is, hg => by
      simp only [genFunctions, bind, Except.bind] at hg
      cases h1 : genFunction callee S a f with
      | error e => simp [h1] at hg
      | ok is1 =>
          cases h2 : genFunctions callee S (after a is1.length) rest with
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
theorem gen_functions {callee : Table} {S : Shared}
    {sig : Nat → Option (Nat × Nat)} (hsig : sigOf callee = sig) :
    ∀ {a : UInt64} {fs : List (Nat × Function)} {is : List Instr},
      genFunctions callee S a fs = .ok is → CodeAt code a is →
      ∀ x ∈ entriesFrom sig a fs, ∃ f fis, (x.1, f) ∈ fs ∧ x.2.2 = (f.params, f.results) ∧
        genFunction callee S x.2.1 f = .ok fis ∧ CodeAt code x.2.1 fis
  | a, [], is, _, _ => fun x hx => by simp [entriesFrom] at hx
  | a, (j, f) :: rest, is, hg, hcode => by
      simp only [genFunctions, bind, Except.bind] at hg
      cases h1 : genFunction callee S a f with
      | error e => simp [h1] at hg
      | ok is1 =>
          cases h2 : genFunctions callee S (after a is1.length) rest with
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

/-! ## A bound of the stack -/

/-- A bound on the bytes of stack that a call of function `k` of `m` uses, following calls `d`
deep, `stackNeedOf` with the frames of `frameSize`.  A call spills registers into its caller's
frame, so the frames of the calls in progress hold all the stack that the program uses below
`main`'s frame. -/
def stackNeed (m : Module) : Nat → Nat → Nat :=
  CallGraph.stackNeedOf m fun f => frameSize (f.params.length + f.locals.length)

/-- `stackNeed` as many calls deep as `m` has functions.  When the calls from `k` reach no cycle,
a chain of calls from `k` holds each function at most once, so the search reaches the end of every
chain and gives the largest sum of the frames along one.  A cycle makes the search reach depth 0
and gives 2^64. -/
def stackBound (m : Module) (k : Nat) : Nat :=
  stackNeed m m.funcs.length k

theorem stackNeed_zero (m : Module) (k : Nat) : stackNeed m 0 k = 2 ^ 64 := rfl

theorem stackNeed_some {m : Module} {k : Nat} {f : Function} (hk : m.funcs[k]? = some f)
    (d : Nat) : stackNeed m (d + 1) k = min (2 ^ 64)
      (frameSize (f.params.length + f.locals.length) + callNeed (stackNeed m d) f.body) :=
  CallGraph.stackNeedOf_some hk d

theorem stackNeed_none {m : Module} {k : Nat} (hk : m.funcs[k]? = none) (d : Nat) :
    stackNeed m (d + 1) k = 0 :=
  CallGraph.stackNeedOf_none hk d

theorem stackNeed_succ_le (m : Module) : ∀ d k, stackNeed m (d + 1) k ≤ stackNeed m d k :=
  CallGraph.stackNeedOf_succ_le m _

/-- `stackNeed` at every depth satisfies `NeedOk` for every function of `m`. -/
theorem stackNeed_ok {m : Module} {k : Nat} {f : Function} (hk : m.funcs[k]? = some f) :
    ∀ d, NeedOk (stackNeed m d) (frameSize (f.params.length + f.locals.length)) f.body
      (stackNeed m d k) :=
  CallGraph.stackNeedOf_ok hk

/-- `stackNeed` of a function whose body calls no function is at most its frame. -/
theorem stackNeed_of_nil {m : Module} {k : Nat} {f : Function} (hk : m.funcs[k]? = some f)
    (hc : callsIn f.body = []) (d : Nat) :
    stackNeed m (d + 1) k ≤ frameSize (f.params.length + f.locals.length) :=
  CallGraph.stackNeedOf_of_nil hk hc d

/-! ## The generator's program -/

theorem gen_program {m : Module} {k : Nat} {args : List UInt64} {uart base room : UInt64}
    {cap : Nat} {o : Output} {is : List Instr}
    (hg : genProgram m k args uart base room cap o = .ok is) :
    ∃ gts fs first T main fns e pk rk g1 g2 g3 g4,
      areaOk m cap = true ∧ globalTypesOf m = some gts ∧ gts.length ≤ 511 ∧
      (reachFrom m k).mapM (funcOf m) = .ok fs ∧
      first = after (after base 1) (mainSize args.length o) ∧
      T = endOf (sigIn (callTargets m k) fs) first fs ∧
      entryIn (sigIn (callTargets m k) fs) first fs k = some (e, pk, rk) ∧
      pk.all wordType = true ∧
      genMain (after base 1) e args uart room o = .ok main ∧
      genFunctions (tableOf (callTargets m k) first fs)
        ⟨T, after T 5, after T 10, after T 15, cap, gts⟩ first fs = .ok fns ∧
      is = main ++ fns ++ (movImm 0 (UInt64.ofNat 1) ++ [.b g1] ++
        (movImm 0 (UInt64.ofNat 2) ++ [.b g2]) ++ (movImm 0 (UInt64.ofNat 3) ++ [.b g3]) ++
        (movImm 0 (UInt64.ofNat 4) ++ [.b g4])) ∧
      bField (after T 4) base = .ok g1 ∧ bField (after (after T 5) 4) base = .ok g2 ∧
      bField (after (after T 10) 4) base = .ok g3 ∧
      bField (after (after T 15) 4) base = .ok g4 := by
  simp only [genProgram] at hg
  cases hok : areaOk m cap with
  | false => simp [hok, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  | true =>
  cases hgt : globalTypesOf m with
  | none => simp [hok, hgt, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  | some gts =>
  have hgl : gts.length ≤ 511 := by
    refine Classical.byContradiction fun h => ?_
    simp [hok, hgt, h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  simp only [hok, hgt, hgl, Bool.not_true, Bool.false_eq_true, if_false, if_true, bind,
    Except.bind, pure, Except.pure] at hg
  cases hfs : (reachFrom m k).mapM (funcOf m) with
  | error e => simp [hfs, bind, Except.bind] at hg
  | ok fs =>
      simp only [hfs, bind, Except.bind] at hg
      generalize hfirst : after (after base 1) (mainSize args.length o) = first at hg
      generalize hT : endOf (sigIn (callTargets m k) fs) first fs = T at hg
      cases hen : entryIn (sigIn (callTargets m k) fs) first fs k with
      | none => simp [hen, throw, throwThe, MonadExceptOf.throw] at hg
      | some c =>
          obtain ⟨e, pk, rk⟩ := c
          have hps : pk.all wordType = true := by
            cases h : pk.all wordType with
            | true => rfl
            | false => simp [hen, h, throw, throwThe, MonadExceptOf.throw] at hg
          simp only [hen, hps, if_true, pure, Except.pure] at hg
          cases hmn : genMain (after base 1) e args uart room o with
          | error err => simp [hmn] at hg
          | ok main =>
              simp only [hmn] at hg
              cases hfn : genFunctions (tableOf (callTargets m k) first fs)
                  ⟨T, after T 5, after T 10, after T 15, cap, gts⟩ first fs with
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
                  refine ⟨gts, fs, first, T, main, fns, e, pk, rk, g1, g2, g3, g4, rfl, rfl, hgl,
                    rfl, rfl, hT.symm, hen, hps, hmn, hfn, ?_, hb1, hb2, hb3, hb4⟩
                  rw [← hg]
                  simp [List.append_assoc]

theorem genProgram_length {m : Module} {k : Nat} {args : List UInt64}
    {uart base room : UInt64} {cap : Nat} {o : Output} {is : List Instr}
    (hg : genProgram m k args uart base room cap o = .ok is)
    {fs : List (Nat × Function)} (hfs : (reachFrom m k).mapM (funcOf m) = .ok fs) :
    is.length = mainSize args.length o +
      (fs.map fun x => functionSize (sigIn (callTargets m k) fs) x.2).sum + 20 := by
  obtain ⟨gts, fs', first, T, main, fns, e, pk, rk, g1, g2, g3, g4, -, -, -, hfs', -, -, -, -,
    hmg, hfg, rfl, -⟩ := gen_program hg
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
theorem run_writes {a : UInt64} {s : State} {r : Fin 32} (hr1 : r ≠ 1) (hr2 : r ≠ 2)
    (hcode : CodeAt code a (writesOf r)) (hpc : s.pc = a) (h1 : s.x 1 = P.uart) :
    ∃ s', Reach P code s s' ∧ s'.pc = after a 16 ∧
      s'.out = s.out ++ (List.range 8).map (fun j => (s.x r >>> UInt64.ofNat (8 * j)).toUInt8) ∧
      (∀ q, q ≠ 2 → s'.x q = s.x q) ∧ s'.sp = s.sp ∧ s'.mem = s.mem := by
  have key : ∀ j ≤ 8, ∃ s', Reach P code s s' ∧ s'.pc = after a (2 * j) ∧
      s'.out = s.out ++ (List.range j).map (fun j => (s.x r >>> UInt64.ofNat (8 * j)).toUInt8) ∧
      (∀ q, q ≠ 2 → s'.x q = s.x q) ∧ s'.sp = s.sp ∧ s'.mem = s.mem := by
    intro j
    induction j with
    | zero =>
        exact fun _ => ⟨s, .refl _, by rw [hpc, Nat.mul_zero, after_zero], by simp,
          fun _ _ => rfl, rfl, rfl⟩
    | succ j ih =>
        intro hj
        obtain ⟨s', hr, hp, hout, hxq, hsp, hmem⟩ := ih (by omega)
        have cj := CodeAt.flatMap code (c := 2) (fun _ => rfl) hcode j (by simp; omega)
        simp only [List.getElem_range] at cj
        have c0 := (CodeAt.cons.mp cj).1
        have c1 := (CodeAt.cons.mp (CodeAt.cons.mp cj).2).1
        let w : UInt64 := s'.x r >>> UInt64.ofNat (8 * j % 64)
        let s1 : State := { s'.setX 2 w with pc := s'.pc + 4 }
        have e1 : LeanExe.A64.exec P (.lsrImm 2 r ⟨8 * j % 64, Nat.mod_lt _ (by decide)⟩) s' =
            some s1 := rfl
        have hx1' : s1.x 1 = P.uart := by
          show (s'.setX 2 w).x 1 = P.uart
          rw [State.x_setX_ne (by decide), hxq 1 (by decide), h1]
        let s2 : State := { s1 with out := s1.out ++ [(s1.x 2).toUInt8], pc := s1.pc + 4 }
        have hxsp : s1.xsp 1 = P.uart := by rw [State.xsp_eq_x (by decide), hx1']
        have e2 : LeanExe.A64.exec P (.strb 2 1 0) s1 = some s2 := by
          simp [exec, hxsp, State.spAligned, s2]
        have p1 : s1.pc = after (after a (2 * j)) 1 := by
          rw [after_succ, after_zero]
          show s'.pc + 4 = _
          rw [hp]
        have hw : s1.x 2 = s.x r >>> UInt64.ofNat (8 * j) := by
          show (s'.setX 2 w).x 2 = _
          rw [State.x_setX_same (by decide)]
          show s'.x r >>> UInt64.ofNat (8 * j % 64) = _
          rw [hxq r hr2, Nat.mod_eq_of_lt (by omega)]
        refine ⟨s2, hr.trans (reach_exec P code (by rw [hp]; exact c0) e1
          (reach_exec P code (by rw [p1]; exact c1) e2 (.refl _))), ?_, ?_, fun q hq => ?_, ?_,
          ?_⟩
        · show s1.pc + 4 = _
          rw [p1, ← after_succ, after_after, Nat.mul_succ]
        · show s1.out ++ [(s1.x 2).toUInt8] = _
          rw [hw, List.range_succ, List.map_append, ← List.append_assoc, ← hout]
          rfl
        · show (s'.setX 2 w).x q = _
          rw [State.x_setX_ne (Ne.symm hq), hxq q hq]
        · show (s'.setX 2 w).sp = _
          rw [State.setX_sp, hsp]
        · show (s'.setX 2 w).mem = _
          rw [State.setX_mem, hmem]
  obtain ⟨s', hr, hp, hout, hxq, hsp, hmem⟩ := key 8 (Nat.le_refl _)
  exact ⟨s', hr, hp, hout, hxq, hsp, hmem⟩

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

/-- The value of a parameter of type `t` whose word is `w`: an `f64` for `f64` and an `i64`
otherwise. -/
def argValue : ValueType → UInt64 → Value
  | .f64, w => .f64 w
  | _, w => .i64 w

/-- The values of parameters of the types `ts` whose words are `ws`. -/
def argValues (ts : List ValueType) (ws : List UInt64) : List Value :=
  List.zipWith argValue ts ws

theorem valRel_argValue (t : ValueType) (w : UInt64) : ValRel (argValue t w) w := by
  cases t <;> rfl

theorem length_argValues (ts : List ValueType) (ws : List UInt64) :
    (argValues ts ws).length = min ts.length ws.length :=
  List.length_zipWith

theorem getElem_argValues {ts : List ValueType} {ws : List UInt64} {i : Nat}
    (h : i < (argValues ts ws).length) :
    (argValues ts ws)[i] = argValue (ts[i]'(by rw [length_argValues] at h; omega))
      (ws[i]'(by rw [length_argValues] at h; omega)) :=
  List.getElem_zipWith

theorem typed_words : ∀ {ts : List ValueType} {ws : List UInt64}, ts.all wordType = true →
    ts.length = ws.length → Typed ts (argValues ts ws)
  | [], [], _, _ => trivial
  | t :: ts, w :: ws, h, hl => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      cases t <;> first
        | exact ⟨trivial, typed_words h.2 (by simpa using hl)⟩
        | exact absurd h.1 (by intro e; cases e)
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

/-- The operand registers of the heights below 16 are X0 to X15. -/
theorem regOf_small : ∀ i < 16, regOf i = ⟨i % 32, Nat.mod_lt _ (by decide)⟩ := by decide

/-! ## The area -/

/-- The store in which the program's function starts: the module's initial store with a memory
of `cap` pages. -/
def initStore (m : Module) (cap : Nat) : Store Unit :=
  { (m.initialStore : Store Unit) with memoryCaps := [cap] }

theorem memIs64_of_areaOk {m : Module} {cap : Nat} (h : areaOk m cap = true) :
    m.memIs64 = false := by
  unfold areaOk at h
  unfold Module.memIs64
  cases hd : m.memory with
  | none => rfl
  | some d =>
      rw [hd] at h
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      exact h.1.1.1

theorem cap_lt_of_areaOk {m : Module} {cap : Nat} (h : areaOk m cap = true) : cap < 4096 := by
  unfold areaOk at h
  cases hd : m.memory with
  | none => rw [hd] at h; cases h
  | some d =>
      rw [hd] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2

/-- The memory of `m` starts with at most `cap` pages when `areaOk m cap` holds. -/
theorem pages_le_of_areaOk {m : Module} {cap : Nat} (h : areaOk m cap = true) :
    (m.memory.map (·.pagesMin.toNat)).getD 0 ≤ cap := by
  unfold areaOk at h
  cases hd : m.memory with
  | none => rw [hd] at h; cases h
  | some d =>
      rw [hd] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      simpa using h.1.2

theorem foldl_pages {β : Type} (f : Mem → β → Mem) (hf : ∀ acc b, (f acc b).pages = acc.pages) :
    ∀ (l : List β) (m0 : Mem), (l.foldl f m0).pages = m0.pages
  | [], _ => rfl
  | b :: l, m0 => by rw [List.foldl_cons, foldl_pages f hf l, hf]

theorem initialStore_pages {m : Module} {d : MemDecl} (h : m.memory = some d) :
    (m.initialStore : Store Unit).mem.pages = d.pagesMin.toNat := by
  unfold Module.initialStore
  simp only [h]
  rw [foldl_pages]
  · rfl
  · intro acc seg
    split
    · split
      · split
        · rfl
        · rfl
      · rfl
    · rfl

theorem hasType_of_valueType {v : Value} {t : ValueType} (h : valueType v = some t) :
    HasType t v := by
  cases v <;> simp [valueType] at h <;> subst h <;> trivial

theorem valRel_wordOf {t : ValueType} {v : Value} (h : HasType t v) : ValRel v (wordOf v) := by
  cases v <;> first | rfl | (cases t <;> exact h.elim)

theorem typed_of_valueTypes : ∀ (gs : List GlobalDecl) (gts : List ValueType),
    gs.mapM (fun g => valueType g.init) = some gts → Typed gts (gs.map (·.init))
  | [], gts, h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      trivial
  | g :: gs, gts, h => by
      rw [List.mapM_cons] at h
      cases hv : valueType g.init with
      | none => simp [hv] at h
      | some t =>
          cases hr : gs.mapM (fun g => valueType g.init) with
          | none => simp [hv, hr] at h
          | some ts =>
              simp [hv, hr] at h
              subst h
              exact ⟨hasType_of_valueType hv, typed_of_valueTypes gs ts hr⟩

/-- A machine whose X17 holds the address of the bytes of the area of the module's initial store
holds that store with a memory of `cap` pages. -/
theorem storeRel_init {m : Module} {cap : Nat} {gts : List ValueType} {s : State}
    (hok : areaOk m cap = true) (hgt : globalTypesOf m = some gts) (hgl : gts.length ≤ 511)
    (harea : ∀ j < areaSize cap, s.mem (s.x 17 + UInt64.ofNat j) = areaByte m.initialStore j)
    (hmap : ∀ j < areaSize cap, P.normal (s.x 17 + UInt64.ofNat j) = true)
    (hbelow : (s.x 17).toNat + areaSize cap ≤ (s.x 18).toNat) :
    StoreRel P cap gts (initStore m cap) s := by
  unfold areaOk at hok
  cases hd : m.memory with
  | none => rw [hd] at hok; cases hok
  | some d =>
      rw [hd] at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨-, h1⟩, h2⟩, h3⟩ := hok
      have hpg : (initStore m cap).mem.pages = d.pagesMin.toNat := initialStore_pages hd
      have hty : Typed gts (initStore m cap).globals.globals := typed_of_valueTypes _ _ hgt
      have hgl' := hty.length
      refine ⟨rfl, h3, hgl, by rw [hpg]; omega, ?_, hty, ?_, ?_, hmap, hbelow⟩
      · apply load64_bytes
        intro k hk
        rw [harea k (by unfold areaSize; omega)]
        simp only [areaByte, if_pos hk]
        rfl
      · intro i hi
        have hti := hty.getElem (i := i) (by omega)
        rw [load64_bytes (w := wordOf (initStore m cap).globals.globals[i]) fun k hk => ?_]
        · exact valRel_wordOf hti
        · rw [add_ofNat_add, harea _ (by unfold areaSize; omega)]
          have e1 : (8 * (i + 1) + k) / 8 - 1 = i := by omega
          have e2 : (8 * (i + 1) + k) % 8 = k := by omega
          simp only [areaByte, e1, e2]
          rw [if_neg (by omega), if_pos (by omega)]
          have hi' : i < (m.initialStore : Store Unit).globals.globals.length := hi
          rw [List.getElem?_eq_getElem hi']
          rfl
      · intro j hj
        rw [harea _ (by unfold areaSize; omega)]
        simp only [areaByte]
        rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]
        rfl

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

/-! ## The output of an array -/

/-- The bytes of the word `w`, the lowest first. -/
def bytesOf (w : UInt64) : List UInt8 :=
  (List.range 8).map fun j => (w >>> UInt64.ofNat (8 * j)).toUInt8

/-- The bytes of an array of words: its length word, then its elements. -/
def arrayBytes (ws : Array UInt64) : List UInt8 :=
  bytesOf (UInt64.ofNat ws.size) ++ ws.toList.flatMap bytesOf

/-- One pass of the loop of an array's output from `u` at its head, `after a 18`, with a count in
X4 that is not zero: the address in X3 steps by 8, X6 receives the word 4096 bytes above it, its
bytes reach the UART, and the count decreases by 1. -/
theorem run_arrayStep {u : State} {a : UInt64} {cz : Fin 524288} {back : Fin 67108864}
    (hc18 : code (after a 18) = some (encode (.cbz 4 cz)))
    (hc19 : code (after a 19) = some (encode (.addImm 3 3 8)))
    (hc20 : code (after a 20) = some (encode (.ldr 6 3 512)))
    (hw : CodeAt code (after a 21) (writesOf 6))
    (hc37 : code (after a 37) = some (encode (.subImm 4 4 1)))
    (hc38 : code (after a 38) = some (encode (.b back)))
    (hback : bField (after a 38) (after a 18) = .ok back)
    (hpc : u.pc = after a 18) (h4 : u.x 4 ≠ 0) (h1 : u.x 1 = P.uart)
    (hmap : ∀ k < 8, P.normal (u.x 3 + 8 + UInt64.ofNat (8 * 512 + k)) = true) :
    ∃ u', Reach P code u u' ∧ u'.pc = after a 18 ∧ u'.x 3 = u.x 3 + 8 ∧
      u'.x 4 = u.x 4 - UInt64.ofNat 1 ∧
      u'.out = u.out ++ bytesOf (load64 u.mem (u.x 3 + 8 + UInt64.ofNat (8 * 512))) ∧
      u'.sp = u.sp ∧ u'.mem = u.mem ∧
      (∀ q : Fin 32, q ≠ 2 → q ≠ 3 → q ≠ 4 → q ≠ 6 → u'.x q = u.x q) := by
  have hd3 : (3 : Fin 32).val < 31 := by decide
  have hd4 : (4 : Fin 32).val < 31 := by decide
  let u1 : State := { u with pc := u.pc + 4 }
  have e1 : LeanExe.A64.exec P (.cbz 4 cz) u = some u1 := cbz_next P h4
  let u2 : State := { u1.setX 3 (u1.x 3 + UInt64.ofNat 8) with pc := u1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.addImm 3 3 8) u1 = some u2 := by
    simp only [exec, State.xsp_eq_x hd3, State.setXsp_eq_setX hd3]
    rfl
  have hx23 : u2.x 3 = u.x 3 + 8 := by
    show (u1.setX 3 (u1.x 3 + UInt64.ofNat 8)).x 3 = _
    rw [State.x_setX_same hd3]
    rfl
  have e3 := exec_ldr_base P (s := u2) (t := 6) (i := 512) (by decide) (n := 3) hd3
    (fun k hk => by rw [hx23]; exact hmap k hk)
  let u3 : State := { u2.setX 6 (load64 u2.mem (u2.x 3 + UInt64.ofNat (8 * 512))) with
    pc := u2.pc + 4 }
  have p1 : u1.pc = after a 19 := by
    show u.pc + 4 = _
    rw [hpc, ← after_succ]
  have p2 : u2.pc = after a 20 := by
    show u1.pc + 4 = _
    rw [p1, ← after_succ]
  have p3 : u3.pc = after a 21 := by
    show u2.pc + 4 = _
    rw [p2, ← after_succ]
  have hk3 : ∀ q : Fin 32, q ≠ 3 → q ≠ 6 → u3.x q = u.x q := fun q hq3 hq6 => by
    show (u2.setX 6 (load64 u2.mem (u2.x 3 + UInt64.ofNat (8 * 512)))).x q = _
    rw [State.x_setX_ne (Ne.symm hq6)]
    show (u1.setX 3 (u1.x 3 + UInt64.ofNat 8)).x q = _
    rw [State.x_setX_ne (Ne.symm hq3)]
    rfl
  have hmem2 : u2.mem = u.mem := by
    show (u1.setX 3 (u1.x 3 + UInt64.ofNat 8)).mem = _
    rw [State.setX_mem]
  have hx63 : u3.x 6 = load64 u.mem (u.x 3 + 8 + UInt64.ofNat (8 * 512)) := by
    show (u2.setX 6 (load64 u2.mem (u2.x 3 + UInt64.ofNat (8 * 512)))).x 6 = _
    rw [State.x_setX_same (by decide), hmem2, hx23]
  have hx13 : u3.x 1 = P.uart := by rw [hk3 1 (by decide) (by decide), h1]
  obtain ⟨u4, r4, p4, out4, hk4, sp4, mem4⟩ :=
    run_writes P code (r := 6) (by decide) (by decide) hw p3 hx13
  let u5 : State := { u4.setX 4 (u4.x 4 - UInt64.ofNat 1) with pc := u4.pc + 4 }
  have e5 : LeanExe.A64.exec P (.subImm 4 4 1) u4 = some u5 := by
    simp only [exec, State.xsp_eq_x hd4, State.setXsp_eq_setX hd4]
    rfl
  let u6 : State := { u5 with pc := u5.pc + sext 26 back.val * 4 }
  have e6 : LeanExe.A64.exec P (.b back) u5 = some u6 := rfl
  have p5 : u5.pc = after a 38 := by
    show u4.pc + 4 = _
    rw [p4, after_after, ← after_succ]
  have hsp3 : u3.sp = u.sp := by
    show (u2.setX 6 (load64 u2.mem (u2.x 3 + UInt64.ofNat (8 * 512)))).sp = _
    rw [State.setX_sp]
    show (u1.setX 3 (u1.x 3 + UInt64.ofNat 8)).sp = _
    rw [State.setX_sp]
  have hmem3 : u3.mem = u.mem := by
    show (u2.setX 6 (load64 u2.mem (u2.x 3 + UInt64.ofNat (8 * 512)))).mem = _
    rw [State.setX_mem, hmem2]
  have hout3 : u3.out = u.out := by
    show (u2.setX 6 (load64 u2.mem (u2.x 3 + UInt64.ofNat (8 * 512)))).out = _
    rw [State.setX_out]
    show (u1.setX 3 (u1.x 3 + UInt64.ofNat 8)).out = _
    rw [State.setX_out]
  refine ⟨u6, reach_exec P code (by rw [hpc]; exact hc18) e1
      (reach_exec P code (by rw [p1]; exact hc19) e2
        (reach_exec P code (by rw [p2]; exact hc20) e3
          (r4.trans (reach_exec P code (by rw [p4, after_after]; exact hc37) e5
            (reach_exec P code (by rw [p5]; exact hc38) e6 (.refl _)))))), ?_, ?_, ?_, ?_, ?_,
    ?_, fun q hq2 hq3 hq4 hq6 => ?_⟩
  · show u5.pc + sext 26 back.val * 4 = _
    rw [p5, bField_target hback]
  · show (u4.setX 4 (u4.x 4 - UInt64.ofNat 1)).x 3 = _
    rw [State.x_setX_ne (by decide), hk4 3 (by decide)]
    show (u2.setX 6 (load64 u2.mem (u2.x 3 + UInt64.ofNat (8 * 512)))).x 3 = _
    rw [State.x_setX_ne (by decide), hx23]
  · show (u4.setX 4 (u4.x 4 - UInt64.ofNat 1)).x 4 = _
    rw [State.x_setX_same hd4, hk4 4 (by decide), hk3 4 (by decide) (by decide)]
  · show (u4.setX 4 (u4.x 4 - UInt64.ofNat 1)).out = _
    rw [State.setX_out, out4, hout3, hx63]
    rfl
  · show (u4.setX 4 (u4.x 4 - UInt64.ofNat 1)).sp = _
    rw [State.setX_sp, sp4, hsp3]
  · show (u4.setX 4 (u4.x 4 - UInt64.ofNat 1)).mem = _
    rw [State.setX_mem, mem4, hmem3]
  · show (u4.setX 4 (u4.x 4 - UInt64.ofNat 1)).x q = _
    rw [State.x_setX_ne (Ne.symm hq4), hk4 q hq2, hk3 q hq3 hq6]

/-- The word `k` of an array in Talos's memory, read from the area: the length word for `k = 0`
and element `k - 1` above it. -/
theorem array_word {cap : Nat} {gts : List ValueType} {st : Store Unit} {s : State}
    (hsr : StoreRel P cap gts st s) {ptr : UInt64} {ws : Array UInt64}
    (hat : LeanExe.ProofKit.UInt64Array.At st ptr ws) {k : Nat} (hk : k ≤ ws.size) :
    load64 s.mem (s.x 17 + ptr + UInt64.ofNat (8 * k) + UInt64.ofNat (8 * 512)) =
      st.mem.read64 (ptr + UInt64.ofNat (8 * k)).toUInt32 := by
  obtain ⟨h1, h2, -, -⟩ := hat
  have hcap : st.mem.pages * 65536 ≤ cap * 65536 := Nat.mul_le_mul_right _ hsr.pages.2
  have hy : (ptr + UInt64.ofNat (8 * k)).toUInt32.toNat = ptr.toNat + 8 * k := by
    rw [UInt64.toNat_toUInt32, UInt64.toNat_add, UInt64.toNat_ofNat']
    simp only [Nat.reducePow] at *
    omega
  apply load64_read64
  intro j hj
  have e : s.x 17 + ptr + UInt64.ofNat (8 * k) + UInt64.ofNat (8 * 512) + UInt64.ofNat j =
      s.x 17 + UInt64.ofNat (4096 + (ptr.toNat + 8 * k + j)) := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
    have := ptr.toNat_lt
    simp only [Nat.reducePow] at *
    omega
  rw [e, hsr.bytes _ (by omega), hy]

/-- The run of the output of an array from `s` at `a`, with the array's pointer in X0 and the
UART's address in X1: its length word's bytes, then its elements' bytes, reach the UART. -/
theorem run_arrayOut {cap : Nat} {gts : List ValueType} {st : Store Unit} {s : State}
    {a : UInt64} {cz : Fin 524288} {back : Fin 67108864} {ptr : UInt64} {ws : Array UInt64}
    (hcode : CodeAt code a ([.addReg 3 17 0, .ldr 4 3 512] ++ writesOf 4 ++
      [.cbz 4 cz, .addImm 3 3 8, .ldr 6 3 512] ++ writesOf 6 ++ [.subImm 4 4 1, .b back]))
    (hcz : cbField (after a 18) (after a 39) = .ok cz)
    (hback : bField (after a 38) (after a 18) = .ok back)
    (hpc : s.pc = a) (hsr : StoreRel P cap gts st s) (hx0 : s.x 0 = ptr)
    (hx1 : s.x 1 = P.uart) (hat : LeanExe.ProofKit.UInt64Array.At st ptr ws) :
    ∃ t, Reach P code s t ∧ t.pc = after a 39 ∧ t.sp = s.sp ∧ t.mem = s.mem ∧
      t.out = s.out ++ arrayBytes ws ∧
      (∀ q : Fin 32, q ≠ 2 → q ≠ 3 → q ≠ 4 → q ≠ 6 → t.x q = s.x q) := by
  have hat' := hat
  obtain ⟨hA1, hA2, hA3, hA4⟩ := hat'
  have hcap : st.mem.pages * 65536 ≤ cap * 65536 := Nat.mul_le_mul_right _ hsr.pages.2
  have hbelow := hsr.below
  unfold areaSize at hbelow
  have hS := CodeAt.split code hcode (n := 37) (by simp [writesOf_length])
  have hS2 := CodeAt.split code hS.1 (n := 21) (by simp [writesOf_length])
  have hS3 := CodeAt.split code hS2.1 (n := 18) (by simp [writesOf_length])
  have hS4 := CodeAt.split code hS3.1 (n := 2) (by simp)
  have c0 := (CodeAt.cons.mp hS4.1).1
  have c1 := (CodeAt.cons.mp (CodeAt.cons.mp hS4.1).2).1
  have c18 := (CodeAt.cons.mp hS3.2).1
  have c19 := (CodeAt.cons.mp (CodeAt.cons.mp hS3.2).2).1
  have c20 := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp hS3.2).2).2).1
  have c37 := (CodeAt.cons.mp hS.2).1
  have c38 := (CodeAt.cons.mp (CodeAt.cons.mp hS.2).2).1
  simp only [after_after] at c19 c20 c38
  -- the length word
  let s1 : State := { s.setX 3 (s.x 17 + s.x 0) with pc := s.pc + 4 }
  have e1 : LeanExe.A64.exec P (.addReg 3 17 0) s = some s1 := rfl
  have hx31 : s1.x 3 = s.x 17 + ptr := by
    show (s.setX 3 (s.x 17 + s.x 0)).x 3 = _
    rw [State.x_setX_same (by decide), hx0]
  have hmapw : ∀ k ≤ ws.size, ∀ j < 8,
      P.normal (s.x 17 + ptr + UInt64.ofNat (8 * k) + UInt64.ofNat (8 * 512 + j)) = true := by
    intro k hk j hj
    have e : s.x 17 + ptr + UInt64.ofNat (8 * k) + UInt64.ofNat (8 * 512 + j) =
        s.x 17 + UInt64.ofNat (4096 + (ptr.toNat + 8 * k + j)) := by
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
      have := ptr.toNat_lt
      simp only [Nat.reducePow] at *
      omega
    rw [e]
    exact hsr.mapped _ (by unfold areaSize; omega)
  have e2 := exec_ldr_base P (s := s1) (t := 4) (i := 512) (by decide) (n := 3) (by decide)
    (fun j hj => by
      rw [hx31]
      have := hmapw 0 (Nat.zero_le _) j hj
      rwa [Nat.mul_zero, add_ofNat_zero] at this)
  let s2 : State := { s1.setX 4 (load64 s1.mem (s1.x 3 + UInt64.ofNat (8 * 512))) with
    pc := s1.pc + 4 }
  have hmem1 : s1.mem = s.mem := State.setX_mem
  have hx42 : s2.x 4 = UInt64.ofNat ws.size := by
    show (s1.setX 4 (load64 s1.mem (s1.x 3 + UInt64.ofNat (8 * 512)))).x 4 = _
    rw [State.x_setX_same (by decide), hmem1, hx31]
    have := array_word P hsr hat (k := 0) (Nat.zero_le _)
    rw [Nat.mul_zero, add_ofNat_zero, add_ofNat_zero] at this
    rw [this]
    exact hA3
  have hk2 : ∀ q : Fin 32, q ≠ 3 → q ≠ 4 → s2.x q = s.x q := fun q hq3 hq4 => by
    show (s1.setX 4 (load64 s1.mem (s1.x 3 + UInt64.ofNat (8 * 512)))).x q = _
    rw [State.x_setX_ne (Ne.symm hq4)]
    show (s.setX 3 (s.x 17 + s.x 0)).x q = _
    rw [State.x_setX_ne (Ne.symm hq3)]
  have p1 : s1.pc = after a 1 := by simp [s1, hpc, after]
  have p2 : s2.pc = after a 2 := by
    show s.pc + 4 + 4 = a + 4 * UInt64.ofNat 2
    rw [hpc, UInt64.add_assoc]
    congr 1
  obtain ⟨s3, r3, p3, out3, hk3, sp3, mem3⟩ :=
    run_writes P code (r := 4) (by decide) (by decide) hS4.2 p2
      (by rw [hk2 1 (by decide) (by decide), hx1])
  -- the loop
  have hsp2 : s2.sp = s.sp := by
    show (s1.setX 4 (load64 s1.mem (s1.x 3 + UInt64.ofNat (8 * 512)))).sp = _
    rw [State.setX_sp]
    exact State.setX_sp
  have hmem2 : s2.mem = s.mem := by
    show (s1.setX 4 (load64 s1.mem (s1.x 3 + UInt64.ofNat (8 * 512)))).mem = _
    rw [State.setX_mem, hmem1]
  have hout2 : s2.out = s.out := by
    show (s1.setX 4 (load64 s1.mem (s1.x 3 + UInt64.ofNat (8 * 512)))).out = _
    rw [State.setX_out]
    exact State.setX_out
  have loop : ∀ m k, k + m = ws.size → ∀ u : State, Reach P code s u → u.pc = after a 18 →
      u.x 3 = s.x 17 + ptr + UInt64.ofNat (8 * k) → u.x 4 = UInt64.ofNat m →
      u.x 1 = P.uart → u.sp = s.sp → u.mem = s.mem →
      u.out = s.out ++ bytesOf (UInt64.ofNat ws.size) ++ (ws.toList.take k).flatMap bytesOf →
      (∀ q : Fin 32, q ≠ 2 → q ≠ 3 → q ≠ 4 → q ≠ 6 → u.x q = s.x q) →
      ∃ t, Reach P code s t ∧ t.pc = after a 39 ∧ t.sp = s.sp ∧ t.mem = s.mem ∧
        t.out = s.out ++ arrayBytes ws ∧
        (∀ q : Fin 32, q ≠ 2 → q ≠ 3 → q ≠ 4 → q ≠ 6 → t.x q = s.x q) := by
    intro m
    induction m with
    | zero =>
        intro k hk u hr hp h3 h4 h1 hsp hmem hout hq
        have h40 : u.x 4 = 0 := by rw [h4]; rfl
        refine ⟨{ u with pc := after a 39 }, hr.trans (reach_exec P code (by rw [hp]; exact c18)
          (by simp [exec, h40, hp, cbField_target hcz]) (.refl _)), rfl, hsp, hmem, ?_, hq⟩
        show u.out = _
        have hkn : k = ws.size := by omega
        rw [hout, hkn, List.take_of_length_le (by simp), List.append_assoc]
        rfl
    | succ m ih =>
        intro k hk u hr hp h3 h4 h1 hsp hmem hout hq
        have hm64 : m + 1 < 2 ^ 64 := by have := hA1; omega
        have h4' : u.x 4 ≠ 0 := by
          rw [h4]
          intro e
          have := congrArg UInt64.toNat e
          rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hm64] at this
          exact absurd this (by simp)
        obtain ⟨u', r', p', h3', h4'', hout', hsp', hmem', hq'⟩ :=
          run_arrayStep P code c18 c19 c20 hS2.2 c37 c38 hback hp h4' h1
            (fun j hj => by
              rw [h3, UInt64.add_assoc (s.x 17 + ptr), show (8 : UInt64) = UInt64.ofNat 8 from rfl,
                ← UInt64.ofNat_add, show 8 * k + 8 = 8 * (k + 1) by omega]
              exact hmapw (k + 1) (by omega) j hj)
        have hval : load64 u.mem (u.x 3 + 8 + UInt64.ofNat (8 * 512)) = ws[k]'(by omega) := by
          rw [hmem, h3, UInt64.add_assoc (s.x 17 + ptr),
            show (8 : UInt64) = UInt64.ofNat 8 from rfl, ← UInt64.ofNat_add,
            show 8 * k + 8 = 8 * (k + 1) by omega,
            array_word P hsr hat (k := k + 1) (by omega)]
          exact hA4 k (by omega)
        refine ih (k + 1) (by omega) u' (hr.trans r') p' ?_ ?_ ?_ (by rw [hsp', hsp])
          (by rw [hmem', hmem]) ?_ (fun q hq2 hq3 hq4 hq6 => by
            rw [hq' q hq2 hq3 hq4 hq6, hq q hq2 hq3 hq4 hq6])
        · rw [h3', h3, UInt64.add_assoc, show (8 : UInt64) = UInt64.ofNat 8 from rfl,
            ← UInt64.ofNat_add, show 8 * k + 8 = 8 * (k + 1) by omega]
        · rw [h4'', h4]
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.toNat_ofNat', UInt64.toNat_ofNat']
          simp only [Nat.reducePow] at *
          omega
        · rw [hq' 1 (by decide) (by decide) (by decide) (by decide), h1]
        · rw [hout', hout, hval, List.take_succ, List.getElem?_eq_getElem (by simp; omega)]
          simp [List.flatMap_append, List.append_assoc]
  exact loop ws.size 0 (by omega) s3
    (reach_exec P code (by rw [hpc]; exact c0) e1
      (reach_exec P code (by rw [p1]; exact c1) e2 r3))
    (by rw [p3, after_after])
    (by
      rw [hk3 3 (by decide), Nat.mul_zero, add_ofNat_zero]
      show (s1.setX 4 (load64 s1.mem (s1.x 3 + UInt64.ofNat (8 * 512)))).x 3 = _
      rw [State.x_setX_ne (by decide), hx31])
    (by rw [hk3 4 (by decide), hx42])
    (by rw [hk3 1 (by decide), hk2 1 (by decide) (by decide), hx1])
    (by rw [sp3, hsp2]) (by rw [mem3, hmem2])
    (by
      rw [out3, hout2, hx42, List.take_zero, List.flatMap_nil, List.append_nil]
      rfl)
    (fun q hq2 hq3 hq4 hq6 => by rw [hk3 q hq2, hk2 q hq3 hq4])

/-- What the machine does from `main` at `ms` when Talos's run of the program's function gives
`res`: a return of one value writes the result to the UART as `o` says, the eight bytes of its
word or, for every array that the final store holds at the pointer that the value is, the array's
bytes, and returns 0 to the address in X30 with SP as it was.  A trap at `unreachable`, an access
outside the memory, or a division by zero reaches the exit word at `base` with the trap's code in
X0 and the UART's output as it was. -/
def ProgramResult (base : UInt64) (o : Output) (res : Result Unit) (ms : State) : Prop :=
  match res, o with
  | .Success [v] _, .word => ∃ w ms', ValRel v w ∧ Reach P code ms ms' ∧ ms'.pc = ms.x 30 ∧
      ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧ ms'.out = ms.out ++ bytesOf w
  | .Success [v] st', .array => ∀ ptr ws, v = .i64 ptr →
      LeanExe.ProofKit.UInt64Array.At st' ptr ws → ∃ ms', Reach P code ms ms' ∧
        ms'.pc = ms.x 30 ∧ ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧ ms'.out = ms.out ++ arrayBytes ws
  | .Trap _ msg, _ => ∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧ ms'.out = ms.out ∧
      ((msg = "unreachable" ∧ ms'.x 0 = 1) ∨ (msg = "out of bounds memory access" ∧ ms'.x 0 = 2) ∨
        (msg = "integer divide by zero" ∧ ms'.x 0 = 3))
  | _, _ => True

/-- `ProgramResult`, or, when `calls` holds, the machine reaches the exit word with the status 4
of an overflow of the stack and the UART's output as it was. -/
def ProgramOutcome (base : UInt64) (calls : Prop) (o : Output) (res : Result Unit) (ms : State) :
    Prop :=
  (calls ∧ ∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧ ms'.x 0 = 4 ∧ ms'.out = ms.out) ∨
    ProgramResult P code base o res ms

theorem ProgramOutcome.mono {base : UInt64} {calls calls' : Prop} {o : Output}
    {res : Result Unit} {ms : State} (h : ProgramOutcome P code base calls o res ms)
    (hc : calls → calls') : ProgramOutcome P code base calls' o res ms := by
  rcases h with ⟨h1, h2⟩ | h
  · exact .inl ⟨hc h1, h2⟩
  · exact .inr h

theorem ProgramResult.success {base : UInt64} {res : Result Unit} {v : Value}
    {st' : Store Unit} {ms : State} (h : ProgramResult P code base .word res ms)
    (hres : res = .Success [v] st') :
    ∃ w ms', ValRel v w ∧ Reach P code ms ms' ∧ ms'.pc = ms.x 30 ∧ ms'.sp = ms.sp ∧
      ms'.x 0 = 0 ∧ ms'.out = ms.out ++ bytesOf w := by
  subst hres
  exact h

theorem ProgramResult.array {base : UInt64} {res : Result Unit} {ptr : UInt64}
    {ws : Array UInt64} {st' : Store Unit} {ms : State}
    (h : ProgramResult P code base .array res ms) (hres : res = .Success [.i64 ptr] st')
    (hat : LeanExe.ProofKit.UInt64Array.At st' ptr ws) :
    ∃ ms', Reach P code ms ms' ∧ ms'.pc = ms.x 30 ∧ ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧
      ms'.out = ms.out ++ arrayBytes ws := by
  subst hres
  exact h ptr ws rfl hat

theorem ProgramOutcome.success {base : UInt64} {calls : Prop} {res : Result Unit}
    {v : Value} {st' : Store Unit} {ms : State} (h : ProgramOutcome P code base calls .word res ms)
    (hres : res = .Success [v] st') :
    (calls ∧ ∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧ ms'.x 0 = 4 ∧ ms'.out = ms.out) ∨
      ∃ w ms', ValRel v w ∧ Reach P code ms ms' ∧ ms'.pc = ms.x 30 ∧ ms'.sp = ms.sp ∧
        ms'.x 0 = 0 ∧ ms'.out = ms.out ++ bytesOf w := by
  subst hres
  exact h

theorem ProgramOutcome.array {base : UInt64} {calls : Prop} {res : Result Unit}
    {ptr : UInt64} {ws : Array UInt64} {st' : Store Unit} {ms : State}
    (h : ProgramOutcome P code base calls .array res ms) (hres : res = .Success [.i64 ptr] st')
    (hat : LeanExe.ProofKit.UInt64Array.At st' ptr ws) :
    (calls ∧ ∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧ ms'.x 0 = 4 ∧ ms'.out = ms.out) ∨
      ∃ ms', Reach P code ms ms' ∧ ms'.pc = ms.x 30 ∧ ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧
        ms'.out = ms.out ++ arrayBytes ws := by
  subst hres
  rcases h with h | h
  · exact .inl h
  · exact .inr (h ptr ws rfl hat)

theorem ProgramOutcome.unreachable {base : UInt64} {calls : Prop} {o : Output} {res : Result Unit}
    {st' : Store Unit} {ms : State} (h : ProgramOutcome P code base calls o res ms)
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
`args`, from `main` at `after base 1`, for Talos's run of the function at any fuel from the
module's initial store with a memory of `cap` pages on the arguments `argValues f.params args`,
whose words are `args`.  The machine may reach the exit
word with the status of an overflow of the stack only when the functions that calls reach from
function `k` call others and `room` lies below `stackBound m k`.  `main` sets the stack's limit
`room` bytes below its frame of 16 bytes, and those `room + 16` bytes below SP must be Normal
memory above address 4096.  X17 must hold the area's address `area`, and the area must hold
`areaBytes`, lie in Normal memory, and end at or below the stack's limit. -/
theorem program_sim_stack {m : Module} {k : Nat} {f : Function} {args : List UInt64}
    {base room area : UInt64} {cap : Nat} {o : Output} {is : List Instr}
    (hg : genProgram m k args P.uart base room cap o = .ok is)
    (hcode : CodeAt code (after base 1) is) (hm : m.imports = []) (hk : m.funcs[k]? = some f)
    (hp : args.length = f.params.length) (F : Nat)
    (ms : State) (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0)
    (hroom : 4096 ≤ room.toNat) (htop : ms.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true)
    (h17 : ms.x 17 = area)
    (harea : ∀ j < areaSize cap, ms.mem (area + UInt64.ofNat j) = areaByte m.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true)
    (habove : area.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat) :
    ProgramOutcome P code base (callTargets m k ≠ [] ∧ room.toNat < stackBound m k) o
      (Wasm.run F m k (initStore m cap) (argValues f.params args).reverse) ms := by
  obtain ⟨gts, fs, first, T, main, fns, e, pk, rk, g1, g2, g3, g4, hok, hgt, hgl, hfs, hfirst, hT,
    hen, hps, hmg, hfg, his, hb1, hb2, hb3, hb4⟩ := gen_program hg
  subst his
  have hsp : 4096 + room.toNat + 16 ≤ ms.sp.toNat := by unfold areaSize at habove; omega
  have h64 : m.memIs64 = false := memIs64_of_areaOk hok
  have hfm := mapM_funcOf hfs
  have hsig := sigOf_tableOf (callTargets m k) first fs
  have hend := (genFunctions_length hsig hfg).2
  obtain ⟨h8, g, out, hbl, hgo, hmeq⟩ := gen_main hmg
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
      genFunction (tableOf (callTargets m k) first fs)
        ⟨T, after T 5, after T 10, after T 15, cap, gts⟩ c.1 f = .ok is ∧ CodeAt code c.1 is := by
    intro j c hj
    unfold tableOf at hj
    split at hj
    · obtain ⟨f', fis, hmem, hpr, hgen, hcd⟩ := gen_functions code hsig hfg cfns _ (entryIn_mem hj)
      exact ⟨f', fis, hfm _ hmem, hpr, hgen, hcd⟩
    · cases hj
  have hcl := calls_ok P code hm h64 htab (need := stackNeed m m.funcs.length)
    (fun _ _ hj => stackNeed_ok hj _) F
  have cmain := hc2.1
  rw [hmeq] at cmain
  generalize hA : after base 1 = A at *
  generalize hn : args.length = n at *
  have hL := loads_length args
  rw [hn] at hL
  have s8 := CodeAt.split code cmain (n := 4 * n + 17 + outSize o) (by
    simp only [List.length_append, hL, genOut_length hgo, movImm_length, List.length_cons,
      List.length_nil]
    all_goals omega)
  have s7 := CodeAt.split code s8.1 (n := 4 * n + 13 + outSize o) (by
    simp only [List.length_append, hL, genOut_length hgo, movImm_length, List.length_cons,
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
  have s3x := CodeAt.split code s4.1 (n := 8) (by
    simp only [List.length_append, movImm_length, List.length_cons, List.length_nil]
    all_goals omega)
  have s2 := CodeAt.split code s3x.1 (n := 7) (by
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
  have h17b : t3b.x 17 = ms.x 17 := by
    rw [State.x_withPc, State.x_setX_ne (by decide), hk3a 17 (by decide), State.x_withPc,
      State.x_setX_ne (by decide)]
    rfl
  -- the loads
  obtain ⟨t3, r3, p3, hx3, hhi3, sp3, mem3, out3⟩ :=
    run_loads P code (args := args) (by omega) s3x.2 p3b
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
  have h174 : t4.x 17 = area := by
    show (t3.setX 30 (t3.pc + 4)).x 17 = _
    rw [State.x_setX_ne (by decide), hhi3 17 (by decide), h17b, h17]
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
  have mem4 : t4.mem = store64 ms.mem (slotAddr (ms.sp - 16) 0) (ms.x 30) := by
    show (t3.setX 30 (t3.pc + 4)).mem = _
    rw [State.setX_mem, mem3]
    show (t3a.setX 18 (t3a.x 18 - t3a.x 16)).mem = _
    rw [State.setX_mem, mem3a]
    show (t2.setX 18 (t2.sp + UInt64.ofNat 0)).mem = _
    exact State.setX_mem
  have hsr4 : StoreRel P cap gts (initStore m cap) t4 := by
    refine storeRel_init P hok hgt hgl (fun j hj => ?_) (fun j hj => by rw [h174]; exact hamap j hj)
      (by rw [h174, h184, e16r]; unfold areaSize at habove ⊢; omega)
    rw [mem4, h174, store64_other _ _ _ _ ?_]
    · exact harea j hj
    · have := area.toNat_lt
      unfold areaSize at habove hj
      exact below_slot (Nat.le_refl _) (by rw [e16]; omega) (by decide)
        (by rw [UInt64.toNat_add, UInt64.toNat_ofNat', e16]; simp only [Nat.reducePow] at *; omega)
  have hvs : ((argValues f.params args).reverse).length = f.params.length := by
    rw [List.length_reverse, length_argValues]
    omega
  have hvt : Typed f.params.reverse
      (((argValues f.params args).reverse).take f.params.length) := by
    rw [List.take_of_length_le (by omega)]
    exact Typed.reverse (typed_words hps (by omega))
  rcases run_outcome P code hm h64 hk hgk cfk hcl (stackNeed_ok hk _) (initStore m cap)
    (argValues f.params args).reverse t4 (by omega) hvt p4 hstk hsr4 (by
      rw [List.take_of_length_le (by omega)]
      refine ⟨by rw [List.length_reverse, length_argValues]; omega, fun i hi => ?_⟩
      have hi' : i < args.length := by
        rw [List.length_reverse, length_argValues] at hi
        omega
      simp only [List.reverse_reverse, getElem_argValues]
      have hx : t4.x (regOf i) = args[i] := by
        rw [regOf_small i (by omega)]
        show (t3.setX 30 (t3.pc + 4)).x ⟨i % 32, Nat.mod_lt _ (by decide)⟩ = _
        rw [State.x_setX_ne (fun e => by
          have : 30 = i % 32 := congrArg Fin.val e
          omega)]
        exact hx3 i hi'
      rw [hx]
      exact valRel_argValue _ _) with ⟨hov, hovr⟩ | hro
  · rw [hd4] at hov
    have hct : callTargets m k ≠ [] := by
      intro hct
      have hc0 : callsIn f.body = [] := List.eq_nil_iff_forall_not_mem.mpr fun j hj => by
        simpa [hct] using callsIn_callTargets hk hj
      have hlen : 0 < m.funcs.length := Nat.lt_of_not_le fun h => by
        rw [List.getElem?_eq_none (by omega)] at hk
        cases hk
      have hle := stackNeed_of_nil hk hc0 (m.funcs.length - 1)
      rw [Nat.sub_add_cancel hlen] at hle
      omega
    obtain ⟨u, ru, pu, outu⟩ := hovr
    obtain ⟨u2, ru2, pu2, xu2, outu2⟩ := run_stub P code cs4.2 hb4 pu
    exact .inl ⟨⟨hct, hov⟩, u2, r4.trans (ru.trans ru2), pu2, xu2, by rw [outu2, outu, out4]⟩
  refine .inr ?_
  revert hro
  cases Wasm.run F m k (initStore m cap) (argValues f.params args).reverse with
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
  obtain ⟨t5, r5, p5, sp5, -, out5, mf5, hlen5, -, hres5, -, hsr5⟩ := hro
  rcases vs' with _ | ⟨v, _ | ⟨v2, rest⟩⟩
  · cases o <;> trivial
  rotate_left
  · cases o <;> trivial
  have hr1 : f.results.length = 1 := by simp [hvs] at hlen5; omega
  rw [hr1] at hres5
  have hy : ValRel v (t5.x 0) := by
    have := hres5.2 0 (by simp)
    simpa [show regOf 0 = 0 by decide] using this
  -- the UART's address
  obtain ⟨t6, r6, p6, hx6, hk6, sp6, mem6, out6⟩ :=
    run_movImm P code (d := 1) (v := P.uart) (by decide) s5.2 (by rw [p5, h30])
  have hp6 : t6.pc = after A (13 + 4 * n) := by
    rw [p6, after_after, show 4 * n + 9 + 4 = 13 + 4 * n by omega]
  have cO : CodeAt code (after A (13 + 4 * n)) out := by
    rw [show 13 + 4 * n = 4 * n + 13 by omega]
    exact s6.2
  -- the return after the output
  have ht4 : t4.sp.toNat < 2 ^ 63 := by
    rw [sp4, e16]
    simp only [Nat.reducePow] at *
    omega
  have hab : ∀ k < 8, t4.sp.toNat + 8 * 0 ≤ (slotAddr (ms.sp - 16) 0 + UInt64.ofNat k).toNat :=
    fun k hk => by
      rw [← sp4]
      exact le_slot hk ht4 (by decide) (Nat.le_refl _)
  have exit : ∀ u : State, Reach P code ms u → u.pc = after A (4 * n + 13 + outSize o) →
      u.sp = ms.sp - 16 → u.mem = t5.mem →
      ∃ t9, Reach P code ms t9 ∧ t9.pc = ms.x 30 ∧ t9.sp = ms.sp ∧ t9.x 0 = 0 ∧
        t9.out = u.out := by
    intro u hru hpu hspu hmemu
    obtain ⟨t8, r8, p8, hx8, hk8, sp8, mem8, out8⟩ :=
      run_movImm P code (d := 0) (v := 0) (by decide) s7.2 hpu
    have sp8' : t8.sp = ms.sp - 16 := by rw [sp8, hspu]
    have p8' : t8.pc = after A (4 * n + 17 + outSize o) := by
      rw [p8, after_after, show 4 * n + 13 + outSize o + 4 = 4 * n + 17 + outSize o by omega]
    have al8 : t8.sp % 16 = 0 := by rw [sp8']; exact halm
    have mp8 : ∀ j < 8, P.normal (t8.sp + UInt64.ofNat (8 * 0 + j)) = true := fun j hj => by
      rw [sp8']
      simpa using hmain j (by omega)
    obtain ⟨t9, r9, p9, sp9, out9, mem9, hx9⟩ :=
      run_epilogue P code (n := 0) (fs := 16) (by decide) (by decide) s8.2 p8' al8 mp8
    refine ⟨t9, hru.trans (r8.trans r9), ?_, ?_, ?_, ?_⟩
    · rw [p9, sp8', mem8, hmemu, load64_congr (m' := t4.mem) fun k hk => mf5 _ (hab k hk)]
      show load64 t3.mem _ = _
      rw [mem3]
      show load64 t3a.mem _ = _
      rw [mem3a]
      exact load64_store64_same _ _ _
    · rw [sp9, sp8', show UInt64.ofNat 16 = 16 from rfl, UInt64.sub_add_cancel]
    · rw [hx9 0 (by decide), hx8]
    · rw [out9, out8]
  cases o with
  | word =>
      have hout : out = writesOf 0 := by
        simp only [genOut, pure, Except.pure, Except.ok.injEq] at hgo
        exact hgo.symm
      subst hout
      obtain ⟨t7, r7, p7, out7, hk7, sp7, mem7⟩ :=
        run_writes P code (r := 0) (by decide) (by decide) (s := t6) cO hp6 hx6
      obtain ⟨t9, r9, p9, sp9, x9, out9⟩ := exit t7 (r4.trans (r5.trans (r6.trans r7)))
        (by rw [p7, after_after]; congr 1; simp only [outSize]; omega)
        (by rw [sp7, sp6, sp5, sp4]) (by rw [mem7, mem6])
      refine ⟨t5.x 0, t9, hy, r9, p9, sp9, x9, ?_⟩
      rw [out9, out7, hk6 0 (by decide), out6, out5, out4]
      rfl
  | array =>
      obtain ⟨cz, back, hcz, hback, rfl⟩ := gen_out_array hgo
      intro ptr ws hv hat
      subst hv
      have hx0 : t6.x 0 = ptr := by rw [hk6 0 (by decide)]; exact hy
      have hsr6 := hsr5.regs (hk6 17 (by decide)) (hk6 18 (by decide)) mem6
      obtain ⟨t7, r7, p7, sp7, mem7, out7, -⟩ :=
        run_arrayOut P code cO hcz hback hp6 hsr6 hx0 hx6 hat
      obtain ⟨t9, r9, p9, sp9, x9, out9⟩ := exit t7 (r4.trans (r5.trans (r6.trans r7)))
        (by rw [p7, after_after]; congr 1; simp only [outSize]; omega)
        (by rw [sp7, sp6, sp5, sp4]) (by rw [mem7, mem6])
      refine ⟨t9, r9, p9, sp9, x9, ?_⟩
      rw [out9, out7, out6, out5, out4]

/-- `program_sim_stack` without its condition on `room`: the machine may reach the exit word with
the status of an overflow of the stack only when the functions that calls reach from function `k`
call others. -/
theorem program_sim {m : Module} {k : Nat} {f : Function} {args : List UInt64}
    {base room area : UInt64} {cap : Nat} {o : Output} {is : List Instr}
    (hg : genProgram m k args P.uart base room cap o = .ok is)
    (hcode : CodeAt code (after base 1) is) (hm : m.imports = []) (hk : m.funcs[k]? = some f)
    (hp : args.length = f.params.length) (F : Nat)
    (ms : State) (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0)
    (hroom : 4096 ≤ room.toNat) (htop : ms.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true)
    (h17 : ms.x 17 = area)
    (harea : ∀ j < areaSize cap, ms.mem (area + UInt64.ofNat j) = areaByte m.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true)
    (habove : area.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat) :
    ProgramOutcome P code base (callTargets m k ≠ []) o
      (Wasm.run F m k (initStore m cap) (argValues f.params args).reverse) ms :=
  (program_sim_stack P code hg hcode hm hk hp F ms hpc hal hroom htop hstack h17 harea hamap
    habove).mono P code And.left

/-- `program_sim_stack` with `room` at or above `stackBound m k`: the machine does what
`ProgramResult` states, without the outcome of an overflow of the stack.  The premise can hold
only when the calls from function `k` reach no cycle, since a cycle makes `stackBound m k` 2^64. -/
theorem program_sim_bounded {m : Module} {k : Nat} {f : Function} {args : List UInt64}
    {base room area : UInt64} {cap : Nat} {o : Output} {is : List Instr}
    (hg : genProgram m k args P.uart base room cap o = .ok is)
    (hcode : CodeAt code (after base 1) is) (hm : m.imports = []) (hk : m.funcs[k]? = some f)
    (hp : args.length = f.params.length) (F : Nat)
    (ms : State) (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0)
    (hroom : 4096 ≤ room.toNat) (hbound : stackBound m k ≤ room.toNat)
    (htop : ms.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true)
    (h17 : ms.x 17 = area)
    (harea : ∀ j < areaSize cap, ms.mem (area + UInt64.ofNat j) = areaByte m.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true)
    (habove : area.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat) :
    ProgramResult P code base o
      (Wasm.run F m k (initStore m cap) (argValues f.params args).reverse) ms := by
  rcases program_sim_stack P code hg hcode hm hk hp F ms hpc hal hroom htop hstack h17 harea hamap
    habove with ⟨⟨-, hlt⟩, -⟩ | h
  · omega
  · exact h

end LeanExe.A64
