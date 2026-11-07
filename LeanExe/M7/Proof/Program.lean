import LeanExe.M7.Proof.Function

/-!
The simulation of the step that the generator's program calls, as `LeanExe/A64/Proof/Program.lean`
lays out the AArch64 program.  `gen_program` inverts `genProgram`: `main`, of `mainSize s0` units
of 4 bytes, the functions that calls reach from the step, the step first, the trap stubs, three
or, for a program with an area, four, and the code of `udivmod64`, and `gen_program_entry` adds
that the step comes first among the functions, so that `main`'s call of the step targets the
address after `main`.  `gen_functions` places each function at the entry that `entriesFrom` gives
it, from `genFunctions`'s check that each function's halfwords number twice its size in units, and
`sigOf_tableOf` identifies the numbers of parameters and results of the table with those from
which the generator computed the frames.  `step_sim` combines these with `calls_ok` and `fun_sim`:
the step's code, from its entry after `main`, simulates a call of the step at every fuel, with the
bound `stackBound` of the stack that the call uses.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit LeanExe.CallGraph

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-! ## Sizes -/

theorem size_halfwords (i : Instr) : i.size = 2 * i.halfwords := by
  cases i <;> rfl

theorem codeSize_halfwords : ∀ is : List Instr, codeSize is = 2 * halfwordsOf is
  | [] => rfl
  | i :: is => by
      rw [codeSize_cons, codeSize_halfwords is, size_halfwords]
      simp only [halfwordsOf, List.map_cons, List.sum_cons]
      omega

theorem all_flatten_wide : ∀ {L : List (List Instr)},
    (∀ i (hi : i < L.length), L[i].all Instr.wide = true) → L.flatten.all Instr.wide = true
  | [], _ => rfl
  | l :: L, h => by
      have h0 : l.all Instr.wide = true := h 0 (by simp)
      rw [List.flatten_cons, List.all_append, h0,
        all_flatten_wide (L := L) fun i hi => h (i + 1) (by simp; omega)]
      rfl

theorem movPair_wide (v : UInt64) : (movPair v).all Instr.wide = true := by
  rw [movPair, List.all_append, movConst_wide, movConst_wide]
  rfl

/-- Every instruction of `main` takes 4 bytes. -/
theorem genMain_wide {a step dev : UInt32} {s0 : List UInt64} {main : List Instr}
    (hg : genMain a step dev s0 = .ok main) : main.all Instr.wide = true := by
  unfold genMain at hg
  simp only [except_bind_ok, except_pure_ok] at hg
  obtain ⟨_, -, _, -, _, -, words, hw, b1, hb1, b2, hb2, b3, hb3, b4, hb4, rfl⟩ := hg
  obtain ⟨o1, rfl, -⟩ := blAt_ok hb1
  obtain ⟨o2, rfl, -⟩ := bcondAt_ok hb2
  obtain ⟨o3, rfl, -⟩ := bAt_ok hb3
  obtain ⟨o4, rfl, -⟩ := bAt_ok hb4
  obtain ⟨hl, hr⟩ := mapM_ok hw
  have hww : words.flatten.all Instr.wide = true := all_flatten_wide fun i hi => by
    have := hr i (by omega) hi
    simp only [except_bind_ok, except_pure_ok] at this
    obtain ⟨l, hsl, e⟩ := this
    obtain ⟨h0, h1, rfl⟩ := stPair_ok hsl
    rw [← e, List.all_append, movPair_wide]
    rfl
  simp only [List.all_append, hww]
  rfl

/-! ## The generator's program -/

theorem codeSize_trapStubs (area : Option (List ValueType)) :
    codeSize (trapStubs area) = 4 * stubCount area := by
  cases area <;> rfl

theorem gen_program {m : Module} {k : Nat} {s0 : List UInt64} {base limit dev : UInt32}
    {div is : List Instr} (hg : genProgram m k s0 base limit dev div = .ok is) :
    ∃ fs e main area fns, (reachFrom m k).mapM (funcOf m) = .ok fs ∧
      ((entriesFrom (sigIn (callTargets m k) fs) (after base (mainSize s0)) fs).find?
          (·.1 = k)).map (·.2) =
        some (e, List.replicate (s0.length + 1) .i64, List.replicate (s0.length + 1) .i64) ∧
      genMain base e dev s0 = .ok main ∧ main.length = mainSize s0 ∧
      areaOf m fs limit = .ok area ∧
      genFunctions (tableOf (callTargets m k)
          (entriesFrom (sigIn (callTargets m k) fs) (after base (mainSize s0)) fs))
        (progShared (endOf (sigIn (callTargets m k) fs) (after base (mainSize s0)) fs) limit area)
        (after base (mainSize s0)) fs = .ok fns ∧
      is = main ++ fns ++ trapStubs area ++ div := by
  unfold genProgram at hg
  simp only [except_bind_ok] at hg
  obtain ⟨fs, hfs, hg⟩ := hg
  split at hg
  · rename_i e ps rs hen
    split at hg
    · rename_i hps
      obtain ⟨rfl, rfl⟩ := hps
      simp only [except_bind_ok, except_pure_ok] at hg
      obtain ⟨e', he', main, hmain, hg⟩ := hg
      subst he'
      split at hg
      · simp only [except_bind_ok] at hg
        obtain ⟨_, h, -⟩ := hg
        exact absurd h except_throw_ok
      · rename_i hlen
        simp only [except_bind_ok, except_pure_ok] at hg
        obtain ⟨area, harea, fns, hfns, rfl⟩ := hg
        exact ⟨fs, _, main, area, fns, hfs, hen, hmain, by omega, harea, hfns, rfl⟩
    · simp only [except_bind_ok] at hg
      obtain ⟨_, h, -⟩ := hg
      exact absurd h except_throw_ok
  · simp only [except_bind_ok] at hg
    obtain ⟨_, h, -⟩ := hg
    exact absurd h except_throw_ok

/-- The step `k` is the first function after `main`, and `main`'s call of the step targets the
address after `main`: the program is `main`, generated for that address, the functions that
calls reach from `k`, `k` first with `s0.length + 1` parameters and results of type `i64`, the
trap stubs, and `div`. -/
theorem gen_program_entry {m : Module} {k : Nat} {s0 : List UInt64} {base limit dev : UInt32}
    {div is : List Instr} (hg : genProgram m k s0 base limit dev div = .ok is) :
    ∃ f fs', (reachFrom m k).mapM (funcOf m) = .ok ((k, f) :: fs') ∧ m.funcs[k]? = some f ∧
      f.params = List.replicate (s0.length + 1) .i64 ∧
      f.results = List.replicate (s0.length + 1) .i64 ∧
      ∃ main fns area, genMain base (after base (mainSize s0)) dev s0 = .ok main ∧
        main.length = mainSize s0 ∧ areaOf m ((k, f) :: fs') limit = .ok area ∧
        genFunctions (tableOf (callTargets m k)
            (entriesFrom (sigIn (callTargets m k) ((k, f) :: fs')) (after base (mainSize s0))
              ((k, f) :: fs')))
          (progShared (endOf (sigIn (callTargets m k) ((k, f) :: fs')) (after base (mainSize s0))
            ((k, f) :: fs')) limit area)
          (after base (mainSize s0)) ((k, f) :: fs') = .ok fns ∧
        is = main ++ fns ++ trapStubs area ++ div := by
  obtain ⟨fs, e, main, area, fns, hfs, hen, hmain, hml, harea, hfns, rfl⟩ := gen_program hg
  obtain ⟨rest, hrk⟩ := reachFrom_cons m k
  rw [hrk] at hfs
  obtain ⟨f, fs', hkf, rfl⟩ := mapM_funcOf_cons hfs
  rw [← hrk] at hfs
  have hen' : after base (mainSize s0) = e ∧ f.params = List.replicate (s0.length + 1) .i64 ∧
      f.results = List.replicate (s0.length + 1) .i64 := by
    simpa [entriesFrom] using hen
  obtain ⟨rfl, hps, hrs⟩ := hen'
  exact ⟨f, fs', hfs, hkf, hps, hrs, main, fns, area, hmain, hml, harea, hfns, rfl⟩

/-! ## The layout of the functions -/

theorem find_entriesFrom (sig : Nat → Option (Nat × Nat)) (j : Nat) :
    ∀ (a : UInt32) (fs : List (Nat × Function)),
      ((entriesFrom sig a fs).find? (·.1 = j)).map (fun x => (x.2.2.1.length, x.2.2.2.length)) =
        (fs.find? (·.1 = j)).map (fun x => (x.2.params.length, x.2.results.length))
  | _, [] => rfl
  | a, (j', f) :: rest => by
      by_cases h : j' = j
      · simp [entriesFrom, h]
      · simp only [entriesFrom, List.find?_cons, h, decide_false]
        exact find_entriesFrom sig j _ rest

theorem sigOf_tableOf (targets : List Nat) (sig : Nat → Option (Nat × Nat)) (a : UInt32)
    (fs : List (Nat × Function)) :
    sigOf (tableOf targets (entriesFrom sig a fs)) = sigIn targets fs := by
  funext j
  simp only [sigOf, tableOf, sigIn]
  split
  · rw [Option.map_map]
    exact find_entriesFrom sig j a fs
  · rfl

/-- The code that `genFunctions` lays out from the even address `a`: its size, the address after
it, and each function's code at its entry. -/
theorem gen_functions {callee : Table} {S : Shared} {sig : Nat → Option (Nat × Nat)}
    (hsig : sigOf callee = sig) :
    ∀ {a : UInt32} {fs : List (Nat × Function)} {is : List Instr},
      genFunctions callee S a fs = .ok is → CodeAt code a is → a.toNat % 2 = 0 →
      codeSize is = 4 * (fs.map fun x => functionSize sig x.2).sum ∧
      endOf sig a fs = after a (fs.map fun x => functionSize sig x.2).sum ∧
      ∀ x ∈ entriesFrom sig a fs, ∃ f fis, (x.1, f) ∈ fs ∧ x.2.2 = (f.params, f.results) ∧
        genFunction callee S x.2.1 f = .ok fis ∧ CodeAt code x.2.1 fis ∧ x.2.1.toNat % 2 = 0
  | a, [], is, hg, _, _ => by
      simp only [genFunctions, pure, Except.pure, Except.ok.injEq] at hg
      subst hg
      refine ⟨rfl, by rw [after_eq]; simp [endOf], fun x hx => by simp [entriesFrom] at hx⟩
  | a, (j, f) :: rest, is, hg, hcode, hev => by
      simp only [genFunctions, except_bind_ok] at hg
      obtain ⟨is1, h1, hg⟩ := hg
      split at hg
      · simp only [except_bind_ok] at hg
        obtain ⟨_, h, -⟩ := hg
        exact absurd h except_throw_ok
      rename_i hhw
      simp only [except_bind_ok, except_pure_ok] at hg
      obtain ⟨is2, h2, rfl⟩ := hg
      rw [hsig] at hhw h2
      have hc1 : codeSize is1 = 4 * functionSize sig f := by
        rw [codeSize_halfwords]
        omega
      obtain ⟨hca, hcb⟩ := CodeAt.append.mp hcode
      rw [hc1, ← after_eq] at hcb
      obtain ⟨hs2, he2, ht2⟩ := gen_functions hsig h2 hcb (even_after hev _)
      refine ⟨?_, ?_, fun x hx => ?_⟩
      · rw [codeSize_append, hc1, hs2]
        simp only [List.map_cons, List.sum_cons]
        omega
      · simp only [endOf, List.map_cons, List.sum_cons]
        rw [he2, after_after]
      · simp only [entriesFrom, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨f, is1, by simp, rfl, h1, hca, hev⟩
        · obtain ⟨f', fis, hm, hp, hgen, hcd, hev'⟩ := ht2 x hx
          exact ⟨f', fis, List.mem_cons_of_mem _ hm, hp, hgen, hcd, hev'⟩

/-! ## The step -/

/-- A bound on the bytes of stack that a call of function `k` of `m` uses, `stackNeedOf` as many
calls deep as `m` has functions, with the frames that the generator gives the functions that calls
reach from `k`.  When the calls from `k` reach no cycle, a chain of calls from `k` holds each
function at most once, so the bound is the largest sum of the frames along one chain; a cycle makes
it 2^64.  `udivmod64` uses no stack. -/
def stackBound (m : Module) (k : Nat) : Nat :=
  match (reachFrom m k).mapM (funcOf m) with
  | .ok fs =>
      stackNeedOf m (fun f => (frameOf (sigIn (callTargets m k) fs) f).size) m.funcs.length k
  | .error _ => 0

/-- The functions that calls reach from function `k` of `m` have the covered forms. -/
def reachCovered (m : Module) (k : Nat) : Bool :=
  (reachFrom m k).all fun j => ((m.funcs[j]?).map fun f => coveredList f.body).getD true

/-- Whether a function that calls reach from function `k` of `m` loads, stores, or accesses a
global, which gives the generator's program an area: the test of `areaOf`. -/
def usesArea (m : Module) (k : Nat) : Bool :=
  match (reachFrom m k).mapM (funcOf m) with
  | .ok fs => fs.any fun x => listArea x.2.body
  | .error _ => false

/-- A program whose functions do not access the area has none. -/
theorem areaOf_none {m : Module} {fs : List (Nat × Function)} {limit : UInt32}
    (h : (fs.any fun x => listArea x.2.body) = false) : areaOf m fs limit = .ok none := by
  unfold areaOf
  rw [h]
  rfl

/-- The area of a program whose functions access it: the module's globals, at most 511 `i32`s and
`i64`s, a memory that `areaOk` accepts for `areaPages` pages, and the stack's limit at or above the
area's end. -/
theorem areaOf_some {m : Module} {fs : List (Nat × Function)} {limit : UInt32}
    {area : Option (List ValueType)} (h : (fs.any fun x => listArea x.2.body) = true)
    (ha : areaOf m fs limit = .ok area) :
    ∃ gts, area = some gts ∧ globalTypesOf m = some gts ∧ areaOk m areaPages = true ∧
      gts.length ≤ 511 ∧ gts.all intType = true ∧ areaEnd.toNat ≤ limit.toNat := by
  unfold areaOf at ha
  simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ha
  by_cases hok : areaOk m areaPages = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ha
    cases hg : globalTypesOf m with
    | none => simp [hg, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ha
    | some gts =>
        by_cases h511 : 511 < gts.length
        · simp [hg, h511, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ha
        · by_cases hint : gts.all intType = true
          · by_cases hlim : limit.toNat < areaEnd.toNat
            · simp [hg, h511, hint, hlim, throw, throwThe, MonadExceptOf.throw, bind,
                Except.bind, pure, Except.pure] at ha
            · simp [hg, h511, hint, hlim, bind, Except.bind, pure, Except.pure] at ha
              exact ⟨gts, ha.symm, rfl, hok, by omega, hint, by omega⟩
          · simp [hg, h511, hint, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ha
  · simp [hok, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ha

/-- The area of the generator's program, by `usesArea`. -/
theorem area_of_usesArea {m : Module} {k : Nat} {fs : List (Nat × Function)} {limit : UInt32}
    {area : Option (List ValueType)} (hfs : (reachFrom m k).mapM (funcOf m) = .ok fs)
    (ha : areaOf m fs limit = .ok area) :
    (usesArea m k = false → area = none) ∧
      (usesArea m k = true → ∃ gts, area = some gts ∧ globalTypesOf m = some gts ∧
        areaOk m areaPages = true ∧ gts.length ≤ 511 ∧ gts.all intType = true ∧
        areaEnd.toNat ≤ limit.toNat) := by
  unfold usesArea
  rw [hfs]
  refine ⟨fun h => ?_, fun h => areaOf_some h ha⟩
  rw [areaOf_none h] at ha
  cases ha
  rfl

/-- The simulation of a call of the step `k` of the generator's program, placed at the even
address `base`: the step's code, from its entry after `main`, simulates the call at every fuel, in
a module that imports nothing and whose functions that calls reach from `k` have the covered
forms, with a bound `need` of the stack that its calls use whose value for `k` is
`stackBound m k`. -/
theorem step_sim {m : Module} {k : Nat} {s0 : List UInt64} {base limit dev : UInt32}
    {is : List Instr} (hm : m.imports = [])
    (hg : genProgram m k s0 base limit dev udivmod64 = .ok is) (hcode : CodeAt code base is)
    (hev : base.toNat % 2 = 0) (hcov : reachCovered m k = true) :
    ∃ (f : Function) (S : Shared) (need : Nat → Nat), m.funcs[k]? = some f ∧ S.limit = limit ∧
      f.params = List.replicate (s0.length + 1) .i64 ∧
      f.results = List.replicate (s0.length + 1) .i64 ∧ need k = stackBound m k ∧
      ∀ g, FunSim P σ code m S need g k (after base (mainSize s0), f.params, f.results) := by
  obtain ⟨f, fs', hfs, hkf, hps, hrs, main, fns, area, hmain, hml, -, hfns, rfl⟩ :=
    gen_program_entry hg
  generalize hsig : sigIn (callTargets m k) ((k, f) :: fs') = sig at hfns
  generalize hfirst : after base (mainSize s0) = first at hmain hfns ⊢
  generalize hcallee : tableOf (callTargets m k) (entriesFrom sig first ((k, f) :: fs')) =
    callee at hfns
  have htab : sigOf callee = sig := by
    rw [← hcallee, sigOf_tableOf]
    exact hsig
  -- the code of `main`, the functions, the stubs, and `udivmod64`
  have hcm : codeSize main = 4 * mainSize s0 := by
    rw [codeSize_of_wide (genMain_wide hmain), hml]
  have hcode' : CodeAt code base (main ++ (fns ++ (trapStubs area ++ udivmod64))) := by
    simpa only [List.append_assoc] using hcode
  obtain ⟨-, hc1⟩ := CodeAt.append.mp hcode'
  rw [hcm, ← after_eq, hfirst] at hc1
  obtain ⟨hcF, hc2⟩ := CodeAt.append.mp hc1
  obtain ⟨hfsz, hend, hents⟩ :=
    gen_functions htab hfns hcF (by rw [← hfirst]; exact even_after hev _)
  obtain ⟨-, hcD⟩ := CodeAt.append.mp hc2
  have hdiv : DivAt code (progShared (endOf sig first ((k, f) :: fs')) limit area) := by
    show CodeAt code (after (endOf sig first ((k, f) :: fs')) (stubCount area)) udivmod64
    rw [hend, after_after, after_eq]
    rw [hfsz, codeSize_trapStubs, add_ofNat_add] at hcD
    rw [show 4 * ((((k, f) :: fs').map fun x => functionSize sig x.2).sum + stubCount area) =
      4 * (((k, f) :: fs').map fun x => functionSize sig x.2).sum + 4 * stubCount area by omega]
    exact hcD
  -- the table and the bound
  let need : Nat → Nat := stackNeedOf m (fun f => (frameOf sig f).size) m.funcs.length
  have hneed : ∀ j f', m.funcs[j]? = some f' →
      NeedOk need (frameOf (sigOf callee) f').size f'.body (need j) := fun j f' hj => by
    rw [htab]
    exact stackNeedOf_ok hj _
  have hcovj : ∀ j, j ∈ reachFrom m k → ∀ f', m.funcs[j]? = some f' →
      coveredList f'.body = true := fun j hj f' hf => by
    have := List.all_eq_true.mp hcov j hj
    rw [hf] at this
    simpa using this
  have hcl := calls_ok (P := P) (σ := σ) (code := code) hm hdiv (need := need)
    (fun j c hc => by
      rw [← hcallee] at hc
      simp only [tableOf] at hc
      split at hc
      · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hc
        have hxj := List.find?_some hx
        simp only [decide_eq_true_eq] at hxj
        obtain ⟨f', fis, hm', hp', hgen, hcd, hev'⟩ := hents x (List.mem_of_find?_eq_some hx)
        rw [hxj] at hm'
        have hjf : m.funcs[j]? = some f' := mapM_funcOf hfs _ hm'
        exact ⟨f', fis, hjf, hp', hcovj j (mapM_funcOf_mem hfs _ hm') f' hjf, hgen, hcd, hev'⟩
      · cases hc)
    hneed
  obtain ⟨f', fis, hm', hp', hgen, hcd, hev'⟩ := hents (k, first, f.params, f.results)
    (by simp [entriesFrom])
  have hkf' : m.funcs[k]? = some f' := mapM_funcOf hfs _ hm'
  rw [hkf] at hkf'
  cases hkf'
  refine ⟨f, progShared (endOf sig first ((k, f) :: fs')) limit area, need, hkf, rfl, hps, hrs,
    ?_, fun g => ?_⟩
  · show stackNeedOf m (fun f => (frameOf sig f).size) m.funcs.length k = stackBound m k
    unfold stackBound
    rw [hfs]
    simp only [hsig]
  · exact fun_sim hm hkf (hcovj k (mem_reachFrom m k) f hkf) hgen hcd hev' hdiv (hcl g)
      (hneed k f hkf)

end LeanExe.M7
