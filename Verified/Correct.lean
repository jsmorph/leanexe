import Verified.TailSpec

/-! The compiler's correctness theorem.  Every function of a compiled program returns the value
that the program gives it, with the heap and store changed only as `ImplementsA` allows.  The code
of an expression traps only through a call of a function whose code takes the call depth, or when
`top` cannot rise by the potential of the paid owned variables that die in the expression plus its
allocation bound, `Expr.allocs`, within the memory cap.  `top` after the code, plus the potential of
a paid value, is at most `top` before it plus that sum.  `ImplementsB.trapFree` gives the theorem
without a trap for a function whose bound fits. -/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- The functions of a program, placed from position 2 of a module without imports, compute
their meanings `funs` within their bounds, at every depth with the frames it leaves. -/
theorem Prog.calls {S : List Sig} (prog : Prog S) (funs : Funs S) (hMeaning : prog.Meaning funs)
    (m : Module) (hm : Runtime m)
    (hFuncs : ∀ k < S.length, m.funcs[2 + k]? = prog.functions[k]?) :
    Calls m funs prog.flags (prog.boundsAt funs) (prog.fitsAt funs) := by
  have h0 : framesAt (999 + 1) = 0 := rfl
  induction hMeaning with
  | nil => intro g fv; cases fv
  | @cons S' f rest funs' _ ih =>
    have hRest : Calls m funs' rest.flags (rest.boundsAt funs') (rest.fitsAt funs') :=
      ih fun k hk => by
      rw [hFuncs k (by simp; omega)]
      simp [Prog.functions, List.getElem?_append_left (by rw [rest.functions_length]; exact hk)]
    have hpos : m.funcs[2 + S'.length]? =
        some (bodyFunction f.modes f.body f.depth (2 + S'.length)) := by
      rw [hFuncs _ (by simp)]
      simp [Prog.functions, rest.functions_length, Func.function]
    have hrf : f.paidResult rest.flags = true →
        f.body.paid rest.flags (entryModes f.params f.modes) (f.paidParams rest.flags)
          (fun _ => false) = true := fun h => by
      simp only [Func.paidResult, Bool.and_eq_true] at h; exact h.2
    intro g fv d
    cases fv with
    | here =>
      rw [FVar.callIndex_here]
      refine ⟨fun hdep => ?_, fun hdep d' hd' => ?_, _, hpos,
        bodyFunction_numParams f.modes f.body f.depth _⟩
      · have hdep' : f.depth = false := hdep
        rw [hdep'] at hpos
        have hC : CallsAt m funs' rest.flags (rest.boundsAt funs' 0) (rest.fitsAt funs' 0) 999 :=
          Calls.at (@hRest) 999
        rw [Prog.boundsAt_cons_here]
        simp only [hdep', Bool.false_eq_true, ↓reduceIte]
        exact bodyFunction_implements f.modes f.body f.placeArgs funs' rest.flags
          (rest.boundsAt funs' 0) (rest.fitsAt funs' 0) _ _ hrf m _ hm hpos hC hdep' f.aborts id
      · have hdep' : f.depth = true := hdep
        rw [hdep'] at hpos
        subst hd'
        refine bodyFunction_depth f.modes f.body f.placeArgs funs' rest.flags
          (rest.boundsAt funs' (framesAt (d' + 1))) (rest.fitsAt funs' (framesAt (d' + 1))) _ _ hrf
          m _ hm hpos d' (fun _ => Calls.at (@hRest) d') _ _ (fun args => ?_) (fun hlt args => ?_)
        · by_cases hlt : d' < depthLimit
          · rw [framesAt_succ hlt, Prog.fitsAt_cons_here]
            simp only [hdep', ↓reduceIte, hlt, decide_true, Bool.true_and]
            rfl
          · rw [framesAt_eq_zero hlt, Prog.fitsAt_cons_here]
            simp only [hdep', ↓reduceIte, hlt, decide_false, Bool.false_and]
            rfl
        · rw [framesAt_succ hlt, Prog.boundsAt_cons_here]
          simp only [hdep', ↓reduceIte]
          rfl
    | there g' =>
      rw [FVar.callIndex_there]
      exact hRest g' d
  | @consTail S' f rest funs' M _ hDecreases hM ih =>
    have hRest : Calls m funs' rest.flags (rest.boundsAt funs') (rest.fitsAt funs') :=
      ih fun k hk => by
      rw [hFuncs k (by simp; omega)]
      simp [Prog.functions, List.getElem?_append_left (by rw [rest.functions_length]; exact hk)]
    have hpos : m.funcs[2 + S'.length]? = some (f.function (2 + S'.length)) := by
      rw [hFuncs _ (by simp)]
      simp [Prog.functions, rest.functions_length]
    intro g fv d
    cases fv with
    | here =>
      rw [FVar.callIndex_here]
      refine ⟨fun hdep => ?_, fun hdep d' hd' => ?_, _, hpos, f.function_numParams _⟩
      · have hdep' : f.depth = false := hdep
        have hC : CallsAt m funs' rest.flags (rest.boundsAt funs' 0) (rest.fitsAt funs' 0) 999 :=
          Calls.at (@hRest) 999
        rw [Prog.boundsAt_consTail_here]
        simp only [hdep', Bool.false_eq_true, ↓reduceIte]
        exact f.function_implements funs' rest.flags (rest.boundsAt funs' 0) (rest.fitsAt funs' 0)
          hDecreases M hM m _ hm hpos hC hdep'
      · have hdep' : f.depth = true := hdep
        subst hd'
        refine f.function_depth funs' rest.flags (rest.boundsAt funs' (framesAt (d' + 1)))
          (rest.fitsAt funs' (framesAt (d' + 1))) hDecreases M hM m _ hm hpos hdep' d'
          (fun _ => Calls.at (@hRest) d') _ _ (fun args => ?_) (fun hlt args => ?_)
        · by_cases hlt : d' < depthLimit
          · rw [framesAt_succ hlt, Prog.fitsAt_consTail_here]
            simp only [hdep', ↓reduceIte, hlt, decide_true, Bool.true_and]
            rfl
          · rw [framesAt_eq_zero hlt, Prog.fitsAt_consTail_here]
            simp only [hdep', ↓reduceIte, hlt, decide_false, Bool.false_and]
            rfl
        · rw [framesAt_succ hlt, Prog.boundsAt_consTail_here]
          simp only [hdep', ↓reduceIte]
          rfl
    | there g' =>
      rw [FVar.callIndex_there]
      exact hRest g' d
  | @consRec S' f rest funs' M _ hM ih =>
    have hRest : Calls m funs' rest.flags (rest.boundsAt funs') (rest.fitsAt funs') :=
      ih fun k hk => by
      rw [hFuncs k (by simp; omega)]
      simp [Prog.functions, List.getElem?_append_left (by rw [rest.functions_length]; exact hk)]
    have hpos : m.funcs[2 + S'.length]? =
        some (bodyFunction f.modes f.body true (2 + S'.length)) := by
      rw [hFuncs _ (by simp)]
      simp [Prog.functions, rest.functions_length, RecFunc.function]
    have hMeaning : depthMeaning M = depthMeaning (f.body.denote (.cons (g := f.sig) M funs')) := by
      funext env
      cases env with
      | cons _ args => exact hM args
    have hrf : f.paidResult rest.flags = true →
        f.body.paid (f.flags rest.flags) (entryModes f.params f.modes) (f.paidParams rest.flags)
          (fun _ => false) = true := fun h => by
      have h' := h
      simp only [RecFunc.paidResult, Bool.and_eq_true] at h'
      simp only [RecFunc.flags, h]
      exact h'.2
    -- The function at each depth, by induction on the frames left.
    have hAt : ∀ n d, framesAt d = n →
        @ImplementsP _ _ (Env.represent (.word :: f.params) (.borrowed :: f.modes))
          (Ty.represent f.result) (fun env => env.depthOf = d)
          (fun env => f.fitsAt (.cons M funs') (rest.fitsAt funs') (framesAt d) env.dropDepth)
          (fun store ws x => Env.argPot store (f.sig.depthSel (f.paidParams rest.flags)) ws x)
          (fun store ws v => if f.paidResult rest.flags then f.result.pot store ws v else 0)
          true m (2 + S'.length) (depthMeaning M)
          (fun env => f.boundAt (.cons M funs') rest.flags (rest.boundsAt funs') (framesAt d)
            env.dropDepth) := by
      intro n
      induction n using Nat.strongRecOn with
      | _ n ih' =>
        intro d hn
        rw [hMeaning]
        refine bodyFunction_depth f.modes f.body f.placeArgs _ (f.flags rest.flags)
          (.cons (f.boundAt (.cons M funs') rest.flags (rest.boundsAt funs') (framesAt (d + 1)))
            (rest.boundsAt funs' (framesAt (d + 1))))
          (.cons (f.fitsAt (.cons M funs') (rest.fitsAt funs') (framesAt (d + 1)))
            (rest.fitsAt funs' (framesAt (d + 1))))
          _ _ hrf m _ hm hpos d (fun hlt => ?_) _ _ (fun args => ?_) (fun hlt args => ?_)
        · intro g fv
          cases fv with
          | here =>
            rw [FVar.callIndex_here]
            refine ⟨nofun, fun _ d' hd' => ?_, _, hpos,
              bodyFunction_numParams f.modes f.body true _⟩
            subst hd'
            exact ih' _ (by rw [← hn, framesAt_succ hlt]; omega) (d + 1) rfl
          | there g' =>
            rw [FVar.callIndex_there]
            exact Calls.at (@hRest) d g'
        · by_cases hlt : d < depthLimit
          · rw [framesAt_succ hlt]
            simp only [hlt, decide_true, Bool.true_and]
            rfl
          · rw [framesAt_eq_zero hlt]
            simp only [hlt, decide_false, Bool.false_and]
            rfl
        · rw [framesAt_succ hlt]; rfl
    intro g fv d
    cases fv with
    | here =>
      rw [FVar.callIndex_here]
      exact ⟨nofun, fun _ d' hd' => by subst hd'; exact hAt _ d' rfl, _, hpos,
        bodyFunction_numParams f.modes f.body true _⟩
    | there g' =>
      rw [FVar.callIndex_there]
      exact hRest g' d

/-- `ImplementsA` under a stronger precondition and with a weaker postcondition. -/
theorem _root_.LeanExe.Pipeline.ImplementsA.mono {α β : Type} {_ : Represent α}
    {_ : Represent β} {aborts : Bool} {m : Module} {entry : Nat} {f : α → β}
    {Pre Pre' : α → Heap → Store Unit → Prop}
    {Post Post' : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA aborts m entry f Pre Post)
    (hPre : ∀ x heap store, Pre' x heap store → Pre x heap store)
    (hPost : ∀ x heap store heap' store', Pre' x heap store →
      Post x heap store heap' store' → Post' x heap store heap' store') :
    ImplementsA aborts m entry f Pre' Post' :=
  fun env store heap params x hAt hPre' hRep hSep hCap =>
    (h env store heap params x hAt (hPre x heap store hPre') hRep hSep hCap).mono
      fun final _ ⟨heap', hAt', hOwned, hCaps, hRegions, hPost0⟩ =>
        ⟨heap', hAt', hOwned, hCaps, hRegions, hPost x heap store heap' final hPre' hPost0⟩

/-- `ImplementsB` gives `ImplementsA` without the bound. -/
theorem ImplementsB.implementsA {α β : Type} {_ : Represent α} {_ : Represent β} {aborts : Bool}
    {m : Module} {entry : Nat} {f : α → β} {bound : α → Nat}
    (h : ImplementsB aborts m entry f bound) :
    ImplementsA aborts m entry f (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  fun env store heap params x hAt _ hRep hSep hCap =>
    ((h env store heap params x hAt hRep hSep hCap).of_imp fun hf => by
      simp only [Bool.and_eq_true] at hf; exact hf.1).mono
      fun _ _ ⟨heap', hAt', hOwned, hCaps, hRegions, _⟩ =>
        ⟨heap', hAt', hOwned, hCaps, hRegions, trivial⟩

/-- `ImplementsB` for a call that cannot trap gives `ImplementsA false` without a precondition, and
the call raises `top` by at most the bound. -/
theorem ImplementsB.noTrap {α β : Type} {_ : Represent α} {_ : Represent β} {m : Module}
    {entry : Nat} {f : α → β} {bound : α → Nat} (h : ImplementsB false m entry f bound) :
    ImplementsA false m entry f (fun _ _ _ => True)
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + bound x) :=
  fun env store heap params x hAt _ hRep hSep hCap => h env store heap params x hAt hRep hSep hCap

/-- `ImplementsB` gives a call that does not trap when `top` can rise by the bound within the
cap, and that raises `top` by at most the bound. -/
theorem ImplementsB.trapFree {α β : Type} {_ : Represent α} {_ : Represent β} {aborts : Bool}
    {m : Module} {entry : Nat} {f : α → β} {bound : α → Nat}
    (h : ImplementsB aborts m entry f bound) :
    ImplementsA false m entry f (fun x heap store => heap.Within store m (bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + bound x) :=
  fun env store heap params x hAt hW hRep hSep hCap =>
    (h env store heap params x hAt hRep hSep hCap).of_imp fun hf => by
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hf
      exact absurd hW hf.2

theorem compileWith_runtime {S : List Sig} (prog : Prog S) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) : Runtime (compileWith prog tables wrappers) :=
  ⟨rfl, rfl, by simp [compileWith], by simp [compileWith]⟩

theorem compile_runtime {S : List Sig} (prog : Prog S) : Runtime (compile prog) :=
  compileWith_runtime prog [] []

/-- The correctness theorem.  For meanings `funs` of a program's functions, every function of the
program's module, at its call index, computes the function that `funs` gives it, as `FunSpec`
states at each depth with the flags `Prog.flags` and the bounds and frames `Prog.boundsAt` and
`Prog.fitsAt` at the frames that the depth leaves: it returns words that represent the value, with
the heap and store changed only as `ImplementsA` allows.  A function traps only at `unreachable`:
when it may allocate and `top` cannot rise within the cap by the potential of its paid arguments
plus its bound, or, when its code takes the call depth, when a call lacks its frames.  When its
calls find their frames, `top` after the call, plus the potential of a paid result, is at most
`top` before it plus that sum. -/
theorem Prog.correct {S : List Sig} (prog : Prog S) (funs : Funs S) (h : prog.Meaning funs) :
    Calls (compile prog) funs prog.flags (prog.boundsAt funs) (prog.fitsAt funs) :=
  prog.calls funs h _ (compile_runtime prog) fun _ hk => compile_funcs prog hk

/-- The correctness theorem for a program with tables and wrappers. -/
theorem Prog.correctWith {S : List Sig} (prog : Prog S) (funs : Funs S) (h : prog.Meaning funs)
    (tables : List (Array UInt64)) (wrappers : List (Wrapper S tables.length)) :
    Calls (compileWith prog tables wrappers) funs prog.flags (prog.boundsAt funs)
      (prog.fitsAt funs) :=
  prog.calls funs h _ (compileWith_runtime prog tables wrappers) fun _ hk =>
    compileWith_funcs prog tables wrappers hk

/-- The `local.get` of each position from `k`, in order, pushes the words `vs` that they hold. -/
theorem wp_localGets {m : Module} {host : HostEnv Unit} {Q : Assertion Unit} {store : Store Unit}
    {rest : Program} : (vs : List Value) → (k : Nat) → (s : Locals) →
    (∀ i (hi : i < vs.length), s.get (k + i) = some vs[i]) →
    wp m rest Q store { s with values := vs.reverse ++ s.values } host →
    wp m ((List.range' k vs.length).map Instruction.localGet ++ rest) Q store s host
  | [], _, s, _, h => by
    simp only [List.reverse_nil, List.nil_append, List.length_nil, List.range'_zero,
      List.map_nil] at h ⊢
    exact h
  | v :: vs, k, s, hget, h => by
    have h0 : s.get k = some v := hget 0 (by simp)
    simp only [List.length_cons, List.range'_succ, List.map_cons, List.cons_append,
      wp_localGet_cons, h0]
    refine wp_localGets vs (k + 1) _ (fun i hi => ?_) ?_
    · rw [Locals.get_values, show k + 1 + i = k + (i + 1) by omega]
      exact hget (i + 1) (by simp; omega)
    · simpa using h

/-- The entry of a function whose code takes the call depth, at position `e`: it calls the code
at `idx` with depth 0 and its own arguments, and so computes the function's meaning, with a trap
allowed. -/
theorem entry_correct {m : Module} (hm : Runtime m) {g : Sig} {idx typeIdx e : Nat}
    {F : Env g.params → g.result.denote} {pf : List Bool} {rf : Bool} {A : Env g.params → Nat}
    {Fi : Env g.params → Bool} {D : UInt64 → Prop} (hF : FunSpec m g idx F pf rf A Fi D)
    (hd : g.depth = true) (hD : D 0)
    (he : m.funcs[e]? = some (entryFunction g.params g.result idx typeIdx)) :
    @ImplementsA _ _ (Env.represent g.params g.modes) (Ty.represent g.result) true m e F
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  intro host store heap ws args hAt _ hRep hSep hCap
  have hLength : ws.length = widthSum g.params := hRep.length
  have hNum : (entryFunction g.params g.result idx typeIdx).numParams = widthSum g.params := by
    simp only [entryFunction, Function.numParams, flatMap_types_length]
  apply Runs.of_wp_entry_for (f := entryFunction g.params g.result idx typeIdx)
    (by rw [hm.imports, List.length_nil, Nat.sub_zero]; exact he) (hImp := by simp [hm.imports])
  rw [List.take_of_length_le (by rw [hNum, List.length_reverse, hLength]), List.reverse_reverse]
  have hRun := (FunSpec.runs hF hm host hAt hRep hSep hCap (d := 0) (fun _ => hD) []).of_imp
    (a' := true) fun _ => rfl
  simp only [hd, ↓reduceIte] at hRun
  simp only [entryFunction, List.append_assoc, List.cons_append, List.nil_append,
    wp_constI64_cons, List.range_eq_range', flatMap_types_length, ← hLength]
  refine wp_localGets ws 0 _ (fun i hi => by simp [Function.toLocals, hi]) ?_
  refine wp_call_runs hRun (TrapOK.of_msg fun _ => Iff.rfl) fun st' vs hPost => ?_
  obtain ⟨out, rfl, heap', hAt', hOwned, hCaps, hRegions, _⟩ := hPost
  rw [wp_nil]
  have hOut : out.length = g.result.width := by
    have := hOwned.length; rwa [List.length_reverse] at this
  have hTake : out.take g.result.types.length = out :=
    List.take_of_length_le (by rw [Ty.types_length, hOut])
  have hDrop : ws.reverse.drop (List.flatMap Ty.types g.params).length = [] :=
    List.drop_of_length_le (by rw [List.length_reverse, flatMap_types_length, hLength])
  dsimp only [Function.numParams]
  rw [List.append_nil, hTake, hDrop, List.append_nil]
  exact ⟨heap', hAt', hOwned, hCaps, hRegions, trivial⟩

/-- The potential of a call's paid owned arguments is at most their credits. -/
theorem Env.argPot_le_paidCredit {heap : Heap} {store : Store Unit} {g : Sig} {pf : List Bool}
    {ws : List Value} {x : Env g.params} (hRep : Env.Rep g.mode heap store ws x) :
    Env.argPot store (g.paidSel pf) ws x ≤ Env.credit (g.paidSel pf) x :=
  Env.argPot_le_credit g.mode _ ws x hRep fun i h => by
    simp only [Sig.paidSel, Bool.and_eq_true, beq_iff_eq] at h; exact h.2

/-- `ImplementsB` for a function whose code takes no call depth, with the credits of its paid
owned parameters added to its bound. -/
theorem FunSpec.implementsB {m : Module} {g : Sig} {idx : Nat}
    {F : Env g.params → g.result.denote} {pf : List Bool} {rf : Bool} {A : Env g.params → Nat}
    {Fi : Env g.params → Bool} {D : UInt64 → Prop} (hF : FunSpec m g idx F pf rf A Fi D)
    (hd : g.depth = false) :
    @ImplementsB _ _ (Env.represent g.params g.modes) (Ty.represent g.result) g.aborts m idx F
      (fun x => Env.credit (g.paidSel pf) x + A x) := by
  intro host store heap ws x hAt hRep hSep hCap
  have hle := Env.argPot_le_paidCredit (pf := pf) hRep
  refine ((hF.1 hd host store heap ws x trivial hAt hRep hSep hCap).of_imp fun h => ?_).mono
    fun final values ⟨heap', hAt', hOwned, hCaps, hRegions, hTop⟩ =>
      ⟨heap', hAt', hOwned, hCaps, hRegions, by have := hTop rfl; simp only at this ⊢; omega⟩
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h ⊢
  exact ⟨h.1, fun hw => h.2 (hw.mono (by omega))⟩

/-- A signature with no paid flags picks no parameter. -/
theorem Sig.paidSel_none {g : Sig} {pf : List Bool} (h : (pf.all fun b => !b) = true) (i : Nat) :
    g.paidSel pf i = false := by
  simp only [Sig.paidSel, paidAt, Bool.and_eq_false_iff]
  left
  rw [List.getD_eq_getElem?_getD]
  cases hi : pf[i]? with
  | none => rfl
  | some b =>
    have := List.all_eq_true.mp h b (List.mem_of_getElem? hi)
    simpa using this

/-- `FunSpec.implementsB` for a function without paid parameters: its bound alone. -/
theorem FunSpec.implementsB_unpaid {m : Module} {g : Sig} {idx : Nat}
    {F : Env g.params → g.result.denote} {pf : List Bool} {rf : Bool} {A : Env g.params → Nat}
    {Fi : Env g.params → Bool} {D : UInt64 → Prop} (hF : FunSpec m g idx F pf rf A Fi D)
    (hd : g.depth = false) (hpf : (pf.all fun b => !b) = true) :
    @ImplementsB _ _ (Env.represent g.params g.modes) (Ty.represent g.result) g.aborts m idx F
      A := by
  have h := hF.implementsB hd
  simp only [Env.credit_eq_zero (Sig.paidSel_none hpf), Nat.zero_add] at h
  exact h

/-- The entry of a function whose code takes the call depth, at position `e`, computes the function
without a trap when its calls find their frames, as `Fi` states, and `top` can rise by the credits
of its paid owned parameters plus its bound `A` within the cap, and it raises `top` by at most that
sum. -/
theorem entry_trapFree {m : Module} (hm : Runtime m) {g : Sig} {idx typeIdx e : Nat}
    {F : Env g.params → g.result.denote} {pf : List Bool} {rf : Bool} {A : Env g.params → Nat}
    {Fi : Env g.params → Bool} {D : UInt64 → Prop} (hF : FunSpec m g idx F pf rf A Fi D)
    (hd : g.depth = true) (hD : D 0)
    (he : m.funcs[e]? = some (entryFunction g.params g.result idx typeIdx)) :
    @ImplementsA _ _ (Env.represent g.params g.modes) (Ty.represent g.result) false m e F
      (fun x heap store => Fi x = true ∧
        heap.Within store m (Env.credit (g.paidSel pf) x + A x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + (Env.credit (g.paidSel pf) x + A x)) := by
  intro host store heap ws args hAt hPre hRep hSep hCap
  have hLength : ws.length = widthSum g.params := hRep.length
  have hNum : (entryFunction g.params g.result idx typeIdx).numParams = widthSum g.params := by
    simp only [entryFunction, Function.numParams, flatMap_types_length]
  apply Runs.of_wp_entry_for (f := entryFunction g.params g.result idx typeIdx)
    (by rw [hm.imports, List.length_nil, Nat.sub_zero]; exact he) (hImp := by simp [hm.imports])
  rw [List.take_of_length_le (by rw [hNum, List.length_reverse, hLength]), List.reverse_reverse]
  have hle := Env.argPot_le_paidCredit (pf := pf) hRep
  have hFlag : ((g.depth && !Fi args) ||
      ((g.aborts || g.depth) &&
        !decide (heap.Within store m (Env.argPot store (g.paidSel pf) ws args + A args)))) =
      false := by
    have hW : heap.Within store m (Env.argPot store (g.paidSel pf) ws args + A args) :=
      hPre.2.mono (by omega)
    simp [hd, hPre.1, hW]
  have hRun := FunSpec.runs hF hm host hAt hRep hSep hCap (d := 0) (fun _ => hD) []
  rw [hFlag] at hRun
  simp only [hd, ↓reduceIte] at hRun
  simp only [entryFunction, List.append_assoc, List.cons_append, List.nil_append,
    wp_constI64_cons, List.range_eq_range', flatMap_types_length, ← hLength]
  refine wp_localGets ws 0 _ (fun i hi => by simp [Function.toLocals, hi]) ?_
  refine wp_call_runs hRun (TrapOK.of_msg fun _ => Iff.rfl) fun st' vs hPost => ?_
  obtain ⟨out, rfl, heap', hAt', hOwned, hCaps, hRegions, hTop⟩ := hPost
  rw [wp_nil]
  have hOut : out.length = g.result.width := by
    have := hOwned.length; rwa [List.length_reverse] at this
  have hTake : out.take g.result.types.length = out :=
    List.take_of_length_le (by rw [Ty.types_length, hOut])
  have hDrop : ws.reverse.drop (List.flatMap Ty.types g.params).length = [] :=
    List.drop_of_length_le (by rw [List.length_reverse, flatMap_types_length, hLength])
  dsimp only [Function.numParams]
  rw [List.append_nil, hTake, hDrop, List.append_nil]
  exact ⟨heap', hAt', hOwned, hCaps, hRegions, by have := hTop (by simp [hd, hPre.1]); omega⟩

/-- The correctness theorem for a program without recursion, whose functions' meanings
`Prog.funs` gives. -/
theorem Prog.correct_funs {S : List Sig} (prog : Prog S) (h : prog.recFree = true) :
    Calls (compile prog) prog.funs prog.flags (prog.boundsAt prog.funs) (prog.fitsAt prog.funs) :=
  prog.correct _ (prog.meaning_funs h)

/-- The correctness theorem at the exported entry of a function whose code takes the call depth,
the `j`-th such function: the entry computes the function that `funs` gives it, and it may trap
at `unreachable`. -/
theorem Prog.correct_entry {S : List Sig} (prog : Prog S) (funs : Funs S)
    (h : prog.Meaning funs) {g : Sig} (f : FVar S g) (hd : g.depth = true) {j : Nat}
    (hj : prog.depthFuns[j]? = some (f.callIndex, g.params, g.result)) :
    @ImplementsA _ _ (Env.represent g.params g.modes) (Ty.represent g.result) true (compile prog)
      (2 + S.length + j) (funs.get f) (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  entry_correct (compile_runtime prog) (prog.correct funs h f 0) hd rfl (compile_entries prog hj)

/-- `Prog.correct_entry` for a program with tables and wrappers. -/
theorem Prog.correct_entryWith {S : List Sig} (prog : Prog S) (funs : Funs S)
    (h : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) {g : Sig} (f : FVar S g) (hd : g.depth = true)
    {j : Nat} (hj : prog.depthFuns[j]? = some (f.callIndex, g.params, g.result)) :
    @ImplementsA _ _ (Env.represent g.params g.modes) (Ty.represent g.result) true
      (compileWith prog tables wrappers) (2 + S.length + j) (funs.get f) (fun _ _ _ => True)
      (fun _ _ _ _ _ => True) :=
  entry_correct (compileWith_runtime prog tables wrappers)
    (prog.correctWith funs h tables wrappers f 0) hd rfl
    (compileWith_entries prog tables wrappers hj)

/-- `entry_trapFree` at the exported entry of the `j`-th function whose code takes the call depth,
of a program with tables and wrappers: with 1000 frames, which the entry's depth 0 leaves, and the
credits of the function's paid owned parameters. -/
theorem Prog.entry_trapFreeWith {S : List Sig} (prog : Prog S) (funs : Funs S)
    (h : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) {g : Sig} (f : FVar S g) (hd : g.depth = true)
    {j : Nat} (hj : prog.depthFuns[j]? = some (f.callIndex, g.params, g.result)) :
    @ImplementsA _ _ (Env.represent g.params g.modes) (Ty.represent g.result) false
      (compileWith prog tables wrappers) (2 + S.length + j) (funs.get f)
      (fun x heap store => (prog.fitsAt funs (framesAt 0)).get f x = true ∧
        heap.Within store (compileWith prog tables wrappers)
          (Env.credit (g.paidSel (prog.flags.params f)) x +
            (prog.boundsAt funs (framesAt 0)).get f x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat +
          (Env.credit (g.paidSel (prog.flags.params f)) x +
            (prog.boundsAt funs (framesAt 0)).get f x)) :=
  entry_trapFree (compileWith_runtime prog tables wrappers)
    (prog.correctWith funs h tables wrappers f 0) hd rfl
    (compileWith_entries prog tables wrappers hj)

/-- `Prog.entry_trapFreeWith` for a function without paid parameters: its bound alone. -/
theorem Prog.entry_trapFreeWith_unpaid {S : List Sig} (prog : Prog S) (funs : Funs S)
    (h : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) {g : Sig} (f : FVar S g) (hd : g.depth = true)
    {j : Nat} (hj : prog.depthFuns[j]? = some (f.callIndex, g.params, g.result))
    (hpf : ((prog.flags.params f).all fun b => !b) = true) :
    @ImplementsA _ _ (Env.represent g.params g.modes) (Ty.represent g.result) false
      (compileWith prog tables wrappers) (2 + S.length + j) (funs.get f)
      (fun x heap store => (prog.fitsAt funs (framesAt 0)).get f x = true ∧
        heap.Within store (compileWith prog tables wrappers)
          ((prog.boundsAt funs (framesAt 0)).get f x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + (prog.boundsAt funs (framesAt 0)).get f x) := by
  have h0 := prog.entry_trapFreeWith funs h tables wrappers f hd hj
  simp only [Env.credit_eq_zero (Sig.paidSel_none hpf), Nat.zero_add] at h0
  exact h0

/-- A function's theorem for the verified compiler's representation gives the theorem for a Lean
function `F` on types whose representations agree with it: each argument `y` is represented as
`g y` is, and the result of `f` at `g y` represents `F y`. -/
theorem ImplementsA.transfer {α β γ δ : Type} {_ : Represent α} [Represent β] {_ : Represent γ}
    [Represent δ] {aborts : Bool} {m : Module} {entry : Nat} {f : α → γ}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA aborts m entry f Pre Post) (g : β → α) (F : β → δ)
    (hArgs : ∀ heap store vs y, Represent.borrowed heap store vs y →
      Represent.borrowed heap store vs (g y))
    (hSep : ∀ heap store vs y, Represent.borrowed heap store vs y →
      Separate store (Represent.moves store vs y) (Represent.reads store vs y) →
        Separate store (Represent.moves store vs (g y)) (Represent.reads store vs (g y)))
    (hMoves : ∀ heap store vs y, Represent.borrowed heap store vs y →
      Represent.moves store vs (g y) = Represent.moves store vs y)
    (hResult : ∀ heap store vs y, Represent.owned heap store vs (f (g y)) →
      Represent.owned heap store vs (F y))
    (hBlocks : ∀ store vs y,
      Represent.blocks store vs (F y) = Represent.blocks store vs (f (g y))) :
    ImplementsA aborts m entry F (fun y => Pre (g y)) (fun y => Post (g y)) := by
  intro env store heap vs y hAt hPre hY hSep' hCap
  exact (h env store heap vs (g y) hAt hPre (hArgs _ _ _ _ hY) (hSep _ _ _ _ hY hSep')
    hCap).mono fun final values ⟨heap', hAt', hOwned, hCaps, hRegions, hPost⟩ =>
      ⟨heap', hAt', hResult _ _ _ _ hOwned, hCaps, fun r hr hpos hA => by
        obtain ⟨hb, hreg, hout⟩ := hRegions r hr hpos (by rw [hMoves _ _ _ _ hY]; exact hA)
        refine ⟨hb, hreg, ?_⟩
        simp only [Represent.outside, hBlocks]
        exact hout, hPost⟩

/-- Two `Represent` instances agree along `φ`: a value `y` of the first type is represented as
`φ y` is in the second. -/
structure Agree {α β : Type} (instA : Represent α) (instB : Represent β) (φ : α → β) : Prop where
  borrowed : ∀ heap store vs y, @Represent.borrowed _ instA heap store vs y ↔
    @Represent.borrowed _ instB heap store vs (φ y)
  owned : ∀ heap store vs y, @Represent.owned _ instA heap store vs y ↔
    @Represent.owned _ instB heap store vs (φ y)
  width : ∀ y, @Represent.width _ instA y = @Represent.width _ instB (φ y)
  blocks : ∀ store vs y,
    @Represent.blocks _ instA store vs y = @Represent.blocks _ instB store vs (φ y)
  reads : ∀ store vs y,
    @Represent.reads _ instA store vs y = @Represent.reads _ instB store vs (φ y)
  moves : ∀ store vs y,
    @Represent.moves _ instA store vs y = @Represent.moves _ instB store vs (φ y)

/-- An instance agrees with itself along the identity. -/
theorem Agree.refl {α : Type} (inst : Represent α) : Agree inst inst id :=
  ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- Instances from `Scalar` agree along a map that keeps each value's words. -/
theorem Agree.scalar {α β : Type} [Scalar α] [Scalar β] (φ : α → β)
    (h : ∀ x, Scalar.values x = Scalar.values (φ x)) :
    Agree (instRepresentOfScalar (α := α)) (instRepresentOfScalar (α := β)) φ where
  borrowed _ _ vs y := by show vs = _ ↔ vs = _; rw [h]
  owned _ _ vs y := by show vs = _ ↔ vs = _; rw [h]
  width y := by show List.length _ = List.length _; rw [h]
  blocks _ _ _ := rfl
  reads _ _ _ := rfl
  moves _ _ _ := rfl

/-- Pairs agree componentwise. -/
theorem Agree.prod {α β γ δ : Type} {ia : Represent α} {ib : Represent β} {ja : Represent γ}
    {jb : Represent δ} {φ : α → β} {ψ : γ → δ} (ha : Agree ia ib φ) (hb : Agree ja jb ψ) :
    Agree (@instRepresentProd _ _ ia ja) (@instRepresentProd _ _ ib jb)
      (fun p => (φ p.1, ψ p.2)) where
  borrowed heap store vs p := by
    show (∃ first second, vs = first ++ second ∧ _ ∧ _) ↔
      (∃ first second, vs = first ++ second ∧ _ ∧ _)
    simp only [ha.borrowed, hb.borrowed]
  owned heap store vs p := by
    show (∃ first second, vs = first ++ second ∧ _ ∧ _ ∧ _) ↔
      (∃ first second, vs = first ++ second ∧ _ ∧ _ ∧ _)
    simp only [ha.owned, hb.owned, Represent.outside, ha.blocks, hb.blocks]
  width p := by
    show @Represent.width _ ia p.1 + @Represent.width _ ja p.2 = _ + _
    rw [ha.width, hb.width]
  blocks store vs p := by
    show @Represent.blocks _ ia store _ p.1 ++ @Represent.blocks _ ja store _ p.2 = _ ++ _
    rw [ha.width, ha.blocks, hb.blocks]
  reads store vs p := by
    show @Represent.reads _ ia store _ p.1 ++ @Represent.reads _ ja store _ p.2 = _ ++ _
    rw [ha.width, ha.reads, hb.reads]
  moves store vs p := by
    show @Represent.moves _ ia store _ p.1 ++ @Represent.moves _ ja store _ p.2 = _ ++ _
    rw [ha.width, ha.moves, hb.moves]

/-- A structure represented as its `Flat` tuple agrees along `φ ∘ Flat.flat` with whatever its
tuple agrees with along `φ`. -/
theorem Agree.flat {α β γ : Type} [Flat α β] {ib : Represent β} {ic : Represent γ} {φ : β → γ}
    (h : Agree ib ic φ) :
    Agree (@instRepresentOfFlat α β _ ib) ic (fun x => φ (Flat.flat x)) where
  borrowed heap store vs x := h.borrowed heap store vs (Flat.flat x)
  owned heap store vs x := h.owned heap store vs (Flat.flat x)
  width x := h.width (Flat.flat x)
  blocks store vs x := h.blocks store vs (Flat.flat x)
  reads store vs x := h.reads store vs (Flat.flat x)
  moves store vs x := h.moves store vs (Flat.flat x)

/-- The words of an array of a `Flat` type are the words of its elements' flattenings. -/
theorem flatWords_map {α β : Type} [Flat α β] [Scalar β] (e : Elem) (φ : α → e.denote)
    (hφ : ∀ x, (Scalar.values (Flat.flat x)).map Value.word = e.toWords (φ x)) (xs : Array α) :
    flatWords xs = e.words (xs.map φ) := by
  rw [Elem.words_eq, Array.toList_map, List.flatMap_map]
  show (xs.toList.flatMap fun x => (Scalar.values (Flat.flat x)).map Value.word).toArray = _
  rw [show (fun x => (Scalar.values (Flat.flat x)).map Value.word) = fun x => e.toWords (φ x) from
    funext hφ]

/-- An array of a `Flat` type agrees with the array of its elements' flattenings. -/
theorem Agree.flatArray {α β : Type} [Flat α β] [Scalar β] (e : Elem) (φ : α → e.denote)
    (hφ : ∀ x, (Scalar.values (Flat.flat x)).map Value.word = e.toWords (φ x)) :
    Agree (instRepresentArrayOfFlatOfScalar (α := α) (β := β)) e.arrayInst
      (fun xs => xs.map φ) where
  borrowed heap store vs xs := by
    rw [e.arrayInst_borrowed]
    show (∃ ptr, vs = [.i64 ptr] ∧ heap.Borrowed store ptr (flatWords xs)) ↔
      ∃ ptr, vs = [.i64 ptr] ∧ Mode.array .borrowed heap store ptr (e.words (xs.map φ))
    rw [flatWords_map e φ hφ]; rfl
  owned heap store vs xs := by
    rw [e.arrayInst_owned]
    show (∃ ptr, vs = [.i64 ptr] ∧ heap.Owned store ptr (flatWords xs)) ↔
      ∃ ptr, vs = [.i64 ptr] ∧ Mode.array .owned heap store ptr (e.words (xs.map φ))
    rw [flatWords_map e φ hφ]; rfl
  width xs := by rw [e.arrayInst_width]; rfl
  blocks store vs xs := by rw [e.arrayInst_blocks]; rfl
  reads store vs xs := by
    rw [e.arrayInst_reads]
    show (match vs with
      | [.i64 ptr] => [(ptr.toNat, 8 * ((flatWords xs).size + 1))]
      | _ => []) = _
    rw [flatWords_map e φ hφ]; rfl
  moves store vs xs := by rw [e.arrayInst_moves]; rfl

/-- An owned array of a `Flat` type agrees with the owned array of its elements' flattenings. -/
theorem Agree.flatMoved {α β : Type} [Flat α β] [Scalar β] (e : Elem) (φ : α → e.denote)
    (hφ : ∀ x, (Scalar.values (Flat.flat x)).map Value.word = e.toWords (φ x)) :
    Agree (instRepresentMovedArrayOfFlatOfScalar (α := α) (β := β)) e.movedInst
      (fun xs => Moved.mk (xs.val.map φ)) where
  borrowed heap store vs xs := by
    rw [e.movedInst_borrowed]
    show (∃ ptr, vs = [.i64 ptr] ∧ heap.Owned store ptr (flatWords xs.val)) ↔
      ∃ ptr, vs = [.i64 ptr] ∧ Mode.array .owned heap store ptr (e.words (xs.val.map φ))
    rw [flatWords_map e φ hφ]; rfl
  owned heap store vs xs := by
    show (∃ ptr, vs = [.i64 ptr] ∧ heap.Owned store ptr (flatWords xs.val)) ↔ _
    rw [show @Represent.owned _ e.movedInst heap store vs (Moved.mk (xs.val.map φ)) ↔
      (Ty.array e).Rep .owned heap store vs (xs.val.map φ) by cases e <;> exact Iff.rfl]
    show _ ↔ ∃ ptr, vs = [.i64 ptr] ∧ Mode.array .owned heap store ptr (e.words (xs.val.map φ))
    rw [flatWords_map e φ hφ]; rfl
  width xs := by rw [e.movedInst_width]; rfl
  blocks store vs xs := by
    show (match vs with | [.i64 ptr] => [block store ptr] | _ => []) = _
    cases e <;> rfl
  reads store vs xs := by rw [e.movedInst_reads]; rfl
  moves store vs xs := by rw [e.movedInst_moves]; rfl

/-- `transfer` for a Lean function `F` whose result `F y` the compiled function gives as `r (F y)`,
from the agreement of the instances of the arguments along `g` and of the result along `r`. -/
theorem ImplementsA.transferAgree {α β γ δ : Type} {ia : Represent α} {ib : Represent β}
    {ic : Represent γ} {id : Represent δ} {aborts : Bool} {m : Module} {entry : Nat}
    {f : α → γ} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA aborts m entry f Pre Post)
    (g : β → α) (r : δ → γ) (F : β → δ) (hF : ∀ y, f (g y) = r (F y)) (hArgs : Agree ib ia g)
    (hResult : Agree id ic r) :
    ImplementsA aborts m entry F (fun y => Pre (g y)) (fun y => Post (g y)) :=
  ImplementsA.transfer h g F (fun _ _ _ _ hy => (hArgs.borrowed _ _ _ _).mp hy)
    (fun _ _ _ _ _ hs => by rw [← hArgs.moves, ← hArgs.reads]; exact hs)
    (fun _ _ _ _ _ => (hArgs.moves _ _ _).symm)
    (fun _ _ _ y hy => (hResult.owned _ _ _ _).mpr (hF y ▸ hy))
    (fun _ _ y => by rw [hF]; exact hResult.blocks _ _ _)

/-- A function's theorem for the verified compiler's representation gives the theorem for Lean
types whose representations agree with it. -/
theorem ImplementsA.comap {α β γ δ : Type} [Represent α] [Represent β] [Represent γ]
    [Represent δ] {aborts : Bool} {m : Module} {entry : Nat} {f : α → γ}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA aborts m entry f Pre Post) (g : β → α) (k : γ → δ)
    (hArgs : ∀ heap store vs y, Represent.borrowed heap store vs y →
      Represent.borrowed heap store vs (g y))
    (hSep : ∀ heap store vs y, Represent.borrowed heap store vs y →
      Separate store (Represent.moves store vs y) (Represent.reads store vs y) →
        Separate store (Represent.moves store vs (g y)) (Represent.reads store vs (g y)))
    (hMoves : ∀ heap store vs y, Represent.borrowed heap store vs y →
      Represent.moves store vs (g y) = Represent.moves store vs y)
    (hResult : ∀ heap store vs z, Represent.owned heap store vs z →
      Represent.owned heap store vs (k z))
    (hBlocks : ∀ store vs z, Represent.blocks store vs (k z) = Represent.blocks store vs z) :
    ImplementsA aborts m entry (k ∘ f ∘ g) (fun y => Pre (g y)) (fun y => Post (g y)) :=
  ImplementsA.transfer h g (k ∘ f ∘ g) hArgs hSep hMoves (fun _ _ _ _ hz => hResult _ _ _ _ hz)
    (fun _ _ _ => hBlocks _ _ _)

/-- A function's theorem in the form of Lean's instances: for the Lean tuple of its arguments and
its result type, with the instances Lean synthesizes for them. -/
theorem ImplementsA.lean {ps : List Ty} {ms : List Mode} {r : Ty} {aborts : Bool} {m : Module}
    {entry : Nat} {f : Env ps → r.denote} {Pre : Env ps → Heap → Store Unit → Prop}
    {Post : Env ps → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : @ImplementsA _ _ (Env.represent ps ms) (Ty.represent r) aborts m entry f Pre Post) :
    @ImplementsA _ _ (argsInst ps ms) r.leanInst aborts m entry
      (fun y => f (Env.ofArgs ps ms y)) (fun y => Pre (Env.ofArgs ps ms y))
      (fun y => Post (Env.ofArgs ps ms y)) :=
  @ImplementsA.comap _ _ _ _ (Env.represent ps ms) (argsInst ps ms) (Ty.represent r) r.leanInst
    aborts m entry f Pre Post h (Env.ofArgs ps ms) id
    (fun _ _ _ _ hy => (argsInst_borrowed ps ms).mp hy)
    (fun _ _ _ _ hy hS => by
      have hl := ((argsInst_borrowed ps ms).mp hy).length
      rw [argsInst_moves ps ms hl, argsInst_reads ps ms hl] at hS
      exact hS)
    (fun _ _ _ _ hy => (argsInst_moves ps ms ((argsInst_borrowed ps ms).mp hy).length).symm)
    (fun _ _ _ _ hz => r.leanInst_owned.mpr hz) (fun _ _ _ => r.leanInst_blocks)

/-- `ImplementsA` for an entry that reads constant tables: from a heap and store in which each
table `(p, xs)` of `tables` is a borrowed array at `p` that lies apart from the blocks that the
arguments move.  The other premises and the conclusion are those of `ImplementsA`. -/
def ImplementsTables {α β : Type} [Represent α] [Represent β] (aborts : Bool) (m : Module)
    (entry : Nat) (f : α → β) (tables : List (UInt64 × Array UInt64))
    (Pre : α → Heap → Store Unit → Prop)
    (Post : α → Heap → Store Unit → Heap → Store Unit → Prop) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (params : List Value) (x : α),
    heap.At store → Pre x heap store →
    (∀ t ∈ tables, heap.Borrowed store t.1 t.2 ∧
      Apart store (Represent.moves store params x) (t.1.toNat, 8 * (t.2.size + 1))) →
    Represent.borrowed heap store params x →
    Separate store (Represent.moves store params x) (Represent.reads store params x) →
    store.memoryCap m 0 ≤ 65535 →
    Runs aborts env m entry store params.reverse fun final values =>
      ∃ heap' : Heap, heap'.At final ∧ Represent.owned heap' final values.reverse (f x) ∧
        final.memoryCaps = store.memoryCaps ∧
        (∀ r, heap.Region r → 0 < r.2 → Apart store (Represent.moves store params x) r →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r ∧ Represent.outside final values.reverse (f x) r) ∧
        Post x heap store heap' final

/-- The context of a wrapper's callee: the tables `ks` of `tables`, then the wrapper's own
arguments. -/
def Env.withTables (tables : List (Array UInt64)) {Γ : List Ty} :
    (ks : List (Fin tables.length)) → Env Γ → Env (List.replicate ks.length (.array .word) ++ Γ)
  | [], env => env
  | k :: ks, env => .cons (t := .array .word) tables[k] (Env.withTables tables ks env)

theorem paramMode_tables (n : Nat) (ps : List Ty) (ms : List Mode) (i : Nat) :
    paramMode (List.replicate n (.array .word) ++ ps) ms (i + n) = paramMode ps (ms.drop n) i := by
  induction n generalizing ms with
  | zero => rfl
  | succ n ih =>
    rw [show i + (n + 1) = (i + n) + 1 by omega]
    simp only [paramMode, List.replicate_succ, List.cons_append, paramModes, List.getD_cons_succ]
    have := ih ms.tail
    simp only [paramMode] at this
    rw [this, List.drop_tail]

theorem paramMode_tables_lt (n : Nat) (ps : List Ty) (ms : List Mode)
    (hB : (ms.take n).all (· == .borrowed) = true) (i : Nat) (hi : i < n) :
    paramMode (List.replicate n (.array .word) ++ ps) ms i = .borrowed := by
  induction n generalizing ms i with
  | zero => omega
  | succ n ih =>
    simp only [paramMode, List.replicate_succ, List.cons_append, paramModes]
    cases ms with
    | nil =>
      cases i with
      | zero => rfl
      | succ i =>
        simp only [List.getD_cons_succ, List.tail_nil]
        have := ih [] (by simp) i (by omega)
        simpa [paramMode] using this
    | cons m ms =>
      simp only [List.take_succ_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hB
      cases i with
      | zero => simp [Ty.paramMode, hB.1]
      | succ i =>
        simp only [List.getD_cons_succ, List.tail_cons]
        have := ih ms hB.2 i (by omega)
        simpa [paramMode] using this

theorem Env.withTables_rep {tables : List (Array UInt64)} {Γ : List Ty} :
    (ks : List (Fin tables.length)) → {modes : Nat → Mode} →
    (∀ i < ks.length, modes i = .borrowed) → {heap : Heap} → {store : Store Unit} →
    {ws : List Value} → {env : Env Γ} →
    (∀ k ∈ ks, heap.Borrowed store (tableAddr tables k.val) tables[k]) →
    Env.Rep (fun i => modes (i + ks.length)) heap store ws env →
    Env.Rep modes heap store
      ((ks.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws)
      (Env.withTables tables ks env)
  | [], _, _, _, _, _, _, _, h => h
  | k :: ks, modes, hB, heap, store, ws, env, hT, h => by
    refine ⟨[.i64 (tableAddr tables k.val)],
      (ks.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws,
      rfl, ⟨_, rfl, ?_⟩, ?_⟩
    · rw [hB 0 (by simp)]
      exact hT k (by simp)
    · exact Env.withTables_rep ks (modes := fun i => modes (i + 1))
        (fun i hi => hB (i + 1) (by simp; omega)) (fun k' hk => hT k' (by simp [hk])) h

theorem Env.withTables_moves {tables : List (Array UInt64)} {Γ : List Ty} :
    (ks : List (Fin tables.length)) → {modes : Nat → Mode} →
    (∀ i < ks.length, modes i = .borrowed) → {ws : List Value} → {env : Env Γ} →
    Env.moves modes ((ks.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws)
        (Env.withTables tables ks env) =
      Env.moves (fun i => modes (i + ks.length)) ws env
  | [], _, _, _, _ => rfl
  | k :: ks, modes, hB, ws, env => by
    simp only [List.map_cons, List.cons_append]
    rw [show (Value.i64 (tableAddr tables k.val) ::
        ((ks.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws)) =
        [Value.i64 (tableAddr tables k.val)] ++
          ((ks.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws) from rfl]
    show Env.moves modes ([Value.i64 (tableAddr tables k.val)] ++
        ((ks.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws))
        (.cons (t := .array .word) tables[k] (Env.withTables tables ks env)) = _
    rw [Env.moves_cons rfl, hB 0 (by simp), List.nil_append]
    exact Env.withTables_moves ks (modes := fun i => modes (i + 1))
      (fun i hi => hB (i + 1) (by simp; omega))

theorem Env.withTables_reads {tables : List (Array UInt64)} {Γ : List Ty} :
    (ks : List (Fin tables.length)) → {modes : Nat → Mode} →
    (∀ i < ks.length, modes i = .borrowed) → {ws : List Value} → {env : Env Γ} →
    Env.reads modes ((ks.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws)
        (Env.withTables tables ks env) =
      (ks.map fun k : Fin tables.length =>
          ((tableAddr tables k.val).toNat, 8 * (tables[k].size + 1))) ++
        Env.reads (fun i => modes (i + ks.length)) ws env
  | [], _, _, _, _ => rfl
  | k :: ks, modes, hB, ws, env => by
    simp only [List.map_cons, List.cons_append]
    rw [show (Value.i64 (tableAddr tables k.val) ::
        ((ks.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws)) =
        [Value.i64 (tableAddr tables k.val)] ++
          ((ks.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws) from rfl]
    show Env.reads modes ([Value.i64 (tableAddr tables k.val)] ++
        ((ks.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws))
        (.cons (t := .array .word) tables[k] (Env.withTables tables ks env)) = _
    rw [Env.reads_cons rfl, hB 0 (by simp)]
    rw [Env.withTables_reads ks (modes := fun i => modes (i + 1))
      (fun i hi => hB (i + 1) (by simp; omega))]
    rfl

/-- `i64.const` of each word of `addrs`, in order, pushes the words. -/
theorem wp_constI64s {m : Module} {host : HostEnv Unit} {Q : Assertion Unit} {store : Store Unit}
    {rest : Program} : (addrs : List UInt64) → (s : Locals) →
    wp m rest Q store { s with values := (addrs.map Value.i64).reverse ++ s.values } host →
    wp m (addrs.map Instruction.constI64 ++ rest) Q store s host
  | [], s, h => by simpa using h
  | a :: as, s, h => by
    simp only [List.map_cons, List.cons_append, wp_constI64_cons]
    refine wp_constI64s as _ ?_
    simpa using h

/-- The signature of a wrapper's callee. -/
def Wrapper.sig {S : List Sig} {T : Nat} (w : Wrapper S T) : Sig :=
  ⟨List.replicate w.tables.length (.array .word) ++ w.params, w.result, w.aborts, w.modes, w.depth⟩

/-- The allocation bound of a wrapper: its callee's at the tables and the wrapper's arguments, with
the credits of the callee's paid owned parameters. -/
def Wrapper.bound {S : List Sig} (tables : List (Array UInt64)) (w : Wrapper S tables.length)
    (flags : Flags S) (bounds : Bounds S) (args : Env w.params) : Nat :=
  Env.credit (w.sig.paidSel (flags.params w.callee)) (Env.withTables tables w.tables args) +
    bounds.get w.callee (Env.withTables tables w.tables args)

/-- A run of the wrapper at position `e`: it calls its callee with the tables at their addresses
and its own arguments, and so computes the callee's meaning at the tables, from a store that holds
the tables apart from the blocks that the arguments move.  It traps only where the callee may:
when the callee's code takes the call depth, or when it may allocate and `top` cannot rise by the
wrapper's bound within the cap.  Otherwise it raises `top` by at most the bound. -/
theorem wrapper_runs {m : Module} (hm : Runtime m) {S : List Sig}
    {tables : List (Array UInt64)} (w : Wrapper S tables.length) {funs : Funs S}
    {flags : Flags S} {bounds : Nat → Bounds S} {fits : Nat → Fits S}
    (hCalls : Calls m funs flags bounds fits) {e : Nat}
    (he : m.funcs[e]? = some (wrapperFunction (w.tables.map fun k => tableAddr tables k.val)
      w.params w.result w.depth w.callee.callIndex e))
    (host : HostEnv Unit) {store : Store Unit} {heap : Heap} {ws : List Value}
    {args : Env w.params} (hAt : heap.At store)
    (hTables : ∀ t ∈ w.tables.map fun k => (tableAddr tables k.val, tables[k]),
      heap.Borrowed store t.1 t.2 ∧
        Apart store (Env.moves (paramMode w.params (w.modes.drop w.tables.length)) ws args)
          (t.1.toNat, 8 * (t.2.size + 1)))
    (hRep : Env.Rep (paramMode w.params (w.modes.drop w.tables.length)) heap store ws args)
    (hSep : Separate store (Env.moves (paramMode w.params (w.modes.drop w.tables.length)) ws args)
      (Env.reads (paramMode w.params (w.modes.drop w.tables.length)) ws args))
    (hCap : store.memoryCap m 0 ≤ 65535) :
    Runs ((w.depth && !(fits (framesAt 0)).get w.callee (Env.withTables tables w.tables args)) ||
        ((w.aborts || w.depth) &&
          !decide (heap.Within store m (Wrapper.bound tables w flags (bounds (framesAt 0)) args))))
      host m e store ws.reverse
      fun final values => ∃ heap' : Heap, heap'.At final ∧
        w.result.Rep .owned heap' final values.reverse
          (funs.get w.callee (Env.withTables tables w.tables args)) ∧
        final.memoryCaps = store.memoryCaps ∧
        (∀ r, heap.Region r → 0 < r.2 →
          Apart store (Env.moves (paramMode w.params (w.modes.drop w.tables.length)) ws args) r →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
          heap'.Region r ∧
          ∀ b ∈ w.result.blocks final values.reverse
            (funs.get w.callee (Env.withTables tables w.tables args)), regionsDisjoint r b) ∧
        ((w.depth && !(fits (framesAt 0)).get w.callee (Env.withTables tables w.tables args)) =
            false →
          heap'.top.toNat ≤ heap.top.toNat + Wrapper.bound tables w flags (bounds (framesAt 0)) args) := by
  have hShift : (fun i => paramMode (List.replicate w.tables.length (.array .word) ++ w.params)
      w.modes (i + w.tables.length)) = paramMode w.params (w.modes.drop w.tables.length) :=
    funext fun i => paramMode_tables _ _ _ i
  have hB : ∀ i < w.tables.length,
      paramMode (List.replicate w.tables.length (.array .word) ++ w.params) w.modes i =
        .borrowed :=
    fun i hi => paramMode_tables_lt _ _ _ w.borrowed i hi
  have hT : ∀ k ∈ w.tables, heap.Borrowed store (tableAddr tables k.val) tables[k] := fun k hk =>
    (hTables _ (List.mem_map.mpr ⟨k, hk, rfl⟩)).1
  have hRep' := Env.withTables_rep w.tables hB hT (by rw [hShift]; exact hRep)
  have hMoves := Env.withTables_moves (tables := tables) w.tables hB (ws := ws) (env := args)
  have hReads := Env.withTables_reads (tables := tables) w.tables hB (ws := ws) (env := args)
  rw [hShift] at hMoves hReads
  have hSep' : Separate store
      (Env.moves (paramMode (List.replicate w.tables.length (.array .word) ++ w.params) w.modes)
        ((w.tables.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws)
        (Env.withTables tables w.tables args))
      (Env.reads (paramMode (List.replicate w.tables.length (.array .word) ++ w.params) w.modes)
        ((w.tables.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws)
        (Env.withTables tables w.tables args)) := by
    rw [hMoves, hReads]
    refine ⟨hSep.1, fun r hr => ?_⟩
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
      exact (hTables _ (List.mem_map.mpr ⟨k, hk, rfl⟩)).2
    · exact hSep.2 r hr
  have hLength : ws.length = widthSum w.params := hRep.length
  have hle := Env.argPot_le_paidCredit (g := w.sig) (pf := flags.params w.callee) hRep'
  have hRun := (FunSpec.runs (hCalls w.callee 0) hm host hAt hRep' hSep' hCap (d := 0)
    (fun _ => rfl) []).of_imp (a' := (w.depth &&
      !(fits (framesAt 0)).get w.callee (Env.withTables tables w.tables args)) ||
      ((w.aborts || w.depth) &&
        !decide (heap.Within store m (Wrapper.bound tables w flags (bounds (framesAt 0)) args))))
    fun h => by
      change ((w.depth && !(fits (framesAt 0)).get w.callee (Env.withTables tables w.tables args)) ||
        ((w.aborts || w.depth) && !decide (heap.Within store m
          (Env.argPot store (w.sig.paidSel (flags.params w.callee))
            ((w.tables.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws)
            (Env.withTables tables w.tables args) +
          (bounds (framesAt 0)).get w.callee (Env.withTables tables w.tables args))))) = true at h
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not] at h ⊢
      rcases h with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, fun hw => h2 (hw.mono (by
          simp only [Wrapper.bound]; exact Nat.add_le_add_right hle _))⟩
  have hNum : (wrapperFunction (w.tables.map fun k => tableAddr tables k.val) w.params w.result
      w.depth w.callee.callIndex e).numParams = widthSum w.params := by
    simp only [wrapperFunction, Function.numParams, flatMap_types_length]
  apply Runs.of_wp_entry_for (f := wrapperFunction (w.tables.map fun k => tableAddr tables k.val)
      w.params w.result w.depth w.callee.callIndex e)
    (by rw [hm.imports, List.length_nil, Nat.sub_zero]; exact he) (hImp := by simp [hm.imports])
  rw [List.take_of_length_le (by rw [hNum, List.length_reverse, hLength]), List.reverse_reverse]
  have hAddrs : (w.tables.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) =
      (w.tables.map fun k => tableAddr tables k.val).map Value.i64 := by
    simp only [List.map_map]; rfl
  rw [hAddrs] at hRun hle
  simp only [wrapperFunction, List.append_assoc, List.range_eq_range', flatMap_types_length,
    ← hLength]
  refine wp_constI64s _ _ ?_
  refine wp_localGets ws 0 _ (fun i hi => by simp [Function.toLocals, hi]) ?_
  have hStack : ws.reverse ++ ((((if w.depth then ([0] : List UInt64) else []) ++
        (w.tables.map fun k : Fin tables.length => tableAddr tables k.val)).map
          Value.i64).reverse ++
        []) =
      ((w.tables.map fun k : Fin tables.length => tableAddr tables k.val).map Value.i64 ++
        ws).reverse ++ ((if w.depth then [Value.i64 0] else []) ++ []) := by
    cases w.depth <;> simp [List.reverse_append]
  rw [← hStack] at hRun
  refine wp_call_runs hRun (TrapOK.of_msg fun _ => Iff.rfl) fun st' vs hPost => ?_
  obtain ⟨out, rfl, heap', hAt', hOwned, hCaps, hRegions, hTop⟩ := hPost
  rw [wp_nil]
  have hOut : out.length = w.result.width := by
    have := hOwned.length; rwa [List.length_reverse] at this
  have hTake : (out ++ []).take w.result.types.length = out := by
    rw [List.append_nil]; exact List.take_of_length_le (by rw [Ty.types_length, hOut])
  have hDrop : ws.reverse.drop (List.flatMap Ty.types w.params).length = [] :=
    List.drop_of_length_le (by rw [List.length_reverse, flatMap_types_length, hLength])
  dsimp only [Function.numParams]
  rw [hTake, hDrop, List.append_nil]
  exact ⟨heap', hAt', hOwned, hCaps, fun r hr hpos hA =>
    hRegions r hr hpos (by rw [← hAddrs]; exact hMoves ▸ hA), fun h =>
      (Nat.le_add_right _ _).trans ((hTop h).trans (by
        simp only [Wrapper.bound]
        rw [Nat.add_assoc]
        exact Nat.add_le_add_left (Nat.add_le_add_right hle _) _))⟩

/-- A wrapper at position `e` computes its callee's meaning at the tables, from a store that holds
the tables apart from the blocks that the arguments move.  It may trap where the callee may. -/
theorem wrapper_correct {m : Module} (hm : Runtime m) {S : List Sig}
    {tables : List (Array UInt64)} (w : Wrapper S tables.length) {funs : Funs S}
    {flags : Flags S} {bounds : Nat → Bounds S} {fits : Nat → Fits S}
    (hCalls : Calls m funs flags bounds fits) {e : Nat}
    (he : m.funcs[e]? = some (wrapperFunction (w.tables.map fun k => tableAddr tables k.val)
      w.params w.result w.depth w.callee.callIndex e)) :
    @ImplementsTables _ _ (Env.represent w.params (w.modes.drop w.tables.length))
      (Ty.represent w.result) (w.aborts || w.depth) m e
      (fun env => funs.get w.callee (Env.withTables tables w.tables env))
      (w.tables.map fun k => (tableAddr tables k.val, tables[k])) (fun _ _ _ => True)
      (fun _ _ _ _ _ => True) :=
  fun host _ _ _ _ hAt _ hTables hRep hSep hCap =>
    ((wrapper_runs hm w hCalls he host hAt hTables hRep hSep hCap).of_imp fun h => by
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
      rcases h with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inr h
      · simpa only [Bool.or_eq_true] using h).mono
      fun _ _ ⟨heap', hAt', hOwned, hCaps, hRegions, _⟩ =>
        ⟨heap', hAt', hOwned, hCaps, hRegions, trivial⟩

/-- A wrapper whose code takes no call depth computes its callee's meaning at the tables without
a trap when `top` can rise by its bound within the cap, and it raises `top` by at most the
bound. -/
theorem wrapper_trapFree {m : Module} (hm : Runtime m) {S : List Sig}
    {tables : List (Array UInt64)} (w : Wrapper S tables.length) {funs : Funs S}
    {flags : Flags S} {bounds : Nat → Bounds S} {fits : Nat → Fits S}
    (hCalls : Calls m funs flags bounds fits) {e : Nat}
    (he : m.funcs[e]? = some (wrapperFunction (w.tables.map fun k => tableAddr tables k.val)
      w.params w.result w.depth w.callee.callIndex e)) (hd : w.depth = false) :
    @ImplementsTables _ _ (Env.represent w.params (w.modes.drop w.tables.length))
      (Ty.represent w.result) false m e
      (fun env => funs.get w.callee (Env.withTables tables w.tables env))
      (w.tables.map fun k => (tableAddr tables k.val, tables[k]))
      (fun x heap store => heap.Within store m (Wrapper.bound tables w flags (bounds (framesAt 0)) x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + Wrapper.bound tables w flags (bounds (framesAt 0)) x) :=
  fun host _ _ _ _ hAt hW hTables hRep hSep hCap =>
    ((wrapper_runs hm w hCalls he host hAt hTables hRep hSep hCap).of_imp fun h => by
      simp [hd, hW] at h).mono fun _ _ ⟨heap', hAt', hOwned, hCaps, hRegions, hTop⟩ =>
        ⟨heap', hAt', hOwned, hCaps, hRegions, hTop (by simp [hd])⟩

/-- A wrapper that cannot trap and whose code takes no call depth computes its callee's meaning at
the tables, and it raises `top` by at most its bound. -/
theorem wrapper_noTrap {m : Module} (hm : Runtime m) {S : List Sig}
    {tables : List (Array UInt64)} (w : Wrapper S tables.length) {funs : Funs S}
    {flags : Flags S} {bounds : Nat → Bounds S} {fits : Nat → Fits S}
    (hCalls : Calls m funs flags bounds fits) {e : Nat}
    (he : m.funcs[e]? = some (wrapperFunction (w.tables.map fun k => tableAddr tables k.val)
      w.params w.result w.depth w.callee.callIndex e)) (ha : w.aborts = false)
    (hd : w.depth = false) :
    @ImplementsTables _ _ (Env.represent w.params (w.modes.drop w.tables.length))
      (Ty.represent w.result) false m e
      (fun env => funs.get w.callee (Env.withTables tables w.tables env))
      (w.tables.map fun k => (tableAddr tables k.val, tables[k])) (fun _ _ _ => True)
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + Wrapper.bound tables w flags (bounds (framesAt 0)) x) :=
  fun host _ _ _ _ hAt _ hTables hRep hSep hCap =>
    ((wrapper_runs hm w hCalls he host hAt hTables hRep hSep hCap).of_imp fun h => by
      simp [ha, hd] at h).mono fun _ _ ⟨heap', hAt', hOwned, hCaps, hRegions, hTop⟩ =>
        ⟨heap', hAt', hOwned, hCaps, hRegions, hTop (by simp [hd])⟩

/-- The wrapper theorem for the `j`-th wrapper of a program with tables. -/
theorem Prog.correct_wrapper {S : List Sig} (prog : Prog S) (funs : Funs S)
    (h : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) {j : Nat} {w : Wrapper S tables.length}
    (hj : wrappers[j]? = some w) :
    @ImplementsTables _ _ (Env.represent w.params (w.modes.drop w.tables.length))
      (Ty.represent w.result) (w.aborts || w.depth) (compileWith prog tables wrappers)
      (2 + S.length + prog.depthFuns.length + j)
      (fun env => funs.get w.callee (Env.withTables tables w.tables env))
      (w.tables.map fun k => (tableAddr tables k.val, tables[k])) (fun _ _ _ => True)
      (fun _ _ _ _ _ => True) :=
  wrapper_correct (compileWith_runtime prog tables wrappers) w
    (prog.correctWith funs h tables wrappers) (compileWith_wrappers prog tables wrappers hj)

/-- `wrapper_trapFree` for the `j`-th wrapper of a program with tables. -/
theorem Prog.wrapper_trapFree {S : List Sig} (prog : Prog S) (funs : Funs S)
    (h : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) {j : Nat} {w : Wrapper S tables.length}
    (hj : wrappers[j]? = some w) (hd : w.depth = false) :
    @ImplementsTables _ _ (Env.represent w.params (w.modes.drop w.tables.length))
      (Ty.represent w.result) false (compileWith prog tables wrappers)
      (2 + S.length + prog.depthFuns.length + j)
      (fun env => funs.get w.callee (Env.withTables tables w.tables env))
      (w.tables.map fun k => (tableAddr tables k.val, tables[k]))
      (fun x heap store => heap.Within store (compileWith prog tables wrappers)
        (Wrapper.bound tables w prog.flags (prog.boundsAt funs (framesAt 0)) x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + Wrapper.bound tables w prog.flags (prog.boundsAt funs (framesAt 0)) x) :=
  Verified.wrapper_trapFree (compileWith_runtime prog tables wrappers) w
    (prog.correctWith funs h tables wrappers) (compileWith_wrappers prog tables wrappers hj) hd

/-- `wrapper_noTrap` for the `j`-th wrapper of a program with tables. -/
theorem Prog.wrapper_noTrap {S : List Sig} (prog : Prog S) (funs : Funs S)
    (h : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) {j : Nat} {w : Wrapper S tables.length}
    (hj : wrappers[j]? = some w) (ha : w.aborts = false) (hd : w.depth = false) :
    @ImplementsTables _ _ (Env.represent w.params (w.modes.drop w.tables.length))
      (Ty.represent w.result) false (compileWith prog tables wrappers)
      (2 + S.length + prog.depthFuns.length + j)
      (fun env => funs.get w.callee (Env.withTables tables w.tables env))
      (w.tables.map fun k => (tableAddr tables k.val, tables[k])) (fun _ _ _ => True)
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + Wrapper.bound tables w prog.flags (prog.boundsAt funs (framesAt 0)) x) :=
  Verified.wrapper_noTrap (compileWith_runtime prog tables wrappers) w
    (prog.correctWith funs h tables wrappers) (compileWith_wrappers prog tables wrappers hj) ha hd

/-- `ImplementsTables` for a Lean function `F` on types whose representations agree with it, as
`ImplementsA.transfer` states for `ImplementsA`. -/
theorem ImplementsTables.transfer {α β γ δ : Type} {_ : Represent α} [Represent β]
    {_ : Represent γ} [Represent δ] {aborts : Bool} {m : Module} {entry : Nat} {f : α → γ}
    {tables : List (UInt64 × Array UInt64)} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsTables aborts m entry f tables Pre Post) (g : β → α) (F : β → δ)
    (hArgs : ∀ heap store vs y, Represent.borrowed heap store vs y →
      Represent.borrowed heap store vs (g y))
    (hSep : ∀ heap store vs y, Represent.borrowed heap store vs y →
      Separate store (Represent.moves store vs y) (Represent.reads store vs y) →
        Separate store (Represent.moves store vs (g y)) (Represent.reads store vs (g y)))
    (hMoves : ∀ heap store vs y, Represent.borrowed heap store vs y →
      Represent.moves store vs (g y) = Represent.moves store vs y)
    (hResult : ∀ heap store vs y, Represent.owned heap store vs (f (g y)) →
      Represent.owned heap store vs (F y))
    (hBlocks : ∀ store vs y,
      Represent.blocks store vs (F y) = Represent.blocks store vs (f (g y))) :
    ImplementsTables aborts m entry F tables (fun y => Pre (g y)) (fun y => Post (g y)) := by
  intro env store heap vs y hAt hPre hT hY hSep' hCap
  exact (h env store heap vs (g y) hAt hPre (fun t ht => by
      rw [hMoves _ _ _ _ hY]; exact hT t ht) (hArgs _ _ _ _ hY) (hSep _ _ _ _ hY hSep')
    hCap).mono fun final values ⟨heap', hAt', hOwned, hCaps, hRegions, hPost⟩ =>
      ⟨heap', hAt', hResult _ _ _ _ hOwned, hCaps, fun r hr hpos hA => by
        obtain ⟨hb, hreg, hout⟩ := hRegions r hr hpos (by rw [hMoves _ _ _ _ hY]; exact hA)
        refine ⟨hb, hreg, ?_⟩
        simp only [Represent.outside, hBlocks]
        exact hout, hPost⟩

theorem ImplementsTables.transferAgree {α β γ δ : Type} {ia : Represent α} {ib : Represent β}
    {ic : Represent γ} {id : Represent δ} {aborts : Bool} {m : Module} {entry : Nat}
    {f : α → γ} {tables : List (UInt64 × Array UInt64)} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsTables aborts m entry f tables Pre Post)
    (g : β → α) (r : δ → γ) (F : β → δ) (hF : ∀ y, f (g y) = r (F y)) (hArgs : Agree ib ia g)
    (hResult : Agree id ic r) :
    ImplementsTables aborts m entry F tables (fun y => Pre (g y)) (fun y => Post (g y)) :=
  ImplementsTables.transfer h g F (fun _ _ _ _ hy => (hArgs.borrowed _ _ _ _).mp hy)
    (fun _ _ _ _ _ hs => by rw [← hArgs.moves, ← hArgs.reads]; exact hs)
    (fun _ _ _ _ _ => (hArgs.moves _ _ _).symm)
    (fun _ _ _ y hy => (hResult.owned _ _ _ _).mpr (hF y ▸ hy))
    (fun _ _ y => by rw [hF]; exact hResult.blocks _ _ _)

/-- The wrapper theorem in the form of Lean's instances, as `ImplementsA.lean` states it. -/
theorem ImplementsTables.lean {ps : List Ty} {ms : List Mode} {r : Ty} {aborts : Bool}
    {m : Module} {entry : Nat} {f : Env ps → r.denote} {tables : List (UInt64 × Array UInt64)}
    {Pre : Env ps → Heap → Store Unit → Prop}
    {Post : Env ps → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : @ImplementsTables _ _ (Env.represent ps ms) (Ty.represent r) aborts m entry f tables Pre
      Post) :
    @ImplementsTables _ _ (argsInst ps ms) r.leanInst aborts m entry
      (fun y => f (Env.ofArgs ps ms y)) tables (fun y => Pre (Env.ofArgs ps ms y))
      (fun y => Post (Env.ofArgs ps ms y)) :=
  @ImplementsTables.transfer _ _ _ _ (Env.represent ps ms) (argsInst ps ms) (Ty.represent r)
    r.leanInst aborts m entry f tables Pre Post h (Env.ofArgs ps ms)
    (fun y => f (Env.ofArgs ps ms y))
    (fun _ _ _ _ hy => (argsInst_borrowed ps ms).mp hy)
    (fun _ _ _ _ hy hS => by
      have hl := ((argsInst_borrowed ps ms).mp hy).length
      rw [argsInst_moves ps ms hl, argsInst_reads ps ms hl] at hS
      exact hS)
    (fun _ _ _ _ hy => (argsInst_moves ps ms ((argsInst_borrowed ps ms).mp hy).length).symm)
    (fun _ _ _ _ hz => r.leanInst_owned.mpr hz) (fun _ _ _ => r.leanInst_blocks)

end Verified
