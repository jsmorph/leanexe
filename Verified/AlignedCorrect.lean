import Verified.AlignedTailEntry
import Verified.Correct

/-!
`Prog.calls` under the flag.  `CallsX strict` is `Calls` with `FunSpecX strict`, and
`Prog.callsX` proves it by the induction that proves `Prog.calls`: each function's `FunSpec` as
before, and under `strict = true` its `FunAligned`, from the `FunAligned` of the functions it
calls.  A recursive function needs a second induction on the frames left, whose step takes the
function's own `FunSpec` at the next depth from the first.  Tail functions take their
`FunAligned` from `TailFunc.function_runsX`.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- `Calls` under the flag. -/
def CallsX (strict : Bool) {S : List Sig} (m : Module) (funs : Funs S) (flags : Flags S)
    (bounds : Nat → Bounds S) (fits : Nat → Fits S) (pool : Bytes.LiteralPool) : Prop :=
  ∀ {g : Sig} (f : FVar S g) (d : UInt64), FunSpecX strict m g f.callIndex (funs.get f)
    (flags.params f) (flags.result f) ((bounds (framesAt d)).get f) ((fits (framesAt d)).get f)
    (fun d' => d' = d) pool

section

variable {strict : Bool} {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S}
  {pool : Bytes.LiteralPool}

theorem CallsX.at {bounds : Nat → Bounds S} {fits : Nat → Fits S}
    (h : CallsX strict m funs flags bounds fits pool) (d0 : UInt64) :
    CallsAtX strict m funs flags (bounds (framesAt (d0 + 1))) (fits (framesAt (d0 + 1))) d0 pool :=
  fun f => h f (d0 + 1)

theorem CallsX.false_iff {bounds : Nat → Bounds S} {fits : Nat → Fits S} :
    CallsX false m funs flags bounds fits pool ↔ Calls m funs flags bounds fits pool :=
  ⟨fun h _ f d => (h f d).1, fun h _ f d => ⟨h f d, nofun⟩⟩

theorem CallsAtX.toCallsAt {bounds : Bounds S} {fits : Fits S} {d0 : UInt64}
    (h : CallsAtX strict m funs flags bounds fits d0 pool) :
    CallsAt m funs flags bounds fits d0 pool :=
  fun f => (h f).1

end

theorem FunAligned.congr {m : Module} {g : Sig} {idx : Nat} {F F' : Env g.params → g.result.denote}
    {pf : List Bool} {rf : Bool} {A : Env g.params → Nat} {Fi : Env g.params → Bool}
    {D : UInt64 → Prop} {pool : Bytes.LiteralPool} (hF : ∀ args, F args = F' args)
    (h : FunAligned m g idx F' pf rf A Fi D pool) : FunAligned m g idx F pf rf A Fi D pool := by
  obtain rfl : F = F' := funext hF
  exact h

/-- `FunAligned` of a tail function whose code takes no call depth. -/
theorem TailFunc.function_aligned {S : List Sig} (func : TailFunc S) {m : Module}
    {pool : Bytes.LiteralPool} (hRA : ReleaseAligned m) (hRt : AllocAligned m)
    (hCopy : ∀ host, CopyCodeX true m host)
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (fits : Fits S)
    (decreases : func.Decreases funs) (meaning : Env func.params → func.result.denote)
    (fixed : ∀ state, meaning state = (func.body.denote funs state).elim meaning id)
    (pos : Nat) (hm : Runtime m)
    (hFunc : m.funcs[pos]? = some (func.function (pool := pool) pos))
    (hCovered : func.body.Covered pool) {d0 : UInt64}
    (hCalls : CallsAtX true m funs flags bounds fits d0 pool) (hDepth : func.depth = false)
    (Fi : Env func.params → Bool) (D : UInt64 → Prop) :
    FunAligned m func.sig pos meaning (func.paidParams flags) (func.paidResult flags)
      (func.bound funs flags bounds) Fi D pool := by
  intro host heap store ws args hAt hInput hRep hSep hCap hHeap hVals d _ rest
  have hRun : RunsA _ host m pos store _ _ := func.function_runsX (strict := true) funs flags
    bounds fits decreases meaning fixed m pos hm hFunc hCovered d0 (fun _ => hCalls) host store heap ws args hAt hInput hRep hSep
    hCap (fun _ => hRA)
    (fun _ => hRt) (hCopy host) (fun _ => ⟨hHeap, hVals⟩)
  have hApp := hRun.append_args (f := func.function (pool := pool) pos)
    (by simp [hm.imports]) (by simpa [hm.imports] using hFunc)
    (by simp [hRep.length, TailFunc.function_numParams, TailFunc.sig, hDepth]) rest
  have hStack : ((if func.depth then [Value.i64 d0] else []) ++ ws).reverse ++ rest =
      ws.reverse ++ ((if func.sig.depth then [Value.i64 d] else []) ++ rest) := by
    simp [TailFunc.sig, hDepth]
  rw [hStack] at hApp
  refine (hApp.of_imp fun h => ?_).mono
    fun final values ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, hTop, hAl⟩ =>
      ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, fun _ => hTop (by simp [hDepth]),
        fun _ => hAl rfl⟩
  have e : func.sig.paidSel (func.paidParams flags) = fun i =>
      paidAt (func.paidParams flags) i && paramMode func.params func.modes i == .owned := rfl
  rw [e]
  simp only [TailFunc.sig, hDepth, Bool.false_and, Bool.false_or, Bool.or_false] at h ⊢
  exact h

/-- `FunAligned` of a tail function whose code takes the call depth, at the depth `d`. -/
theorem TailFunc.function_depthAligned {S : List Sig} (func : TailFunc S) {m : Module}
    {pool : Bytes.LiteralPool} (hRA : ReleaseAligned m) (hRt : AllocAligned m)
    (hCopy : ∀ host, CopyCodeX true m host)
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (fits : Fits S)
    (decreases : func.Decreases funs) (meaning : Env func.params → func.result.denote)
    (fixed : ∀ state, meaning state = (func.body.denote funs state).elim meaning id)
    (pos : Nat) (hm : Runtime m)
    (hFunc : m.funcs[pos]? = some (func.function (pool := pool) pos))
    (hCovered : func.body.Covered pool) (hDepth : func.depth = true) (d : UInt64)
    (hCalls : d < depthLimit → CallsAtX true m funs flags bounds fits d pool)
    (Fi : Env func.params → Bool) (A : Env func.params → Nat)
    (hFi : ∀ args, Fi args = (decide (d < depthLimit) && func.fits funs fits args))
    (hA : d < depthLimit → ∀ args, A args = func.bound funs flags bounds args) :
    FunAligned m func.sig pos meaning (func.paidParams flags) (func.paidResult flags) A Fi
      (fun d' => d' = d) pool := by
  intro host heap store ws args hAt hInput hRep hSep hCap hHeap hVals d' hd rest
  obtain rfl : d' = d := hd (by simp [TailFunc.sig, hDepth])
  have hRun : RunsA _ host m pos store _ _ := func.function_runsX (strict := true) funs flags
    bounds fits decreases meaning fixed m pos hm hFunc hCovered d' (fun h => hCalls (h hDepth)) host store heap ws args hAt hInput
    hRep hSep hCap (fun _ => hRA)
    (fun _ => hRt) (hCopy host) (fun _ => ⟨hHeap, hVals⟩)
  have hApp := hRun.append_args (f := func.function (pool := pool) pos)
    (by simp [hm.imports]) (by simpa [hm.imports] using hFunc)
    (by simp [hRep.length, TailFunc.function_numParams, TailFunc.sig, hDepth]; omega) rest
  have hStack : ((if func.depth then [Value.i64 d'] else []) ++ ws).reverse ++ rest =
      ws.reverse ++ ((if func.sig.depth then [Value.i64 d'] else []) ++ rest) := by
    simp [TailFunc.sig, hDepth]
  rw [hStack] at hApp
  refine (hApp.of_imp fun h => ?_).mono
    fun final values ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, hTop, hAl⟩ =>
      ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, fun hf => ?_, fun _ => hAl rfl⟩
  · have e : func.sig.paidSel (func.paidParams flags) = fun i =>
        paidAt (func.paidParams flags) i && paramMode func.params func.modes i == .owned := rfl
    rw [e]
    simp only [TailFunc.sig, hDepth, Bool.true_and, Bool.or_true] at h ⊢
    rw [hFi args]
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_false_iff_not,
      Bool.and_eq_false_iff] at h ⊢
    by_cases hlt : d' < depthLimit
    · rcases h with h | h
      · exact Or.inl (Or.inr (h.resolve_left (by simpa using hlt)))
      · refine Or.inr ?_
        rw [hA hlt args]
        exact decide_eq_false h.2
    · exact Or.inl (Or.inl (by simpa using hlt))
  · have hFi' : Fi args = true := by simpa [TailFunc.sig, hDepth] using hf
    rw [hFi args] at hFi'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hFi'
    rw [hA hFi'.1 args]
    exact hTop (by simp [hDepth, hFi'.1, hFi'.2])

/-- `Prog.calls` under the flag. -/
theorem Prog.callsX {strict : Bool} {S : List Sig} (prog : Prog S) (funs : Funs S) (hMeaning : prog.Meaning funs)
    (m : Module) (hm : Runtime m) {pool : Bytes.LiteralPool}
    (hRA : strict = true → ReleaseAligned m) (hRt : strict = true → AllocAligned m)
    (hCopy : ∀ host, CopyCodeX strict m host)
    (hFuncs : ∀ k < S.length, m.funcs[2 + k]? = (prog.functions (pool := pool))[k]?)
    (hCovered : prog.Covered pool) :
    CallsX strict m funs prog.flags (prog.boundsAt funs) (prog.fitsAt funs) pool := by
  have h0 : framesAt (999 + 1) = 0 := rfl
  induction hMeaning with
  | nil => intro g fv; cases fv
  | @cons S' f rest funs' _ ih =>
    have hBody : f.body.Covered pool := fun _ hb =>
      hCovered (List.mem_append_right _ hb)
    have hRest : CallsX strict m funs' rest.flags (rest.boundsAt funs') (rest.fitsAt funs') pool :=
      ih (fun k hk => by
        rw [hFuncs k (by simp; omega)]
        simp [Prog.functions, List.getElem?_append_left (by
          rw [rest.functions_length (pool := pool)]; exact hk)])
        (fun _ hb => hCovered (List.mem_append_left _ hb))
    have hpos : m.funcs[2 + S'.length]? =
        some (bodyFunction f.modes f.body f.depth (2 + S'.length) pool) := by
      rw [hFuncs _ (by simp)]
      simp [Prog.functions, rest.functions_length (pool := pool), Func.function]
    have hrf : f.paidResult rest.flags = true →
        f.body.paid rest.flags (entryModes f.params f.modes) (f.paidParams rest.flags)
          (fun _ => false) = true := fun h => by
      simp only [Func.paidResult, Bool.and_eq_true] at h; exact h.2
    intro g fv d
    cases fv with
    | here =>
      rw [FVar.callIndex_here]
      refine ⟨⟨fun hdep => ?_, fun hdep d' hd' => ?_, _, hpos,
        bodyFunction_numParams (pool := pool) f.modes f.body f.depth _⟩, fun hs => ?_⟩
      · have hdep' : f.depth = false := hdep
        rw [hdep'] at hpos
        have hC : CallsAt m funs' rest.flags (rest.boundsAt funs' 0) (rest.fitsAt funs' 0) 999 pool :=
          fun f => (CallsX.at (@hRest) 999 f).1
        rw [Prog.boundsAt_cons_here]
        simp only [hdep', Bool.false_eq_true, ↓reduceIte]
        exact bodyFunction_implements f.modes f.body f.placeArgs funs' rest.flags
          (rest.boundsAt funs' 0) (rest.fitsAt funs' 0) _ _ hrf m _ hm hpos hBody hC hdep' f.aborts id
      · have hdep' : f.depth = true := hdep
        rw [hdep'] at hpos
        subst hd'
        refine bodyFunction_depth f.modes f.body f.placeArgs funs' rest.flags
          (rest.boundsAt funs' (framesAt (d' + 1))) (rest.fitsAt funs' (framesAt (d' + 1))) _ _ hrf
          m _ hm hpos hBody d' (fun _ => fun f => (CallsX.at (@hRest) d' f).1) _ _ (fun args => ?_) (fun hlt args => ?_)
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
      · subst hs
        cases hdep : f.depth
        · have hCX : CallsAtX true m funs' rest.flags (rest.boundsAt funs' 0) (rest.fitsAt funs' 0)
              999 pool := CallsX.at (@hRest) 999
          rw [Prog.boundsAt_cons_here]
          simp only [hdep, Bool.false_eq_true, ↓reduceIte]
          exact bodyFunction_aligned f.modes f.body f.placeArgs funs' rest.flags
            (rest.boundsAt funs' 0) (rest.fitsAt funs' 0) _ _ hrf m _ hm (hRA rfl) (hRt rfl) hCopy
            f.depth hdep hpos hBody hCX hdep f.aborts id _ _
        · refine bodyFunction_depthAligned f.modes f.body f.placeArgs funs' rest.flags
            (rest.boundsAt funs' (framesAt (d + 1))) (rest.fitsAt funs' (framesAt (d + 1))) _ _ hrf
            m _ hm (hRA rfl) (hRt rfl) hCopy f.depth hdep hpos hBody d
            (fun _ => CallsX.at (@hRest) d) f.aborts _ _ (fun args => ?_) (fun hlt args => ?_)
          · by_cases hlt : d < depthLimit
            · rw [framesAt_succ hlt, Prog.fitsAt_cons_here]
              simp only [hdep, ↓reduceIte, hlt, decide_true, Bool.true_and]
              rfl
            · rw [framesAt_eq_zero hlt, Prog.fitsAt_cons_here]
              simp only [hdep, ↓reduceIte, hlt, decide_false, Bool.false_and]
              rfl
          · rw [framesAt_succ hlt, Prog.boundsAt_cons_here]
            simp only [hdep, ↓reduceIte]
            rfl
    | there g' =>
      rw [FVar.callIndex_there]
      exact hRest g' d
  | @consTail S' f rest funs' M _ hDecreases hM ih =>
    have hBody : f.body.Covered pool := fun _ hb =>
      hCovered (List.mem_append_right _ hb)
    have hRest : CallsX strict m funs' rest.flags (rest.boundsAt funs') (rest.fitsAt funs') pool :=
      ih (fun k hk => by
        rw [hFuncs k (by simp; omega)]
        simp [Prog.functions, List.getElem?_append_left (by
          rw [rest.functions_length (pool := pool)]; exact hk)])
        (fun _ hb => hCovered (List.mem_append_left _ hb))
    have hpos : m.funcs[2 + S'.length]? = some (f.function (pool := pool) (2 + S'.length)) := by
      rw [hFuncs _ (by simp)]
      simp [Prog.functions, rest.functions_length (pool := pool)]
    intro g fv d
    cases fv with
    | here =>
      rw [FVar.callIndex_here]
      refine ⟨⟨fun hdep => ?_, fun hdep d' hd' => ?_, _, hpos,
        f.function_numParams (pool := pool) _⟩, fun hs => ?_⟩
      · have hdep' : f.depth = false := hdep
        have hC : CallsAt m funs' rest.flags (rest.boundsAt funs' 0) (rest.fitsAt funs' 0) 999 pool :=
          fun f => (CallsX.at (@hRest) 999 f).1
        rw [Prog.boundsAt_consTail_here]
        simp only [hdep', Bool.false_eq_true, ↓reduceIte]
        exact f.function_implements funs' rest.flags (rest.boundsAt funs' 0) (rest.fitsAt funs' 0)
          hDecreases M hM m _ hm hpos hBody hC hdep'
      · have hdep' : f.depth = true := hdep
        subst hd'
        refine f.function_depth funs' rest.flags (rest.boundsAt funs' (framesAt (d' + 1)))
          (rest.fitsAt funs' (framesAt (d' + 1))) hDecreases M hM m _ hm hpos hBody hdep' d'
          (fun _ => fun f => (CallsX.at (@hRest) d' f).1) _ _ (fun args => ?_) (fun hlt args => ?_)
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
      · subst hs
        cases hdep : f.depth
        · have hCX : CallsAtX true m funs' rest.flags (rest.boundsAt funs' 0) (rest.fitsAt funs' 0)
              999 pool := CallsX.at (@hRest) 999
          rw [Prog.boundsAt_consTail_here]
          simp only [hdep, Bool.false_eq_true, ↓reduceIte]
          exact f.function_aligned (hRA rfl) (hRt rfl) hCopy funs' rest.flags (rest.boundsAt funs' 0)
            (rest.fitsAt funs' 0) hDecreases M hM _ hm hpos hBody hCX hdep _ _
        · refine f.function_depthAligned (hRA rfl) (hRt rfl) hCopy funs' rest.flags
            (rest.boundsAt funs' (framesAt (d + 1))) (rest.fitsAt funs' (framesAt (d + 1)))
            hDecreases M hM _ hm hpos hBody hdep d (fun _ => CallsX.at (@hRest) d) _ _
            (fun args => ?_) (fun hlt args => ?_)
          · by_cases hlt : d < depthLimit
            · rw [framesAt_succ hlt, Prog.fitsAt_consTail_here]
              simp only [hdep, ↓reduceIte, hlt, decide_true, Bool.true_and]
              rfl
            · rw [framesAt_eq_zero hlt, Prog.fitsAt_consTail_here]
              simp only [hdep, ↓reduceIte, hlt, decide_false, Bool.false_and]
              rfl
          · rw [framesAt_succ hlt, Prog.boundsAt_consTail_here]
            simp only [hdep, ↓reduceIte]
            rfl
    | there g' =>
      rw [FVar.callIndex_there]
      exact hRest g' d
  | @consRec S' f rest funs' M _ hM ih =>
    have hBody : f.body.Covered pool := fun _ hb =>
      hCovered (List.mem_append_right _ hb)
    have hRest : CallsX strict m funs' rest.flags (rest.boundsAt funs') (rest.fitsAt funs') pool :=
      ih (fun k hk => by
        rw [hFuncs k (by simp; omega)]
        simp [Prog.functions, List.getElem?_append_left (by
          rw [rest.functions_length (pool := pool)]; exact hk)])
        (fun _ hb => hCovered (List.mem_append_left _ hb))
    have hpos : m.funcs[2 + S'.length]? =
        some (bodyFunction f.modes f.body true (2 + S'.length) pool) := by
      rw [hFuncs _ (by simp)]
      simp [Prog.functions, rest.functions_length (pool := pool), RecFunc.function]
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
            env.dropDepth) pool := by
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
          _ _ hrf m _ hm hpos hBody d (fun hlt => ?_) _ _ (fun args => ?_) (fun hlt args => ?_)
        · intro g fv
          cases fv with
          | here =>
            rw [FVar.callIndex_here]
            refine ⟨nofun, fun _ d' hd' => ?_, _, hpos,
              bodyFunction_numParams (pool := pool) f.modes f.body true _⟩
            subst hd'
            exact ih' _ (by rw [← hn, framesAt_succ hlt]; omega) (d + 1) rfl
          | there g' =>
            rw [FVar.callIndex_there]
            exact (CallsX.at (@hRest) d g').1
        · by_cases hlt : d < depthLimit
          · rw [framesAt_succ hlt]
            simp only [hlt, decide_true, Bool.true_and]
            rfl
          · rw [framesAt_eq_zero hlt]
            simp only [hlt, decide_false, Bool.false_and]
            rfl
        · rw [framesAt_succ hlt]; rfl
    -- The aligned runs at each depth, by a second induction on the frames left.
    have hAtA : strict = true → ∀ n d, framesAt d = n →
        FunAligned m f.sig (2 + S'.length) M (f.paidParams rest.flags) (f.paidResult rest.flags)
          (f.boundAt (.cons M funs') rest.flags (rest.boundsAt funs') (framesAt d))
          (f.fitsAt (.cons M funs') (rest.fitsAt funs') (framesAt d)) (fun d' => d' = d) pool := by
      intro hs n
      subst hs
      induction n using Nat.strongRecOn with
      | _ n ih' =>
        intro d hn
        refine FunAligned.congr hM (bodyFunction_depthAligned f.modes f.body f.placeArgs _
          (f.flags rest.flags)
          (.cons (f.boundAt (.cons M funs') rest.flags (rest.boundsAt funs') (framesAt (d + 1)))
            (rest.boundsAt funs' (framesAt (d + 1))))
          (.cons (f.fitsAt (.cons M funs') (rest.fitsAt funs') (framesAt (d + 1)))
            (rest.fitsAt funs' (framesAt (d + 1))))
          _ _ hrf m _ hm (hRA rfl) (hRt rfl) hCopy true rfl hpos hBody d
          (fun hlt => ?_) true _ _ (fun args => ?_) (fun hlt args => ?_))
        · intro g fv
          cases fv with
          | here =>
            rw [FVar.callIndex_here]
            refine ⟨⟨nofun, fun _ d' hd' => ?_, _, hpos,
              bodyFunction_numParams (pool := pool) f.modes f.body true _⟩, fun _ => ?_⟩
            · subst hd'
              exact hAt _ (d + 1) rfl
            · exact ih' _ (by rw [← hn, framesAt_succ hlt]; omega) (d + 1) rfl
          | there g' =>
            rw [FVar.callIndex_there]
            exact CallsX.at (@hRest) d g'
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
      exact ⟨⟨nofun, fun _ d' hd' => by subst hd'; exact hAt _ d' rfl, _, hpos,
        bodyFunction_numParams (pool := pool) f.modes f.body true _⟩, fun hs => hAtA hs _ d rfl⟩
    | there g' =>
      rw [FVar.callIndex_there]
      exact hRest g' d

end Verified
