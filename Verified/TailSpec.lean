import Verified.TailEntry

namespace Verified

open Wasm LeanExe.Pipeline

theorem TailFunc.function_implements {S : List Sig} (func : TailFunc S)
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (fits : Fits S)
    (decreases : func.Decreases funs) (meaning : Env func.params → func.result.denote)
    (fixed : ∀ state, meaning state = (func.body.denote funs state).elim meaning id)
    (m : Module) (pos : Nat) (hm : Runtime m) {pool : Bytes.LiteralPool}
    (hFunc : m.funcs[pos]? = some (func.function (pool := pool) pos))
    (hCovered : func.body.Covered pool) {d : UInt64}
    (hCalls : CallsAt m funs flags bounds fits d pool) (hDepth : func.depth = false) :
    @ImplementsP _ _ (Env.represent func.params func.modes) (Ty.represent func.result)
      (fun _ => True) (fun _ => true)
      (fun store ws x => Env.argPot store
        (fun i => paidAt (func.paidParams flags) i && paramMode func.params func.modes i == .owned)
        ws x)
      (fun store ws v => if func.paidResult flags then func.result.pot store ws v else 0)
      func.aborts m pos meaning (func.bound funs flags bounds) pool := by
  intro host store heap ws args _ hAt hInput hRep hSep hCap
  have run := func.function_runs funs flags bounds fits decreases meaning fixed m pos hm hFunc
    hCovered d (fun _ => hCalls) host store heap ws args hAt hInput hRep hSep hCap
  simp only [hDepth, Bool.false_eq_true, ↓reduceIte, List.nil_append, Bool.false_and,
    Bool.false_or] at run
  exact run.mono fun final values ⟨heap', at_, rep, caps, regions, top⟩ =>
    ⟨heap', at_, rep, caps, regions, fun _ => top trivial⟩

theorem TailFunc.function_depth {S : List Sig} (func : TailFunc S)
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (fits : Fits S)
    (decreases : func.Decreases funs) (meaning : Env func.params → func.result.denote)
    (fixed : ∀ state, meaning state = (func.body.denote funs state).elim meaning id)
    (m : Module) (pos : Nat) (hm : Runtime m) {pool : Bytes.LiteralPool}
    (hFunc : m.funcs[pos]? = some (func.function (pool := pool) pos))
    (hCovered : func.body.Covered pool) (hDepth : func.depth = true) (d : UInt64)
    (hCalls : d < depthLimit → CallsAt m funs flags bounds fits d pool)
    (Fi : Env func.params → Bool) (A : Env func.params → Nat)
    (hFi : ∀ args, Fi args = (decide (d < depthLimit) && func.fits funs fits args))
    (hA : d < depthLimit → ∀ args, A args = func.bound funs flags bounds args) :
    @ImplementsP _ _ (Env.represent (.word :: func.params) (.borrowed :: func.modes))
      (Ty.represent func.result) (fun env => env.depthOf = d) (fun env => Fi env.dropDepth)
      (fun store ws x => Env.argPot store
        (depthSelOf fun i => paidAt (func.paidParams flags) i &&
          paramMode func.params func.modes i == .owned) ws x)
      (fun store ws v => if func.paidResult flags then func.result.pot store ws v else 0)
      true m pos (depthMeaning meaning) (fun env => A env.dropDepth) pool := by
  intro host store heap vs env hd hAt hInput hRep hSep hCap
  cases env with
  | cons depth args =>
    change depth = d at hd
    subst hd
    obtain ⟨ws, rfl, rep⟩ := Env.rep_depth.mp hRep
    have separate : Separate store (Env.moves store (paramMode func.params func.modes) ws args)
        (Env.reads store (paramMode func.params func.modes) ws args) := by
      have hs := hSep
      change Separate store
        (Env.moves store (paramMode (.word :: func.params) (.borrowed :: func.modes))
          (.i64 depth :: ws) (.cons (t := .word) depth args))
        (Env.reads store (paramMode (.word :: func.params) (.borrowed :: func.modes))
          (.i64 depth :: ws) (.cons (t := .word) depth args)) at hs
      rw [Env.moves_depth, Env.reads_depth] at hs
      exact hs
    have input : @Bytes.LiteralPool.Input (Env func.params) (Env.represent func.params func.modes)
        pool heap store ws args := by
      refine ⟨hInput.1, ?_⟩
      intro region hRegion
      have apart := hInput.2 region hRegion
      change Apart store
        (Env.moves store (paramMode (.word :: func.params) (.borrowed :: func.modes))
          (.i64 depth :: ws) (.cons (t := .word) depth args)) region at apart
      rw [Env.moves_depth] at apart
      exact apart
    have run := func.function_runs funs flags bounds fits decreases meaning fixed m pos hm hFunc
      hCovered depth (fun h => hCalls (h hDepth)) host store heap ws args hAt input rep separate hCap
    simp only [hDepth, ↓reduceIte, List.singleton_append, Bool.true_and] at run
    change Runs (!Fi args || (true && !decide (heap.Within store m
      (Env.argPot store (depthSelOf fun i => paidAt (func.paidParams flags) i &&
        paramMode func.params func.modes i == .owned) (.i64 depth :: ws) (.cons (t := .word) depth args) +
          A args)))) host m pos store (Value.i64 depth :: ws).reverse _
    rw [Env.argPot_depthOf]
    refine (run.of_imp fun ht => ?_).mono
      fun final values ⟨heap', at_, owned, caps, regions, top⟩ =>
        ⟨heap', at_, owned, caps, fun r hr hp ha => regions r hr hp (by
          change Apart store
            (Env.moves store (paramMode (.word :: func.params) (.borrowed :: func.modes))
              (.i64 depth :: ws) (.cons (t := .word) depth args)) r at ha
          rw [Env.moves_depth] at ha
          exact ha), fun hf => ?_⟩
    · rw [hFi]
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
        Bool.true_and, decide_eq_false_iff_not, Bool.and_eq_false_iff] at ht ⊢
      by_cases hlt : depth < depthLimit
      · rcases ht with ht | ht
        · exact Or.inl (Or.inr (ht.resolve_left (by simpa using hlt)))
        · refine Or.inr ?_
          rw [hA hlt]
          exact ht.2
      · exact Or.inl (Or.inl (by simpa using hlt))
    · change Fi args = true at hf
      rw [hFi] at hf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
      show _ ≤ heap.top.toNat + Env.argPot store
        (depthSelOf fun i => paidAt (func.paidParams flags) i &&
          paramMode func.params func.modes i == .owned) (.i64 depth :: ws)
          (.cons (t := .word) depth args) + A args
      rw [Env.argPot_depthOf, hA hf.1]
      exact top (by simp [hf.1, hf.2])

#print axioms TailFunc.function_implements
#print axioms TailFunc.function_depth

end Verified
