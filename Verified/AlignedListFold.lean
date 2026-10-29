import Verified.AlignedTailTree
import Verified.AlignedTailBody
import Verified.AlignedTailLoop
import Verified.ListFoldCode
import Verified.ListFoldSource
import Verified.TailCorrect
import Verified.TreeMatchFacts
import Verified.TailBindPrefix
import Verified.TailAllocExpand
import Verified.TreeMatchPotential
import Verified.OwnedExpr
import Verified.Bytes.StaticPrefix
import Verified.TreeDispatch
import Verified.TailBind
import Verified.TailArgs
import Verified.ListFoldResource
import Verified.ListFoldBorrowed
import Verified.TailHeap

/-!
The fold over a list under the flag.  `ListFold.step_specX` assembles the flagged tail constructs
into the specification of the loop's body, `ListFold.loop_specX` runs the tail loop on the state
that the arguments' values make, which are borrowed and so aligned as the arguments are, and
`specX_listFold` evaluates the arguments, stores them, runs the loop, and releases the variables
that die in the fold.  The result is an element, which holds no pointer.  Each theorem is its
original with `wpX strict`, the flagged constructs, and the alignment premises.
-/

namespace Verified.ListFold

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem step_specX {strict : Bool} {S : List Sig} {e : Elem} {captures : List Ty}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) (hCopy : CopyCodeX strict m host)
    (body : Expr S (context e captures) (.elem e))
    (bodySpec : ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv body env slots paid live) :
    TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv [] (tailBody body) := by
  apply tail_treeCase_specX hm hRA hCopy []
  · intro _
    exact tail_ret_specX hm hCopy [] _ (specX_var hCopy _)
  · intro r
    obtain rfl := listShape_cell r
    change TailCodeSpecX strict _ _ _ _ _ _ _ [] (TailBody.letE body _) pool
    apply tail_let_specX hm hRA [] body _ bodySpec
    apply tail_next_specX hm hRA hCopy []
    intro i
    obtain ⟨x, hx⟩ := nextArgs_get_var (S := S) e captures i
    rw [hx]
    exact specX_var hCopy x

theorem step_spec {S : List Sig} {e : Elem} {captures : List Ty}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (body : Expr S (context e captures) (.elem e))
    (bodySpec : ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv body env slots paid live) :
    TailCodeSpec (pool := pool) m funs flags bounds fits host pv [] (tailBody body) :=
  TailCodeSpecX.false_iff.mp (step_specX (strict := false) hm nofun (copyCodeX hm) body
    (fun env slots paid live => CodeSpecX.false_iff.mpr (bodySpec env slots paid live)))
#print axioms step_spec

theorem loop_specX {strict : Bool} {S : List Sig} {e : Elem} {captures : List Ty}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) (hCopy : CopyCodeX strict m host)
    (body : Expr S (context e captures) (.elem e)) (place : body.placeArgs = true)
    (bodySpec : ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv body env slots paid live)
    (h stateBase : Nat) (env : Env (params e captures))
    (heap : Heap) (store : Store Unit) (s : Locals) (ws : List Value)
    (hh : s.positions = h) (hpv : s.params = pv)
    (rep : Env.Rep (paramMode (params e captures) []) heap store ws env)
    (sep : Separate store (Env.moves store (paramMode (params e captures) []) ws env)
      (Env.reads store (paramMode (params e captures) []) ws env))
    (hold : LocalsHold s stateBase ((params e captures).flatMap Ty.types) ws)
    (at_ : heap.At store)
    (aligned : strict = true →
      heap.Aligned ∧ Env.AlignedVals store (paramMode (params e captures) []) ws env)
    (input : @Bytes.LiteralPool.Input (Env (params e captures))
      (Env.represent (params e captures) []) pool heap store ws env)
    (cap : store.memoryCap m 0 ≤ 65535)
    (low : s.params.length ≤ stateBase)
    (room : stateBase + widthSum (params e captures) + e.width + (tailBody body).width [] ≤ h)
    (rest : Program) (Q : Assertion Unit)
    (trap : TrapOK (!(func body place).fits funs fits env ||
      !decide (heap.Within store m ((func body place).bound funs flags bounds env))) Q)
    (next : ∀ heap' store' s' words,
      Step heap store (Apart store (Env.moves store (paramMode (params e captures) []) ws env))
        heap' store' [] →
      Frame stateBase s s' → (.elem e : Ty).Rep .owned heap' store' words (meaning body funs env) →
      LocalsHold s' (stateBase + widthSum (params e captures)) e.types words →
      (strict = true → heap'.Aligned ∧
        Ty.AlignedVal .owned store' (.elem e) words (meaning body funs env)) →
      ((func body place).fits funs fits env = true →
        heap'.top.toNat ≤ heap.top.toNat + (func body place).bound funs flags bounds env) →
      wpX strict m rest Q store' { s' with values := s.values } host) :
    wpX strict m (loopCode body h stateBase (fun slots base live => body.code (pool := pool) h slots base live) ++ rest)
      Q store s host := by
  rw [loopCode_eq]
  simp only [List.singleton_append]
  refine wpX_block_cons ?_
  refine tail_loop_specX hm hRA (func body place) (func_decreases body place funs)
    (meaning body funs) (fixed body funs) (step_specX hm hRA hCopy body bodySpec)
    h stateBase (stateBase + widthSum (params e captures))
    (stateBase + widthSum (params e captures) + e.width) env heap store s ws hh hpv rep sep hold
    at_ aligned input cap low le_rfl le_rfl room _ ?_ ?_
  · simp only [func_aborts, Bool.true_and, argPot_eq_zero, Nat.zero_add]
    cases hb : (!(func body place).fits funs fits env ||
        !decide (heap.Within store m ((func body place).bound funs flags bounds env))) with
    | false => trivial
    | true =>
      intro st
      rw [hb] at trap
      exact trap st
  · intro heap' store' s' words step frame result held al top
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    apply next heap' store' s' words step frame result held al
    simpa only [func_paidResult, Bool.false_eq_true, ↓reduceIte, argPot_eq_zero,
      Nat.add_zero] using top

theorem loop_spec {S : List Sig} {e : Elem} {captures : List Ty}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (body : Expr S (context e captures) (.elem e)) (place : body.placeArgs = true)
    (bodySpec : ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv body env slots paid live)
    (h stateBase : Nat) (env : Env (params e captures))
    (heap : Heap) (store : Store Unit) (s : Locals) (ws : List Value)
    (hh : s.positions = h) (hpv : s.params = pv)
    (rep : Env.Rep (paramMode (params e captures) []) heap store ws env)
    (sep : Separate store (Env.moves store (paramMode (params e captures) []) ws env)
      (Env.reads store (paramMode (params e captures) []) ws env))
    (hold : LocalsHold s stateBase ((params e captures).flatMap Ty.types) ws)
    (at_ : heap.At store)
    (input : @Bytes.LiteralPool.Input (Env (params e captures))
      (Env.represent (params e captures) []) pool heap store ws env)
    (cap : store.memoryCap m 0 ≤ 65535)
    (low : s.params.length ≤ stateBase)
    (room : stateBase + widthSum (params e captures) + e.width + (tailBody body).width [] ≤ h)
    (rest : Program) (Q : Assertion Unit)
    (trap : TrapOK (!(func body place).fits funs fits env ||
      !decide (heap.Within store m ((func body place).bound funs flags bounds env))) Q)
    (next : ∀ heap' store' s' words,
      Step heap store (Apart store (Env.moves store (paramMode (params e captures) []) ws env))
        heap' store' [] →
      Frame stateBase s s' → (.elem e : Ty).Rep .owned heap' store' words (meaning body funs env) →
      LocalsHold s' (stateBase + widthSum (params e captures)) e.types words →
      ((func body place).fits funs fits env = true →
        heap'.top.toNat ≤ heap.top.toNat + (func body place).bound funs flags bounds env) →
      wp m rest Q store' { s' with values := s.values } host) :
    wp m (loopCode body h stateBase (fun slots base live => body.code (pool := pool) h slots base live) ++ rest)
      Q store s host :=
  loop_specX (strict := false) hm nofun (copyCodeX hm) body place
    (fun env slots paid live => CodeSpecX.false_iff.mpr (bodySpec env slots paid live)) h stateBase
    env heap store s ws hh hpv rep sep hold at_ nofun input cap low room rest Q trap
    (fun heap' store' s' words a1 a2 a3 a4 _ a6 => next heap' store' s' words a1 a2 a3 a4 a6)
#print axioms loop_spec

end Verified.ListFold

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem specX_listFold {strict : Bool} {S : List Sig} {Γ : List Ty} {e : Elem} {captures : List Ty}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) (hCopy : CopyCodeX strict m host)
    (args : (i : Fin (ListFold.params e captures).length) →
      Expr S Γ ((ListFold.params e captures).get i))
    (body : Expr S (ListFold.context e captures) (.elem e))
    (argsSpec : ∀ i env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (args i) env slots paid live)
    (bodySpec : ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv body env slots paid live) :
    ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (.listFold args body) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom hPlace rest Q hTrap
    hNext
  let value := Expr.listFold args body
  let all := fun i => live i || argsAny fun j => (args j).uses i
  let state := Env.ofFn fun i => (args i).denote funs env
  let charge := argsSum (argCost funs flags bounds (slots.map Slot.mode) paid all all
    (fun _ => .borrowed) args env)
  simp only [Expr.placeArgs, Bool.and_eq_true, Bool.not_eq_true'] at hPlace
  obtain ⟨⟨hPlaces, hArgs⟩, hBody⟩ := hPlace
  let f := ListFold.func body hBody
  have allocEq : value.allocs funs flags bounds (slots.map Slot.mode) paid live env =
      charge + f.bound funs flags bounds state := by
    rw [ListFold.func_bound_env]
    rfl
  have fitsEq : value.fits funs fits env =
      ((argsAll fun i => (args i).fits funs fits env) && f.fits funs fits state) := by
    rw [ListFold.func_fits_env]
    rfl
  have argsFits (hf : value.fits funs fits env = true) :
      (argsAll fun i => (args i).fits funs fits env) = true := by
    rw [fitsEq] at hf
    simp only [Bool.and_eq_true] at hf
    exact hf.1
  have loopFits (hf : value.fits funs fits env = true) : f.fits funs fits state = true := by
    rw [fitsEq] at hf
    simp only [Bool.and_eq_true] at hf
    exact hf.2
  have trap : TrapOK (!value.fits funs fits env ||
      !decide (heap.Within store m (dyingPot store s env slots paid all live +
        value.allocs funs flags bounds (slots.map Slot.mode) paid live env))) Q := by
    convert hTrap using 1 <;>
      simp only [value, all, Expr.uses, trapFlag, Expr.aborts, Bool.true_or, Bool.true_and] <;> rfl
  have roomArgs (i : Fin (ListFold.params e captures).length) : base + (args i).width ≤ h := by
    simp only [Expr.width] at hRoom
    have hi := le_argsMax (fun j => (args j).width) i
    have hm := Nat.le_max_left (argsMax fun j => (args j).width)
      (widthSum (ListFold.params e captures) + e.width + 3 +
        max treeCopyScratch (e.width + max body.width treeCopyScratch))
    omega
  have roomLoop : base + widthSum (ListFold.params e captures) + e.width +
      (ListFold.tailBody body).width [] ≤ h := by
    simp only [Expr.width] at hRoom
    have ht := ListFold.tail_width body
    have hm := Nat.le_max_right (argsMax fun j => (args j).width)
      (widthSum (ListFold.params e captures) + e.width + 3 +
        max treeCopyScratch (e.width + max body.width treeCopyScratch))
    omega
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  refine args_specX hCopy (paid := paid) (all := all) (kept := all) (d := !(argsAll fun i =>
      (args i).fits funs fits env)) (a := true) (fun _ => .borrowed) args argsSpec
    (fun i k hk => by
      change (live k || argsAny fun j => (args j).uses k) = true
      simp only [Bool.or_eq_true]
      exact .inr (le_argsAny _ i hk))
    (fun _ hk => hk) (fun _ => nofun)
    (fun i hs _ => by
      have hi := argsAny_eq_false hPlaces i
      simpa only [hs, Bool.not_false, Bool.true_and, Bool.not_eq_false'] using hi)
    (fun _ => nofun)
    (fun i => by simpa only [Bool.not_eq_false'] using argsAny_eq_false hArgs i)
    (fun i hf => by simpa only [Bool.not_eq_true'] using argsAll_false _ i (by simpa using hf))
    (fun _ _ => rfl) heap store s hh hpv hVars hAt hAl hSafe hCap hBase
    (fun i => roomArgs i) _ _
    (trap.part (a := true) (fun hd => by
        simp only [Bool.not_eq_true'] at hd ⊢
        rw [fitsEq, hd, Bool.false_and])
      (fun _ => rfl) (fun _ hw => hw.mono (by rw [allocEq]; omega)))
    fun heap1 store1 s1 ws fresh step1 frame1 vars1 rep1 hAl1 sep1 _ _ top1 _ => ?_
  rw [storeParamsCode_eq]
  refine wpX_storeCode ws h base ((ListFold.params e captures).flatMap Ty.types) s1 s.values
    (by rw [flatMap_types_length]; exact rep1.length)
    (frame1.positions.trans hh) (by rw [frame1.params]; exact hBase)
    (by rw [flatMap_types_length, frame1.positions, hh]; omega)
    fun s2 frame2 hold2 _ => ?_
  have hInput : @pool.Input (Env (ListFold.params e captures))
      (Env.represent (ListFold.params e captures) []) heap1 store1 ws state := by
    obtain ⟨hStatic, _⟩ := hSafe.static.step step1 (fun _ _ => trivial)
    refine ⟨hStatic, ?_⟩
    intro region hRegion
    change Apart store1 (Env.moves store1 (paramMode (ListFold.params e captures) []) ws state) region
    rw [ListFold.moves_eq_nil]
    exact Apart.nil
  refine ListFold.loop_specX hm hRA hCopy body hBody bodySpec h base state heap1 store1
    { s2 with values := s.values } ws
    (frame2.positions.trans (frame1.positions.trans hh))
    (frame2.params.trans (frame1.params.trans hpv))
    (by simpa only [ListFold.paramMode_eq_borrowed] using rep1)
    (by simpa only [ListFold.paramMode_eq_borrowed] using sep1)
    hold2 step1.at_
    (fun hs => ⟨(hAl1 hs).1.1, by simpa only [ListFold.paramMode_eq_borrowed] using (hAl1 hs).2⟩)
    hInput (by rw [step1.cap m]; exact hCap)
    (by rw [frame2.params, frame1.params]; exact hBase) roomLoop _ _
    (trap.part (a := true) (a' := true)
      (fun hd => by
        simp only [Bool.not_eq_true'] at hd ⊢
        rw [fitsEq, hd, Bool.and_false]) (fun _ => rfl)
      (fun good hw => by
        have hf : value.fits funs fits env = true := by simpa using good
        exact hw.shift (top1 (by simp only [argsFits hf, Bool.not_true]))
          (by rw [allocEq]; dsimp only [f, charge]; omega) (step1.cap m)))
    fun heap2 store2 s3 words step2 frame3 result held al2 top2 => ?_
  rw [ListFold.moves_eq_nil] at step2
  have finalFrame : Frame base s s3 := frame1.trans (frame2.trans frame3.values)
  have finalVars : Holds env slots all base heap2 store2 s3 :=
    ((vars1.agree frame2).step step2 (fun _ _ _ _ _ _ _ _ => Apart.nil)).agree frame3.values
  have finalAl : strict = true → HoldsA env slots all heap2 store2 s3 := fun hs =>
    HoldsA.agree ((vars1.agree frame2).step step2 (fun _ _ _ _ _ _ _ _ => Apart.nil))
      (HoldsA.step (vars1.agree frame2) (HoldsA.agree vars1 (hAl1 hs).1 frame2) step2 (al2 hs).1
        (fun _ _ _ _ _ _ _ _ => Apart.nil)) frame3.values
  have after : After env slots all all base heap store s (.elem e) .borrowed
      (value.denote funs env) heap2 store2 s3 words := by
    refine ⟨step1.trans step2 (fun _ _ => ⟨trivial, fun _ => Apart.nil⟩),
      finalFrame, finalVars, result.borrow, Holds.Apart.ofScalar rfl⟩
  refine After.releaseX hm hRA (live := live) (sel := fun i => all i && !live i)
    hVars after (fun hs => ⟨finalAl hs, Ty.AlignedVal.scalar rfl⟩) (fun _ hk => hk)
    (fun _ hk => by simp only [Bool.and_eq_true] at hk; exact hk.1)
    (fun i hi => by simp [all, hi])
    fun heap3 store3 released topRelease _ hAl3 => ?_
  refine wpX_loadCode words released.rep.typed (finalFrame.positions.trans hh) held ?_
  apply hNext heap3 store3 s3 words released hAl3
  intro hf
  have ha := top1 (by simp only [argsFits hf, Bool.not_true])
  have hl := top2 (loopFits hf)
  have hr := congrArg UInt64.toNat topRelease
  simp only [Expr.paid, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  rw [allocEq]
  dsimp only [f, charge]
  omega

theorem spec_listFold {S : List Sig} {Γ : List Ty} {e : Elem} {captures : List Ty}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (args : (i : Fin (ListFold.params e captures).length) →
      Expr S Γ ((ListFold.params e captures).get i))
    (body : Expr S (ListFold.context e captures) (.elem e))
    (argsSpec : ∀ i env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (args i) env slots paid live)
    (bodySpec : ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv body env slots paid live) :
    ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (.listFold args body) env slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_listFold (strict := false) hm nofun (copyCodeX hm) args body
      (fun i env slots paid live => CodeSpecX.false_iff.mpr (argsSpec i env slots paid live))
      (fun env slots paid live => CodeSpecX.false_iff.mpr (bodySpec env slots paid live)) env slots
      paid live)
#print axioms spec_listFold

end Verified
