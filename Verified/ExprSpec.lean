import Verified.ArgPot
import Verified.ArrayFold
import Verified.InsertIdx
import LeanExe.ProofKit.F32Bits
import Verified.Bytes.StaticInput

/-! The expression specification and shared rules for calls, budgets, and operand sequencing. -/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

section

variable {m : Module} {host : HostEnv Unit}

/-- A value turned from mode `source` into mode `target` after an expression's code: a borrowed
value that must be owned is copied into new blocks, which raises `top` by at most
`coerceCost t source target v`, a value already owned keeps its store and words, and the facts of
`After` carry over. -/
theorem After.coerce (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {liveIn live : Nat → Bool} {h base base' : Nat} {heap : Heap} {store : Store Unit}
    {s : Locals} {t : Ty} {source target : Mode} {v : t.denote} {heap1 : Heap}
    {store1 : Store Unit} {s1 : Locals} {ws vs : List Value} {rest : Program}
    {Q : Assertion Unit}
    (a : After env slots liveIn live base heap store s t source v heap1 store1 s1 ws)
    (hTarget : source = .owned → target = .owned) (hBase' : base ≤ base')
    (hLow : s1.params.length ≤ base') (hh : s1.positions = h) (hRoom : base' + copyWidth t ≤ h)
    (hCap : store1.memoryCap m 0 ≤ 65535)
    (hTrap : source = .borrowed → target = .owned → t.scalar = false →
      TrapOK (!decide (heap1.Within store1 m (t.copyCost v))) Q)
    (hNext : ∀ heap2 store2 s2 ws2,
      After env slots liveIn live base heap store s t target v heap2 store2 s2 ws2 →
      heap2.top.toNat ≤ heap1.top.toNat + coerceCost t source target v →
      (source = .owned → store2 = store1 ∧ ws2 = ws) →
      wp m rest Q store2 { s2 with values := ws2.reverse ++ vs } host) :
    wp m (coerceCode h t source target base' ++ rest) Q store1
      { s1 with values := ws.reverse ++ vs } host := by
  by_cases hCopy : source = .borrowed ∧ target = .owned ∧ t.scalar = false
  · obtain ⟨hs, ht, hScalar⟩ := hCopy
    subst hs ht
    have hW : copyWidth t = t.width + t.copyScratch := by
      simp [copyWidth, Ty.copyScratch, hScalar]
    simp only [coerceCode, and_self, hScalar, ↓reduceIte, List.append_assoc]
    refine wp_storeCode ws h base' t.types s1 vs a.rep.typed hh hLow
      (by rw [Ty.types_length, hh]; omega) fun s2 hF2 hold2 _ => ?_
    refine wp_copyCode hm t a.step.at_ hCap (hTrap rfl rfl hScalar)
      (hF2.positions.trans hh) a.rep
      hold2 (le_refl _) (by rw [hF2.params]; omega)
      (by simp only [Locals.positions_values, hF2.positions, hh]; omega)
      fun heap3 store3 s3 ws3 hStep3 hRep3 hF3 hTop3 => ?_
    have hF13 : Frame base s1 s3 :=
      (hF2.mono hBase').trans (Frame.ofValues.trans (hF3.mono (by omega)))
    have hF : Frame base s s3 := a.frame.trans hF13
    have hStep0 := a.step
    simp only [Mode.fresh] at hStep0
    refine hNext heap3 store3 s3 ws3 ⟨?_, hF, ?_, hRep3, ?_⟩ (by simpa [coerceCost] using hTop3)
      nofun
    · exact hStep0.trans hStep3 fun _ hr => ⟨hr, fun _ => trivial⟩
    · exact (a.holds.step hStep3 fun _ _ _ _ _ _ _ _ => trivial).agree hF13
    · intro u y hy _ wy hwy hly b hb c hc
      have hwy' := (a.holds.hold_agree hF13 hy hly).mp hwy
      obtain ⟨hSame, hFresh⟩ := a.holds.regions_after hStep3 hy hwy' hly fun _ _ => trivial
      rw [hSame] at hc
      exact regionsDisjoint_symm (hFresh c hc b hb)
  · have hEmpty : coerceCode h t source target base' = [] := by
      simp only [coerceCode]; rw [ite_eq_right hCopy]
    rw [hEmpty, List.nil_append]
    -- No copy: the modes agree, or the type holds no arrays.
    have hSame : source = target ∨ t.scalar = true := by
      cases source <;> cases target <;> simp_all
    rcases hSame with rfl | hScalar
    · exact hNext heap1 store1 s1 ws a (Nat.le_add_right _ _) fun _ => ⟨rfl, rfl⟩
    · refine hNext heap1 store1 s1 ws ⟨?_, a.frame, a.holds, ?_, ?_⟩ (Nat.le_add_right _ _)
        fun _ => ⟨rfl, rfl⟩
      · have hStep := a.step
        rw [Mode.fresh_scalar hScalar] at hStep ⊢
        exact hStep
      · cases target
        · exact a.rep.borrow
        · exact a.rep.owned hScalar
      · intro u y hy hm wy hwy hly b hb
        rw [Ty.regions_scalar t hScalar] at hb
        exact nomatch hb

end

/-- The traps that the code of `e` may have from `heap` at `store`: any, when a call that it makes
of a function whose code takes the call depth may lack its frames, as `fits` false states, and
otherwise those of allocation, when it may allocate and `top` cannot rise by `bound` within the
cap. -/
abbrev trapFlag {S : List Sig} {Γ : List Ty} {t : Ty} (m : Module) (e : Expr S Γ t)
    (slots : List Slot) (heap : Heap) (store : Store Unit) (bound : Nat) (fits : Bool) : Bool :=
  !fits ||
    ((e.aborts || slots.any (·.mode == .owned)) && !decide (heap.Within store m bound))

/-- The code of an expression, for the variables `live` live after it, pushes words that
represent its value: from any heap and store with the allocator invariant, in which the locals
have `h` positions, the variables live before the expression hold their values below position
`base`, and the positions from `base` on are free, the code ends as `After` states.  The flags
`paid` state which variables' potential counts.  The code may trap at `unreachable` only as
`trapFlag` allows for the potential of the paid owned variables that die plus the bound
`e.allocs`, and the frames `e.fits`, for callees with the flags `flags`, the bounds `bounds`, and
the frames `fits`.  When it finds its frames, `top` after the code, plus the potential of a paid
value, is at most `top` before it plus that sum.  The locals' parameters are `pv`, the function's arguments, which no
code changes. -/
def CodeSpec {S : List Sig} {Γ : List Ty} {t : Ty} (m : Module) (funs : Funs S)
    (flags : Flags S) (bounds : Bounds S) (fits : Fits S) (host : HostEnv Unit) (pv : List Value)
    (e : Expr S Γ t)
    (env : Env Γ) (slots : List Slot) (paid : List Bool) (live : Nat → Bool)
    (pool : Bytes.LiteralPool := Bytes.LiteralPool.empty) : Prop :=
  ∀ (h base : Nat) (heap : Heap) (store : Store Unit) (s : Locals), s.positions = h → s.params = pv →
    Holds env slots (fun i => live i || e.uses i) base heap store s → heap.At store →
    pool.Safe env slots (fun i => live i || e.uses i) heap store s →
    store.memoryCap m 0 ≤ 65535 → s.params.length ≤ base → base + e.width ≤ h →
    e.placeArgs = true →
    ∀ (rest : Program) (Q : Assertion Unit),
    TrapOK (trapFlag m e slots heap store
      (dyingPot store s env slots paid (fun i => live i || e.uses i) live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env) (e.fits funs fits env)) Q →
    (∀ heap' store' s' ws,
      After env slots (fun i => live i || e.uses i) live base heap store s t
        (e.mode (slots.map Slot.mode)) (e.denote funs env) heap' store' s' ws →
      (e.fits funs fits env = true →
        heap'.top.toNat +
            (if e.paid flags (slots.map Slot.mode) paid live then t.pot store' ws (e.denote funs env)
              else 0) ≤
          heap.top.toNat + dyingPot store s env slots paid (fun i => live i || e.uses i) live +
            e.allocs funs flags bounds (slots.map Slot.mode) paid live env) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) →
    wp m (e.code (pool := pool) h slots base live ++ rest) Q store s host

/-- The allowance of a part of an expression from that of the whole: the part calls a function
whose code takes the call depth only when the whole does, may allocate only when the whole may,
and, when the whole takes no call depth, has room for its bound when the whole has room for its
own. -/
theorem _root_.Wasm.TrapOK.part {Q : Assertion Unit} {d d' a a' : Bool} {P P' : Prop}
    [Decidable P] [Decidable P'] (h : TrapOK (d || (a && !decide P)) Q)
    (hd : d' = true → d = true) (ha : a' = true → a = true) (hP : d = false → P → P') :
    TrapOK (d' || (a' && !decide P')) Q := by
  cases hdv : d
  · have hd' : d' = false := by cases d' <;> simp_all
    refine h.of_imp fun h' => ?_
    simp only [hd', Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h'
    simp only [hdv, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    exact ⟨ha h'.1, fun hp => h'.2 (hP hdv hp)⟩
  · exact TrapOK.any (by simpa [hdv] using h)

/-- Room for `total` before a step that raises `top` by at most `c1` leaves room for any `c2`
with `c1 + c2 ≤ total` after it. -/
theorem _root_.LeanExe.Pipeline.Heap.Within.shift {heap heap1 : Heap} {store store1 : Store Unit}
    {m : Module} {total c1 c2 : Nat} (h : heap.Within store m total)
    (hTop : heap1.top.toNat ≤ heap.top.toNat + c1) (hc : c1 + c2 ≤ total)
    (hCaps : store1.memoryCap m 0 = store.memoryCap m 0) : heap1.Within store1 m c2 := by
  unfold Heap.Within at *; rw [hCaps]; omega

/-- Closes a fact that a part's frames or allocation flag implies the whole's. -/
macro "flag_tac" : tactic =>
  `(tactic| (
    intro h
    simp only [Expr.fits, Expr.aborts, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff]
      at h ⊢
    first | (simp [h]; done) | tauto))

/-- The bytes of a call's argument `i`: those of its code when it holds no arrays, those of its
owned code when its parameter is owned, and none for a borrowed place. -/
def argCost {S : List Sig} {Γ : List Ty} (funs : Funs S) (flags : Flags S) (bounds : Bounds S)
    (modesL : List Mode)
    (paidL : List Bool) (all kept : Nat → Bool) {ps : List Ty} (modes : Nat → Mode)
    (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) (env : Env Γ) (i : Fin ps.length) : Nat :=
  if (ps.get i).scalar then (args i).allocs funs flags bounds modesL paidL all env
  else if modes i = .owned then (args i).ownedCost modesL kept env else 0

/-- `ImplementsA` with the allocation bound `bound`: the call traps only when `aborts` holds and
`top` cannot rise by `bound x` within the cap, and it raises `top` by at most `bound x`. -/
def ImplementsB {α β : Type} [Represent α] [Represent β] (aborts : Bool) (m : Module) (entry : Nat)
    (f : α → β) (bound : α → Nat) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (params : List Value) (x : α),
    heap.At store → Represent.borrowed heap store params x →
    Separate store (Represent.moves store params x) (Represent.reads store params x) →
    store.memoryCap m 0 ≤ 65535 →
    Runs (aborts && !decide (heap.Within store m (bound x))) env m entry store params.reverse
      fun final values =>
      ∃ heap' : Heap, heap'.At final ∧ Represent.owned heap' final values.reverse (f x) ∧
        final.memoryCaps = store.memoryCaps ∧
        (∀ r, heap.Region r → 0 < r.2 → Apart store (Represent.moves store params x) r →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r ∧ Represent.outside final values.reverse (f x) r) ∧
        heap'.top.toNat ≤ heap.top.toNat + bound x

theorem fits_of_not {b : Bool} (h : (!b) = false) : b = true := by simpa using h

/-- The arguments of an environment that starts with the call depth. -/
def Env.dropDepth {Γ : List Ty} : Env (.word :: Γ) → Env Γ
  | .cons _ args => args

/-- The code at index `entry` computes `f` from the arguments that `pre` admits, with the heap and
store changed only as `ImplementsA` allows, for a call that may lack its frames.  The call traps
only when `fits x` fails, or when `aborts` holds and `top` cannot rise by the arguments' potential
`potIn` plus `bound x`.  When `fits x` holds, `top` after the call plus the result's potential
`potOut` is at most `top` before it plus the arguments' potential and `bound x`. -/
def ImplementsP {α β : Type} [Represent α] [Represent β] (pre : α → Prop) (fits : α → Bool)
    (potIn : Store Unit → List Value → α → Nat) (potOut : Store Unit → List Value → β → Nat)
    (aborts : Bool) (m : Module) (entry : Nat) (f : α → β) (bound : α → Nat)
    (pool : Bytes.LiteralPool := Bytes.LiteralPool.empty) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (params : List Value) (x : α),
    pre x → heap.At store → pool.Input heap store params x →
    Represent.borrowed heap store params x →
    Separate store (Represent.moves store params x) (Represent.reads store params x) →
    store.memoryCap m 0 ≤ 65535 →
    Runs (!fits x ||
        (aborts && !decide (heap.Within store m (potIn store params x + bound x)))) env m entry
      store params.reverse fun final values =>
      ∃ heap' : Heap, heap'.At final ∧ Represent.owned heap' final values.reverse (f x) ∧
        final.memoryCaps = store.memoryCaps ∧
        (∀ r, heap.Region r → 0 < r.2 → Apart store (Represent.moves store params x) r →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r ∧ Represent.outside final values.reverse (f x) r) ∧
        (fits x = true →
          heap'.top.toNat + potOut final values.reverse (f x) ≤
            heap.top.toNat + potIn store params x + bound x)

/-- The code at index `idx` computes `F`, the meaning of a function with signature `g`, with the
heap and store changed only as `ImplementsA` allows, as `ImplementsP` states with the potential of
the arguments at the parameters that the flags `pf` pick and, when `rf` holds, of the result:
from its arguments, within the allocation bound `A`, or, when the code takes the call depth, at
each depth that `D` admits, within `A` when its calls find their frames as `Fi` states. -/
def FunSpec (m : Module) (g : Sig) (idx : Nat) (F : Env g.params → g.result.denote)
    (pf : List Bool) (rf : Bool) (A : Env g.params → Nat) (Fi : Env g.params → Bool)
    (D : UInt64 → Prop) (pool : Bytes.LiteralPool := Bytes.LiteralPool.empty) : Prop :=
  (g.depth = false →
    @ImplementsP _ _ (Env.represent g.params g.modes) (Ty.represent g.result) (fun _ => True)
      (fun _ => true) (fun store ws x => Env.argPot store (g.paidSel pf) ws x)
      (fun store ws v => if rf then g.result.pot store ws v else 0) g.aborts m idx F A pool) ∧
  (g.depth = true → ∀ d, D d →
    @ImplementsP _ _ (Env.represent (.word :: g.params) (.borrowed :: g.modes))
      (Ty.represent g.result) (fun env => env.depthOf = d) (fun env => Fi env.dropDepth)
      (fun store ws x => Env.argPot store (g.depthSel pf) ws x)
      (fun store ws v => if rf then g.result.pot store ws v else 0) true m idx
      (depthMeaning F) (fun env => A env.dropDepth) pool) ∧
  ∃ fn, m.funcs[idx]? = some fn ∧ fn.numParams = (if g.depth then 1 else 0) + widthSum g.params

/-- The frames available to a function's code at call depth `d`: `depthLimit - d`. -/
def framesAt (d : UInt64) : Nat := depthLimit.toNat - d.toNat

/-- The functions that `funs` gives are the module's functions at their call indices, as
`FunSpec` states at every depth `d`, with the flags `flags`, and the bounds `bounds` and frames
`fits` at the frames available at `d`. -/
def Calls {S : List Sig} (m : Module) (funs : Funs S) (flags : Flags S) (bounds : Nat → Bounds S)
    (fits : Nat → Fits S) (pool : Bytes.LiteralPool := Bytes.LiteralPool.empty) : Prop :=
  ∀ {g : Sig} (f : FVar S g) (d : UInt64), FunSpec m g f.callIndex (funs.get f)
    (flags.params f) (flags.result f) ((bounds (framesAt d)).get f) ((fits (framesAt d)).get f)
    (fun d' => d' = d) pool

/-- The functions that code may call in a frame at call depth `d0`, with the flags `flags`, the
bounds `bounds`, and the frames `fits` of the callees: those whose code takes the call depth
compute their meanings at the next depth. -/
def CallsAt {S : List Sig} (m : Module) (funs : Funs S) (flags : Flags S) (bounds : Bounds S)
    (fits : Fits S) (d0 : UInt64) (pool : Bytes.LiteralPool := Bytes.LiteralPool.empty) : Prop :=
  ∀ {g : Sig} (f : FVar S g), FunSpec m g f.callIndex (funs.get f) (flags.params f)
    (flags.result f) (bounds.get f) (fits.get f) (fun d => d = d0 + 1) pool

theorem Calls.at {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Nat → Bounds S} {fits : Nat → Fits S} {pool : Bytes.LiteralPool}
    (h : Calls m funs flags bounds fits pool)
    (d0 : UInt64) :
    CallsAt m funs flags (bounds (framesAt (d0 + 1))) (fits (framesAt (d0 + 1))) d0 pool :=
  fun f => h f (d0 + 1)

/-- The potential of a call's arguments after the call depth is that of the arguments. -/
theorem Env.argPot_depthOf {store : Store Unit} {ps : List Ty} {sel : Nat → Bool}
    {ws : List Value} {d : UInt64} {args : Env ps} :
    Env.argPot store (depthSelOf sel) (.i64 d :: ws) (.cons (t := .word) d args) =
      Env.argPot store sel ws args := by
  simp only [Env.argPot, depthSelOf, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  rfl

theorem Env.argPot_depth {store : Store Unit} {g : Sig} {pf : List Bool} {ws : List Value}
    {d : UInt64} {args : Env g.params} :
    Env.argPot store (g.depthSel pf) (.i64 d :: ws) (.cons (t := .word) d args) =
      Env.argPot store (g.paidSel pf) ws args :=
  Env.argPot_depthOf

/-- A call of the function that `FunSpec` describes, from the words `ws` of its arguments above,
when its code takes the call depth, a depth `d` that `D` admits: the call returns words that
represent its value and changes the heap and store only as `ImplementsA` allows, or traps when the
function may trap and `top` cannot rise by the potential of the paid arguments plus its bound, or
when its code takes the depth and a call lacks its frames. -/
theorem FunSpec.runs {m : Module} {g : Sig} {idx : Nat} {F : Env g.params → g.result.denote}
    {pf : List Bool} {rf : Bool} {A : Env g.params → Nat} {Fi : Env g.params → Bool}
    {D : UInt64 → Prop} {pool : Bytes.LiteralPool}
    (hF : FunSpec m g idx F pf rf A Fi D pool) (hm : Runtime m)
    (host : HostEnv Unit)
    {heap : Heap} {store : Store Unit} {ws : List Value} {args : Env g.params}
    (hAt : heap.At store)
    (hInput : @Bytes.LiteralPool.Input (Env g.params) (Env.represent g.params g.modes)
      pool heap store ws args)
    (hRep : Env.Rep g.mode heap store ws args)
    (hSep : Separate store (Env.moves store g.mode ws args) (Env.reads store g.mode ws args))
    (hCap : store.memoryCap m 0 ≤ 65535) {d : UInt64} (hd : g.depth = true → D d)
    (rest : List Value) :
    Runs ((g.depth && !Fi args) ||
        ((g.aborts || g.depth) &&
          !decide (heap.Within store m (Env.argPot store (g.paidSel pf) ws args + A args))))
      host m idx store (ws.reverse ++ ((if g.depth then [.i64 d] else []) ++ rest))
      fun final values => ∃ out, values = out ++ rest ∧ ∃ heap' : Heap, heap'.At final ∧
        g.result.Rep .owned heap' final out.reverse (F args) ∧
        final.memoryCaps = store.memoryCaps ∧
        (∀ r, heap.Region r → 0 < r.2 → Apart store (Env.moves store g.mode ws args) r →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
          heap'.Region r ∧
          ∀ b ∈ g.result.blocks final out.reverse (F args), regionsDisjoint r b) ∧
        ((g.depth && !Fi args) = false →
          heap'.top.toNat + (if rf then g.result.pot final out.reverse (F args) else 0) ≤
            heap.top.toNat + Env.argPot store (g.paidSel pf) ws args + A args) := by
  obtain ⟨hFalse, hTrue, fn, hfn, hnum⟩ := hF
  cases hdep : g.depth
  · have hRun := (hFalse hdep host store heap ws args trivial hAt hInput hRep hSep hCap).append_args
      (by simp [hm.imports]) (by simpa [hm.imports] using hfn)
      (by simp [hRep.length, hnum, hdep]) rest
    simp only [Bool.false_and, Bool.false_or, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
      List.nil_append]
    exact hRun.mono fun final values ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, hTop⟩ =>
      ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, fun _ => hTop rfl⟩
  · have hSep' : Separate store
        (Env.moves store (paramMode (.word :: g.params) (.borrowed :: g.modes)) (.i64 d :: ws)
          (.cons (t := .word) d args))
        (Env.reads store (paramMode (.word :: g.params) (.borrowed :: g.modes)) (.i64 d :: ws)
          (.cons (t := .word) d args)) := by
      rw [Env.moves_depth, Env.reads_depth]; exact hSep
    have hRun := (hTrue hdep d (hd hdep) host store heap (.i64 d :: ws)
      (.cons (t := .word) d args) rfl hAt
      ⟨hInput.1, fun r hr => by
        change Apart store
          (Env.moves store (paramMode (.word :: g.params) (.borrowed :: g.modes))
            (.i64 d :: ws) (.cons (t := .word) d args)) r
        rw [Env.moves_depth]
        exact hInput.2 r hr⟩
      (Env.rep_depth.mpr ⟨ws, rfl, hRep⟩) hSep' hCap).append_args
      (by simp [hm.imports]) (by simpa [hm.imports] using hfn)
      (by simp [hRep.length, hnum, hdep]; omega) rest
    simp only [Bool.true_and, Bool.or_true, ↓reduceIte]
    rw [show ws.reverse ++ ([.i64 d] ++ rest) = (.i64 d :: ws).reverse ++ rest by simp]
    simp only [Env.argPot_depth] at hRun
    exact hRun.mono fun final values ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, hTop⟩ =>
      ⟨out, hv, heap', hAt', hOwned, hCaps, fun r hr hpos hA =>
        hRegions r hr hpos (by
          show Apart store (Env.moves store (paramMode (.word :: g.params) (.borrowed :: g.modes))
            (.i64 d :: ws) (.cons (t := .word) d args)) r
          rw [Env.moves_depth]; exact hA), fun h => hTop (fits_of_not h)⟩

theorem loopCost_succ_true {α : Type} {cc : α → Nat} {cond : α → Bool} {bc : UInt64 → α → Nat}
    {step : UInt64 → α → α} {n : Nat} {i : UInt64} {x : α} (h : cond x = true) :
    loopCost cc cond bc step (n + 1) i x = cc x + (bc i x + loopCost cc cond bc step n (i + 1)
      (step i x)) := by
  simp [loopCost, h]

theorem loopCost_succ_false {α : Type} {cc : α → Nat} {cond : α → Bool} {bc : UInt64 → α → Nat}
    {step : UInt64 → α → α} {n : Nat} {i : UInt64} {x : α} (h : cond x = false) :
    loopCost cc cond bc step (n + 1) i x = cc x := by
  simp [loopCost, h]

theorem loopCost_zero {α : Type} {cc : α → Nat} {cond : α → Bool} {bc : UInt64 → α → Nat}
    {step : UInt64 → α → α} {i : UInt64} {x : α} : loopCost cc cond bc step 0 i x = 0 := rfl

/-- The bytes of a loop's iterations from index `i`, with `n` indices left, at the state `x`, as
`Expr.allocs` counts them. -/
def Expr.loopRest {S : List Sig} {Γ : List Ty} {t : Ty} (funs : Funs S) (flags : Flags S)
    (bounds : Bounds S)
    (modes : List Mode) (paid : List Bool) (live : Nat → Bool) (init : Expr S Γ t)
    (cond : Expr S (t :: Γ) .bool)
    (body : Expr S (t :: .word :: Γ) t) (env : Env Γ) (n : Nat) (i : UInt64) (x : t.denote) :
    Nat :=
  loopCost
    (fun s => cond.allocs funs flags bounds (.borrowed :: modes) (false :: paid)
      (fun j => j == 0 || shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j)
      (.cons s env))
    (fun s => cond.denote funs (.cons s env))
    (fun i s =>
      body.allocs funs flags bounds (((init.mode modes).join (body.mode (.borrowed :: .borrowed ::
          modes))) :: .borrowed :: modes)
          (Expr.statePaid flags modes paid live init cond body :: false :: paid)
          (shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)))
          (.cons s (.cons i env)) +
        coerceCost t (body.mode (((init.mode modes).join (body.mode (.borrowed :: .borrowed ::
          modes))) :: .borrowed :: modes))
          ((init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes)))
          (body.denote funs (.cons s (.cons i env))))
    (fun i s => body.denote funs (.cons s (.cons i env))) n i x

theorem Expr.allocs_loop {S : List Sig} {Γ : List Ty} {t : Ty} (funs : Funs S)
    (flags : Flags S) (bounds : Bounds S) (modes : List Mode) (paid : List Bool) (live : Nat → Bool)
    (count : Expr S Γ .word)
    (init : Expr S Γ t) (cond : Expr S (t :: Γ) .bool) (body : Expr S (t :: .word :: Γ) t)
    (env : Env Γ) :
    (Expr.loop count init cond body).allocs funs flags bounds modes paid live env =
      count.allocs funs flags bounds modes paid
          (fun i => (live i || cond.uses (i + 1) || body.uses (i + 2)) || init.uses i) env +
        init.allocs funs flags bounds modes paid
            (fun i => live i || cond.uses (i + 1) || body.uses (i + 2))
          env +
        coerceCost t (init.mode modes)
          ((init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes)))
          (init.denote funs env) +
        (if Expr.statePaid flags modes paid live init cond body &&
            !init.paid flags modes paid (fun i => live i || cond.uses (i + 1) || body.uses (i + 2))
          then t.credit (init.denote funs env) else 0) +
        Expr.loopRest funs flags bounds modes paid live init cond body env (count.denote funs env).toNat 0
          (init.denote funs env) := rfl

theorem Expr.loopRest_true {S : List Sig} {Γ : List Ty} {t : Ty} {funs : Funs S}
    {flags : Flags S} {bounds : Bounds S} {modes : List Mode} {paid : List Bool}
    {live : Nat → Bool} {init : Expr S Γ t}
    {cond : Expr S (t :: Γ) .bool} {body : Expr S (t :: .word :: Γ) t} {env : Env Γ} {n : Nat}
    {i : UInt64} {x : t.denote} (h : cond.denote funs (.cons x env) = true) :
    Expr.loopRest funs flags bounds modes paid live init cond body env (n + 1) i x =
      cond.allocs funs flags bounds (.borrowed :: modes) (false :: paid)
          (fun j => j == 0 || shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j)
          (.cons x env) +
        (body.allocs funs flags bounds (((init.mode modes).join (body.mode (.borrowed :: .borrowed ::
            modes))) :: .borrowed :: modes)
            (Expr.statePaid flags modes paid live init cond body :: false :: paid)
            (shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)))
            (.cons x (.cons i env)) +
          coerceCost t (body.mode (((init.mode modes).join (body.mode (.borrowed :: .borrowed ::
            modes))) :: .borrowed :: modes))
            ((init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes)))
            (body.denote funs (.cons x (.cons i env))) +
          Expr.loopRest funs flags bounds modes paid live init cond body env n (i + 1)
            (body.denote funs (.cons x (.cons i env)))) := by
  unfold Expr.loopRest
  exact loopCost_succ_true (cond := fun s => cond.denote funs (.cons s env)) h

theorem Expr.loopRest_false {S : List Sig} {Γ : List Ty} {t : Ty} {funs : Funs S}
    {flags : Flags S} {bounds : Bounds S} {modes : List Mode} {paid : List Bool}
    {live : Nat → Bool} {init : Expr S Γ t}
    {cond : Expr S (t :: Γ) .bool} {body : Expr S (t :: .word :: Γ) t} {env : Env Γ} {n : Nat}
    {i : UInt64} {x : t.denote} (h : cond.denote funs (.cons x env) = false) :
    Expr.loopRest funs flags bounds modes paid live init cond body env (n + 1) i x =
      cond.allocs funs flags bounds (.borrowed :: modes) (false :: paid)
          (fun j => j == 0 || shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j)
          (.cons x env) := by
  unfold Expr.loopRest
  exact loopCost_succ_false (cond := fun s => cond.denote funs (.cons s env)) h

theorem Expr.loopRest_zero {S : List Sig} {Γ : List Ty} {t : Ty} {funs : Funs S}
    {flags : Flags S} {bounds : Bounds S} {modes : List Mode} {paid : List Bool}
    {live : Nat → Bool} {init : Expr S Γ t}
    {cond : Expr S (t :: Γ) .bool} {body : Expr S (t :: .word :: Γ) t} {env : Env Γ}
    {i : UInt64} {x : t.denote} :
    Expr.loopRest funs flags bounds modes paid live init cond body env 0 i x = 0 := rfl

/-- Whether a loop's passes from index `i`, with `n` indices left, from the state `x`, find their
frames, as `Expr.fits` states for the loop. -/
def Expr.loopFitsRest {S : List Sig} {Γ : List Ty} {t : Ty} (funs : Funs S) (fits : Fits S)
    (cond : Expr S (t :: Γ) .bool) (body : Expr S (t :: .word :: Γ) t) (env : Env Γ) (n : Nat)
    (i : UInt64) (x : t.denote) : Bool :=
  loopFits (fun s => cond.fits funs fits (.cons s env)) (fun s => cond.denote funs (.cons s env))
    (fun i s => body.fits funs fits (.cons s (.cons i env)))
    (fun i s => body.denote funs (.cons s (.cons i env))) n i x

theorem Expr.loopFitsRest_cond {S : List Sig} {Γ : List Ty} {t : Ty} {funs : Funs S}
    {fits : Fits S} {cond : Expr S (t :: Γ) .bool} {body : Expr S (t :: .word :: Γ) t}
    {env : Env Γ} {n : Nat} {i : UInt64} {x : t.denote}
    (h : Expr.loopFitsRest funs fits cond body env (n + 1) i x = true) :
    cond.fits funs fits (.cons x env) = true := by
  simp only [Expr.loopFitsRest, loopFits, Bool.and_eq_true] at h; exact h.1

theorem Expr.loopFitsRest_body {S : List Sig} {Γ : List Ty} {t : Ty} {funs : Funs S}
    {fits : Fits S} {cond : Expr S (t :: Γ) .bool} {body : Expr S (t :: .word :: Γ) t}
    {env : Env Γ} {n : Nat} {i : UInt64} {x : t.denote}
    (h : Expr.loopFitsRest funs fits cond body env (n + 1) i x = true)
    (hc : cond.denote funs (.cons x env) = true) :
    body.fits funs fits (.cons x (.cons i env)) = true ∧
      Expr.loopFitsRest funs fits cond body env n (i + 1)
        (body.denote funs (.cons x (.cons i env))) = true := by
  simp only [Expr.loopFitsRest, loopFits, hc, ↓reduceIte, Bool.and_eq_true] at h
  exact h.2

/-- Room for `total` gives room for `c` at a heap whose `top` plus `c` stays within the first
heap's `top` plus `total`. -/
theorem _root_.LeanExe.Pipeline.Heap.Within.of_le {heap heap1 : Heap} {store store1 : Store Unit}
    {m : Module} {total c : Nat} (h : heap.Within store m total)
    (hle : heap1.top.toNat + c ≤ heap.top.toNat + total)
    (hCaps : store1.memoryCap m 0 = store.memoryCap m 0) : heap1.Within store1 m c := by
  unfold Heap.Within at *; rw [hCaps]; omega

theorem Expr.loopRest_cond_le {S : List Sig} {Γ : List Ty} {t : Ty} {funs : Funs S}
    {flags : Flags S} {bounds : Bounds S} {modes : List Mode} {paid : List Bool}
    {live : Nat → Bool} {init : Expr S Γ t}
    {cond : Expr S (t :: Γ) .bool} {body : Expr S (t :: .word :: Γ) t} {env : Env Γ} {n : Nat}
    {i : UInt64} {x : t.denote} :
    cond.allocs funs flags bounds (.borrowed :: modes) (false :: paid)
        (fun j => j == 0 || shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j)
        (.cons x env) ≤
      Expr.loopRest funs flags bounds modes paid live init cond body env (n + 1) i x := by
  cases h : cond.denote funs (.cons x env)
  · rw [Expr.loopRest_false h]
  · rw [Expr.loopRest_true h]; omega

theorem sumBelow_mono (f : Nat → Nat) {i j : Nat} (h : i ≤ j) : sumBelow f i ≤ sumBelow f j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hl | hg
    · have := ih (by omega); simp only [sumBelow]; omega
    · rw [show i = j + 1 by omega]

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit}
  {pv : List Value}

/-- A fact under `(!b) = false` holds under `b = true`. -/
theorem fitsOf {b : Bool} {P : Prop} (h : (!b) = false → P) (hb : b = true) : P :=
  h (by simp [hb])


/-- An expression's bound with the potentials, from the bound without them, when its value is not
paid. -/
theorem top_unpaid {top' top dying allocs pot : Nat} {paid : Bool} (hp : paid = false)
    (h : top' ≤ top + dying + allocs) :
    top' + (if paid then pot else 0) ≤ top + dying + allocs := by
  subst hp; simpa using h

theorem top_unpaid_le {top' top dying allocs pot : Nat} {paid : Bool} (hp : paid = false)
    (h : top' ≤ top + allocs) : top' + (if paid then pot else 0) ≤ top + dying + allocs := by
  subst hp; simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega

/-- The bound of a whole whose value is a scalar from the bound of its part, whose dying potential
is at most the whole's and whose bound is the whole's. -/
theorem top_part {top' top d d' a pot1 pot2 : Nat} {p1 p2 : Bool} (hp2 : pot2 = 0) (hd : d' ≤ d)
    (h : top' + (if p1 then pot1 else 0) ≤ top + d' + a) :
    top' + (if p2 then pot2 else 0) ≤ top + d + a := by
  subst hp2; split <;> split at h <;> omega

/-- The bound of a moved variable: when it is paid, its potential is among the dying ones. -/
theorem top_move {Γ : List Ty} {env : Env Γ} {slots : List Slot} {paid : List Bool}
    {live : Nat → Bool} {store : Store Unit} {s : Locals} {t : Ty} (x : Var Γ t)
    {ws : List Value} {top a : Nat}
    (hold : LocalsHold s (slots.getD x.index default).loc t.types ws) (hl : ws.length = t.width)
    (hOwned : (slots.getD x.index default).mode = .owned) (hDead : live x.index = false) :
    top + (if (Expr.var (S := S) x).paid flags (slots.map Slot.mode) paid live then
        t.pot store ws (env.get x) else 0) ≤
      top + dyingPot store s env slots paid (fun i => live i || (Expr.var (S := S) x).uses i)
        live + a := by
  split
  · next hp =>
    simp only [Expr.paid, modeAt, Slot.modes_getD, hOwned, hDead, beq_self_eq_true,
      Bool.not_false, Bool.true_and] at hp
    have := dyingPot_var (store := store) (s := s) (env := env) (paid := paid)
      (liveIn := fun i => live i || (Expr.var (S := S) x).uses i) x (by simp [Expr.uses]) hDead
      hp hOwned
    rw [Env.potOf, hold.read_eq (by rw [hl, Ty.types_length])] at this
    omega
  · omega

/-- Two parts of an expression in sequence: the parts trap only as the whole's allowance
`d || (a && …)` allows for the potential of the paid owned variables that die in the whole and the
sum of their bounds, and, when the whole finds its frames, `top` rises by at most that sum.  The
variables that die in the whole are those that die in the first part and those that die in the
second, and the potential of the second's lies in blocks that the first keeps. -/
theorem seq_spec {Γ : List Ty} {t u : Ty} {l : Expr S Γ t} {r : Expr S Γ u}
    {pool : Bytes.LiteralPool}
    (lSpec : ∀ env slots paid live,
      CodeSpec m funs flags bounds fits host pv l env slots paid live pool)
    (rSpec : ∀ env slots paid live,
      CodeSpec m funs flags bounds fits host pv r env slots paid live pool)
    (env : Env Γ) (slots : List Slot) (paid : List Bool) (live : Nat → Bool) (h base : Nat)
    (heap : Heap) (store : Store Unit) (s : Locals) (hh : s.positions = h) (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || (l.uses i || r.uses i)) base heap store s)
    (hAt : heap.At store)
    (hSafe : pool.Safe env slots (fun i => live i || (l.uses i || r.uses i)) heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoomL : base + l.width ≤ h) (hRoomR : base + r.width ≤ h)
    (hPlaceL : l.placeArgs = true) (hPlaceR : r.placeArgs = true) (rest : Program)
    (Q : Assertion Unit) {d a : Bool}
    (hTrap : TrapOK (d || (a && !decide (heap.Within store m
      (dyingPot store s env slots paid (fun i => live i || (l.uses i || r.uses i)) live +
        (l.allocs funs flags bounds (slots.map Slot.mode) paid (fun i => live i || r.uses i) env +
          r.allocs funs flags bounds (slots.map Slot.mode) paid live env))))) Q)
    (hdl : (!l.fits funs fits env) = true → d = true)
    (hdr : (!r.fits funs fits env) = true → d = true)
    (hal : (l.aborts || slots.any (·.mode == .owned)) = true → a = true)
    (har : (r.aborts || slots.any (·.mode == .owned)) = true → a = true)
    (hNext : ∀ heap2 store2 s2 ws1 ws2,
      Step heap store (Holds.KeepDying env slots (fun i => live i || (l.uses i || r.uses i)) live
          store s) heap2 store2
        ((l.mode (slots.map Slot.mode)).fresh store2 t ws1 (l.denote funs env) ++
          (r.mode (slots.map Slot.mode)).fresh store2 u ws2 (r.denote funs env)) →
      Frame base s s2 → Holds env slots live base heap2 store2 s2 →
      t.Rep (l.mode (slots.map Slot.mode)) heap2 store2 ws1 (l.denote funs env) →
      u.Rep (r.mode (slots.map Slot.mode)) heap2 store2 ws2 (r.denote funs env) →
      Holds.Apart env slots live store2 s2 t (l.mode (slots.map Slot.mode)) ws1
        (l.denote funs env) →
      Holds.Apart env slots live store2 s2 u (r.mode (slots.map Slot.mode)) ws2
        (r.denote funs env) →
      (∀ x ∈ t.regions (l.mode (slots.map Slot.mode)) store2 ws1 (l.denote funs env),
        ∀ y ∈ (r.mode (slots.map Slot.mode)).fresh store2 u ws2 (r.denote funs env),
          regionsDisjoint x y) →
      (d = false → heap2.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid (fun i => live i || (l.uses i || r.uses i)) live +
        (l.allocs funs flags bounds (slots.map Slot.mode) paid (fun i => live i || r.uses i) env +
          r.allocs funs flags bounds (slots.map Slot.mode) paid live env)) →
      wp m rest Q store2 { s2 with values := ws2.reverse ++ (ws1.reverse ++ s.values) } host) :
    wp m (l.code (pool := pool) h slots base (fun i => live i || r.uses i) ++
      (r.code (pool := pool) h slots base live ++ rest))
      Q store s host := by
  have hIn : ∀ i, (live i || r.uses i || l.uses i) = true →
      (live i || (l.uses i || r.uses i)) = true := fun i h => live_seq _ _ _ h
  have hVarsL := hVars.live_mono hIn
  have hdl' : d = false → l.fits funs fits env = true := fun hd => by
    cases hl : l.fits funs fits env
    · rw [hdl (by simp [hl])] at hd; exact nomatch hd
    · rfl
  have hdr' : d = false → r.fits funs fits env = true := fun hd => by
    cases hr : r.fits funs fits env
    · rw [hdr (by simp [hr])] at hd; exact nomatch hd
    · rfl
  have hSplit : dyingPot store s env slots paid (fun i => live i || (l.uses i || r.uses i)) live =
      dyingPot store s env slots paid (fun i => live i || r.uses i || l.uses i)
          (fun i => live i || r.uses i) +
        dyingPot store s env slots paid (fun i => live i || r.uses i) live := by
    rw [dyingPot_split _ (fun i => live i || r.uses i) _ (fun i h => by simp_all)
      (fun i h => by simp [h])]
    congr 1
    exact dyingPot_congr (fun i => by
      cases live i <;> cases l.uses i <;> cases r.uses i <;> rfl) fun _ => rfl
  refine lSpec env slots paid _ h base heap store s hh hpv hVarsL hAt (hSafe.mono hIn)
    hCap hBase hRoomL hPlaceL _ _
      (hTrap.part hdl hal fun _ hw => hw.mono (by rw [hSplit]; omega))
    fun heap1 store1 s1 ws1 a1 hTop1 => ?_
  have hDr : dyingPot store1 { s1 with values := ws1.reverse ++ s.values } env slots paid
      (fun i => live i || r.uses i) live =
        dyingPot store s env slots paid (fun i => live i || r.uses i) live := by
    rw [dyingPot_values]
    exact dyingPot_after hVarsL a1 (fun i h => by simp [h]) _ _ fun _ h => h
  refine rSpec env slots paid live h base heap1 store1 { s1 with values := ws1.reverse ++ s.values }
    (a1.frame.positions.trans hh) (a1.frame.params.trans hpv) (a1.holds.agree Frame.ofValues)
    a1.step.at_
    (((hSafe.mono hIn).after hVarsL a1 (fun i hi => by simp [hi])).1.values _)
    (by rw [a1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base; rw [a1.frame.params]; exact hBase) hRoomR hPlaceR _ _
    (hTrap.part hdr har fun hd hw => by
      have := hTop1 (hdl' hd)
      rw [hDr]
      exact hw.shift
          (c1 := dyingPot store s env slots paid (fun i => live i || r.uses i || l.uses i)
          (fun i => live i || r.uses i) +
          l.allocs funs flags bounds (slots.map Slot.mode) paid (fun i => live i || r.uses i) env)
        (by omega) (by rw [hSplit]; omega) (a1.step.cap m))
    fun heap2 store2 s2 ws2 a2 hTop2 => ?_
  obtain ⟨hStep, hFrame, hRep1, hApart1, hDisjoint⟩ :=
    After.seq hVarsL a1 a2 (fun i h => by simp [h]) fun i h => by simp [h]
  exact hNext heap2 store2 s2 ws1 ws2
    (hStep.mono (fun _ hr => hr.mono fun i h1 h2 => ⟨hIn i h1, h2⟩) fun _ hb => hb) hFrame
    a2.holds hRep1 a2.rep hApart1 a2.apart hDisjoint fun hd => by
      have := hTop1 (hdl' hd); have := hTop2 (hdr' hd); rw [hDr] at this; rw [hSplit]; omega

end Cases

end Verified
