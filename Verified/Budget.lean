import Verified.Correct

/-! The compiler's correctness theorem with the allocation bound: the code of an expression traps
only through a call of a function whose code takes the call depth, or when `top` cannot rise by
the expression's bound, `Expr.allocs`, within the memory cap, and it raises `top` by at most that
bound. -/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- The traps that the code of `e` may have from `heap` at `store`: any, when it calls a function
whose code takes the call depth, and otherwise those of allocation, when it may allocate and `top`
cannot rise by `bound` within the cap. -/
abbrev trapFlag {S : List Sig} {Γ : List Ty} {t : Ty} (m : Module) (e : Expr S Γ t)
    (slots : List Slot) (heap : Heap) (store : Store Unit) (bound : Nat) : Bool :=
  e.depthCalls ||
    ((e.aborts || slots.any (·.mode == .owned)) && !decide (heap.Within store m bound))

/-- `CodeSpec` with the allocation bound: the code may trap only as `trapFlag` allows for the
bound `e.allocs`, and, when it takes no call depth, it raises `top` by at most that bound. -/
def CodeSpecB {S : List Sig} {Γ : List Ty} {t : Ty} (m : Module) (funs : Funs S)
    (bounds : Bounds S) (host : HostEnv Unit) (pv : List Value) (e : Expr S Γ t) (env : Env Γ)
    (slots : List Slot) (live : Nat → Bool) : Prop :=
  ∀ (h base : Nat) (heap : Heap) (store : Store Unit) (s : Locals), s.half = h → s.params = pv →
    Holds env slots (fun i => live i || e.uses i) base heap store s → heap.At store →
    store.memoryCap m 0 ≤ 65535 → s.params.length ≤ base → base + e.width ≤ h →
    e.placeArgs = true →
    ∀ (rest : Program) (Q : Assertion Unit),
    TrapOK (trapFlag m e slots heap store (e.allocs funs bounds (slots.map Slot.mode) live env))
      Q →
    (∀ heap' store' s' ws,
      After env slots (fun i => live i || e.uses i) live base heap store s t
        (e.mode (slots.map Slot.mode)) (e.denote funs env) heap' store' s' ws →
      (e.depthCalls = false →
        heap'.top.toNat ≤ heap.top.toNat + e.allocs funs bounds (slots.map Slot.mode) live env) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) →
    wp m (e.code h slots base live ++ rest) Q store s host

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

/-- Closes a fact that a part's call-depth or allocation flag implies the whole's. -/
macro "flag_tac" : tactic =>
  `(tactic| (intro h; simp only [Expr.depthCalls, Expr.aborts, Bool.or_eq_true] at h ⊢; tauto))

/-- The bytes of a call's argument `i`: those of its code when it holds no arrays, those of its
owned code when its parameter is owned, and none for a borrowed place. -/
def argCost {S : List Sig} {Γ : List Ty} (funs : Funs S) (bounds : Bounds S) (modesL : List Mode)
    (all kept : Nat → Bool) {ps : List Ty} (modes : Nat → Mode)
    (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) (env : Env Γ) (i : Fin ps.length) : Nat :=
  if (ps.get i).scalar then (args i).allocs funs bounds modesL all env
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

/-- `FunSpec` with the allocation bound `A`: a function whose code takes no call depth is
`ImplementsB` for `A`, and one whose code takes it is as `FunSpec` states. -/
def FunSpecB (m : Module) (g : Sig) (idx : Nat) (F : Env g.params → g.result.denote)
    (A : Env g.params → Nat) (D : UInt64 → Prop) : Prop :=
  (g.depth = false →
    @ImplementsB _ _ (Env.represent g.params g.modes) (Ty.represent g.result) g.aborts m idx F A) ∧
  (g.depth = true → ∀ d, D d →
    @ImplementsA _ _ (Env.represent (.word :: g.params) (.borrowed :: g.modes))
      (Ty.represent g.result) true m idx (depthMeaning F) (fun env _ _ => env.depthOf = d)
      (fun _ _ _ _ _ => True)) ∧
  ∃ fn, m.funcs[idx]? = some fn ∧ fn.numParams = (if g.depth then 1 else 0) + widthSum g.params

/-- `Calls` with the bounds `bounds`. -/
def CallsB {S : List Sig} (m : Module) (funs : Funs S) (bounds : Bounds S) : Prop :=
  ∀ {g : Sig} (f : FVar S g), FunSpecB m g f.callIndex (funs.get f) (bounds.get f) (fun _ => True)

/-- `CallsAt` with the bounds `bounds`. -/
def CallsAtB {S : List Sig} (m : Module) (funs : Funs S) (bounds : Bounds S) (d0 : UInt64) :
    Prop :=
  ∀ {g : Sig} (f : FVar S g), FunSpecB m g f.callIndex (funs.get f) (bounds.get f)
    (fun d => d = d0 + 1)

theorem CallsB.at {S : List Sig} {m : Module} {funs : Funs S} {bounds : Bounds S}
    (h : CallsB m funs bounds) (d0 : UInt64) : CallsAtB m funs bounds d0 :=
  fun f => ⟨(h f).1, fun hd d _ => (h f).2.1 hd d trivial, (h f).2.2⟩

/-- `callMoves` reads only the slots' modes. -/
theorem callMovesAt_eq {S : List Sig} {Γ : List Ty} {g : Sig} (slots : List Slot)
    (live : Nat → Bool) (args : (i : Fin g.params.length) → Expr S Γ (g.params.get i)) :
    callMovesAt (slots.map Slot.mode) live args = callMoves slots live args := by
  funext i
  cases hv : (args i).varIndex? <;> simp only [callMovesAt, callMoves, hv, modeAt, Slot.modes_getD]

/-- A call of the function that `FunSpec` describes, from the words `ws` of its arguments above,
when its code takes the call depth, a depth `d` that `D` admits: the call returns words that
represent its value and changes the heap and store only as `ImplementsA` allows, or traps when the
function may trap and `top` cannot rise by its bound, or its code takes the depth. -/
theorem FunSpecB.runs {m : Module} {g : Sig} {idx : Nat} {F : Env g.params → g.result.denote}
    {A : Env g.params → Nat} {D : UInt64 → Prop} (hF : FunSpecB m g idx F A D) (hm : Runtime m)
    (host : HostEnv Unit)
    {heap : Heap} {store : Store Unit} {ws : List Value} {args : Env g.params}
    (hAt : heap.At store) (hRep : Env.Rep g.mode heap store ws args)
    (hSep : Separate store (Env.moves g.mode ws args) (Env.reads g.mode ws args))
    (hCap : store.memoryCap m 0 ≤ 65535) {d : UInt64} (hd : g.depth = true → D d)
    (rest : List Value) :
    Runs ((g.aborts && !decide (heap.Within store m (A args))) || g.depth) host m idx store
      (ws.reverse ++ ((if g.depth then [.i64 d] else []) ++ rest))
      fun final values => ∃ out, values = out ++ rest ∧ ∃ heap' : Heap, heap'.At final ∧
        g.result.Rep .owned heap' final out.reverse (F args) ∧
        final.memoryCaps = store.memoryCaps ∧
        (∀ r, heap.Region r → 0 < r.2 → Apart store (Env.moves g.mode ws args) r →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
          heap'.Region r ∧
          ∀ b ∈ g.result.blocks final out.reverse (F args), regionsDisjoint r b) ∧
        (g.depth = false → heap'.top.toNat ≤ heap.top.toNat + A args) := by
  obtain ⟨hFalse, hTrue, fn, hfn, hnum⟩ := hF
  cases hdep : g.depth
  · have hRun := (hFalse hdep host store heap ws args hAt hRep hSep hCap).append_args
      (by simp [hm.imports]) (by simpa [hm.imports] using hfn)
      (by simp [hRep.length, hnum, hdep]) rest
    simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    exact hRun.mono fun final values ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, hTop⟩ =>
      ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, fun _ => hTop⟩
  · have hSep' : Separate store
        (Env.moves (paramMode (.word :: g.params) (.borrowed :: g.modes)) (.i64 d :: ws)
          (.cons (t := .word) d args))
        (Env.reads (paramMode (.word :: g.params) (.borrowed :: g.modes)) (.i64 d :: ws)
          (.cons (t := .word) d args)) := by
      rw [Env.moves_depth, Env.reads_depth]; exact hSep
    have hRun := (hTrue hdep d (hd hdep) host store heap (.i64 d :: ws)
      (.cons (t := .word) d args) hAt rfl
      (Env.rep_depth.mpr ⟨ws, rfl, hRep⟩) hSep' hCap).append_args
      (by simp [hm.imports]) (by simpa [hm.imports] using hfn)
      (by simp [hRep.length, hnum, hdep]; omega) rest
    simp only [Bool.or_true, ↓reduceIte]
    rw [show ws.reverse ++ ([.i64 d] ++ rest) = (.i64 d :: ws).reverse ++ rest by simp]
    exact hRun.mono fun final values ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, _⟩ =>
      ⟨out, hv, heap', hAt', hOwned, hCaps, fun r hr hpos hA =>
        hRegions r hr hpos (by
          show Apart store (Env.moves (paramMode (.word :: g.params) (.borrowed :: g.modes))
            (.i64 d :: ws) (.cons (t := .word) d args)) r
          rw [Env.moves_depth]; exact hA), nofun⟩

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {bounds : Bounds S} {host : HostEnv Unit}
  {pv : List Value}

/-- `seq_spec` with the allocation bound: the two parts trap only as the whole's allowance
`d || (a && …)` allows for the sum of their bounds, and, when the whole takes no call depth,
`top` rises by at most that sum. -/
theorem seq_specB {Γ : List Ty} {t u : Ty} {l : Expr S Γ t} {r : Expr S Γ u}
    (lSpec : ∀ env slots live, CodeSpecB m funs bounds host pv l env slots live)
    (rSpec : ∀ env slots live, CodeSpecB m funs bounds host pv r env slots live)
    (env : Env Γ) (slots : List Slot) (live : Nat → Bool) (h base : Nat) (heap : Heap)
    (store : Store Unit) (s : Locals) (hh : s.half = h) (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || (l.uses i || r.uses i)) base heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoomL : base + l.width ≤ h) (hRoomR : base + r.width ≤ h)
    (hPlaceL : l.placeArgs = true) (hPlaceR : r.placeArgs = true) (rest : Program)
    (Q : Assertion Unit) {d a : Bool}
    (hTrap : TrapOK (d || (a && !decide (heap.Within store m
      (l.allocs funs bounds (slots.map Slot.mode) (fun i => live i || r.uses i) env +
        r.allocs funs bounds (slots.map Slot.mode) live env)))) Q)
    (hdl : l.depthCalls = true → d = true) (hdr : r.depthCalls = true → d = true)
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
        (l.allocs funs bounds (slots.map Slot.mode) (fun i => live i || r.uses i) env +
          r.allocs funs bounds (slots.map Slot.mode) live env)) →
      wp m rest Q store2 { s2 with values := ws2.reverse ++ (ws1.reverse ++ s.values) } host) :
    wp m (l.code h slots base (fun i => live i || r.uses i) ++ (r.code h slots base live ++ rest))
      Q store s host := by
  have hIn : ∀ i, (live i || r.uses i || l.uses i) = true →
      (live i || (l.uses i || r.uses i)) = true := fun i h => live_seq _ _ _ h
  have hVarsL := hVars.live_mono hIn
  have hdl' : d = false → l.depthCalls = false := fun hd => by
    cases hl : l.depthCalls
    · rfl
    · rw [hdl hl] at hd; exact nomatch hd
  have hdr' : d = false → r.depthCalls = false := fun hd => by
    cases hr : r.depthCalls
    · rfl
    · rw [hdr hr] at hd; exact nomatch hd
  refine lSpec env slots _ h base heap store s hh hpv hVarsL hAt hCap hBase hRoomL hPlaceL _ _
      (hTrap.part hdl hal fun _ hw => hw.mono (Nat.le_add_right _ _))
    fun heap1 store1 s1 ws1 a1 hTop1 => ?_
  refine rSpec env slots live h base heap1 store1 { s1 with values := ws1.reverse ++ s.values }
    (a1.frame.half.trans hh) (a1.frame.params.trans hpv) (a1.holds.agree Frame.ofValues)
    a1.step.at_
    (by rw [a1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base; rw [a1.frame.params]; exact hBase) hRoomR hPlaceR _ _
    (hTrap.part hdr har fun hd hw => hw.after (hTop1 (hdl' hd)) (a1.step.cap m))
    fun heap2 store2 s2 ws2 a2 hTop2 => ?_
  obtain ⟨hStep, hFrame, hRep1, hApart1, hDisjoint⟩ :=
    After.seq hVarsL a1 a2 (fun i h => by simp [h]) fun i h => by simp [h]
  exact hNext heap2 store2 s2 ws1 ws2
    (hStep.mono (fun _ hr => hr.mono fun i h1 h2 => ⟨hIn i h1, h2⟩) fun _ hb => hb) hFrame
    a2.holds hRep1 a2.rep hApart1 a2.apart hDisjoint fun hd => by
      have := hTop1 (hdl' hd); have := hTop2 (hdr' hd); omega

/-- A constant word. -/
theorem specB_word {Γ : List Ty} (value : UInt64) :
    ∀ env slots live,
      CodeSpecB m funs bounds host pv (Expr.word (S := S) (Γ := Γ) value) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt _ _ _ _ rest Q _ hNext
  have hNext0 := fun store' s' ws a =>
    hNext heap store' s' ws a (fun _ => Nat.le_add_right _ _)
  simpa [Expr.code, Expr.denote] using
    hNext0 store s [.i64 value] (After.refl hAt hVars (by intro i h; simp [h]) rfl
      (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .word rfl] at hb; exact nomatch hb)


/-- A constant `Bool`. -/
theorem specB_bool {Γ : List Ty} (value : Bool) :
    ∀ env slots live,
      CodeSpecB m funs bounds host pv (Expr.bool (S := S) (Γ := Γ) value) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt _ _ _ _ rest Q _ hNext
  have hNext0 := fun store' s' ws a =>
    hNext heap store' s' ws a (fun _ => Nat.le_add_right _ _)
  simpa [Expr.code, Expr.denote] using
    hNext0 store s [.i64 (boolWord value)] (After.refl hAt hVars (by intro i h; simp [h]) rfl
      (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .bool rfl] at hb; exact nomatch hb)


/-- A float constant, from its bit pattern. -/
theorem specB_float {Γ : List Ty} (bits : UInt64) :
    ∀ env slots live,
      CodeSpecB m funs bounds host pv (Expr.float (S := S) (Γ := Γ) bits) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt _ _ _ _ rest Q _ hNext
  have hNext0 := fun store' s' ws a =>
    hNext heap store' s' ws a (fun _ => Nat.le_add_right _ _)
  simpa [Expr.code, Expr.denote, F64Bits.toBits_ofBits] using
    hNext0 store s [.f64 (Float.ofBits bits).toBits] (After.refl hAt hVars
      (by intro i h; simp [h]) rfl (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .float rfl] at hb; exact nomatch hb)


/-- An operation on words; division and remainder save their operands to test the divisor. -/
theorem specB_bin {Γ : List Ty} (op : BinOp) {left right : Expr S Γ .word}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.bin op left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max op.scratch (max left.width right.width) :=
    (Nat.le_max_left ..).trans (Nat.le_max_right ..)
  have hR : right.width ≤ max op.scratch (max left.width right.width) :=
    (Nat.le_max_right ..).trans (Nat.le_max_right ..)
  have hS : op.scratch ≤ max op.scratch (max left.width right.width) := Nat.le_max_left ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  simp only [Ty.rep_word] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  cases op
  case div | rem =>
    have hW2 : base + 2 ≤ h := by
      have := hRoom
      simp only [Expr.width, BinOp.scratch] at this
      omega
    have hp2 : s2.params = s.params := hF.params
    have hh2 : s2.half = h := hF.half.trans hh
    simp only [BinOp.code, List.cons_append, List.nil_append]
    refine wp_localSet_local (by rw [hp2]; omega)
      (Locals.lt_total (show base + 1 < ({ s2 with values := _ } : Locals).half by
        rw [Locals.half_values, hh2]; omega)) ?_
    refine wp_localSet_local (vs := s.values)
      (s := setLocal { s2 with values := .i64 (left.denote funs env) :: s.values } (base + 1)
        (.i64 (right.denote funs env)))
      (by show s2.params.length ≤ base; rw [hp2]; omega)
      (Locals.lt_total (by simp only [Locals.half_setLocal, Locals.half_values]; omega)) ?_
    let s2a := setLocal { s2 with values := .i64 (left.denote funs env) :: s.values } (base + 1)
      (.i64 (right.denote funs env))
    let s2b := setLocal { s2a with values := s.values } base (.i64 (left.denote funs env))
    show wp m _ Q store2 s2b host
    have hLowA : ({ s2 with values := .i64 (left.denote funs env) :: s.values } :
        Locals).params.length ≤ base + 1 := by
      show s2.params.length ≤ base + 1; rw [hp2]; omega
    have hLowB : ({ s2a with values := s.values } : Locals).params.length ≤ base := by
      show s2.params.length ≤ base; rw [hp2]; omega
    have hRightSlot : s2b.get (base + 1) = some (.i64 (right.denote funs env)) := by
      rw [Locals.get_setLocal_ne hLowB (by omega), Locals.get_values]
      exact Locals.get_setLocal_same hLowA
        (Locals.lt_total (by simp only [Locals.half_values]; omega))
    have hLeftSlot : s2b.get base = some (.i64 (left.denote funs env)) :=
      Locals.get_setLocal_same hLowB
        (Locals.lt_total (by simp only [s2a, Locals.half_setLocal, Locals.half_values]; omega))
    have hF2 : Frame base s2 s2b :=
      (Frame.setValues (s := s2) (vs := .i64 (left.denote funs env) :: s.values)
        (v := .i64 (right.denote funs env)) (by rw [hp2]; omega) (by omega) (by omega)).trans
        (Frame.setValues (s := s2a) (vs := s.values) (v := .i64 (left.denote funs env))
          (by show s2.params.length ≤ base; rw [hp2]; omega) le_rfl
          (by simp only [s2a, Locals.half_setLocal, Locals.half_values]; omega))
    have hFrame : Frame base s s2b := hF.trans hF2
    have hHolds : Holds env slots live base heap2 store2 s2b := hH.agree hF2
    have hs2b : s2b.values = s.values := rfl
    simp only [wp_localGet_cons, hRightSlot, wp_eqzI64_cons]
    rw [wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    by_cases hZero : right.denote funs env = 0
    · simp only [hZero, ite_true, ne_eq]
      simpa [-Locals.get, hLeftSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
        hNext2 store2 s2b _ (After.ofScalar rfl hStep' rfl hFrame hHolds rfl)
    · simp only [hZero, ite_false, ne_eq, not_true_eq_false]
      simpa [-Locals.get, hLeftSlot, hRightSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
        hNext2 store2 s2b _ (After.ofScalar rfl hStep' rfl hFrame hHolds rfl)
  all_goals
    simpa [BinOp.code, Expr.denote, BinOp.apply, ← UInt64.shiftLeft_eq_shiftLeft_mod,
      ← UInt64.shiftRight_eq_shiftRight_mod] using
      hNext2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)


/-- A comparison of words. -/
theorem specB_cmp {Γ : List Ty} (op : CmpOp) {left right : Expr S Γ .word}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.cmp op left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  simp only [Ty.rep_word] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  cases op <;>
    simp only [CmpOp.instr, wp_eqI64_cons, wp_neI64_cons, wp_ltUI64_cons, wp_leUI64_cons,
      wp_extendUI32_cons]
  · by_cases hab : left.denote funs env = right.denote funs env <;>
      simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv
  · by_cases hab : left.denote funs env = right.denote funs env <;>
      simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv
  · by_cases hab : left.denote funs env < right.denote funs env <;>
      simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv
  · by_cases hab : left.denote funs env ≤ right.denote funs env <;>
      simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv


/-- An operation on floats. -/
theorem specB_fbin {Γ : List Ty} (op : FBinOp) {left right : Expr S Γ .float}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.fbin op left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  have hR1' : ws1 = [.f64 (left.denote funs env).toBits] := hR1
  have hR2' : ws2 = [.f64 (right.denote funs env).toBits] := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 store2 s2 [.f64 ((Expr.fbin op left right).denote funs env).toBits]
    (After.ofScalar rfl hStep' rfl hF hH rfl)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hv ⊢
  cases op <;>
    simpa [FBinOp.instr, Expr.denote, FBinOp.apply, f64Add, f64Sub, f64Mul, f64Div,
      F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_div] using hv


/-- A comparison of floats. -/
theorem specB_fcmp {Γ : List Ty} (op : FCmpOp) {left right : Expr S Γ .float}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.fcmp op left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  have hR1' : ws1 = [.f64 (left.denote funs env).toBits] := hR1
  have hR2' : ws2 = [.f64 (right.denote funs env).toBits] := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hv ⊢
  cases op <;>
    simp only [FCmpOp.instr, wp_f64Lt_cons, wp_f64Le_cons, wp_f64Eq_cons, wp_extendUI32_cons]
  · cases hc : IEEE64.lt (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply, F64Bits.decide_lt, f64Lt, boolWord] using hv
  · cases hc : IEEE64.le (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply, F64Bits.decide_le, f64Le, boolWord] using hv
  · cases hc : IEEE64.eq (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply, F64Bits.beq_eq, f64Eq, boolWord] using hv


/-- An operation on one float.  The negation subtracts from negative zero, pushed first. -/
theorem specB_funary {Γ : List Ty} (op : FUnOp) {e : Expr S Γ .float}
    (eSpec : ∀ env slots live, CodeSpecB m funs bounds host pv e env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.funary op e) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  simp only [Expr.code]
  cases op with
  | neg =>
    simp only [FUnOp.code, List.cons_append, List.append_assoc, wp_f64Const_cons]
    refine eSpec env slots live h base heap store { s with values := .f64 0x8000000000000000 ::
      s.values } hh hpv (hVars.agree Frame.ofValues) hAt hCap hBase hRoom hPlace _ _ hTrap
      fun heap1 store1 s1 ws a1 hTop => ?_
    have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a hTop
    have hR : ws = [.f64 (e.denote funs env).toBits] := a1.rep
    subst hR
    have hStep := a1.step
    rw [Mode.fresh_scalar rfl] at hStep
    have hv := hNext1 store1 s1 [.f64 (-(e.denote funs env)).toBits]
      (After.ofValues (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl))
    simpa [Expr.denote, FUnOp.apply, f64Sub, F64Bits.toBits_neg] using hv
  | sqrt | abs =>
    simp only [FUnOp.code, List.append_assoc, List.cons_append, List.nil_append]
    refine eSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace _ _
        hTrap
      fun heap1 store1 s1 ws a1 hTop => ?_
    have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a hTop
    have hR : ws = [.f64 (e.denote funs env).toBits] := a1.rep
    subst hR
    have hStep := a1.step
    rw [Mode.fresh_scalar rfl] at hStep
    have hv := hNext1 store1 s1 [.f64 ((Expr.funary _ e).denote funs env).toBits]
      (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
    simpa [Expr.denote, FUnOp.apply, f64Sqrt, f64Abs, F64Bits.toBits_sqrt, F64Bits.toBits_abs]
      using hv


/-- A conversion of a word to a float. -/
theorem specB_toFloat {Γ : List Ty} (op : ToFloat) {e : Expr S Γ .word}
    (eSpec : ∀ env slots live, CodeSpecB m funs bounds host pv e env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.toFloat op e) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  simp only [Expr.code, List.append_assoc]
  refine eSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace _ _
      hTrap
    fun heap1 store1 s1 ws a1 hTop => ?_
  have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a hTop
  have hR : ws = [.i64 (e.denote funs env)] := a1.rep
  subst hR
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  have hv := hNext1 store1 s1 [.f64 ((Expr.toFloat op e).denote funs env).toBits]
    (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
  cases op <;>
    simpa [ToFloat.code, Expr.denote, ToFloat.apply, f64ConvertI64U, f64Add,
      F64Convert.toBits_toFloat, F64Bits.toBits_ofBits, add_negZero] using hv


/-- A conversion of a float to a word. -/
theorem specB_toWord {Γ : List Ty} (op : ToWord) {e : Expr S Γ .float}
    (eSpec : ∀ env slots live, CodeSpecB m funs bounds host pv e env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.toWord op e) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  simp only [Expr.code, List.append_assoc]
  refine eSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace _ _
      hTrap
    fun heap1 store1 s1 ws a1 hTop => ?_
  have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a hTop
  have hR : ws = [.f64 (e.denote funs env).toBits] := a1.rep
  subst hR
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  have hv := hNext1 store1 s1 [.i64 ((Expr.toWord op e).denote funs env)]
    (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
  cases op <;>
    simpa [ToWord.instr, Expr.denote, ToWord.apply, i64TruncSatF64U, F64Convert.toUInt64_eq]
      using hv


/-- The negation of a `Bool`. -/
theorem specB_not {Γ : List Ty} {e : Expr S Γ .bool}
    (eSpec : ∀ env slots live, CodeSpecB m funs bounds host pv e env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.not e) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  refine eSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace _ _
      hTrap
    fun heap1 store1 s1 ws a1 hTop => ?_
  have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a hTop
  have hR := a1.rep
  simp only [Ty.rep_bool] at hR
  subst hR
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_eqzI64_cons, wp_extendUI32_cons, boolWord_not]
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  simpa [Expr.denote] using
    hNext1 store1 s1 _ (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)


/-- The conjunction of `Bool`s. -/
theorem specB_and {Γ : List Ty} {left right : Expr S Γ .bool}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.and left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  simp only [Ty.rep_bool] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_andI64_cons, boolWord_and]
  simpa [Expr.denote] using hNext2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)


/-- The disjunction of `Bool`s. -/
theorem specB_or {Γ : List Ty} {left right : Expr S Γ .bool}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.or left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  simp only [Ty.rep_bool] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_orI64_cons, boolWord_or]
  simpa [Expr.denote] using hNext2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)


/-- A tuple of two elements: the code of each, in order. -/
theorem specB_mk {Γ : List Ty} {a b : Elem} {first : Expr S Γ (.elem a)}
    {second : Expr S Γ (.elem b)}
    (firstSpec : ∀ env slots live, CodeSpecB m funs bounds host pv first env slots live)
    (secondSpec : ∀ env slots live, CodeSpecB m funs bounds host pv second env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.mk first second) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : first.width ≤ max first.width second.width := Nat.le_max_left ..
  have hR : second.width ≤ max first.width second.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB firstSpec secondSpec env slots live h base heap store s hh hpv hVars hAt hCap
      hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  have hR1' : ws1 = a.values (first.denote funs env) := hR1
  have hR2' : ws2 = b.values (second.denote funs env) := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 store2 s2
    (a.values (first.denote funs env) ++ b.values (second.denote funs env))
    (After.ofScalar rfl hStep' rfl hF hH rfl)
  simpa [List.reverse_append, List.append_assoc] using hv


/-- A variable: read in place when borrowed, moved where it dies, and copied where it stays
live. -/
theorem specB_var (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} (x : Var Γ' tTy) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.var (S := S) x) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom _ rest Q hTrap hNext
  have hx : (fun i => live i || (Expr.var (S := S) x).uses i) x.index = true := by
    simp [Expr.uses]
  obtain ⟨hBelow, ws, hold, hRep⟩ := hVars.get x hx
  have hl := hRep.length
  have hMode : (Expr.var (S := S) x).mode (slots.map Slot.mode) =
      (slots.getD x.index default).mode := Slot.modes_getD slots x.index
  have hLiveIn : ∀ i, live i = true → (live i || (Expr.var (S := S) x).uses i) = true :=
    fun i h => by simp [h]
  by_cases hCopy : (slots.getD x.index default).mode = .owned ∧ live x.index = true
  · -- A copy into new blocks.
    obtain ⟨hOwned, hLiveX⟩ := hCopy
    simp only [Expr.code, Var.code, hOwned, hLiveX, and_self, ↓reduceIte]
    have hc : (Expr.var (S := S) x).allocs funs bounds (slots.map Slot.mode) live env =
        tTy.copyCost (env.get x) := by
      simp only [Expr.allocs, Var.cost, modeAt, Slot.modes_getD, hOwned, hLiveX, and_self,
        ↓reduceIte]
    have hT : TrapOK (false || (true && !decide (heap.Within store m (tTy.copyCost (env.get x)))))
        Q := hTrap.part nofun (fun _ => by simp [Slot.any_owned hOwned])
      fun _ hw => by rwa [hc] at hw
    refine wp_copyCode hm tTy hAt hCap hT hh hRep hold hBelow hBase
      (by rw [hh]; simpa [Expr.width] using hRoom) fun heap' store' s' ws' hStep hRep' hF hTop => ?_
    have hHolds := (hVars.live_mono hLiveIn).step hStep (fun _ _ _ _ _ _ _ _ => trivial)
    refine hNext heap' store' s' ws' ⟨?_, hF, hHolds.frame hF le_rfl, ?_, ?_⟩
      (fun _ => by rw [hc]; exact hTop)
    · rw [hMode, hOwned]
      exact hStep.mono (fun _ _ => trivial) fun _ h => h
    · rw [hMode, hOwned]; exact hRep'
    · rw [hMode, hOwned]
      intro u y hy _ wy hwy hly b hb c hc
      have hwy' := ((hVars.live_mono hLiveIn).hold_agree hF hy hly).mp
        hwy
      obtain ⟨hSame, hFresh⟩ := (hVars.live_mono hLiveIn).regions_after hStep hy hwy' hly
        fun _ _ => trivial
      rw [hSame] at hc
      exact regionsDisjoint_symm (hFresh c hc b hb)
  · simp only [Expr.code, Var.code, hCopy, ↓reduceIte]
    by_cases hOwned : (slots.getD x.index default).mode = .owned
    · -- A move: the variable dies here, and the value owns its blocks.
      have hDead : live x.index = false := by
        cases h : live x.index
        · rfl
        · exact absurd ⟨hOwned, h⟩ hCopy
      refine wp_loadCode ws hRep.typed hh hold (hNext heap store s ws ⟨?_, Frame.refl base s,
        hVars.live_mono hLiveIn, ?_, ?_⟩ fun _ => Nat.le_add_right _ _)
      · rw [hMode, hOwned]
        exact ⟨hAt, rfl, fun r hr _ hk => ⟨fun _ _ _ => rfl, hr,
          fun b hb => hk tTy x hx hDead hOwned ws hold hl b hb⟩⟩
      · rw [hMode]; exact hRep
      · rw [hMode, hOwned]
        intro u y hy _ wy hwy hly b hb c hc
        have hne : x.index ≠ y.index := fun he => by rw [he, hy] at hDead; exact nomatch hDead
        exact hVars.2 tTy u x y hx (hLiveIn _ hy) hne hOwned ws wy hold hl hwy hly b hb c hc
    · -- A view of a borrowed variable.
      have hBorrowed : (slots.getD x.index default).mode = .borrowed := by
        cases h : (slots.getD x.index default).mode
        · rfl
        · exact absurd h hOwned
      refine wp_loadCode ws hRep.typed hh hold (hNext heap store s ws (After.refl hAt hVars hLiveIn
        (by rw [hMode]; exact hRep) (by rw [hMode, hBorrowed]; rfl) ?_)
        fun _ => Nat.le_add_right _ _)
      rw [hMode]
      intro u y hy hm wy hwy hly b hb c hc
      rcases hm with hm | hm
      · exact absurd hm hOwned
      · have hne : y.index ≠ x.index := fun he => by
          rw [he] at hm; exact hOwned hm
        rw [hm] at hc
        exact regionsDisjoint_symm
          (hVars.2 u tTy y x (hLiveIn _ hy) hx hne hm wy ws hwy hly hold hl c hc b hb)


/-- The release of an array variable that a reader reads, when it is owned and dies there,
which leaves `top`. -/
theorem read_releaseT (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {live : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    {vals : List Value} {rest : Program} {Q : Assertion Unit} {e : Elem} (x : Var Γ (.array e))
    (hVars : Holds env slots (fun k => live k || k == x.index) base heap store s)
    (hAt : heap.At store)
    (hNext : ∀ heap' store', Evolves env slots (fun k => live k || k == x.index) live base heap
      store s heap' store' s → heap'.top = heap.top →
      wp m rest Q store' { s with values := vals } host) :
    wp m ((if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
        releaseCode (.array e) (slots.getD x.index default).loc else []) ++ rest) Q store
      { s with values := vals } host := by
  have hCode : (if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
      releaseCode (.array e) (slots.getD x.index default).loc else []) =
      (if live x.index = false then [x.index] else []).flatMap (releaseVar Γ slots) := by
    cases live x.index <;> simp [releaseVar, x.getElem?_index]
  rw [hCode]
  refine wp_releaseVarsT hm _ (by split <;> simp) (hVars.agree Frame.ofValues) hAt
    (by split <;> simp) fun heap' store' e hTop => hNext heap' store' ?_ hTop
  have e' := e.mono (live' := live) fun k h => by
    split
    · next hx =>
      have hne : k ≠ x.index := fun he => by rw [he, hx] at h; exact nomatch h
      simp [h, hne]
    · simp [h]
  exact ⟨e'.step, ⟨e'.frame.params, e'.frame.length, e'.frame.below⟩,
    e'.holds.agree Frame.ofValues⟩

/-- The size of an array variable: the load of its length word, then the release of the variable
when it is owned and dies there. -/
theorem specB_size (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e)) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.size (S := S) x) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt _ _ _ _ rest Q _ hNext
  obtain ⟨-, ws, hold, hRep⟩ := hVars.1 _ x (by simp [Expr.uses])
  obtain ⟨ptr, rfl, hB⟩ := hRep
  have hA := hB.borrow.values
  have hLength := hA.lengthBound
  have hPtr : s.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    exact LocalsHold.word hold
  have hnk : (env.get x).size * e.width < 536870912 := by
    have := hA.1; rw [Elem.words_size] at this; omega
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  simp only [wp_localGet_cons, hPtr, wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead, Elem.words_size, wp_divCode e.width_pos,
    words_div e.width_pos hnk]
  refine read_releaseT hm x hVars hAt fun heap' store' ev hTop => ?_
  exact hNext heap' store' s [.i64 (env.get x).size.toUInt64]
    (After.ofScalar rfl ev.step rfl ev.frame ev.holds rfl) fun _ => by rw [hTop]; omega

/-- A read of an array variable: the position in local `base`, a comparison of it with the
array's size as a flag in local `base + 1`, the position of the element's first word in local
`base`, the loads of its words under the flag, and the release of the variable when it is owned and
dies there. -/
theorem specB_get (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {i : Expr S Γ' .word}
    (iSpec : ∀ env slots live, CodeSpecB m funs bounds host pv i env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.get x i) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hi : i.width ≤ max i.width 2 := Nat.le_max_left ..
  have h2 : 2 ≤ max i.width 2 := Nat.le_max_right ..
  simp only [Expr.placeArgs] at hPlace
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  have hIn : ∀ k, ((live k || k == x.index) || i.uses k) = true →
      (live k || (Expr.get x i).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact live_assoc _ _ _ h
  refine iSpec env slots (fun k => live k || k == x.index) h base heap store s hh hpv
    (hVars.live_mono hIn) hAt hCap hBase (by omega) hPlace _ _
    hTrap fun heap1 store1 s1 ws1 a1 hTop1 => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  have e1 := a1.toEvolves rfl
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.half = h := e1.frame.half.trans hh
  obtain ⟨hBelowX, wx, holdx, hRepx⟩ := e1.holds.1 _ x (by simp)
  obtain ⟨ptr, rfl, hBx⟩ := hRepx
  have hA := hBx.borrow.values
  have hLength := hA.lengthBound
  have hnk : (env.get x).size * e.width < 536870912 := by
    have := hA.1; rw [Elem.words_size] at this; omega
  have hk := e.width_pos
  have hn64 : (env.get x).size < UInt64.size := by
    have := Nat.le_mul_of_pos_right (env.get x).size hk
    rw [show UInt64.size = 18446744073709551616 from rfl]; omega
  simp only [Ty.width] at hBelowX
  have hPtr1 : s1.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    exact LocalsHold.word holdx
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  -- The position, in local `base`.
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; omega
  have hHigh1 : base < s1.half := by rw [hh1]; omega
  refine wp_localSet_local hLow1 (Locals.lt_total hHigh1) ?_
  let s1a := setLocal { s1 with values := s.values } base (.i64 (i.denote funs env))
  have hK : s1a.get base = some (.i64 (i.denote funs env)) :=
    Locals.get_setLocal_same hLow1 (Locals.lt_total hHigh1)
  have hP : s1a.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne hLow1 (by omega)]
    exact hPtr1
  show wp m _ Q store1 s1a host
  simp only [wp_localGet_cons, Locals.get_values, hK, hP, wp_wrapI64_cons, wp_load64_cons,
    wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead, Elem.words_size, wp_divCode hk,
    words_div hk hnk]
  simp only [wp_ltUI64_cons, wp_extendUI32_cons]
  -- The flag, in local `base + 1`.
  have hLess : i.denote funs env < UInt64.ofNat (env.get x).size ↔
      (i.denote funs env).toNat < (env.get x).size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hn64]
  set b := decide ((i.denote funs env).toNat < (env.get x).size) with hb
  have hFlag : UInt64.ofNat (if i.denote funs env < UInt64.ofNat (env.get x).size then (1 : UInt32)
      else 0).toNat = boolWord b := by
    by_cases hc : (i.denote funs env).toNat < (env.get x).size
    · simp [hb, hc, hLess.mpr hc, boolWord]
    · simp [hb, hc, (not_congr hLess).mpr hc, boolWord]
  rw [hFlag]
  have hLowB : ({ s1a with values := s.values } : Locals).params.length ≤ base + 1 := by
    show s1.params.length ≤ base + 1; rw [hp1]; omega
  have hHighB : base + 1 < ({ s1a with values := s.values } : Locals).half := by
    simp only [s1a, Locals.half_setLocal, Locals.half_values, hh1]; omega
  refine wp_localSet_local hLowB (Locals.lt_total hHighB) ?_
  let s1b := setLocal { s1a with values := s.values } (base + 1) (.i64 (boolWord b))
  have hFb : s1b.get (base + 1) = some (.i64 (boolWord b)) :=
    Locals.get_setLocal_same hLowB (Locals.lt_total hHighB)
  have hKb : s1b.get base = some (.i64 (i.denote funs env)) := by
    rw [Locals.get_setLocal_ne hLowB (by omega), Locals.get_values]; exact hK
  have hPb : s1b.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne hLowB (by omega), Locals.get_values]; exact hP
  -- The position of the element's first word, in local `base`.
  show wp m _ Q store1 s1b host
  simp only [wp_localGet_cons, hKb]
  rw [wp_scaleCode]
  have hLowC : ({ s1b with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; omega
  have hHighC : base < ({ s1b with values := s.values } : Locals).half := by
    simp only [s1b, s1a, Locals.half_setLocal, Locals.half_values, hh1]; omega
  refine wp_localSet_local hLowC (Locals.lt_total hHighC) ?_
  let s1c := setLocal { s1b with values := s.values } base
    (.i64 (i.denote funs env * wordCount e.width))
  have hWc : s1c.get base = some (.i64 (i.denote funs env * wordCount e.width)) :=
    Locals.get_setLocal_same hLowC (Locals.lt_total hHighC)
  have hFc : s1c.get (base + 1) = some (.i64 (boolWord b)) := by
    rw [Locals.get_setLocal_ne hLowC (by omega), Locals.get_values]; exact hFb
  have hPc : s1c.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne hLowC (by omega), Locals.get_values]; exact hPb
  have f1 : Frame base s1 s1c :=
    ((Frame.setValues (s := s1) (vs := s.values) hLow1 le_rfl hHigh1).trans
      (Frame.setValues (s := s1a) (vs := s.values) hLowB (by omega)
        (by simpa [s1a, Locals.half_setLocal, Locals.half_values] using hHighB))).trans
      (Frame.setValues (s := s1b) (vs := s.values) hLowC le_rfl
        (by simpa [s1b, s1a, Locals.half_setLocal, Locals.half_values] using hHighC))
  have hFrame : Frame base s s1c := e1.frame.trans f1
  have hVars1 : Holds env slots (fun k => live k || k == x.index) base heap1 store1 s1c :=
    e1.holds.agree f1
  have hsc : s1c.values = s.values := rfl
  -- The words of the element, or zeros past the end.
  show wp m _ Q store1 s1c host
  refine wp_loadWordsCode (ws := e.words (env.get x)) b (fun _ => hA) 0 e.types s1c
    (e.toWords (env.get x)[(i.denote funs env).toNat]!) hPc hWc hFc
    (by rw [e.toWords_length, e.types_length]) (fun hbt => ?_) (fun hbf => ?_) ?_
  · have hc : (i.denote funs env).toNat < (env.get x).size := by simpa [hb] using hbt
    have hw : (i.denote funs env * wordCount e.width).toNat =
        (i.denote funs env).toNat * e.width := by
      have hs := words_scale (i := (i.denote funs env).toNat) hk
        (lt_of_le_of_lt (Nat.mul_le_mul_right e.width (Nat.le_of_lt hc)) hnk)
      rw [UInt64.ofNat_toNat] at hs
      rw [hs, UInt64.toNat_ofNat_of_lt' (by
          rw [show UInt64.size = 18446744073709551616 from rfl]
          have := Nat.mul_le_mul_right e.width (Nat.le_of_lt hc); omega)]
    rw [hw, e.types_length, Elem.words_size]
    refine ⟨by
        have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hc)
        rw [Nat.succ_mul] at this; omega,
      fun j hj => ?_⟩
    rw [e.toWords_length] at hj
    rw [Nat.add_zero, Elem.words_getElem! e _ hc hj, getElem!_pos (env.get x) _ hc]
  · have hc : ¬(i.denote funs env).toNat < (env.get x).size := by simpa [hb] using hbf
    rw [getElem!_neg (env.get x) _ hc, e.toWords_default, e.types_length]
  · rw [e.values_typed, hsc]
    refine read_releaseT hm x hVars1 e1.step.at_ fun heap2 store2 e2 hTop2 => ?_
    have e12 := Evolves.trans (hVars.live_mono hIn) ⟨e1.step, hFrame, hVars1⟩ e2
      (fun k h => by simp [h]) fun k h => by simp [h]
    exact hNext heap2 store2 s1c (e.values (env.get x)[(i.denote funs env).toNat]!)
      ((After.ofScalar (t := .elem e) (mode := .borrowed) rfl e12.step rfl e12.frame e12.holds
        rfl).liveIn hIn) fun hd => by rw [hTop2]; exact hTop1 hd

/-- A component of a tuple variable: the loads of the words that hold it. -/
theorem specB_proj {Γ' : List Ty} {e e' : Elem} (x : Var Γ' (.elem e)) (p : Path e e') :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.proj (S := S) x p) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt _ _ _ _ rest Q _ hNext
  obtain ⟨-, ws, hold, hRep⟩ := hVars.1 _ x (by simp [Expr.uses])
  have hRep' : ws = e.values (env.get x) := hRep
  subst hRep'
  simp only [Expr.code]
  exact wp_loadCode _ (by rw [e'.values_length, e'.types_length]) hh (p.holds hold)
    (hNext heap store s _ (After.refl hAt hVars (by intro i h; simp [Expr.uses, h]) rfl rfl
      (Holds.Apart.ofScalar rfl)) fun _ => Nat.le_add_right _ _)

/-- A value turned from mode `source` into mode `target` after an expression's code: a borrowed
value that must be owned is copied into new blocks, which raises `top` by at most `coerceCost t source target v`, and the
facts of `After` carry over. -/
theorem After.coerceB (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {liveIn live : Nat → Bool} {h base base' : Nat} {heap : Heap} {store : Store Unit}
    {s : Locals} {t : Ty} {source target : Mode} {v : t.denote} {heap1 : Heap}
    {store1 : Store Unit} {s1 : Locals} {ws vs : List Value} {rest : Program}
    {Q : Assertion Unit}
    (a : After env slots liveIn live base heap store s t source v heap1 store1 s1 ws)
    (hTarget : source = .owned → target = .owned) (hBase' : base ≤ base')
    (hLow : s1.params.length ≤ base') (hh : s1.half = h) (hRoom : base' + copyWidth t ≤ h)
    (hCap : store1.memoryCap m 0 ≤ 65535)
    (hTrap : source = .borrowed → target = .owned → t.scalar = false →
      TrapOK (!decide (heap1.Within store1 m (t.copyCost v))) Q)
    (hNext : ∀ heap2 store2 s2 ws2,
      After env slots liveIn live base heap store s t target v heap2 store2 s2 ws2 →
      heap2.top.toNat ≤ heap1.top.toNat + coerceCost t source target v →
      wp m rest Q store2 { s2 with values := ws2.reverse ++ vs } host) :
    wp m (coerceCode h t source target base' ++ rest) Q store1
      { s1 with values := ws.reverse ++ vs } host := by
  by_cases hCopy : source = .borrowed ∧ target = .owned ∧ t.scalar = false
  · obtain ⟨hs, ht, hScalar⟩ := hCopy
    subst hs ht
    have hW : copyWidth t = t.width + 3 := by simp [copyWidth, hScalar]
    simp only [coerceCode, and_self, hScalar, ↓reduceIte, List.append_assoc]
    refine wp_storeCode ws h base' t.types s1 vs a.rep.typed hh hLow
      (by rw [Ty.types_length, hh]; omega) fun s2 hF2 hold2 _ => ?_
    refine wp_copyCode hm t a.step.at_ hCap (hTrap rfl rfl hScalar)
      (hF2.half.trans hh) a.rep
      hold2 (le_refl _) (by rw [hF2.params]; omega)
      (by simp only [Locals.half_values, hF2.half, hh, Ty.copyScratch, hScalar,
        Bool.false_eq_true, ↓reduceIte]; omega)
      fun heap3 store3 s3 ws3 hStep3 hRep3 hF3 hTop3 => ?_
    have hF13 : Frame base s1 s3 :=
      (hF2.mono hBase').trans (Frame.ofValues.trans (hF3.mono (by omega)))
    have hF : Frame base s s3 := a.frame.trans hF13
    have hStep0 := a.step
    simp only [Mode.fresh] at hStep0
    refine hNext heap3 store3 s3 ws3 ⟨?_, hF, ?_, hRep3, ?_⟩ (by simpa [coerceCost] using hTop3)
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
    · exact hNext heap1 store1 s1 ws a (Nat.le_add_right _ _)
    · refine hNext heap1 store1 s1 ws ⟨?_, a.frame, a.holds, ?_, ?_⟩ (Nat.le_add_right _ _)
      · have hStep := a.step
        rw [Mode.fresh_scalar hScalar] at hStep ⊢
        exact hStep
      · cases target
        · exact a.rep.borrow
        · exact a.rep.owned hScalar
      · intro u y hy hm wy hwy hly b hb
        rw [Ty.regions_scalar t hScalar] at hb
        exact nomatch hb

/-- The allowance of an allocation of a part, from that of the whole, which may allocate. -/
theorem _root_.Wasm.TrapOK.alloc {Q : Assertion Unit} {d a : Bool} {P P' : Prop} [Decidable P]
    [Decidable P'] (h : TrapOK (d || (a && !decide P)) Q) (ha : a = true)
    (hP : d = false → P → P') : TrapOK (!decide P') Q :=
  h.part (d' := false) (a' := true) nofun (fun _ => ha) hP

/-- One branch of an `if`, after the condition: the releases of the owned variables that die at
its entry, its code, the coercion of its value to the `if`'s mode, and the store of its words,
which the code loads after the `if`. -/
theorem ite_branchB (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} {c : Expr S Γ' .bool}
    {thenE elseE b : Expr S Γ' tTy}
    (bSpec : ∀ env slots live, CodeSpecB m funs bounds host pv b env slots live)
    {env : Env Γ'} {slots : List Slot} {live : Nat → Bool} {h base : Nat} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit} (hh : s.half = h)
    (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || (Expr.ite c thenE elseE).uses i) base heap
      store s)
    (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoomB : base + tTy.width + max b.width (copyWidth tTy) ≤ h)
    {B cA : Nat}
    (hTrap : TrapOK (trapFlag m (Expr.ite c thenE elseE) slots heap store B) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots (fun i => live i || (Expr.ite c thenE elseE).uses i) live base heap store s
        tTy ((Expr.ite c thenE elseE).mode (slots.map Slot.mode))
        ((Expr.ite c thenE elseE).denote funs env) heap' store' s' ws →
      ((Expr.ite c thenE elseE).depthCalls = false → heap'.top.toNat ≤ heap.top.toNat + B) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host)
    {heap1 : Heap} {store1 : Store Unit} {s1 : Locals}
    (e1 : Evolves env slots (fun i => live i || (Expr.ite c thenE elseE).uses i)
      (fun i => live i || thenE.uses i || elseE.uses i) base heap store s heap1 store1
      { s1 with values := s.values })
    (hTop1 : (Expr.ite c thenE elseE).depthCalls = false → heap1.top.toNat ≤ heap.top.toNat + cA)
    (hB : B = cA + (b.allocs funs bounds (slots.map Slot.mode) live env +
      coerceCost tTy (b.mode (slots.map Slot.mode))
        ((Expr.ite c thenE elseE).mode (slots.map Slot.mode)) (b.denote funs env)))
    (hbd : b.depthCalls = true → (Expr.ite c thenE elseE).depthCalls = true)
    (hbPlace : b.placeArgs = true)
    (hbu : ∀ i, b.uses i = true → (thenE.uses i || elseE.uses i) = true)
    (hba : b.aborts = true → (Expr.ite c thenE elseE).aborts = true)
    (hval : b.denote funs env = (Expr.ite c thenE elseE).denote funs env)
    (hbm : b.mode (slots.map Slot.mode) = .owned →
      (Expr.ite c thenE elseE).mode (slots.map Slot.mode) = .owned)
    (Qb : Assertion Unit) (hQbTrap : ∀ st, Q (.Trap st "unreachable") → Qb (.Trap st "unreachable"))
    (hQb : ∀ st' s', wp m (loadCode h base tTy.types ++ rest) Q st'
      { s' with values := s.values } host → Qb (.Fallthrough st' s')) :
    wp m (releaseWhere Γ' slots (fun i => (live i || thenE.uses i || elseE.uses i) &&
        !(live i || b.uses i)) ++
      (b.code h slots (base + tTy.width) live ++
        (coerceCode h tTy (b.mode (slots.map Slot.mode))
          ((Expr.ite c thenE elseE).mode (slots.map Slot.mode)) (base + tTy.width) ++
          storeCode h base tTy.types))) Qb store1 { s1 with values := s.values } host := by
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.half = h := e1.frame.half.trans hh
  have hTrapB : TrapOK (trapFlag m (Expr.ite c thenE elseE) slots heap store B) Qb :=
    hTrap.imp hQbTrap
  have hbd' : (Expr.ite c thenE elseE).depthCalls = false → b.depthCalls = false := fun hd => by
    cases hb : b.depthCalls
    · rfl
    · rw [hbd hb] at hd; exact nomatch hd
  have hSubMid : ∀ i, (live i || b.uses i) = true →
      (live i || thenE.uses i || elseE.uses i) = true := fun i =>
    ite_live_branch _ _ _ _ (hbu i)
  refine wp_releaseWhereT hm e1.holds e1.step.at_
    (fun i h => by simp only [Bool.and_eq_true] at h; exact h.1) fun heap2 store2 e2 hTop2 => ?_
  have hEq : (fun i => (live i || thenE.uses i || elseE.uses i) &&
      !((live i || thenE.uses i || elseE.uses i) && !(live i || b.uses i))) =
      (fun i => live i || b.uses i) := by
    funext i
    exact live_released _ _ (hSubMid i)
  rw [hEq] at e2
  rw [← List.append_nil (storeCode h base tTy.types)]
  have hbw := Nat.le_max_left b.width (copyWidth tTy)
  have hcw := Nat.le_max_right b.width (copyWidth tTy)
  refine bSpec env slots live h (base + tTy.width) heap2 store2 { s1 with values := s.values }
    hh1 (hp1.trans hpv) (e2.holds.mono (by omega)) e2.step.at_
    (by rw [e2.step.cap m, e1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base + tTy.width; rw [hp1]; omega)
    (by omega) hbPlace _ _ (hTrapB.part hbd (fun h => by
          simp only [Bool.or_eq_true] at h ⊢; exact h.imp_left hba) fun hd hw => by
        rw [hB] at hw
        exact (hw.after (heap1 := heap2) (store1 := store2)
          (by have := hTop1 hd; have := congrArg UInt64.toNat hTop2; omega)
          (by rw [e2.step.cap m, e1.step.cap m])).mono (Nat.le_add_right _ _))
    fun heap3 store3 s3 ws3 a3 hTop3 => ?_
  have hp3 : s3.params = s.params := a3.frame.params.trans hp1
  have hh3 : s3.half = h := a3.frame.half.trans hh1
  refine After.coerceB hm a3 hbm le_rfl (by rw [hp3]; omega) hh3 (by omega)
    (by rw [a3.step.cap m, e2.step.cap m, e1.step.cap m]; exact hCap)
    (fun hs ht _ => hTrapB.alloc (by
      have := (Expr.ite c thenE elseE).mode_owned (slots.map Slot.mode) ht
      rw [Slot.any_map] at this; exact this) fun hd hw => by
        rw [hB, ← Nat.add_assoc] at hw
        have h3 := hw.after (heap1 := heap3) (store1 := store3)
          (c1 := cA + b.allocs funs bounds (slots.map Slot.mode) live env)
          (by have := hTop3 (hbd' hd); have := hTop1 hd; have := congrArg UInt64.toNat hTop2; omega)
          (by rw [a3.step.cap m, e2.step.cap m, e1.step.cap m])
        simpa [coerceCost, hs, ht] using h3)
    fun heap4 store4 s4 ws4 a4 hTop4 => ?_
  have hp4 : s4.params = s.params := a4.frame.params.trans hp1
  have hh4 : s4.half = h := a4.frame.half.trans hh1
  refine wp_storeCode ws4 h base tTy.types s4 s.values a4.rep.typed hh4 (by rw [hp4]; omega)
    (by rw [Ty.types_length, hh4]; omega) fun s5 hF5 hold _ => ?_
  rw [wp_nil]
  refine hQb _ _ (wp_loadCode ws4 a4.rep.typed (hF5.half.trans hh4) hold ?_)
  -- The `if`'s facts: the evolutions of the condition and the releases, then the branch.
  have hLower := a4.lower e2.holds (Nat.le_add_right _ _) (fun i h => by simp [h])
  have hEntry : ∀ i, (live i || thenE.uses i || elseE.uses i) = true →
      (live i || (Expr.ite c thenE elseE).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact ite_live_entry _ _ _ _ h
  have e12 := Evolves.trans hVars e1 e2 hSubMid hEntry
  have aAll := After.prepend hVars e12 hLower (fun i h => hEntry i (hSubMid i h))
    (fun i h => by simp [h])
  have hF45 : Frame base s4 { s5 with values := s.values } := hF5.trans Frame.ofValues
  have hFrame : Frame base s { s5 with values := s.values } := aAll.frame.trans hF45
  rw [hval] at aAll
  refine hNext heap4 store4 _ ws4 ⟨aAll.step, hFrame, aAll.holds.agree hF45, aAll.rep, ?_⟩
    fun hd => by
      have := hTop1 hd; have := hTop3 (hbd' hd); have := congrArg UInt64.toNat hTop2
      have := congrArg UInt64.toNat hTop2
      rw [hB]; omega
  exact aAll.apart.agree aAll.holds hF45

/-- An `if`: the condition, then each branch as `ite_branchB` describes. -/
theorem specB_ite (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} {c : Expr S Γ' .bool}
    {thenE elseE : Expr S Γ' tTy}
    (cSpec : ∀ env slots live, CodeSpecB m funs bounds host pv c env slots live)
    (thenSpec : ∀ env slots live, CodeSpecB m funs bounds host pv thenE env slots live)
    (elseSpec : ∀ env slots live, CodeSpecB m funs bounds host pv elseE env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.ite c thenE elseE) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hc : c.width ≤ max c.width (tTy.width + max (max thenE.width elseE.width)
      (copyWidth tTy)) := Nat.le_max_left ..
  have hb : tTy.width + max (max thenE.width elseE.width) (copyWidth tTy) ≤
      max c.width (tTy.width + max (max thenE.width elseE.width) (copyWidth tTy)) :=
    Nat.le_max_right ..
  have ht : thenE.width ≤ max thenE.width elseE.width := Nat.le_max_left ..
  have he : elseE.width ≤ max thenE.width elseE.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  obtain ⟨⟨hPlaceC, hPlaceT⟩, hPlaceE⟩ := hPlace
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  have hMid : ∀ i, ((live i || thenE.uses i || elseE.uses i) || c.uses i) = true →
      (live i || (Expr.ite c thenE elseE).uses i) = true := by
    intro i h; simp only [Expr.uses]; exact ite_live_cond _ _ _ _ h
  refine cSpec env slots _ h base heap store s hh hpv (hVars.live_mono hMid) hAt hCap hBase
    (by omega) hPlaceC _ _
    (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact ite_trap_cond _ _ _ _ h)
      fun _ hw => hw.mono (by simp only [Expr.allocs]; exact Nat.le_add_right _ _))
    fun heap1 store1 s1 ws1 a1 hTop1 => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_bool] at hR1
  subst hR1
  have e1 : Evolves env slots (fun i => live i || (Expr.ite c thenE elseE).uses i)
      (fun i => live i || thenE.uses i || elseE.uses i) base heap store s heap1 store1
      { s1 with values := s.values } := by
    have e := (a1.toEvolves rfl).values s.values
    exact ⟨e.step.mono (fun r hr => hr.mono fun i h1 h2 => ⟨hMid i h1, h2⟩) fun _ h => h,
      e.frame, e.holds⟩
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_eqzI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have hModeT : thenE.mode (slots.map Slot.mode) = .owned →
      (Expr.ite c thenE elseE).mode (slots.map Slot.mode) = .owned :=
    fun h => by simp [Expr.mode, h, Mode.join]
  have hModeE : elseE.mode (slots.map Slot.mode) = .owned →
      (Expr.ite c thenE elseE).mode (slots.map Slot.mode) = .owned := fun h => by
    simp only [Expr.mode, h]
    cases thenE.mode (slots.map Slot.mode) <;> rfl
  have hRoomT : base + tTy.width + max thenE.width (copyWidth tTy) ≤ h := by
    have := Nat.max_le.mpr ⟨ht.trans (Nat.le_max_left _ (copyWidth tTy)), Nat.le_max_right _ _⟩
    omega
  have hRoomE : base + tTy.width + max elseE.width (copyWidth tTy) ≤ h := by
    have := Nat.max_le.mpr ⟨he.trans (Nat.le_max_left _ (copyWidth tTy)), Nat.le_max_right _ _⟩
    omega
  cases hcv : c.denote funs env
  · simp (config := { decide := true }) only [↓reduceIte]
    exact ite_branchB hm elseSpec hh hpv hVars hCap hBase hRoomE hTrap hNext e1
      (fun hd => hTop1 (by simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.1.1))
      (by simp only [Expr.allocs, Expr.mode, hcv, Bool.false_eq_true, ↓reduceIte])
      (fun h => by simp [Expr.depthCalls, h]) hPlaceE
      (fun i h => by simp [h]) (fun h => by simp [Expr.aborts, h])
      (by simp [Expr.denote, hcv]) hModeE _ (fun _ h => h) fun _ _ h => by simpa using h
  · simp (config := { decide := true }) only [↓reduceIte]
    exact ite_branchB hm thenSpec hh hpv hVars hCap hBase hRoomT hTrap hNext e1
      (fun hd => hTop1 (by simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.1.1))
      (by simp only [Expr.allocs, Expr.mode]; rw [if_pos hcv])
      (fun h => by simp [Expr.depthCalls, h]) hPlaceT
      (fun i h => by simp [h]) (fun h => by simp [Expr.aborts, h])
      (by simp [Expr.denote, hcv]) hModeT _ (fun _ h => h) fun _ _ h => by simpa using h

/-- A `let` binding: the value's code, the store of its words from local `base` on, the release
of the value when it is owned and the body does not use it, and the body's code. -/
theorem specB_letE (hm : Runtime m) {Γ' : List Ty} {sTy tTy : Ty} {value : Expr S Γ' sTy}
    {body : Expr S (sTy :: Γ') tTy}
    (valueSpec : ∀ env slots live, CodeSpecB m funs bounds host pv value env slots live)
    (bodySpec : ∀ env slots live, CodeSpecB m funs bounds host pv body env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.letE value body) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hValueRoom : value.width ≤ max value.width body.width := Nat.le_max_left ..
  have hBodyRoom : body.width ≤ max value.width body.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  have hV : ∀ i, ((live i || body.uses (i + 1)) || value.uses i) = true →
      (live i || (Expr.letE value body).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  refine valueSpec env slots (fun i => live i || body.uses (i + 1)) h (base + sTy.width) heap
    store s hh hpv ((hVars.mono (by omega)).live_mono hV) hAt hCap (by omega) (by omega) hPlace.1 _
        _
    (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
      fun _ hw => hw.mono (by simp only [Expr.allocs]; exact Nat.le_add_right _ _))
    fun heap1 store1 s1 ws1 a1 hTop1 => ?_
  have hp1 : s1.params = s.params := a1.frame.params
  have hh1 : s1.half = h := a1.frame.half.trans hh
  have a1' := a1.lower (hVars.live_mono hV) (Nat.le_add_right _ _) fun i h => by simp [h]
  refine wp_storeCode ws1 h base sTy.types s1 s.values a1.rep.typed hh1 (by rw [hp1]; omega)
    (by rw [Ty.types_length, hh1]; omega) fun s2 hF2 hold _ => ?_
  have f2 : Frame base s1 { s2 with values := s.values } := hF2.trans Frame.ofValues
  have hp2 : s2.params = s.params := hF2.params.trans hp1
  have hh2 : ({ s2 with values := s.values } : Locals).half = h := f2.half.trans hh1
  have hold' : LocalsHold { s2 with values := s.values } base sTy.types ws1 := hold
  -- The body's context: the value as variable 0, in the locals from `base` on.
  have hVarsB : Holds (Env.cons (value.denote funs env) env)
      (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => i == 0 || shift 1 live i || body.uses i) (base + sTy.width) heap1 store1
      { s2 with values := s.values } :=
    Holds.push ((a1'.holds.agree f2).live_mono fun i h => by
        simpa using h)
      hold' a1.rep ((a1'.apart.agree a1'.holds f2).live_mono
        fun i h => by simpa using h)
  have hRelease : (if value.mode (slots.map Slot.mode) = .owned ∧ body.uses 0 = false then
      releaseCode sTy base else []) =
      (if body.uses 0 = false then [0] else []).flatMap
        (releaseVar (sTy :: Γ') (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)) := by
    cases body.uses 0 <;> cases value.mode (slots.map Slot.mode) <;> simp [releaseVar]
  rw [hRelease]
  have hd1 : (Expr.letE value body).depthCalls = false → value.depthCalls = false := fun hd => by
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.1
  have hd3 : (Expr.letE value body).depthCalls = false → body.depthCalls = false := fun hd => by
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.2
  refine wp_releaseVarsT hm _ (by split <;> simp) hVarsB a1.step.at_ (by split <;> simp)
    fun heap2 store2 e2 hTop2 => ?_
  have e2' := e2.mono (live' := fun i => shift 1 live i || body.uses i) fun i h => by
    cases i with
    | zero =>
      have h0 : body.uses 0 = true := by simpa [shift] using h
      simp [h0]
    | succ k => split <;> simpa using h
  refine bodySpec _ _ (shift 1 live) h (base + sTy.width) heap2 store2
    { s2 with values := s.values } hh2 (hp2.trans hpv) e2'.holds e2'.step.at_
    (by rw [e2'.step.cap m, a1.step.cap m]; exact hCap)
    (by show s2.params.length ≤ base + sTy.width; rw [hp2]; omega)
    (by omega) hPlace.2 _ _
    (hTrap.part (by flag_tac) (fun h => by
      have hmo := value.mode_owned (slots.map Slot.mode)
      rw [Slot.any_map] at hmo
      simp only [List.any_cons, Expr.aborts] at h ⊢
      exact let_trap_body _ _ _ _ (fun hv => hmo (by simpa using hv)) h) fun hd hw => by
        simp only [Expr.allocs] at hw
        exact hw.after (heap1 := heap2) (store1 := store2)
          (by have := hTop1 (hd1 hd); have := congrArg UInt64.toNat hTop2; omega)
          (by rw [e2'.step.cap m, a1.step.cap m]))
    fun heap3 store3 s3 ws3 aB hTop3 => ?_
  have aB' := After.prepend hVarsB e2' aB (fun i h => live_right _ _ _ h) fun i h => by simp [h]
  exact hNext heap3 store3 s3 ws3
    ((After.bind (hVars.live_mono hV) a1' f2 hold' aB' (fun i h => by simpa using h)
      (fun i h => by simp [h]) fun i h => by simp [h]).liveIn hV) fun hd => by
      have := hTop1 (hd1 hd); have h3 := hTop3 (hd3 hd); have := congrArg UInt64.toNat hTop2
      simp only [List.map_cons] at h3
      simp only [Expr.allocs]; omega

/-- An allowance for a trap when `top` cannot rise by a charge gives the allowance of a part
that takes no call depth and whose room follows from the charge's. -/
theorem _root_.Wasm.TrapOK.narrow {Q : Assertion Unit} {a : Bool} {P P' : Prop} [Decidable P]
    [Decidable P'] (h : TrapOK (!decide P) Q) (hP : P → P') : TrapOK (false || (a && !decide P')) Q :=
  h.of_imp fun h' => by
    simp only [Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h' ⊢
    exact fun hp => h'.2 (hP hp)

/-- A variable in an owned position: its words as an owned value, which move it when it is owned
and dies, and a copy otherwise, which raises `top` by at most `x.ownedCost` and traps only when
`top` cannot rise by that much. -/
theorem specB_ownedVar (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} (x : Var Γ' tTy)
    {env : Env Γ'} {slots : List Slot} {live : Nat → Bool} {h base : Nat} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit} (hh : s.half = h)
    (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || i == x.index) base heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoom : base + copyWidth tTy ≤ h)
    (hTrap : TrapOK (!decide (heap.Within store m
      (x.ownedCost (slots.map Slot.mode) live (env.get x)))) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots (fun i => live i || i == x.index) live base heap store s tTy .owned
        (env.get x) heap' store' s' ws →
      heap'.top.toNat ≤ heap.top.toNat + x.ownedCost (slots.map Slot.mode) live (env.get x) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wp m (x.ownedCode h slots base live ++ rest) Q store s host := by
  simp only [Var.ownedCode, List.append_assoc]
  have hScratch := tTy.copyScratch_le
  have hMode : modeAt (slots.map Slot.mode) x.index = (slots.getD x.index default).mode :=
    Slot.modes_getD slots x.index
  refine specB_var (S := []) (funs := .nil) (bounds := .nil) hm x env slots live h base heap store
      s hh hpv hVars hAt
    hCap hBase (by simp only [Expr.width]; omega) rfl _ _
    (hTrap.narrow fun hw => hw.mono (by simp only [Expr.allocs, Var.ownedCost]; omega))
    fun heap1 store1 s1 ws1 a1 hTop1 => ?_
  have hTop1' := hTop1 rfl
  simp only [Expr.allocs] at hTop1'
  rw [show (Expr.var (S := []) x).mode (slots.map Slot.mode) = (slots.getD x.index default).mode
    from Slot.modes_getD slots x.index] at a1
  exact After.coerceB hm a1 (fun _ => rfl) le_rfl (by rw [a1.frame.params]; exact hBase)
    (a1.frame.half.trans hh) (by omega) (by rw [a1.step.cap m]; exact hCap)
    (fun hs _ _ => hTrap.within fun hw => by
      have h2 := hw.after (heap1 := heap1) (store1 := store1)
        (c1 := x.cost (slots.map Slot.mode) live (env.get x))
        (c2 := coerceCost tTy (modeAt (slots.map Slot.mode) x.index) .owned (env.get x)) hTop1'
        (a1.step.cap m)
      simp only [coerceCost, hMode, hs, and_self, ↓reduceIte] at h2
      exact h2)
    fun heap2 store2 s2 ws2 a2 hTop2 => hNext heap2 store2 s2 ws2 a2 (by
      simp only [Expr.denote] at hTop2
      simp only [Var.ownedCost]; rw [hMode]; omega)

set_option maxHeartbeats 300000 in
/-- A pair: the code of each component, each followed by its coercion to the pair's mode. -/
theorem specB_pair (hm : Runtime m) {Γ' : List Ty} {sTy tTy : Ty} {first : Expr S Γ' sTy}
    {second : Expr S Γ' tTy}
    (firstSpec : ∀ env slots live, CodeSpecB m funs bounds host pv first env slots live)
    (secondSpec : ∀ env slots live, CodeSpecB m funs bounds host pv second env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.pair first second) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have h1 : first.width ≤ max first.width second.width := Nat.le_max_left ..
  have h2 : second.width ≤ max first.width second.width := Nat.le_max_right ..
  have hc1 : copyWidth sTy ≤ max (copyWidth sTy) (copyWidth tTy) := Nat.le_max_left ..
  have hc2 : copyWidth tTy ≤ max (copyWidth sTy) (copyWidth tTy) := Nat.le_max_right ..
  have hw := Nat.le_max_left (max first.width second.width) (max (copyWidth sTy) (copyWidth tTy))
  have hc := Nat.le_max_right (max first.width second.width) (max (copyWidth sTy) (copyWidth tTy))
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  have hIn : ∀ i, ((live i || second.uses i) || first.uses i) = true →
      (live i || (Expr.pair first second).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  have hVarsL := hVars.live_mono hIn
  have hOwnedA : (Expr.pair first second).mode (slots.map Slot.mode) = .owned →
      ((Expr.pair first second).aborts || slots.any (·.mode == .owned)) = true := fun ht => by
    have := (Expr.pair first second).mode_owned (slots.map Slot.mode) ht
    rw [Slot.any_map] at this
    exact this
  have hdF : (Expr.pair first second).depthCalls = false → first.depthCalls = false := fun hd => by
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.1
  have hdS : (Expr.pair first second).depthCalls = false → second.depthCalls = false := fun hd => by
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.2
  have hB : (Expr.pair first second).allocs funs bounds (slots.map Slot.mode) live env =
      first.allocs funs bounds (slots.map Slot.mode) (fun i => live i || second.uses i) env +
        coerceCost sTy (first.mode (slots.map Slot.mode))
          ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode))) (first.denote funs env) +
        second.allocs funs bounds (slots.map Slot.mode) live env +
        coerceCost tTy (second.mode (slots.map Slot.mode))
          ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode))) (second.denote funs env) := by
    simp only [Expr.allocs, Expr.mode]
  refine firstSpec env slots (fun i => live i || second.uses i) h base heap store s hh hpv
      hVarsL hAt
    hCap hBase (by omega) hPlace.1 _ _
    (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
      fun _ hw => hw.mono (by rw [hB]; omega))
    fun heap1 store1 s1 ws1 a1 hTopF => ?_
  refine After.coerceB hm a1 (fun h => by simp [Mode.join, h]) le_rfl
    (by rw [a1.frame.params]; exact hBase) (a1.frame.half.trans hh) (by omega)
    (by rw [a1.step.cap m]; exact hCap) (fun hs ht _ => hTrap.alloc (hOwnedA ht) fun hd hw => by
      have hcc : coerceCost sTy (first.mode (slots.map Slot.mode))
          ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode))) (first.denote funs env) =
          sTy.copyCost (first.denote funs env) := by rw [coerceCost, if_pos ⟨hs, ht⟩]
      exact hw.shift (c1 := first.allocs funs bounds (slots.map Slot.mode)
        (fun i => live i || second.uses i) env) (hTopF (hdF hd)) (by rw [hB]; omega)
        (a1.step.cap m))
    fun heap1 store1 s1 ws1 a1 hTopC1 => ?_
  refine secondSpec env slots live h base heap1 store1
    { s1 with values := ws1.reverse ++ s.values } (a1.frame.half.trans hh)
    (a1.frame.params.trans hpv) (a1.holds.agree Frame.ofValues) a1.step.at_
    (by rw [a1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base; rw [a1.frame.params]; exact hBase) (by omega) hPlace.2 _ _
    (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact trap_right _ _ _ h)
      fun hd hw => hw.shift (heap1 := heap1) (store1 := store1)
        (c1 := first.allocs funs bounds (slots.map Slot.mode) (fun i => live i || second.uses i)
          env + coerceCost sTy (first.mode (slots.map Slot.mode)) ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode)))
            (first.denote funs env))
        (by have := hTopF (hdF hd); have := hTopC1; omega) (by rw [hB]; omega) (a1.step.cap m))
    fun heap2 store2 s2 ws2 a2 hTopS => ?_
  refine After.coerceB hm a2 (fun h => by
      simp only [Mode.join, h]; cases first.mode (slots.map Slot.mode) <;> rfl) le_rfl
    (by rw [a2.frame.params, a1.frame.params]; exact hBase)
    (a2.frame.half.trans (a1.frame.half.trans hh)) (by omega)
    (by rw [a2.step.cap m, a1.step.cap m]; exact hCap)
    (fun hs ht _ => hTrap.alloc (hOwnedA ht) fun hd hw => by
      have hcc : coerceCost tTy (second.mode (slots.map Slot.mode))
          ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode))) (second.denote funs env) =
          tTy.copyCost (second.denote funs env) := by rw [coerceCost, if_pos ⟨hs, ht⟩]
      exact hw.shift (heap1 := heap2) (store1 := store2)
        (c1 := first.allocs funs bounds (slots.map Slot.mode) (fun i => live i || second.uses i)
          env + coerceCost sTy (first.mode (slots.map Slot.mode)) ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode)))
            (first.denote funs env) + second.allocs funs bounds (slots.map Slot.mode) live env)
        (by have := hTopF (hdF hd); have := hTopC1; have := hTopS (hdS hd); omega)
        (by rw [hB]; omega)
        (by rw [a2.step.cap m, a1.step.cap m]))
    fun heap2 store2 s2 ws2 a2 hTopC2 => ?_
  obtain ⟨hStep, hFrame, hRep1, hApart1, hDisjoint⟩ :=
    After.seq hVarsL a1 a2 (fun i h => by simp [h]) fun i h => by simp [h]
  have hl1 := hRep1.length
  have hv := hNext heap2 store2 s2 (ws1 ++ ws2) ⟨by
      rw [Mode.fresh_pair hl1]
      exact hStep.mono (fun _ hr => hr.mono fun i h1 h2 => ⟨hIn i h1, h2⟩) fun _ hb => hb,
    hFrame, a2.holds, ⟨ws1, ws2, rfl, hRep1, a2.rep, fun hmo x hx y hy => by
      have hmo' : (first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode)) =
          .owned := hmo
      rw [hmo'] at hDisjoint
      exact hDisjoint x hx y hy⟩, fun w y hy hmo wy hwy hly b hb c hc => by
      rw [Ty.regions_append hl1] at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hApart1 w y hy hmo wy hwy hly b hb c hc
      · exact a2.apart w y hy hmo wy hwy hly b hb c hc⟩
      (fun hd => by
        have := hTopF (hdF hd); have := hTopC1; have := hTopS (hdS hd); have := hTopC2
        rw [hB]; omega)
  simpa [List.reverse_append, List.append_assoc] using hv

/-- A binding of a pair's components: the pair's code, the stores of its components' words, the
release of each component that is owned and that the body does not use, and the body's code. -/
theorem specB_letPair (hm : Runtime m) {Γ' : List Ty} {sTy tTy uTy : Ty}
    {e : Expr S Γ' (.pair sTy tTy)} {body : Expr S (tTy :: sTy :: Γ') uTy}
    (eSpec : ∀ env slots live, CodeSpecB m funs bounds host pv e env slots live)
    (bodySpec : ∀ env slots live, CodeSpecB m funs bounds host pv body env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.letPair e body) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hER : e.width ≤ max e.width body.width := Nat.le_max_left ..
  have hBR : body.width ≤ max e.width body.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  have hV : ∀ i, ((live i || body.uses (i + 2)) || e.uses i) = true →
      (live i || (Expr.letPair e body).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  refine eSpec env slots (fun i => live i || body.uses (i + 2)) h
    (base + sTy.width + tTy.width) heap store s hh hpv ((hVars.mono (by omega)).live_mono hV) hAt
        hCap
    (by omega) (by omega) hPlace.1
    _ _ (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
      fun _ hw => hw.mono (by simp only [Expr.allocs]; exact Nat.le_add_right _ _))
    fun heap1 store1 s1 ws a1 hTop1 => ?_
  have hp1 : s1.params = s.params := a1.frame.params
  have hh1 : s1.half = h := a1.frame.half.trans hh
  have a1' := a1.lower (hVars.live_mono hV) (by omega) fun i h => by simp [h]
  obtain ⟨wf, wsec, rfl, hRf, hRs, hDisj⟩ := a1.rep
  have hlf := hRf.length
  have hls := hRs.length
  rw [List.reverse_append, List.append_assoc]
  refine wp_storeCode wsec h (base + sTy.width) tTy.types s1 (wf.reverse ++ s.values) hRs.typed
    hh1 (by rw [hp1]; omega) (by rw [Ty.types_length, hh1]; omega) fun s2 hF2 hold2 _ => ?_
  have hh2 : s2.half = h := hF2.half.trans hh1
  refine wp_storeCode wf h base sTy.types s2 s.values hRf.typed hh2 (by rw [hF2.params, hp1]; omega)
    (by rw [Ty.types_length, hh2]; omega) fun s3 hF3 hold1 habove3 => ?_
  have hold1' : LocalsHold { s3 with values := s.values } base sTy.types wf := hold1
  have hold2' : LocalsHold { s3 with values := s.values } (base + sTy.width) tTy.types wsec :=
    hold2.keep hF3.half habove3 (by rw [Ty.types_length]) (by rw [hls, hh2]; omega)
  have f3 : Frame base s1 { s3 with values := s.values } :=
    (hF2.mono (by omega)).trans (hF3.trans Frame.ofValues)
  have hp3 : s3.params = s.params := hF3.params.trans (hF2.params.trans hp1)
  -- The body's context: the second component as variable 0 and the first as variable 1.
  have hVars1 := (a1'.holds.agree f3)
  have hApart := a1'.apart.agree a1'.holds f3
  have hVarsB : Holds (Env.cons (e.denote funs env).2 (Env.cons (e.denote funs env).1 env))
      (⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
        ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => decide (i < 2) || shift 2 live i || body.uses i)
      (base + sTy.width + tTy.width) heap1 store1 { s3 with values := s.values } := by
    refine Holds.push (Holds.push (hVars1.live_mono fun i h => by simpa using h) hold1' hRf
      ((hApart.fst hlf).live_mono fun i h => by simpa using h)) hold2' hRs ?_
    refine Holds.Apart.push ((hApart.snd hlf).live_mono fun i h => by simpa using h) hold1' hlf
      fun hmo b hb c hc => ?_
    have hmo' : e.mode (slots.map Slot.mode) = .owned := by simpa using hmo
    rw [hmo'] at hb hc hDisj
    exact regionsDisjoint_symm (hDisj rfl c hc b hb)
  have hRelease : ∀ rest' : Program,
      (if e.mode (slots.map Slot.mode) = .owned ∧ body.uses 1 = false then
        releaseCode sTy base else []) ++
      ((if e.mode (slots.map Slot.mode) = .owned ∧ body.uses 0 = false then
        releaseCode tTy (base + sTy.width) else []) ++ rest') =
      ((if body.uses 1 = false then [1] else []) ++
        (if body.uses 0 = false then [0] else [])).flatMap
        (releaseVar (tTy :: sTy :: Γ') (⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
          ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots)) ++ rest' := by
    intro rest'
    cases body.uses 1 <;> cases body.uses 0 <;> cases e.mode (slots.map Slot.mode) <;>
      simp [releaseVar]
  rw [hRelease]
  have hd1 : (Expr.letPair e body).depthCalls = false → e.depthCalls = false := fun hd => by
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.1
  have hd3 : (Expr.letPair e body).depthCalls = false → body.depthCalls = false := fun hd => by
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.2
  refine wp_releaseVarsT hm _ (by split <;> split <;> simp) hVarsB a1.step.at_
    (by split <;> split <;> simp) fun heap2 store2 e2 hTop2 => ?_
  have e2' := e2.mono (live' := fun i => shift 2 live i || body.uses i) fun i h => by
    match i with
    | 0 =>
      have h0 : body.uses 0 = true := by simpa [shift] using h
      simp [h0]
    | 1 =>
      have h1 : body.uses 1 = true := by simpa [shift] using h
      simp [h1]
    | k + 2 => split <;> split <;> simpa using h
  refine bodySpec _ _ (shift 2 live) h (base + sTy.width + tTy.width) heap2 store2
    { s3 with values := s.values } (f3.half.trans hh1) (hp3.trans hpv) e2'.holds e2'.step.at_
    (by rw [e2'.step.cap m, a1.step.cap m]; exact hCap)
    (by show s3.params.length ≤ base + sTy.width + tTy.width; rw [hp3]; omega)
    (by omega) hPlace.2 _ _
    (hTrap.part (by flag_tac) (fun h => by
      have hmo := e.mode_owned (slots.map Slot.mode)
      rw [Slot.any_map] at hmo
      simp only [List.any_cons, Expr.aborts] at h ⊢
      exact let_trap_body2 _ _ _ _ (fun hv => hmo (by simpa using hv)) h) fun hd hw => by
        simp only [Expr.allocs] at hw
        exact hw.shift (heap1 := heap2) (store1 := store2)
          (c1 := e.allocs funs bounds (slots.map Slot.mode) (fun i => live i || body.uses (i + 2))
            env)
          (by have := hTop1 (hd1 hd); have := congrArg UInt64.toNat hTop2; omega)
          (by simp only [List.map_cons]; omega) (by rw [e2'.step.cap m, a1.step.cap m]))
    fun heap3 store3 s4 ws4 aB hTop3 => ?_
  have aB' := After.prepend hVarsB e2' aB (fun i h => live_right _ _ _ h) fun i h => by simp [h]
  have hNew : ∀ r, (∀ b ∈ (e.mode (slots.map Slot.mode)).fresh store1 (.pair sTy tTy) (wf ++ wsec)
      (e.denote funs env), regionsDisjoint r b) →
      ((e.mode (slots.map Slot.mode)) = .owned → ∀ w,
        LocalsHold { s3 with values := s.values } (base + sTy.width) tTy.types w →
        w.length = tTy.width →
        ∀ b ∈ tTy.blocks store1 w (e.denote funs env).2, regionsDisjoint r b) ∧
      ((e.mode (slots.map Slot.mode)) = .owned → ∀ w,
        LocalsHold { s3 with values := s.values } base sTy.types w → w.length = sTy.width →
        ∀ b ∈ sTy.blocks store1 w (e.denote funs env).1, regionsDisjoint r b) := by
    intro r hFresh
    rw [Mode.fresh_pair hlf] at hFresh
    refine ⟨fun hmo w hw hlw b hb => ?_, fun hmo w hw hlw b hb => ?_⟩
    · obtain rfl := LocalsHold.unique hw hold2' (hlw.trans hls.symm)
      rw [hmo] at hFresh
      exact hFresh b (List.mem_append_right _ hb)
    · obtain rfl := LocalsHold.unique hw hold1' (hlw.trans hlf.symm)
      rw [hmo] at hFresh
      exact hFresh b (List.mem_append_left _ hb)
  exact hNext heap3 store3 s4 ws4
    ((After.bind2 (hVars.live_mono hV) a1' f3 aB' (by omega) hNew
      (fun i h => by simpa using h) (fun i h => by simp [h]) fun i h => by simp [h]).liveIn hV)
    fun hd => by
      have := hTop1 (hd1 hd); have h3 := hTop3 (hd3 hd); have := congrArg UInt64.toNat hTop2
      simp only [List.map_cons] at h3
      simp only [Expr.allocs]; omega

/-- The code of a call's arguments pushes words that represent their values in the modes
`modes`, in order.  An argument without arrays runs its code with the variables `all` live after
it, so that no argument consumes a variable.  A borrowed argument with arrays, a place, loads its
variables' words.  An owned argument, a variable, loads its words when it is owned and not in
`kept`, which moves it into the call, and is copied otherwise.  The copies are the fresh blocks
`F` of the arguments' step.  The owned arguments' blocks lie apart from one another and from the
borrowed arguments' arrays, and a region apart from `F` and from the blocks of the moved
variables lies apart from the owned arguments' blocks.  A region apart from the variables that
the arguments with arrays read lies apart from the borrowed arguments' arrays. -/
theorem args_specB (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {all kept : Nat → Bool} {h base : Nat} {d a : Bool} :
    {ps : List Ty} → (modes : Nat → Mode) →
    (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) →
    (∀ i env slots live, CodeSpecB m funs bounds host pv (args i) env slots live) →
    (∀ i k, (args i).uses k = true → all k = true) → (∀ k, kept k = true → all k = true) →
    (∀ i : Fin ps.length, modes i = .owned → (ps.get i).scalar = false) →
    (∀ i, (ps.get i).scalar = false → modes i = .borrowed → (args i).isPlace = true) →
    (∀ i : Fin ps.length, modes i = .owned → ∃ x : Var Γ (ps.get i), args i = .var x ∧
      (kept x.index = false → (slots.getD x.index default).mode = .owned ∧
        ∀ j : Fin ps.length, j ≠ i → (ps.get j).scalar = false →
          (args j).uses x.index = false)) →
    (∀ i, (args i).placeArgs = true) →
    (∀ i, (args i).depthCalls = true → d = true) →
    (∀ i, ((args i).aborts || modes i == .owned || slots.any (·.mode == .owned)) = true →
      a = true) →
    ∀ (heap : Heap) (store : Store Unit) (s : Locals), s.half = h → s.params = pv →
    Holds env slots all base heap store s → heap.At store → store.memoryCap m 0 ≤ 65535 →
    s.params.length ≤ base →
    (∀ i : Fin ps.length,
      base + (if modes i = .owned then copyWidth (ps.get i) else (args i).width) ≤ h) →
    ∀ (rest : Program) (Q : Assertion Unit),
    TrapOK (d || (a && !decide (heap.Within store m
      (argsSum (argCost funs bounds (slots.map Slot.mode) all kept modes args env))))) Q →
    (∀ heap' store' s' ws F, Step heap store (fun _ => True) heap' store' F →
      Frame base s s' → Holds env slots all base heap' store' s' →
      Env.Rep modes heap' store' ws (Env.ofFn fun i => (args i).denote funs env) →
      Separate store' (Env.moves modes ws (Env.ofFn fun i => (args i).denote funs env))
        (Env.reads modes ws (Env.ofFn fun i => (args i).denote funs env)) →
      (∀ r, (∀ b ∈ F, regionsDisjoint r b) →
        Holds.KeepDying env slots
          (fun k => argsAny fun i => modes i == .owned && (args i).uses k && !kept k)
          (fun _ => false) store s r →
        Apart store' (Env.moves modes ws (Env.ofFn fun i => (args i).denote funs env)) r) →
      (∀ r, Holds.ApartFrom env slots
          (fun k => argsAny fun i => !(ps.get i).scalar && (args i).uses k) store s r →
        ∀ c ∈ Env.reads modes ws (Env.ofFn fun i => (args i).denote funs env),
          regionsDisjoint r c) →
      (d = false → heap'.top.toNat ≤ heap.top.toNat +
        argsSum (argCost funs bounds (slots.map Slot.mode) all kept modes args env)) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) →
    wp m (argsCode (fun i => if (ps.get i).scalar then (args i).code h slots base all
      else if modes i = .owned then (args i).ownedCode h slots base kept
      else (args i).placeCode h slots) ++ rest) Q store s host
  | [], _, _, _, _, _, _, _, _, _, _, _, heap, store, s, _, _, hVars, hAt, _, _, _, rest, Q, _,
      hNext => by
    simpa [argsCode, Env.ofFn, Env.Rep, Env.moves, Env.reads] using
      hNext heap store s [] [] (Step.refl hAt _) (Frame.refl base s) hVars rfl Separate.nil
        (fun _ _ _ => Apart.nil) (fun _ _ _ h => nomatch h) fun _ => Nat.le_add_right _ _
  | p :: ps, modes, args, argsSpec, hUses, hKept, hArray, hPlace, hOwned, hPlaceArgs, hdA, haA,
      heap, store, s, hh, hpv, hVars, hAt, hCap, hBase, hRoom, rest, Q, hTrap, hNext => by
    simp only [argsCode, List.append_assoc]
    have hSum : argsSum (argCost funs bounds (slots.map Slot.mode) all kept modes args env) =
        argCost funs bounds (slots.map Slot.mode) all kept modes args env ⟨0, by simp⟩ +
          argsSum (argCost funs bounds (slots.map Slot.mode) all kept (fun i => modes (i + 1))
            (fun i : Fin ps.length => args i.succ) env) := rfl
    have hd0 : d = false → (args ⟨0, by simp⟩).depthCalls = false := fun hd => by
      cases h0 : (args ⟨0, by simp⟩).depthCalls
      · rfl
      · rw [hdA _ h0] at hd; exact nomatch hd
    -- The other arguments, from the state after the first, and the facts of all of them.
    have hRest : ∀ heap1 store1 s1 ws0 F0,
        (d = false → heap1.top.toNat ≤ heap.top.toNat +
          argCost funs bounds (slots.map Slot.mode) all kept modes args env ⟨0, by simp⟩) →
        Step heap store (fun _ => True) heap1 store1 F0 → Frame base s s1 →
        Holds env slots all base heap1 store1 s1 →
        p.Rep (modes 0) heap1 store1 ws0 ((args ⟨0, by simp⟩).denote funs env) →
        (∀ r, (∀ b ∈ F0, regionsDisjoint r b) →
          Holds.KeepDying env slots
            (fun k => modes 0 == .owned && (args ⟨0, by simp⟩).uses k && !kept k)
            (fun _ => false) store s r →
          ∀ q ∈ (match modes 0 with | .owned => p.pointers ws0 | .borrowed => []),
            regionsDisjoint r (block store1 q)) →
        (∀ q ∈ (match modes 0 with | .owned => p.pointers ws0 | .borrowed => []),
          Holds.ApartFrom env slots (fun k => argsAny fun i : Fin ps.length =>
            !(ps.get i).scalar && (args i.succ).uses k) store1 s1 (block store1 q)) →
        (∀ r, Holds.ApartFrom env slots (fun k => !p.scalar && (args ⟨0, by simp⟩).uses k)
            store s r →
          ∀ c ∈ (match modes 0 with
            | .owned => []
            | .borrowed => p.reads ws0 ((args ⟨0, by simp⟩).denote funs env)),
            regionsDisjoint r c) →
        wp m (argsCode (fun i : Fin ps.length =>
            if ((p :: ps).get i.succ).scalar then (args i.succ).code h slots base all
            else if modes i.succ = .owned then (args i.succ).ownedCode h slots base kept
            else (args i.succ).placeCode h slots) ++ rest) Q store1
          { s1 with values := ws0.reverse ++ s.values } host := by
      intro heap1 store1 s1 ws0 F0 hTop0 hStep1 hF1 hH1 hR1 h5a h5c h6b
      have hl0 := hR1.length
      have hAllUses : ∀ (i : Fin ps.length) k, (args i.succ).uses k = true → all k = true :=
        fun i => hUses i.succ
      refine args_specB hm (fun i => modes (i + 1)) (fun i => args i.succ)
        (fun i => argsSpec i.succ) hAllUses hKept (fun i => hArray i.succ)
        (fun i => hPlace i.succ) (fun i hmo => ?_) (fun i => hPlaceArgs i.succ)
        (fun i => hdA i.succ) (fun i => haA i.succ) heap1
        store1 { s1 with values := ws0.reverse ++ s.values } (hF1.half.trans hh)
        (hF1.params.trans hpv) (hH1.agree Frame.ofValues) hStep1.at_ (by rw [hStep1.cap m]; exact
            hCap)
        (by show s1.params.length ≤ base; rw [hF1.params]; exact hBase)
        (fun i => hRoom i.succ) _ _
        (hTrap.part id id fun hd hw => hw.shift (heap1 := heap1) (store1 := store1)
          (hTop0 hd) (by rw [hSum]) (hStep1.cap m))
        fun heap2 store2 s2 ws2 F2 hStep2 hF2 hH2 hRep2 hSep2 hX2 hY2 hTop2 => ?_
      · obtain ⟨x, hx, hk⟩ := hOwned i.succ hmo
        exact ⟨x, hx, fun h => ⟨(hk h).1, fun j hj hs => (hk h).2 j.succ
          (fun he => hj (Fin.succ_injective _ he)) hs⟩⟩
      -- The first argument's value and its regions in the final state.
      obtain ⟨hR0, hSame0, hFresh0⟩ := hR1.step hStep2 fun _ _ => trivial
      have hBlock : ∀ q ∈ (match modes 0 with | .owned => p.pointers ws0 | .borrowed => []),
          block store2 q = block store1 q ∧ ∀ b ∈ F2, regionsDisjoint (block store1 q) b := by
        intro q hq
        cases hmd : modes 0 with
        | borrowed => rw [hmd] at hq; exact nomatch hq
        | owned =>
          rw [hmd] at hq hSame0 hFresh0
          simp only [Ty.regions, Ty.blocks_pointers] at hSame0 hFresh0
          exact ⟨List.map_inj_left.mp hSame0 q hq, hFresh0 _ (List.mem_map_of_mem hq)⟩
      have hMoves : Env.moves modes (ws0 ++ ws2)
          (Env.ofFn fun i : Fin (p :: ps).length => (args i).denote funs env) =
          (match modes 0 with | .owned => p.pointers ws0 | .borrowed => []) ++
            Env.moves (fun i => modes (i + 1)) ws2
              (Env.ofFn fun i : Fin ps.length => (args i.succ).denote funs env) :=
        Env.moves_cons hl0
      have hReads : Env.reads modes (ws0 ++ ws2)
          (Env.ofFn fun i : Fin (p :: ps).length => (args i).denote funs env) =
          (match modes 0 with
            | .owned => []
            | .borrowed => p.reads ws0 ((args ⟨0, by simp⟩).denote funs env)) ++
            Env.reads (fun i => modes (i + 1)) ws2
              (Env.ofFn fun i : Fin ps.length => (args i.succ).denote funs env) :=
        Env.reads_cons hl0
      -- A variable that a later owned argument moves is apart from the first argument's arrays.
      have hMovedRest : ∀ c ∈ (match modes 0 with
          | .owned => []
          | .borrowed => p.reads ws0 ((args ⟨0, by simp⟩).denote funs env)),
          Holds.KeepDying env slots (fun k => argsAny fun i : Fin ps.length =>
            modes (i + 1) == .owned && (args i.succ).uses k && !kept k) (fun _ => false) store1
            { s1 with values := ws0.reverse ++ s.values } c := by
        intro c hc t x hx _ hmx wx hwx hlx b hb
        obtain ⟨i, hi⟩ := argsAny_true.mp hx
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hi
        obtain ⟨⟨hmo, hux⟩, hkx⟩ := hi
        obtain ⟨y, hy, hk⟩ := hOwned i.succ hmo
        have hxy : x.index = y.index := by
          have := hux
          rw [hy] at this
          simpa [Expr.uses] using this
        have hNot0 := (hk (hxy ▸ hkx)).2 ⟨0, by simp⟩
          (fun he => absurd (congrArg Fin.val he) (Nat.succ_ne_zero _).symm)
        have hwx' := (hH1.hold_agree Frame.ofValues (hUses _ _ hux) hlx).mp hwx
        have hSameX := (hVars.regions_after hStep1 (hUses _ _ hux)
          ((hVars.hold_agree hF1 (hUses _ _ hux) hlx).mp hwx') hlx
          fun _ _ => trivial).1
        simp only [Ty.regions, hmx] at hSameX
        rw [hSameX] at hb
        refine regionsDisjoint_symm (h6b b ?_ c hc)
        refine Holds.ApartFrom.owned hVars (hUses _ _ hux) hmx
          ((hVars.hold_agree hF1 (hUses _ _ hux) hlx).mp hwx') hlx
          (fun k hk' => ?_) b hb
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk'
        refine ⟨hUses _ _ hk'.2, fun he => ?_⟩
        rw [he, hxy] at hk'
        have := hNot0 hk'.1
        rw [hk'.2] at this
        exact nomatch this
      have e := hNext heap2 store2 s2 (ws0 ++ ws2) (F0 ++ F2)
        (hStep1.transBoth hStep2 fun _ _ => ⟨trivial, fun _ => trivial⟩)
        (hF1.trans hF2.values) (hH2.agree Frame.ofValues) ⟨ws0, ws2, rfl, hR0, hRep2⟩ ?_ ?_ ?_
        (fun hd => by have := hTop0 hd; have := hTop2 hd; rw [hSum]; omega)
      · simpa [List.reverse_append, List.append_assoc] using e
      · -- The owned arguments' blocks are pairwise apart, and apart from the borrowed arrays.
        rw [hMoves, hReads]
        refine ⟨?_, fun c hc => ?_⟩
        · rw [List.map_append]
          refine List.pairwise_append.mpr ⟨?_, hSep2.1, fun a ha b hb => ?_⟩
          · cases hmd : modes 0 with
            | borrowed => exact List.Pairwise.nil
            | owned =>
              rw [hmd] at hR0
              have := hR0.pairwise
              rwa [Ty.blocks_pointers] at this
          · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
            obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hb
            obtain ⟨hEq, hF⟩ := hBlock q hq
            rw [hEq]
            exact hX2 _ hF (Holds.ApartFrom.keepDying (liveIn := fun k =>
                argsAny fun i : Fin ps.length =>
                  modes (↑i + 1) == .owned && (args i.succ).uses k && !kept k)
                (liveOut := fun _ => false) (h5c q hq) fun k hk _ => by
              obtain ⟨i, hi⟩ := argsAny_true.mp hk
              simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hi
              refine argsAny_true.mpr ⟨i, ?_⟩
              simp only [Bool.and_eq_true, Bool.not_eq_true']
              exact ⟨hArray i.succ hi.1.1, hi.1.2⟩) q' hq'
        · rcases List.mem_append.mp hc with hc | hc
          · refine Apart.append (fun q hq => ?_) (hX2 c ?_ (hMovedRest c hc))
            · cases hmd : modes 0 with
              | borrowed => rw [hmd] at hq; exact nomatch hq
              | owned => rw [hmd] at hc; exact nomatch hc
            · cases hmd : modes 0 with
              | owned => rw [hmd] at hc; exact nomatch hc
              | borrowed =>
                rw [hmd] at hc hFresh0
                exact hFresh0 c hc
          · refine Apart.append (fun q hq => ?_) (hSep2.2 c hc)
            obtain ⟨hEq, -⟩ := hBlock q hq
            rw [hEq]
            exact regionsDisjoint_symm (hY2 _ (h5c q hq) c hc)
      · -- A region apart from the copies and the moved variables lies apart from every owned
        -- argument's blocks.
        intro r hr hk
        rw [hMoves]
        refine Apart.append (fun q hq => ?_) (hX2 r (fun b hb => hr b (List.mem_append_right _ hb))
          ?_)
        · rw [(hBlock q hq).1]
          exact h5a r (fun b hb => hr b (List.mem_append_left _ hb))
            (hk.mono fun i h1 _ => ⟨le_argsAny (fun j : Fin (p :: ps).length =>
              modes j == .owned && (args j).uses i && !kept i) ⟨0, by simp⟩ h1, rfl⟩) q hq
        · refine Holds.KeepDying.transfer (s1 := { s1 with values := ws0.reverse ++ s.values })
            (liveIn := fun k => argsAny fun i : Fin ps.length =>
              modes (↑i + 1) == .owned && (args i.succ).uses k && !kept k)
            (liveOut := fun _ => false) hVars (hStep1.mono (fun _ _ => trivial) fun _ h => h)
            (hF1.trans Frame.ofValues) (fun _ h => h) (fun i h _ => ?_)
            (hk.mono fun i h1 _ => ⟨by
              obtain ⟨j, hj⟩ := argsAny_true.mp h1
              exact le_argsAny (fun j : Fin (p :: ps).length =>
                modes j == .owned && (args j).uses i && !kept i) j.succ hj, rfl⟩)
          obtain ⟨j, hj⟩ := argsAny_true.mp h
          simp only [Bool.and_eq_true] at hj
          exact hUses _ _ hj.1.2
      · -- A region apart from the variables that the arguments with arrays read lies apart from
        -- the borrowed arguments' arrays.
        intro r hr c hc
        rw [hReads] at hc
        rcases List.mem_append.mp hc with hc | hc
        · exact h6b r (hr.mono fun i h => le_argsAny (fun j : Fin (p :: ps).length =>
            !((p :: ps).get j).scalar && (args j).uses i) ⟨0, by simp⟩ h) c hc
        · refine hY2 r ((Holds.ApartFrom.iff hVars hStep1 hF1
            (fun k hk => ?_)).mpr (hr.mono fun i h => by
              obtain ⟨j, hj⟩ := argsAny_true.mp h
              exact le_argsAny (fun j : Fin (p :: ps).length =>
                !((p :: ps).get j).scalar && (args j).uses i) j.succ hj)) c hc
          obtain ⟨j, hj⟩ := argsAny_true.mp hk
          simp only [Bool.and_eq_true] at hj
          exact hUses _ _ hj.2
    by_cases hp : p.scalar = true
    · -- An argument without arrays: its code, with every argument's variables live after it.
      rw [ite_eq_left (show ((p :: ps).get ⟨0, by simp⟩).scalar = true from hp)]
      have hmd : modes 0 = .borrowed := by
        cases h : modes 0 with
        | borrowed => rfl
        | owned => have := hArray ⟨0, by simp⟩ h; simp [hp] at this
      have hSub : ∀ k, (all k || (args ⟨0, by simp⟩).uses k) = true → all k = true :=
        fun k h => by
          simp only [Bool.or_eq_true] at h
          exact h.elim id (hUses _ k)
      have hRoom0 := hRoom ⟨0, by simp⟩
      simp only [show modes ↑(⟨0, by simp⟩ : Fin (p :: ps).length) = .borrowed from hmd,
        reduceCtorEq, ↓reduceIte] at hRoom0
      have hc0 : argCost funs bounds (slots.map Slot.mode) all kept modes args env ⟨0, by simp⟩ =
          (args ⟨0, by simp⟩).allocs funs bounds (slots.map Slot.mode) all env := by
        simp only [argCost]; rw [if_pos (show ((p :: ps).get ⟨0, by simp⟩).scalar = true from hp)]
      refine argsSpec ⟨0, by simp⟩ env slots all h base heap store s hh hpv (hVars.live_mono
          hSub)
        hAt hCap hBase hRoom0 (hPlaceArgs _) _ _
        (hTrap.part (hdA _) (fun h => haA _ (by
            simp only [Bool.or_eq_true] at h ⊢; tauto))
          fun _ hw => hw.mono (by rw [hSum, hc0]; exact Nat.le_add_right _ _))
        fun heap1 store1 s1 ws1 a1 hTop1 => ?_
      have hStep := a1.step
      rw [Mode.fresh_scalar (show ((p :: ps).get ⟨0, by simp⟩).scalar = true from hp)] at hStep
      refine hRest heap1 store1 s1 ws1 [] (fun hd => by rw [hc0]; exact hTop1 (hd0 hd))
        (hStep.mono (fun _ _ => (Holds.KeepDying.none).mono
          fun i h1 h2 => ⟨hSub i h1, h2⟩) fun _ h => h) a1.frame a1.holds
        (by rw [hmd]; exact a1.rep.borrow) (fun _ _ _ q hq => ?_) (fun q hq => ?_)
        (fun _ _ c hc => ?_)
      · rw [hmd] at hq; exact nomatch hq
      · rw [hmd] at hq; exact nomatch hq
      · rw [hmd, Ty.reads_scalar _ hp] at hc; exact nomatch hc
    · rw [ite_eq_right (show ¬((p :: ps).get ⟨0, by simp⟩).scalar = true from hp)]
      cases hmd : modes 0 with
      | owned =>
        -- An owned argument, a variable: moved when it dies, and copied otherwise.
        rw [ite_eq_left (rfl : Mode.owned = Mode.owned)]
        obtain ⟨x, hx, hk⟩ := hOwned ⟨0, by simp⟩ hmd
        have hux : (args ⟨0, by simp⟩).uses x.index = true := by rw [hx]; simp [Expr.uses]
        have hAllX := hUses _ _ hux
        have hv : (args ⟨0, by simp⟩).denote funs env = env.get x := by rw [hx]; rfl
        rw [show (args ⟨0, by simp⟩).ownedCode h slots base kept = x.ownedCode h slots base kept by
          rw [hx]; rfl]
        cases hkx : kept x.index with
        | false =>
          obtain ⟨hmx, hOthers⟩ := hk hkx
          rw [Var.ownedCode_move x hmx hkx]
          obtain ⟨-, ws, hold, hRep⟩ := hVars.get x hAllX
          refine wp_loadCode ws hRep.typed hh hold (hRest heap store s ws []
            (fun _ => Nat.le_add_right _ _) (Step.refl hAt _)
            (Frame.refl base s) hVars (by rw [hmd, hv, ← hmx]; exact hRep)
            (fun r _ hr q hq => ?_) (fun q hq => ?_) (fun _ _ c hc => ?_))
          · rw [hmd] at hq
            refine hr _ x (by simp only [hmd, hux, hkx]; rfl) rfl hmx ws hold hRep.length _ ?_
            rw [Ty.blocks_pointers]
            exact List.mem_map_of_mem hq
          · rw [hmd] at hq
            refine Holds.ApartFrom.owned hVars hAllX hmx hold hRep.length (fun k hk' => ?_) _
              (by rw [Ty.blocks_pointers]; exact List.mem_map_of_mem hq)
            obtain ⟨j, hj⟩ := argsAny_true.mp hk'
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hj
            refine ⟨hUses _ _ hj.2, fun he => ?_⟩
            have := hOthers j.succ (fun h => absurd (congrArg Fin.val h) (Nat.succ_ne_zero _)) hj.1
            rw [he] at hj
            rw [hj.2] at this
            exact nomatch this
          · rw [hmd] at hc; exact nomatch hc
        | true =>
          rw [Var.ownedCode_live x (live' := all) (by rw [hkx, hAllX])]
          have hRoom0 := hRoom ⟨0, by simp⟩
          simp only [show modes ↑(⟨0, by simp⟩ : Fin (p :: ps).length) = .owned from hmd,
            ↓reduceIte] at hRoom0
          have hc0 : argCost funs bounds (slots.map Slot.mode) all kept modes args env ⟨0, by simp⟩ =
              x.ownedCost (slots.map Slot.mode) all (env.get x) := by
            simp only [argCost]
            rw [if_neg (show ¬((p :: ps).get ⟨0, by simp⟩).scalar = true from hp),
              if_pos (show modes ↑(⟨0, by simp⟩ : Fin (p :: ps).length) = .owned from hmd), hx]
            simp only [Expr.ownedCost, Var.ownedCost, Var.cost, hkx, hAllX]
          refine specB_ownedVar hm x hh hpv (hVars.live_mono fun i h => by
              simp only [Bool.or_eq_true, beq_iff_eq] at h
              exact h.elim id fun he => he ▸ hAllX) hAt hCap hBase hRoom0
            (hTrap.alloc (haA ⟨0, by simp⟩ (by simp [hmd])) fun _ hw => hw.mono (by
              rw [hSum, hc0]; exact Nat.le_add_right _ _))
            fun heap1 store1 s1 ws1 a1 hTop1 => ?_
          have hStep := a1.step
          simp only [Mode.fresh] at hStep
          refine hRest heap1 store1 s1 ws1 (p.blocks store1 ws1 (env.get x))
            (fun _ => by rw [hc0]; exact hTop1)
            (hStep.mono (fun _ _ => (Holds.KeepDying.none).mono fun i h1 h2 => ⟨by
              simp only [Bool.or_eq_true, beq_iff_eq] at h1
              exact h1.elim id fun he => he ▸ hAllX, h2⟩) fun _ h => h) a1.frame a1.holds
            (by rw [hmd, hv]; exact a1.rep) (fun r hr _ q hq => ?_) (fun q hq => ?_)
            (fun _ _ c hc => ?_)
          · rw [hmd] at hq
            exact hr _ (by rw [Ty.blocks_pointers]; exact List.mem_map_of_mem hq)
          · rw [hmd] at hq
            intro u y hy wy hwy hly c hc
            obtain ⟨j, hj⟩ := argsAny_true.mp hy
            simp only [Bool.and_eq_true] at hj
            exact a1.apart u y (hUses _ _ hj.2) (Or.inl rfl) wy hwy hly _
              (by simp only [Ty.regions]; rw [Ty.blocks_pointers]; exact List.mem_map_of_mem hq)
              c hc
          · rw [hmd] at hc; exact nomatch hc
      | borrowed =>
        -- A borrowed argument with arrays, a place: its variables' words.
        rw [ite_eq_right (show ¬(Mode.borrowed = Mode.owned) from nofun)]
        exact place_spec hh hVars (args ⟨0, by simp⟩) (hPlace _ (by simpa using hp) hmd)
          (fun k h => hUses _ k h) fun ws1 hR1 hReads1 =>
            hRest heap store s ws1 [] (fun _ => Nat.le_add_right _ _) (Step.refl hAt _)
              (Frame.refl base s) hVars
              (by rw [hmd]; exact hR1) (fun _ _ _ q hq => by rw [hmd] at hq; exact nomatch hq)
              (fun q hq => by rw [hmd] at hq; exact nomatch hq)
              fun r hr c hc => by
                rw [hmd] at hc
                exact hReads1 r (hr.mono fun k h => by
                  rw [Bool.and_eq_true]; exact ⟨by simpa using hp, h⟩) c hc

/-- The release of the owned variables that `sel` selects after an expression's code, those live
in `L1` and not in `live`, gives the facts of the code and the release for `live`.  The value lies
apart from the released blocks, so its words still represent it, and `top` is unchanged. -/
theorem After.releaseT (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 live sel : Nat → Bool} {base : Nat} {heap heap1 : Heap} {store store1 : Store Unit}
    {s s1 : Locals} {t : Ty} {mode : Mode} {v : t.denote} {ws vals : List Value}
    {rest : Program} {Q : Assertion Unit}
    (h0 : Holds env slots L0 base heap store s)
    (a : After env slots L0 L1 base heap store s t mode v heap1 store1 s1 ws)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hSel : ∀ i, sel i = true → L1 i = true)
    (hLive : ∀ i, live i = true → (L1 i && !sel i) = true)
    (hNext : ∀ heap2 store2,
      After env slots L0 live base heap store s t mode v heap2 store2 s1 ws →
      heap2.top = heap1.top → wp m rest Q store2 { s1 with values := vals } host) :
    wp m (releaseWhere Γ slots sel ++ rest) Q store1 { s1 with values := vals } host := by
  refine wp_releaseWhereT hm (a.holds.agree Frame.ofValues) a.step.at_ hSel
    fun heap2 store2 e hTop => ?_
  have e' := e.mono hLive
  have hLiveL1 : ∀ i, live i = true → L1 i = true := fun i h => by
    have := hLive i h
    simp only [Bool.and_eq_true] at this
    exact this.1
  -- The value lies apart from the blocks of the variables that die.
  have hKeepV : ∀ r ∈ t.regions mode store1 ws v,
      Holds.KeepDying env slots L1 live store1 { s1 with values := vals } r := by
    intro r hr u x hx _ hmx wx hwx hlx b hb
    have hb' : b ∈ u.regions (slots.getD x.index default).mode store1 wx (env.get x) := by
      rw [hmx]; exact hb
    exact a.apart u x hx (Or.inr hmx) wx hwx hlx r hr b hb'
  obtain ⟨hRep, hSame, -⟩ := a.rep.step e'.step hKeepV
  have hStep := a.step.transBoth (keep := Holds.KeepDying env slots L0 live store s) e'.step
    fun r hr =>
    ⟨hr.mono fun i h1 h2 => ⟨h1, by
        cases hl : live i with
        | false => rfl
        | true => rw [hLiveL1 i hl] at h2; exact nomatch h2⟩,
      fun _ => Holds.KeepDying.transfer h0 a.step a.frame hL1
        (fun i h1 _ => h1) (hr.mono fun i h1 h2 => ⟨hL1 _ h1, h2⟩)⟩
  refine hNext heap2 store2 ⟨hStep.mono (fun _ h => h) fun b hb => ?_, a.frame,
    e'.holds.agree Frame.ofValues, hRep, ?_⟩ hTop
  · rw [Mode.fresh_congr hSame] at hb
    exact List.mem_append_left _ hb
  · exact Holds.Apart.transfer (a.holds.live_mono hLiveL1) (a.apart.live_mono hLiveL1) e'.step
      Frame.ofValues (fun u y hy wy hwy hly => a.holds.keepDying hLiveL1 hy hwy hly) hSame

/-- A call: the arguments, the callee, whose theorem `Calls` gives, and the release of the owned
variables that the arguments use and that die at the call, other than those that the call
consumes. -/
theorem specB_call (hm : Runtime m) {d0 : UInt64} (hCalls : CallsAtB m funs bounds d0) {sig : Sig}
    {Γ' : List Ty} (g : FVar S sig)
    (args : (i : Fin sig.params.length) → Expr S Γ' (sig.params.get i))
    (argsSpec : ∀ i env slots live, CodeSpecB m funs bounds host pv (args i) env slots live)
    (hDepth : (Expr.call g args).depthCalls = true → pv.head? = some (.i64 d0)) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.call g args) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hRoom' : ∀ i : Fin sig.params.length, base + (if sig.mode i = .owned then
      copyWidth (sig.params.get i)
      else (args i).width) ≤ h := fun i =>
    (Nat.add_le_add_left (le_argsMax (fun i => if sig.mode i = .owned then
      copyWidth (sig.params.get i) else (args i).width) i) base).trans hRoom
  simp only [Expr.placeArgs, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hPlace
  obtain ⟨⟨hA, hV⟩, hB⟩ := hPlace
  have hPlace1 : ∀ i, (sig.params.get i).scalar = false → sig.mode i = .borrowed →
      (args i).isPlace = true := fun i hs _ => by
    cases hi : (args i).isPlace with
    | true => rfl
    | false =>
      have := le_argsAny (fun i => !(sig.params.get i).scalar && !(args i).isPlace) i
        (by simp only [hs, hi, Bool.not_false, Bool.and_self])
      rw [hA] at this
      exact nomatch this
  have hVar : ∀ i : Fin sig.params.length, sig.mode i = .owned → ∃ x, args i = .var x :=
      fun i hmo => by
    refine Expr.exists_var (args i) ?_
    cases hi : (args i).varIndex?.isNone with
    | false => rfl
    | true =>
      have := le_argsAny (fun i => sig.mode i == .owned && (args i).varIndex?.isNone) i
        (by simp [hmo, hi])
      rw [hV] at this
      exact nomatch this
  have hPlace2 : ∀ i, (args i).placeArgs = true := fun i => by
    cases hi : (args i).placeArgs with
    | true => rfl
    | false =>
      have := le_argsAny (fun i => !(args i).placeArgs) i (by simp [hi])
      rw [hB] at this
      exact nomatch this
  -- The variables that the call consumes: those that an argument moves.
  have hMoved : ∀ k, (argsAny fun j => callMoves slots live args j && (args j).uses k) = true →
      ∃ j x, args j = .var x ∧ x.index = k ∧ sig.mode j = .owned ∧
        (slots.getD k default).mode = .owned ∧ live k = false ∧
        ∀ j', j' ≠ j → (sig.params.get j').scalar = false → (args j').uses k = false := by
    intro k hk
    obtain ⟨j, hj⟩ := argsAny_true.mp hk
    simp only [Bool.and_eq_true, callMoves, beq_iff_eq] at hj
    obtain ⟨⟨hmo, hj⟩, hu⟩ := hj
    obtain ⟨x, hx⟩ := hVar j hmo
    rw [hx] at hj hu
    simp only [Expr.varIndex?, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hj
    simp only [Expr.uses, beq_iff_eq] at hu
    subst hu
    obtain ⟨⟨hmx, hlx⟩, hOthers⟩ := hj
    refine ⟨j, x, hx, rfl, hmo, hmx, hlx, fun j' hj' hs => ?_⟩
    cases hu : (args j').uses x.index with
    | false => rfl
    | true =>
      have := le_argsAny (fun j' => j' != j && !(sig.params.get j').scalar &&
        (args j').uses x.index) j' (by rw [hs, hu]; simp [hj'])
      rw [hOthers] at this
      exact nomatch this
  have hAllocs : (Expr.call g args).allocs funs bounds (slots.map Slot.mode) live env =
      argsSum (argCost funs bounds (slots.map Slot.mode)
        (fun i => live i || argsAny fun j => (args j).uses i)
        (fun i => (live i || argsAny fun j => (args j).uses i) &&
          !(argsAny fun j => callMoves slots live args j && (args j).uses i)) sig.mode args env) +
        bounds.get g (Env.ofFn fun i => (args i).denote funs env) := by
    simp only [Expr.allocs, callMovesAt_eq]; rfl
  simp only [Expr.code, List.append_assoc]
  refine wp_depthCode sig.depth (fun hd => by
    rw [hpv]; exact hDepth (by simp [Expr.depthCalls, hd])) ?_
  refine args_specB hm (all := fun i => live i || argsAny fun j => (args j).uses i)
    (kept := fun i => (live i || argsAny fun j => (args j).uses i) &&
      !(argsAny fun j => callMoves slots live args j && (args j).uses i)) sig.mode args argsSpec
    (fun i k h => by
      simp only [Bool.or_eq_true]
      exact Or.inr (le_argsAny (fun j => (args j).uses k) i h))
    (fun k h => by simp only [Bool.and_eq_true] at h; exact h.1)
    (fun i hmo => ?_) hPlace1 (fun i hmo => ?_) hPlace2
    (fun i h => by
      simp only [Expr.depthCalls, Bool.or_eq_true]; exact Or.inr (le_argsAny _ i h))
    (fun i h => by
      simp only [Bool.or_eq_true] at h
      simp only [Expr.aborts, Bool.or_eq_true]
      rcases h with h | h
      · exact Or.inl (Or.inr (le_argsAny (fun j => (args j).aborts || sig.mode j == .owned) i
          (by simpa only [Bool.or_eq_true] using h)))
      · exact Or.inr h) heap store
    { s with values := (if sig.depth then [.i64 (d0 + 1)] else []) ++ s.values } hh hpv hVars hAt
    hCap hBase hRoom' _ _
    (hTrap.part id id fun _ hw => hw.mono (by rw [hAllocs]; exact Nat.le_add_right _ _))
    fun heap1 store1 s1 ws1 F hStep1 hF1 hH1 hRep1 hSep1 hX1 hY1 hTop1 => ?_
  · -- An owned parameter holds arrays.
    have := paramMode_owned hmo
    exact this
  · obtain ⟨x, hx⟩ := hVar i hmo
    refine ⟨x, hx, fun hkx => ?_⟩
    have hux : (args i).uses x.index = true := by rw [hx]; simp [Expr.uses]
    have hAll : (argsAny fun j => (args j).uses x.index) = true := le_argsAny _ i hux
    simp only [hAll, Bool.or_true, Bool.true_and, Bool.not_eq_false'] at hkx
    obtain ⟨j, y, hy, hyx, -, hmy, -, hOthers⟩ := hMoved _ hkx
    have hji : j = i := by
      by_contra hne
      have := hOthers i (Ne.symm hne) (paramMode_owned hmo)
      rw [hux] at this
      exact nomatch this
    subst hji
    exact ⟨hmy, hOthers⟩
  -- The callee, from the arguments' state, above the next call depth when its code takes it.
  replace hF1 : Frame base s s1 := hF1.values
  simp only [Holds.keepDying_values] at hX1
  have hRun := FunSpecB.runs (hCalls g) hm host hStep1.at_ hRep1 hSep1
    (by rw [hStep1.cap m]; exact hCap) (d := d0 + 1) (fun _ => rfl) s.values
  have hsd : (Expr.call g args).depthCalls = false → sig.depth = false := fun hd => by
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.1
  refine wp_call_runs hRun (hTrap.of_imp fun h => by
    simp only [trapFlag, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h ⊢
    cases hdc : (Expr.call g args).depthCalls
    · rcases h with ⟨ha, hw⟩ | hd
      · have hab : ((Expr.call g args).aborts || slots.any (·.mode == .owned)) = true := by
          simp only [Expr.aborts, Bool.or_eq_true]; exact Or.inl (Or.inl (Or.inl (Or.inl ha)))
        refine Or.inr ⟨by simpa only [Bool.or_eq_true] using hab, fun hW => hw ?_⟩
        rw [hAllocs] at hW
        exact hW.shift (hTop1 hdc) le_rfl (hStep1.cap m)
      · rw [hsd hdc] at hd; exact nomatch hd
    · exact Or.inl rfl) fun st' vs hPost => ?_
  obtain ⟨out, rfl, heap', hAt', hOwned, hCaps, hRegions, hTopC⟩ := hPost
  have hRep : sig.result.Rep ((Expr.call g args).mode (slots.map Slot.mode)) heap' st'
      out.reverse (funs.get g (Env.ofFn fun i => (args i).denote funs env)) := by
    simp only [Expr.mode]
    split
    · exact Ty.Rep.borrow hOwned
    · exact hOwned
  have hStepC : Step heap1 store1
      (Apart store1 (Env.moves sig.mode ws1 (Env.ofFn fun i => (args i).denote funs env))) heap'
      st' (((Expr.call g args).mode (slots.map Slot.mode)).fresh st' sig.result out.reverse
        (funs.get g (Env.ofFn fun i => (args i).denote funs env))) :=
    ⟨hAt', hCaps, fun r hr hpos hA => by
      obtain ⟨hb, hreg, hout⟩ := hRegions r hr hpos hA
      exact ⟨hb, hreg, fun b hb' => hout b (Mode.fresh_sub hb')⟩⟩
  -- The variables live after the call: those that its arguments use, other than the moved ones.
  have hKeptAll : ∀ i, ((live i || argsAny fun j => (args j).uses i) &&
      !(argsAny fun j => callMoves slots live args j && (args j).uses i)) = true →
      (live i || argsAny fun j => (args j).uses i) = true :=
    fun i h => by simp only [Bool.and_eq_true] at h; exact h.1
  have hMovedDie : ∀ i, (argsAny fun j => sig.mode j == .owned && (args j).uses i &&
      !((live i || argsAny fun j => (args j).uses i) &&
        !(argsAny fun j => callMoves slots live args j && (args j).uses i))) = true →
      (live i || argsAny fun j => (args j).uses i) = true ∧
        ((live i || argsAny fun j => (args j).uses i) &&
          !(argsAny fun j => callMoves slots live args j && (args j).uses i)) = false := by
    intro i h
    obtain ⟨j, hj⟩ := argsAny_true.mp h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hj
    refine ⟨?_, hj.2⟩
    simp only [Bool.or_eq_true]
    exact Or.inr (le_argsAny (fun j => (args j).uses i) j hj.1.2)
  have hKeepC : ∀ (u : Ty) (y : Var Γ' u),
      ((live y.index || argsAny fun j => (args j).uses y.index) &&
        !(argsAny fun j => callMoves slots live args j && (args j).uses y.index)) = true →
      ∀ wy, LocalsHold s1 (slots.getD y.index default).loc u.types wy → wy.length = u.width →
      ∀ c ∈ u.regions (slots.getD y.index default).mode store1 wy (env.get y),
        Apart store1 (Env.moves sig.mode ws1 (Env.ofFn fun i => (args i).denote funs env)) c := by
    intro u y hy wy hwy hly c hc
    have hyAll := hKeptAll _ hy
    have hwy' := (hVars.hold_agree hF1 hyAll hly).mp hwy
    obtain ⟨hSame, hFresh⟩ := hVars.regions_after hStep1 hyAll hwy' hly fun _ _ => trivial
    rw [hSame] at hc
    refine hX1 c (hFresh c hc) fun t x hx _ hmx wx hwx hlx b hb => ?_
    obtain ⟨hxAll, hxKept⟩ := hMovedDie _ hx
    have hne : x.index ≠ y.index := fun he => by rw [he, hy] at hxKept; exact nomatch hxKept
    exact regionsDisjoint_symm
      (hVars.2 t u x y hxAll hyAll hne hmx wx wy hwx hlx hwy' hly b hb c hc)
  have aCall : After env slots (fun i => live i || (Expr.call g args).uses i)
      (fun i => (live i || argsAny fun j => (args j).uses i) &&
        !(argsAny fun j => callMoves slots live args j && (args j).uses i)) base heap store s
      sig.result ((Expr.call g args).mode (slots.map Slot.mode))
      (funs.get g (Env.ofFn fun i => (args i).denote funs env)) heap' st' s1 out.reverse := by
    refine ⟨hStep1.trans hStepC fun r hr => ⟨trivial, fun hF => hX1 r hF
        (hr.mono fun i h _ => hMovedDie i h)⟩, hF1,
      (hH1.live_mono hKeptAll).step hStepC hKeepC, hRep, ?_⟩
    intro u y hy _ wy hwy hly b hb c hc
    obtain ⟨hSame, hFresh⟩ := (hH1.live_mono hKeptAll).regions_after hStepC hy hwy hly
      (hKeepC u y hy wy hwy hly)
    rw [hSame] at hc
    have hb' : b ∈ ((Expr.call g args).mode (slots.map Slot.mode)).fresh st' sig.result
        out.reverse (funs.get g (Env.ofFn fun i => (args i).denote funs env)) := by
      simp only [Expr.mode] at hb ⊢
      cases hsc : sig.result.scalar
      · simp only [hsc, Bool.false_eq_true, ↓reduceIte] at hb ⊢
        exact hb
      · simp only [hsc, ↓reduceIte] at hb
        rw [Ty.regions_scalar _ hsc] at hb
        exact nomatch hb
    exact regionsDisjoint_symm (hFresh c hc b hb')
  refine After.releaseT hm (s1 := s1) (live := live)
    (sel := fun i => ((live i || argsAny fun j => (args j).uses i) &&
      !(argsAny fun j => callMoves slots live args j && (args j).uses i)) && !live i) hVars aCall
    hKeptAll (fun i h => by simp only [Bool.and_eq_true] at h ⊢; exact h.1) (fun i h => ?_)
    fun heap2 store2 a2 hTopR => ?_
  · have hk : (argsAny fun j => callMoves slots live args j && (args j).uses i) = false := by
      cases hm' : argsAny fun j => callMoves slots live args j && (args j).uses i with
      | false => rfl
      | true =>
        obtain ⟨_, _, _, _, _, _, hl, _⟩ := hMoved i hm'
        rw [hl] at h
        exact nomatch h
    simp [h, hk]
  · simpa using hNext heap2 store2 s1 out.reverse a2 fun hd => by
      have := hTop1 hd; have := hTopC (hsd hd); have := congrArg UInt64.toNat hTopR
      rw [hAllocs]; omega

end Cases

end Verified
