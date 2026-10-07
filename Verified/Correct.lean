import Verified.Heap

/-! The compiler's correctness theorem: every function of a compiled program returns the value
that the program gives it, with the heap and store changed only as `ImplementsA` allows, and
without a trap when the function cannot trap. -/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem boolWord_and (x y : Bool) : boolWord x &&& boolWord y = boolWord (x && y) := by
  cases x <;> cases y <;> decide

theorem boolWord_or (x y : Bool) : boolWord x ||| boolWord y = boolWord (x || y) := by
  cases x <;> cases y <;> decide

theorem boolWord_not (x : Bool) :
    UInt64.ofNat ((if boolWord x = 0 then (1 : UInt32) else 0).toNat) = boolWord (!x) := by
  cases x <;> decide

@[simp] theorem shift_add (k : Nat) (live : Nat → Bool) (i : Nat) :
    shift k live (i + k) = live i := by
  simp [shift]

/-- Closes an inclusion between sets of live variables. -/
macro "live_tac" : tactic =>
  `(tactic| (intro i h; simp only [Expr.uses, Nat.add_assoc, Nat.reduceAdd, shift_add,
    Bool.or_eq_true] at h ⊢; tauto))

/-- The entry rule's assertion accepts the traps that its flag allows. -/
theorem _root_.Wasm.TrapOK.of_msg {a : Bool} {Q : Assertion Unit}
    (hQ : ∀ st, Q (.Trap st "unreachable") ↔ TrapMsg a "unreachable") : TrapOK a Q := by
  cases a
  · trivial
  · exact fun st => (hQ st).mpr rfl

theorem _root_.Wasm.TrapOK.of_imp {a b : Bool} {Q : Assertion Unit} (h : TrapOK b Q)
    (hab : a = true → b = true) : TrapOK a Q := by
  cases a
  · trivial
  · rw [hab rfl] at h; exact h

/-- The functions that `funs` gives are the module's functions at their call indices, each
returning its value with the heap and store changed only as `ImplementsA` allows, and without a
trap when the function cannot trap. -/
def Calls {S : List Sig} (m : Module) (funs : Funs S) : Prop :=
  ∀ {g : Sig} (f : FVar S g),
    @ImplementsA _ _ (Env.represent g.params) (Ty.represent g.result) g.aborts m f.callIndex
        (funs.get f) (fun _ _ _ => True) (fun _ _ _ _ _ => True) ∧
      ∃ fn, m.funcs[f.callIndex]? = some fn ∧ fn.numParams = widthSum g.params

theorem le_argsMax : {ps : List Ty} → (w : (i : Fin ps.length) → Nat) →
    (i : Fin ps.length) → w i ≤ argsMax w
  | _ :: _, w, ⟨0, _⟩ => Nat.le_max_left _ _
  | _ :: _, w, ⟨i + 1, h⟩ =>
    (le_argsMax (fun j => w j.succ) ⟨i, by simpa using h⟩).trans (Nat.le_max_right _ _)

theorem le_argsAny : {n : Nat} → (b : (i : Fin n) → Bool) → (i : Fin n) → b i = true →
    argsAny b = true
  | _ + 1, b, ⟨0, _⟩, h => by simp only [argsAny, Bool.or_eq_true]; exact Or.inl h
  | _ + 1, b, ⟨i + 1, hi⟩, h => by
    simp only [argsAny, Bool.or_eq_true]
    exact Or.inr (le_argsAny (fun j => b j.succ) ⟨i, by omega⟩ h)

/-- The state of `LeanExe.loop` after `k` iterations. -/
def loopState (init : α) (f : UInt64 → α → α) : Nat → α
  | 0 => init
  | k + 1 => f (UInt64.ofNat k) (loopState init f k)

theorem loopState_eq (n : UInt64) (init : α) (f : UInt64 → α → α) :
    loopState init f n.toNat = LeanExe.loop n init f := by
  unfold LeanExe.loop
  induction n.toNat with
  | zero => rfl
  | succ k ih => rw [Nat.fold_succ, ← ih]; rfl

theorem Mode.fresh_scalar {mode : Mode} {store : Store Unit} {t : Ty} (h : t.scalar = true)
    (ws : List Value) (v : t.denote) : mode.fresh store t ws v = [] := by
  cases mode
  · rfl
  · exact Ty.blocks_scalar t h ws v

theorem Mode.fresh_sub {mode : Mode} {store : Store Unit} {t : Ty} {ws : List Value}
    {v : t.denote} {b : Nat × Nat} (h : b ∈ mode.fresh store t ws v) : b ∈ t.blocks store ws v := by
  cases mode
  · exact nomatch h
  · exact h

theorem Mode.fresh_congr {mode : Mode} {store store' : Store Unit} {t : Ty} {ws : List Value}
    {v : t.denote} (h : t.regions mode store' ws v = t.regions mode store ws v) :
    mode.fresh store' t ws v = mode.fresh store t ws v := by
  cases mode
  · rfl
  · exact h

theorem Mode.fresh_pair {mode : Mode} {store : Store Unit} {a b : Ty} {first second : List Value}
    {p : a.denote × b.denote} (h : first.length = a.width) :
    mode.fresh store (.pair a b) (first ++ second) p =
      mode.fresh store a first p.1 ++ mode.fresh store b second p.2 := by
  cases mode
  · rfl
  · exact Ty.blocks_append h

theorem Slot.modes_getD (slots : List Slot) (i : Nat) :
    (slots.map Slot.mode).getD i .borrowed = (slots.getD i default).mode := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases slots[i]? <;> rfl

theorem Slot.any_owned {slots : List Slot} {i : Nat}
    (h : (slots.getD i default).mode = .owned) : slots.any (·.mode == .owned) = true := by
  simp only [List.getD_eq_getElem?_getD] at h
  cases hi : slots[i]? with
  | none => rw [hi] at h; exact nomatch h
  | some sl =>
    rw [hi] at h
    exact List.any_eq_true.mpr ⟨sl, List.mem_of_getElem? hi, by simp [Option.getD] at h; simp [h]⟩

/-- What the code of an expression leaves, from `heap` at `store` with locals `s`: a step that
consumes the blocks of the owned variables that die, those live in `liveIn` and not in `live`,
and whose fresh blocks are the value's blocks when it is owned; no change below `base`; the
variables live after still holding their values; the words `ws` representing the value `v` in
mode `mode`; and the value apart from those variables. -/
structure After {Γ : List Ty} (env : Env Γ) (slots : List Slot) (liveIn live : Nat → Bool)
    (base : Nat) (heap : Heap) (store : Store Unit) (s : Locals) (t : Ty) (mode : Mode)
    (v : t.denote) (heap' : Heap) (store' : Store Unit) (s' : Locals) (ws : List Value) :
    Prop where
  step : Step heap store (Holds.KeepDying env slots liveIn live store s) heap' store'
    (mode.fresh store' t ws v)
  frame : Frame base s s'
  holds : Holds env slots live base heap' store' s'
  rep : t.Rep mode heap' store' ws v
  apart : Holds.Apart env slots live store' s' t mode ws v

/-- The code of an expression, for the variables `live` live after it, pushes words that
represent its value: from any heap and store with the allocator invariant, in which the variables
live before the expression hold their values below `base` and the locals from `base` on are free,
the code ends as `After` states.  It may trap at `unreachable` when the expression may trap or an
owned variable is in scope, since only then does it allocate. -/
def CodeSpec {S : List Sig} {Γ : List Ty} {t : Ty} (m : Module) (funs : Funs S)
    (host : HostEnv Unit) (e : Expr S Γ t) (env : Env Γ) (slots : List Slot)
    (live : Nat → Bool) : Prop :=
  ∀ (base : Nat) (heap : Heap) (store : Store Unit) (s : Locals),
    Holds env slots (fun i => live i || e.uses i) base heap store s → heap.At store →
    store.memoryCap m 0 ≤ 65535 → s.params.length ≤ base →
    base + e.width ≤ s.params.length + s.locals.length → e.placeArgs = true →
    ∀ (rest : Program) (Q : Assertion Unit),
    TrapOK (e.aborts || slots.any (·.mode == .owned)) Q →
    (∀ heap' store' s' ws,
      After env slots (fun i => live i || e.uses i) live base heap store s t
        (e.mode (slots.map Slot.mode)) (e.denote funs env) heap' store' s' ws →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) →
    wp m (e.code slots base live ++ rest) Q store s host

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {host : HostEnv Unit}

/-- An expression that leaves its value where it found the state: a step that changes nothing,
for a value that consumes nothing. -/
theorem After.refl {Γ : List Ty} {env : Env Γ} {slots : List Slot} {liveIn live : Nat → Bool}
    {base : Nat} {heap : Heap} {store : Store Unit} {s : Locals} {t : Ty} {mode : Mode}
    {v : t.denote} {ws : List Value} (hAt : heap.At store)
    (hVars : Holds env slots liveIn base heap store s)
    (hLive : ∀ i, live i = true → liveIn i = true)
    (hRep : t.Rep mode heap store ws v) (hFresh : mode.fresh store t ws v = [])
    (hApart : Holds.Apart env slots live store s t mode ws v) :
    After env slots liveIn live base heap store s t mode v heap store s ws :=
  ⟨by rw [hFresh]; exact Step.refl hAt _, Frame.refl base s, hVars.live_mono hLive, hRep, hApart⟩

/-- A constant word. -/
theorem spec_word {Γ : List Ty} (value : UInt64) :
    ∀ env slots live,
      CodeSpec m funs host (Expr.word (S := S) (Γ := Γ) value) env slots live := by
  intro env slots live base heap store s hVars hAt _ _ _ _ rest Q _ hNext
  simpa [Expr.code, Expr.denote] using
    hNext heap store s [.i64 value] (After.refl hAt hVars (by intro i h; simp [h]) rfl
      (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .word rfl] at hb; exact nomatch hb)

/-- A constant `Bool`. -/
theorem spec_bool {Γ : List Ty} (value : Bool) :
    ∀ env slots live,
      CodeSpec m funs host (Expr.bool (S := S) (Γ := Γ) value) env slots live := by
  intro env slots live base heap store s hVars hAt _ _ _ _ rest Q _ hNext
  simpa [Expr.code, Expr.denote] using
    hNext heap store s [.i64 (boolWord value)] (After.refl hAt hVars (by intro i h; simp [h]) rfl
      (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .bool rfl] at hb; exact nomatch hb)

/-- A variable: read in place when borrowed, moved where it dies, and copied where it stays
live. -/
theorem spec_var (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} (x : Var Γ' tTy) :
    ∀ env slots live, CodeSpec m funs host (Expr.var (S := S) x) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom _ rest Q hTrap hNext
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
    refine wp_copyCode hm tTy hAt hCap
      (hTrap.of_imp fun _ => by simp [Slot.any_owned hOwned]) hRep hold hBelow hBase
      (by simpa [Expr.width] using hRoom) fun heap' store' s' ws' hStep hRep' hF => ?_
    have hHolds := (hVars.live_mono hLiveIn).step hStep (fun _ _ _ _ _ _ _ _ => trivial)
    refine hNext heap' store' s' ws' ⟨?_, hF, hHolds.frame hF le_rfl, ?_, ?_⟩
    · rw [hMode, hOwned]
      exact hStep.mono (fun _ _ => trivial) fun _ h => h
    · rw [hMode, hOwned]; exact hRep'
    · rw [hMode, hOwned]
      intro u y hy _ wy hwy hly b hb c hc
      have hwy' := ((hVars.live_mono hLiveIn).hold_agree (fun j hj => hF.below j hj) hy hly).mp
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
      refine wp_loadCode ws hl hold (hNext heap store s ws ⟨?_, Frame.refl base s,
        hVars.live_mono hLiveIn, ?_, ?_⟩)
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
      refine wp_loadCode ws hl hold (hNext heap store s ws (After.refl hAt hVars hLiveIn
        (by rw [hMode]; exact hRep) (by rw [hMode, hBorrowed]; rfl) ?_))
      rw [hMode]
      intro u y hy hm wy hwy hly b hb c hc
      rcases hm with hm | hm
      · exact absurd hm hOwned
      · have hne : y.index ≠ x.index := fun he => by
          rw [he] at hm; exact hOwned hm
        rw [hm] at hc
        exact regionsDisjoint_symm
          (hVars.2 u tTy y x (hLiveIn _ hy) hx hne hm wy ws hwy hly hold hl c hc b hb)

/-- The variables live before two expressions in a row: `a` for those live after both, and `v`
and `b` for those that the first and the second use. -/
theorem live_seq : ∀ a b v : Bool, (a || b || v) = true → (a || (v || b)) = true := by decide

/-- Two codes in a row, each with the facts of `After`, the first value on the stack below the
second's.  The second's step keeps the first value's regions, so the first value still holds
after it and lies apart from the variables live after both, and its regions lie apart from the
second's fresh blocks. -/
theorem After.seq {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L1 live : Nat → Bool}
    {base : Nat} {heap heap1 heap2 : Heap} {store store1 store2 : Store Unit}
    {s s1 s2 : Locals} {t u : Ty} {m1 m2 : Mode} {v1 : t.denote} {v2 : u.denote}
    {ws1 ws2 vs : List Value}
    (h0 : Holds env slots L0 base heap store s)
    (a1 : After env slots L0 L1 base heap store s t m1 v1 heap1 store1 s1 ws1)
    (a2 : After env slots L1 live base heap1 store1 { s1 with values := vs } u m2 v2 heap2
      store2 s2 ws2)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hLive : ∀ i, live i = true → L1 i = true) :
    Step heap store (Holds.KeepDying env slots L0 live store s) heap2 store2
        (m1.fresh store2 t ws1 v1 ++ m2.fresh store2 u ws2 v2) ∧
      Frame base s s2 ∧ t.Rep m1 heap2 store2 ws1 v1 ∧
      Holds.Apart env slots live store2 s2 t m1 ws1 v1 ∧
      ∀ x ∈ t.regions m1 store2 ws1 v1, ∀ y ∈ m2.fresh store2 u ws2 v2, regionsDisjoint x y := by
  have hKeep1 : ∀ c ∈ t.regions m1 store1 ws1 v1,
      Holds.KeepDying env slots L1 live store1 { s1 with values := vs } c := by
    intro c hc w x hx _ hm wx hwx hlx b hb
    have hb' : b ∈ w.regions (slots.getD x.index default).mode store1 wx (env.get x) := by
      rw [hm]; exact hb
    exact a1.apart w x hx (Or.inr hm) wx hwx hlx c hc b hb'
  obtain ⟨hRep1, hSame1, hFresh1⟩ := a1.rep.step a2.step hKeep1
  have hStep := a1.step.transBoth (keep := Holds.KeepDying env slots L0 live store s) a2.step
    fun c hc =>
    ⟨hc.mono fun i h1 h2 => ⟨h1, by
        cases hl : live i with
        | false => rfl
        | true => rw [hLive i hl] at h2; exact nomatch h2⟩,
      fun _ => Holds.KeepDying.transfer h0 a1.step (fun j hj => a1.frame.below j hj) hL1
        (fun i h1 _ => h1) (hc.mono fun i h1 h2 => ⟨hL1 _ h1, h2⟩)⟩
  refine ⟨by rw [Mode.fresh_congr hSame1]; exact hStep, a1.frame.trans a2.frame.values, hRep1,
    ?_, fun x hx y hy => by rw [hSame1] at hx; exact hFresh1 x hx y hy⟩
  exact (a1.apart.live_mono hLive).transfer (a1.holds.live_mono hLive) a2.step
    (fun j hj => a2.frame.below j hj)
    (fun w y hy wy hwy hly c hc => a1.holds.keepDying hLive hy hwy hly c hc) hSame1

/-- Two expressions in a row: the first's value stays on the stack below the second's, and the
facts of `After.seq` hold. -/
theorem seq_spec {Γ : List Ty} {t u : Ty} {l : Expr S Γ t} {r : Expr S Γ u}
    (lSpec : ∀ env slots live, CodeSpec m funs host l env slots live)
    (rSpec : ∀ env slots live, CodeSpec m funs host r env slots live)
    (env : Env Γ) (slots : List Slot) (live : Nat → Bool) (base : Nat) (heap : Heap)
    (store : Store Unit) (s : Locals)
    (hVars : Holds env slots (fun i => live i || (l.uses i || r.uses i)) base heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoomL : base + l.width ≤ s.params.length + s.locals.length)
    (hRoomR : base + r.width ≤ s.params.length + s.locals.length)
    (hPlaceL : l.placeArgs = true) (hPlaceR : r.placeArgs = true) (rest : Program)
    (Q : Assertion Unit) (hTrapL : TrapOK (l.aborts || slots.any (·.mode == .owned)) Q)
    (hTrapR : TrapOK (r.aborts || slots.any (·.mode == .owned)) Q)
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
      wp m rest Q store2 { s2 with values := ws2.reverse ++ (ws1.reverse ++ s.values) } host) :
    wp m (l.code slots base (fun i => live i || r.uses i) ++ (r.code slots base live ++ rest))
      Q store s host := by
  have hIn : ∀ i, (live i || r.uses i || l.uses i) = true →
      (live i || (l.uses i || r.uses i)) = true := fun i h => live_seq _ _ _ h
  have hVarsL := hVars.live_mono hIn
  refine lSpec env slots _ base heap store s hVarsL hAt hCap hBase hRoomL hPlaceL _ _ hTrapL
    fun heap1 store1 s1 ws1 a1 => ?_
  refine rSpec env slots live base heap1 store1 { s1 with values := ws1.reverse ++ s.values }
    (a1.holds.agree fun _ _ => rfl) a1.step.at_ (by rw [a1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base; rw [a1.frame.params]; exact hBase)
    (by show base + r.width ≤ s1.params.length + s1.locals.length
        rw [a1.frame.params, a1.frame.length]; exact hRoomR) hPlaceR _ _ hTrapR
    fun heap2 store2 s2 ws2 a2 => ?_
  obtain ⟨hStep, hFrame, hRep1, hApart1, hDisjoint⟩ :=
    After.seq hVarsL a1 a2 (fun i h => by simp [h]) fun i h => by simp [h]
  exact hNext heap2 store2 s2 ws1 ws2
    (hStep.mono (fun _ hr => hr.mono fun i h1 h2 => ⟨hIn i h1, h2⟩) fun _ hb => hb) hFrame
    a2.holds hRep1 a2.rep hApart1 a2.apart hDisjoint

/-- The facts of `After` for a value without arrays: its fresh blocks and regions are empty. -/
theorem After.ofScalar {Γ : List Ty} {env : Env Γ} {slots : List Slot} {liveIn live : Nat → Bool}
    {base : Nat} {heap : Heap} {store : Store Unit} {s : Locals} {t : Ty} {mode : Mode}
    {v : t.denote} {heap' : Heap} {store' : Store Unit} {s' : Locals} {ws : List Value}
    {fresh : List (Nat × Nat)} (hScalar : t.scalar = true)
    (hStep : Step heap store (Holds.KeepDying env slots liveIn live store s) heap' store' fresh)
    (hFresh : fresh = []) (hF : Frame base s s') (hH : Holds env slots live base heap' store' s')
    (hRep : t.Rep mode heap' store' ws v) :
    After env slots liveIn live base heap store s t mode v heap' store' s' ws :=
  ⟨by rw [Mode.fresh_scalar hScalar]; rw [hFresh] at hStep; exact hStep, hF, hH, hRep,
    fun _ _ _ _ _ _ _ b hb => by rw [Ty.regions_scalar t hScalar] at hb; exact nomatch hb⟩

theorem fresh_scalar_append {store : Store Unit} {m1 m2 : Mode} {t u : Ty} (ht : t.scalar = true)
    (hu : u.scalar = true) (w1 w2 : List Value) (v1 : t.denote) (v2 : u.denote) :
    m1.fresh store t w1 v1 ++ m2.fresh store u w2 v2 = [] := by
  rw [Mode.fresh_scalar ht, Mode.fresh_scalar hu]; rfl

/-- An operation on words; division and remainder save their operands to test the divisor. -/
theorem spec_bin {Γ : List Ty} (op : BinOp) {left right : Expr S Γ .word}
    (leftSpec : ∀ env slots live, CodeSpec m funs host left env slots live)
    (rightSpec : ∀ env slots live, CodeSpec m funs host right env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.bin op left right) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max op.scratch (max left.width right.width) :=
    (Nat.le_max_left ..).trans (Nat.le_max_right ..)
  have hR : right.width ≤ max op.scratch (max left.width right.width) :=
    (Nat.le_max_right ..).trans (Nat.le_max_right ..)
  have hS : op.scratch ≤ max op.scratch (max left.width right.width) := Nat.le_max_left ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_spec leftSpec rightSpec env slots live base heap store s hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts, Bool.or_eq_true] at h ⊢; tauto)
    (hTrap.of_imp fun h => by simp only [Expr.aborts, Bool.or_eq_true] at h ⊢; tauto)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ => ?_
  simp only [Ty.rep_word] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  cases op
  case div | rem =>
    have hW2 : base + 2 ≤ s.params.length + s.locals.length := by
      have := hRoom
      simp only [Expr.width, BinOp.scratch] at this
      omega
    have hp2 : s2.params = s.params := hF.params
    have hl2 : s2.locals.length = s.locals.length := hF.length
    simp only [BinOp.code, List.cons_append, List.nil_append]
    refine wp_localSet_local (by rw [hp2]; omega) (by rw [hp2, hl2]; omega) ?_
    refine wp_localSet_local (vs := s.values)
      (s := setLocal { s2 with values := .i64 (left.denote funs env) :: s.values } (base + 1)
        (.i64 (right.denote funs env)))
      (by show s2.params.length ≤ base; rw [hp2]; omega)
      (by show base < s2.params.length + (s2.locals.set (base + 1 - s2.params.length) _).length
          rw [List.length_set, hp2, hl2]; omega) ?_
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
        (by show base + 1 < s2.params.length + s2.locals.length; rw [hp2, hl2]; omega)
    have hLeftSlot : s2b.get base = some (.i64 (left.denote funs env)) :=
      Locals.get_setLocal_same hLowB
        (by show base < s2a.params.length + s2a.locals.length; simp [s2a, setLocal]
            rw [hp2, hl2]; omega)
    have hFrame : Frame base s s2b := by
      refine ⟨hp2, by simp [s2b, s2a, setLocal, hl2], fun j hj => ?_⟩
      rw [Locals.get_setLocal_ne hLowB (by omega), Locals.get_values,
        Locals.get_setLocal_ne hLowA (by omega), Locals.get_values]
      exact hF.below j hj
    have hHolds : Holds env slots live base heap2 store2 s2b :=
      (hH.setLocal (i := base + 1) (by omega) (by rw [hp2]; omega)).setLocal (le_refl _)
        (by show s2.params.length ≤ base; rw [hp2]; omega)
    have hs2b : s2b.values = s.values := rfl
    simp only [wp_localGet_cons, hRightSlot, wp_eqzI64_cons]
    rw [wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    by_cases hZero : right.denote funs env = 0
    · simp only [hZero, ite_true, ne_eq]
      simpa [-Locals.get, hLeftSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
        hNext heap2 store2 s2b _ (After.ofScalar rfl hStep' rfl hFrame hHolds rfl)
    · simp only [hZero, ite_false, ne_eq, not_true_eq_false]
      simpa [-Locals.get, hLeftSlot, hRightSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
        hNext heap2 store2 s2b _ (After.ofScalar rfl hStep' rfl hFrame hHolds rfl)
  all_goals
    simpa [BinOp.code, Expr.denote, BinOp.apply, ← UInt64.shiftLeft_eq_shiftLeft_mod,
      ← UInt64.shiftRight_eq_shiftRight_mod] using
      hNext heap2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)

/-- A comparison of words. -/
theorem spec_cmp {Γ : List Ty} (op : CmpOp) {left right : Expr S Γ .word}
    (leftSpec : ∀ env slots live, CodeSpec m funs host left env slots live)
    (rightSpec : ∀ env slots live, CodeSpec m funs host right env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.cmp op left right) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_spec leftSpec rightSpec env slots live base heap store s hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts, Bool.or_eq_true] at h ⊢; tauto)
    (hTrap.of_imp fun h => by simp only [Expr.aborts, Bool.or_eq_true] at h ⊢; tauto)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ => ?_
  simp only [Ty.rep_word] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext heap2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)
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

/-- The negation of a `Bool`. -/
theorem spec_not {Γ : List Ty} {e : Expr S Γ .bool}
    (eSpec : ∀ env slots live, CodeSpec m funs host e env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.not e) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  refine eSpec env slots live base heap store s hVars hAt hCap hBase hRoom hPlace _ _ hTrap
    fun heap1 store1 s1 ws a1 => ?_
  have hR := a1.rep
  simp only [Ty.rep_bool] at hR
  subst hR
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_eqzI64_cons, wp_extendUI32_cons, boolWord_not]
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  simpa [Expr.denote] using
    hNext heap1 store1 s1 _ (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)

/-- The conjunction of `Bool`s. -/
theorem spec_and {Γ : List Ty} {left right : Expr S Γ .bool}
    (leftSpec : ∀ env slots live, CodeSpec m funs host left env slots live)
    (rightSpec : ∀ env slots live, CodeSpec m funs host right env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.and left right) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_spec leftSpec rightSpec env slots live base heap store s hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts, Bool.or_eq_true] at h ⊢; tauto)
    (hTrap.of_imp fun h => by simp only [Expr.aborts, Bool.or_eq_true] at h ⊢; tauto)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ => ?_
  simp only [Ty.rep_bool] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_andI64_cons, boolWord_and]
  simpa [Expr.denote] using hNext heap2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)

/-- The disjunction of `Bool`s. -/
theorem spec_or {Γ : List Ty} {left right : Expr S Γ .bool}
    (leftSpec : ∀ env slots live, CodeSpec m funs host left env slots live)
    (rightSpec : ∀ env slots live, CodeSpec m funs host right env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.or left right) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_spec leftSpec rightSpec env slots live base heap store s hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts, Bool.or_eq_true] at h ⊢; tauto)
    (hTrap.of_imp fun h => by simp only [Expr.aborts, Bool.or_eq_true] at h ⊢; tauto)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ => ?_
  simp only [Ty.rep_bool] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_orI64_cons, boolWord_or]
  simpa [Expr.denote] using hNext heap2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)

/-- A value turned from mode `source` into mode `target` after an expression's code: a borrowed
value that must be owned is copied into new blocks, and the facts of `After` carry over. -/
theorem After.coerce (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {liveIn live : Nat → Bool} {base base' : Nat} {heap : Heap} {store : Store Unit}
    {s : Locals} {t : Ty} {source target : Mode} {v : t.denote} {heap1 : Heap}
    {store1 : Store Unit} {s1 : Locals} {ws vs : List Value} {rest : Program}
    {Q : Assertion Unit}
    (a : After env slots liveIn live base heap store s t source v heap1 store1 s1 ws)
    (hTarget : source = .owned → target = .owned) (hBase' : base ≤ base')
    (hLow : s1.params.length ≤ base')
    (hRoom : base' + copyWidth t ≤ s1.params.length + s1.locals.length)
    (hCap : store1.memoryCap m 0 ≤ 65535)
    (hTrap : source = .borrowed → target = .owned → t.scalar = false → TrapOK true Q)
    (hNext : ∀ heap2 store2 s2 ws2,
      After env slots liveIn live base heap store s t target v heap2 store2 s2 ws2 →
      wp m rest Q store2 { s2 with values := ws2.reverse ++ vs } host) :
    wp m (coerceCode t source target base' ++ rest) Q store1
      { s1 with values := ws.reverse ++ vs } host := by
  by_cases hCopy : source = .borrowed ∧ target = .owned ∧ t.scalar = false
  · obtain ⟨hs, ht, hScalar⟩ := hCopy
    subst hs ht
    have hW : copyWidth t = t.width + 3 := by simp [copyWidth, hScalar]
    simp only [coerceCode, and_self, hScalar, ↓reduceIte, List.append_assoc]
    have hl := a.rep.length
    refine wp_storeCode ws base' t.width s1 vs hl hLow (by omega)
      fun s2 hp2 hl2 hold2 hout2 => ?_
    refine wp_copyCode hm t a.step.at_ hCap (hTrap rfl rfl hScalar) a.rep hold2 (le_refl _)
      (by rw [hp2]; omega) (by rw [hp2, hl2]; simp [Ty.copyScratch, hScalar]; omega)
      fun heap3 store3 s3 ws3 hStep3 hRep3 hF3 => ?_
    have hF : Frame base s s3 := by
      refine ⟨hF3.params.trans (hp2.trans a.frame.params),
        hF3.length.trans (hl2.trans a.frame.length), fun j hj => ?_⟩
      rw [hF3.below j (by omega)]
      show s2.get j = s.get j
      rw [hout2 j (Or.inl (by omega))]
      exact a.frame.below j hj
    have hStep0 := a.step
    simp only [Mode.fresh] at hStep0
    refine hNext heap3 store3 s3 ws3 ⟨?_, hF, ?_, hRep3, ?_⟩
    · exact hStep0.trans hStep3 fun _ hr => ⟨hr, fun _ => trivial⟩
    · exact (a.holds.step hStep3 fun _ _ _ _ _ _ _ _ => trivial).agree fun j hj => by
        rw [hF3.below j (by omega)]
        show s2.get j = s1.get j
        exact hout2 j (Or.inl (by omega))
    · intro u y hy _ wy hwy hly b hb c hc
      have hAgree : ∀ j < base, s3.get j = s1.get j := fun j hj => by
        rw [hF3.below j (by omega)]
        exact hout2 j (Or.inl (by omega))
      have hwy' := (a.holds.hold_agree hAgree hy hly).mp hwy
      obtain ⟨hSame, hFresh⟩ := a.holds.regions_after hStep3 hy hwy' hly fun _ _ => trivial
      rw [hSame] at hc
      exact regionsDisjoint_symm (hFresh c hc b hb)
  · have hEmpty : coerceCode t source target base' = [] := by
      simp only [coerceCode]; rw [ite_eq_right hCopy]
    rw [hEmpty, List.nil_append]
    -- No copy: the modes agree, or the type holds no arrays.
    have hSame : source = target ∨ t.scalar = true := by
      cases source <;> cases target <;> simp_all
    rcases hSame with rfl | hScalar
    · exact hNext heap1 store1 s1 ws a
    · refine hNext heap1 store1 s1 ws ⟨?_, a.frame, a.holds, ?_, ?_⟩
      · have hStep := a.step
        rw [Mode.fresh_scalar hScalar] at hStep ⊢
        exact hStep
      · cases target
        · exact a.rep.borrow
        · exact a.rep.owned hScalar
      · intro u y hy hm wy hwy hly b hb
        rw [Ty.regions_scalar t hScalar] at hb
        exact nomatch hb

/-- An evolution of the state followed by an expression's code. -/
theorem After.prepend {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L1 live : Nat → Bool}
    {base : Nat} {heap heap1 heap2 : Heap} {store store1 store2 : Store Unit} {s s1 s2 : Locals}
    {t : Ty} {mode : Mode} {v : t.denote} {ws : List Value}
    (h0 : Holds env slots L0 base heap store s)
    (e : Evolves env slots L0 L1 base heap store s heap1 store1 s1)
    (a : After env slots L1 live base heap1 store1 s1 t mode v heap2 store2 s2 ws)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hL : ∀ i, live i = true → L1 i = true) :
    After env slots L0 live base heap store s t mode v heap2 store2 s2 ws :=
  ⟨e.step.trans a.step fun r hr =>
      ⟨hr.mono fun i h1 h2 => ⟨h1, by
          cases h : live i with
          | false => rfl
          | true => rw [hL i h] at h2; exact nomatch h2⟩,
        fun _ => Holds.KeepDying.transfer h0 e.step (fun j hj => e.frame.below j hj) hL1
          (fun i h1 _ => h1) (hr.mono fun i h1 h2 => ⟨hL1 _ h1, h2⟩)⟩,
    e.frame.trans a.frame, a.holds, a.rep, a.apart⟩

/-- An owned value arises only where an expression may trap or an owned variable is in scope. -/
theorem Expr.mode_owned {Γ : List Ty} {t : Ty} (e : Expr S Γ t) :
    ∀ modes : List Mode, e.mode modes = .owned →
      (e.aborts || modes.any (· == .owned)) = true := by
  induction e with
  | var x =>
    intro modes h
    simp only [Expr.mode] at h
    simp only [Expr.aborts, Bool.false_or, List.any_eq_true]
    simp only [List.getD_eq_getElem?_getD] at h
    cases hi : modes[x.index]? with
    | none => rw [hi] at h; exact nomatch h
    | some md =>
      rw [hi] at h
      exact ⟨md, List.mem_of_getElem? hi, by simp [Option.getD] at h; simp [h]⟩
  | ite c a b _ ihA ihB =>
    intro modes h
    simp only [Expr.mode] at h
    have : a.mode modes = .owned ∨ b.mode modes = .owned := by
      cases ha : a.mode modes <;> cases hb : b.mode modes <;> simp_all [Mode.join]
    rcases this with h' | h'
    · have := ihA modes h'
      simp only [Expr.aborts, Bool.or_eq_true] at this ⊢; tauto
    · have := ihB modes h'
      simp only [Expr.aborts, Bool.or_eq_true] at this ⊢; tauto
  | letE value body ihV ihB =>
    intro modes h
    simp only [Expr.mode] at h
    have := ihB _ h
    simp only [List.any_cons, Bool.or_eq_true] at this
    simp only [Expr.aborts, Bool.or_eq_true]
    rcases this with h1 | h1 | h1
    · exact Or.inl (Or.inr h1)
    · have := ihV modes (by simpa using h1)
      simp only [Bool.or_eq_true] at this; tauto
    · exact Or.inr h1
  | call f args _ =>
    intro modes h
    simp only [Expr.mode] at h
    split at h
    · exact nomatch h
    · rename_i hs
      simp [Expr.aborts, hs]
  | pair a b ihA ihB =>
    intro modes h
    simp only [Expr.mode] at h
    have : a.mode modes = .owned ∨ b.mode modes = .owned := by
      cases ha : a.mode modes <;> cases hb : b.mode modes <;> simp_all [Mode.join]
    rcases this with h' | h'
    · have := ihA modes h'
      simp only [Expr.aborts, Bool.or_eq_true] at this ⊢; tauto
    · have := ihB modes h'
      simp only [Expr.aborts, Bool.or_eq_true] at this ⊢; tauto
  | letPair e body ihE ihB =>
    intro modes h
    simp only [Expr.mode] at h
    have := ihB _ h
    simp only [List.any_cons, Bool.or_eq_true] at this
    simp only [Expr.aborts, Bool.or_eq_true]
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl (Or.inr h1)
    · have := ihE modes (by simpa using h1)
      simp only [Bool.or_eq_true] at this; tauto
    · have := ihE modes (by simpa using h1)
      simp only [Bool.or_eq_true] at this; tauto
    · exact Or.inr h1
  | loop count init body _ ihI ihB =>
    intro modes h
    simp only [Expr.mode] at h
    have : init.mode modes = .owned ∨ body.mode (.borrowed :: .borrowed :: modes) = .owned := by
      cases ha : init.mode modes <;>
        cases hb : body.mode (.borrowed :: .borrowed :: modes) <;> simp_all [Mode.join]
    rcases this with h' | h'
    · have := ihI modes h'
      simp only [Expr.aborts, Bool.or_eq_true] at this ⊢; tauto
    · have := ihB _ h'
      simp only [List.any_cons, Bool.or_eq_true] at this
      simp only [Expr.aborts, Bool.or_eq_true]
      rcases this with h1 | h1 | h1 | h1
      · exact Or.inl (Or.inr h1)
      · exact nomatch h1
      · exact nomatch h1
      · exact Or.inr h1
  | build _ _ _ _ | set _ _ _ _ _ => intro _ _; simp [Expr.aborts]
  | _ => intro modes h; simp [Expr.mode] at h

theorem Slot.any_map (slots : List Slot) :
    (slots.map Slot.mode).any (· == .owned) = slots.any (·.mode == .owned) := by
  simp [List.any_map, Function.comp_def]

/-- The facts of `After` for a value without arrays, as an evolution of the state. -/
theorem After.toEvolves {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap' : Heap} {store store' : Store Unit} {s s' : Locals} {t : Ty}
    {mode : Mode} {v : t.denote} {ws : List Value}
    (a : After env slots L0 L base heap store s t mode v heap' store' s' ws)
    (hScalar : t.scalar = true) : Evolves env slots L0 L base heap store s heap' store' s' :=
  ⟨by have h := a.step; rw [Mode.fresh_scalar hScalar] at h; exact h, a.frame, a.holds⟩

/-- `After` at a lower first free local, when the variables' locals lie below it. -/
theorem After.lower {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base base' : Nat} {heap heap' : Heap} {store store' : Store Unit} {s s' : Locals} {t : Ty}
    {mode : Mode} {v : t.denote} {ws : List Value}
    (a : After env slots L0 L base' heap store s t mode v heap' store' s' ws)
    (h0 : Holds env slots L0 base heap store s) (hb : base ≤ base')
    (hL : ∀ i, L i = true → L0 i = true) :
    After env slots L0 L base heap store s t mode v heap' store' s' ws :=
  ⟨a.step, a.frame.mono hb, a.holds.lower h0 hL, a.rep, a.apart⟩

/-- An evolution to locals with another operand stack. -/
theorem Evolves.values {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap' : Heap} {store store' : Store Unit} {s s' : Locals}
    (e : Evolves env slots L0 L base heap store s heap' store' s') (vs : List Value) :
    Evolves env slots L0 L base heap store s heap' store' { s' with values := vs } :=
  ⟨e.step, ⟨e.frame.params, e.frame.length, e.frame.below⟩, e.holds.agree fun _ _ => rfl⟩

/-- `After` for more variables live before the code, when they include those that die in it. -/
theorem After.liveIn {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L0' L : Nat → Bool}
    {base : Nat} {heap heap' : Heap} {store store' : Store Unit} {s s' : Locals} {t : Ty}
    {mode : Mode} {v : t.denote} {ws : List Value}
    (a : After env slots L0 L base heap store s t mode v heap' store' s' ws)
    (h : ∀ i, L0 i = true → L0' i = true) :
    After env slots L0' L base heap store s t mode v heap' store' s' ws :=
  ⟨a.step.mono (fun _ hr => hr.mono fun i h1 h2 => ⟨h i h1, h2⟩) fun _ hb => hb, a.frame,
    a.holds, a.rep, a.apart⟩

/-- The release of the owned variables that `sel` selects after an expression's code, those live
in `L1` and not in `live`, gives the facts of the code and the release for `live`.  The value lies
apart from the released blocks, so its words still represent it. -/
theorem After.release (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 live sel : Nat → Bool} {base : Nat} {heap heap1 : Heap} {store store1 : Store Unit}
    {s s1 : Locals} {t : Ty} {mode : Mode} {v : t.denote} {ws vals : List Value}
    {rest : Program} {Q : Assertion Unit}
    (h0 : Holds env slots L0 base heap store s)
    (a : After env slots L0 L1 base heap store s t mode v heap1 store1 s1 ws)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hSel : ∀ i, sel i = true → L1 i = true)
    (hLive : ∀ i, live i = true → (L1 i && !sel i) = true)
    (hNext : ∀ heap2 store2,
      After env slots L0 live base heap store s t mode v heap2 store2 s1 ws →
      wp m rest Q store2 { s1 with values := vals } host) :
    wp m (releaseWhere Γ slots sel ++ rest) Q store1 { s1 with values := vals } host := by
  refine wp_releaseWhere hm (a.holds.agree fun _ _ => rfl) a.step.at_ hSel
    fun heap2 store2 e => ?_
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
      fun _ => Holds.KeepDying.transfer h0 a.step (fun j hj => a.frame.below j hj) hL1
        (fun i h1 _ => h1) (hr.mono fun i h1 h2 => ⟨hL1 _ h1, h2⟩)⟩
  refine hNext heap2 store2 ⟨hStep.mono (fun _ h => h) fun b hb => ?_, a.frame,
    e'.holds.agree fun _ _ => rfl, hRep, ?_⟩
  · rw [Mode.fresh_congr hSame] at hb
    exact List.mem_append_left _ hb
  · exact Holds.Apart.transfer (a.holds.live_mono hLiveL1) (a.apart.live_mono hLiveL1) e'.step
      (fun _ _ => rfl) (fun u y hy wy hwy hly => a.holds.keepDying hLiveL1 hy hwy hly) hSame

/-- A binding: the facts of the value's code, the store of its words in the locals from `base`
on, and the facts of the body's code for the context with the value as variable 0, give the
facts of the whole for the context without it.  The owned variables that die in the body die in
the whole, and the value's blocks, when it is owned and dies, are fresh blocks of the value's
step. -/
theorem After.bind {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L1 LB live : Nat → Bool}
    {base : Nat} {heap heap1 heap' : Heap} {store store1 store' : Store Unit}
    {s s1 s2 s' : Locals} {sTy t : Ty} {mv mode : Mode} {vv : sTy.denote} {v : t.denote}
    {ws1 ws : List Value}
    (h0 : Holds env slots L0 base heap store s)
    (a1 : After env slots L0 L1 base heap store s sTy mv vv heap1 store1 s1 ws1)
    (f2 : Frame base s1 s2) (hold : LocalsHold s2 base ws1)
    (aB : After (Env.cons vv env) (⟨base, mv⟩ :: slots) LB (shift 1 live) (base + sTy.width)
      heap1 store1 s2 t mode v heap' store' s' ws)
    (hLB : ∀ i, LB (i + 1) = true → L1 i = true) (hL1 : ∀ i, L1 i = true → L0 i = true)
    (hLive : ∀ i, live i = true → L1 i = true) :
    After env slots L0 live base heap store s t mode v heap' store' s' ws := by
  have hl1 := a1.rep.length
  refine ⟨a1.step.trans aB.step fun r hr => ⟨hr.mono fun i h1 h2 => ⟨h1, ?_⟩, fun hFresh => ?_⟩,
    a1.frame.trans (f2.trans (aB.frame.mono (Nat.le_add_right _ _))), ?_, aB.rep, ?_⟩
  · cases hl : live i with
    | false => rfl
    | true => rw [hLive i hl] at h2; exact nomatch h2
  · have hr1 : Holds.KeepDying env slots L1 live store1 s1 r :=
      Holds.KeepDying.transfer h0 a1.step (fun j hj => a1.frame.below j hj) hL1
        (fun i h1 _ => h1) (hr.mono fun i h1 h2 => ⟨hL1 _ h1, h2⟩)
    intro t' x hx hxo hm wx hwx hlx b hb
    cases x with
    | here =>
      change mv = .owned at hm
      change LocalsHold s2 base wx at hwx
      obtain rfl := LocalsHold.unique hwx hold (hlx.trans hl1.symm)
      subst hm
      exact hFresh b hb
    | there x =>
      change (slots.getD x.index default).mode = .owned at hm
      change LocalsHold s2 (slots.getD x.index default).loc wx at hwx
      have hx1 : L1 x.index = true := hLB _ hx
      have hxo' : live x.index = false := by simpa [Var.index] using hxo
      exact hr1 t' x hx1 hxo' hm wx
        ((a1.holds.hold_agree (fun j hj => f2.below j hj) hx1 hlx).mp hwx) hlx b hb
  · exact ((aB.holds.pop).live_mono fun i h => by simpa using h).lower h0
      fun i h => hL1 _ (hLive _ h)
  · exact aB.apart.pop.live_mono fun i h => by simpa using h

/-- A binding of two variables: the facts of a value's code, a change of locals below `base`,
and the facts of the body's code for the context with two new variables, give the facts of the
whole for the context without them, when the blocks of each new variable that is owned and dies
in the body lie among the value's fresh blocks. -/
theorem After.bind2 {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 LB live : Nat → Bool} {base base' : Nat} {heap heap1 heap' : Heap}
    {store store1 store' : Store Unit} {s s1 s2 s' : Locals} {tv t0 t1 u : Ty} {mv mode : Mode}
    {vv : tv.denote} {v0 : t0.denote} {v1 : t1.denote} {sl0 sl1 : Slot} {v : u.denote}
    {wsv ws : List Value}
    (h0 : Holds env slots L0 base heap store s)
    (a1 : After env slots L0 L1 base heap store s tv mv vv heap1 store1 s1 wsv)
    (f2 : Frame base s1 s2)
    (aB : After (Env.cons v0 (Env.cons v1 env)) (sl0 :: sl1 :: slots) LB (shift 2 live) base'
      heap1 store1 s2 u mode v heap' store' s' ws) (hBase : base ≤ base')
    (hNew : ∀ r, (∀ b ∈ mv.fresh store1 tv wsv vv, regionsDisjoint r b) →
      (sl0.mode = .owned → ∀ w, LocalsHold s2 sl0.loc w → w.length = t0.width →
        ∀ b ∈ t0.blocks store1 w v0, regionsDisjoint r b) ∧
      (sl1.mode = .owned → ∀ w, LocalsHold s2 sl1.loc w → w.length = t1.width →
        ∀ b ∈ t1.blocks store1 w v1, regionsDisjoint r b))
    (hLB : ∀ i, LB (i + 2) = true → L1 i = true) (hL1 : ∀ i, L1 i = true → L0 i = true)
    (hLive : ∀ i, live i = true → L1 i = true) :
    After env slots L0 live base heap store s u mode v heap' store' s' ws := by
  refine ⟨a1.step.trans aB.step fun r hr => ⟨hr.mono fun i h1 h2 => ⟨h1, ?_⟩, fun hFresh => ?_⟩,
    a1.frame.trans (f2.trans (aB.frame.mono hBase)), ?_, aB.rep, ?_⟩
  · cases hl : live i with
    | false => rfl
    | true => rw [hLive i hl] at h2; exact nomatch h2
  · have hr1 : Holds.KeepDying env slots L1 live store1 s1 r :=
      Holds.KeepDying.transfer h0 a1.step (fun j hj => a1.frame.below j hj) hL1
        (fun i h1 _ => h1) (hr.mono fun i h1 h2 => ⟨hL1 _ h1, h2⟩)
    obtain ⟨hNew0, hNew1⟩ := hNew r hFresh
    intro t' x hx hxo hm wx hwx hlx b hb
    cases x with
    | here => exact hNew0 hm wx hwx hlx b hb
    | there x =>
      cases x with
      | here => exact hNew1 hm wx hwx hlx b hb
      | there x =>
        change (slots.getD x.index default).mode = .owned at hm
        change LocalsHold s2 (slots.getD x.index default).loc wx at hwx
        have hx1 : L1 x.index = true := hLB x.index hx
        have hxo' : live x.index = false := by
          simpa [Var.index, Nat.add_assoc] using hxo
        exact hr1 t' x hx1 hxo' hm wx
          ((a1.holds.hold_agree (fun j hj => f2.below j hj) hx1 hlx).mp hwx) hlx b hb
  · exact ((aB.holds.pop.pop).live_mono fun i h => by simpa [Nat.add_assoc] using h).lower h0
      fun i h => hL1 _ (hLive _ h)
  · exact aB.apart.pop.pop.live_mono fun i h => by simpa [Nat.add_assoc] using h

/-- The write of element `k` of an owned array value: the array with that element replaced, in
the same block.  The write keeps every region apart from the block, and the variables' regions
lie apart from it. -/
theorem After.writeElement {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap1 : Heap} {store store1 : Store Unit} {s s1 : Locals}
    {words : Array UInt64} {root : UInt64}
    (a : After env slots L0 L base heap store s .array .owned words heap1 store1 s1 [.i64 root])
    {k : Nat} (hk : k < words.size) (v : UInt64) :
    After env slots L0 L base heap store s .array .owned (words.set k v hk) heap1
      (UInt64Array.writeElement store1 root k v) s1 [.i64 root] := by
  obtain ⟨p, hp, hOwned⟩ := a.rep
  obtain rfl : p = root := by simp only [List.cons.injEq, Value.i64.injEq] at hp; exact hp.1.symm
  have hA := hOwned.values
  have hFit := hA.1
  have hBase := hOwned.base
  have hCapacity := hOwned.capacity
  have hFrame := UInt64Array.writeElement_frame store1 p words.size k v hFit hk
  have hWithin : WritesWithin store1 (UInt64Array.writeElement store1 p k v) p.toNat
      (capacityAt store1 p) :=
    ⟨by rw [hFrame.1], hFrame.2.1, fun a ha => hFrame.2.2 a (by omega)⟩
  obtain ⟨hOwned', hCapSame⟩ := hOwned.rewrite hWithin (hA.writeElement hk v)
    (by rw [Array.size_set]; exact hCapacity)
  have hBlock : block (UInt64Array.writeElement store1 p k v) p = block store1 p :=
    block_eq hCapSame
  have hW : Step heap1 store1 (fun r => regionsDisjoint r (block store1 p)) heap1
      (UInt64Array.writeElement store1 p k v) [] :=
    ⟨Heap.At.writesOwned a.step.at_ hOwned hWithin, rfl, fun r hr _ hd =>
      ⟨fun x hl hh => hWithin.bytes x (by simp only [block, regionsDisjoint] at hd; omega), hr,
        nofun⟩⟩
  -- The variables' regions lie apart from the block.
  have hKeep : ∀ (u : Ty) (y : Var Γ u), L y.index = true → ∀ wy,
      LocalsHold s1 (slots.getD y.index default).loc wy → wy.length = u.width →
      ∀ c ∈ u.regions (slots.getD y.index default).mode store1 wy (env.get y),
        regionsDisjoint c (block store1 p) := fun u y hy wy hwy hly c hc =>
    regionsDisjoint_symm (a.apart u y hy (Or.inl rfl) wy hwy hly (block store1 p)
      (List.mem_singleton_self _) c hc)
  have hStep := a.step.transBoth (keep := Holds.KeepDying env slots L0 L store s) hW
    fun _ hr => ⟨hr, fun hf => hf _ (List.mem_singleton_self _)⟩
  have hSame : Ty.array.regions .owned (UInt64Array.writeElement store1 p k v) [.i64 p] words =
      Ty.array.regions .owned store1 [.i64 p] words := by
    show [block _ p] = [block _ p]
    rw [hBlock]
  refine ⟨hStep.mono (fun _ h => h) fun b hb => ?_, a.frame, a.holds.step hW hKeep,
    ⟨p, rfl, hOwned'⟩, ?_⟩
  · have hb' : b = block store1 p := by
      rw [← hBlock]; exact List.mem_singleton.mp hb
    exact List.mem_append_left _ (hb' ▸ List.mem_singleton_self _)
  · exact Holds.Apart.transfer (t := .array) (mode := .owned) (ws := [.i64 p]) (v := words)
      a.holds a.apart hW (fun _ _ => rfl) hKeep hSame

/-- The store of a word value into local `loc`, at or above `base`: the facts of `After` as an
evolution to the locals with the word. -/
theorem After.storeWord {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap1 : Heap} {store store1 : Store Unit} {s s1 : Locals} {mode : Mode}
    {v : UInt64} {vs : List Value} {loc : Nat} {rest : Program} {Q : Assertion Unit}
    (a : After env slots L0 L base heap store s .word mode v heap1 store1 s1 [.i64 v])
    (hLoc : base ≤ loc) (hLow : s.params.length ≤ loc)
    (hHigh : loc < s.params.length + s.locals.length)
    (hNext : Evolves env slots L0 L base heap store s heap1 store1
        (setLocal { s1 with values := vs } loc (.i64 v)) →
      (setLocal { s1 with values := vs } loc (.i64 v)).get loc = some (.i64 v) →
      wp m rest Q store1 (setLocal { s1 with values := vs } loc (.i64 v)) host) :
    wp m (.localSet loc :: rest) Q store1 { s1 with values := [.i64 v].reverse ++ vs } host := by
  have hLow1 : ({ s1 with values := vs } : Locals).params.length ≤ loc := by
    show s1.params.length ≤ loc; rw [a.frame.params]; exact hLow
  have hHigh1 : loc < ({ s1 with values := vs } : Locals).params.length +
      ({ s1 with values := vs } : Locals).locals.length := by
    show loc < s1.params.length + s1.locals.length; rw [a.frame.params, a.frame.length]
    exact hHigh
  refine wp_localSet_local hLow1 hHigh1 ?_
  have e := a.toEvolves rfl
  exact hNext ⟨e.step, ⟨e.frame.params, by simp [setLocal, e.frame.length], fun j hj => by
      rw [Locals.get_setLocal_ne hLow1 (by omega)]; exact e.frame.below j hj⟩,
    (e.holds.agree (s' := { s1 with values := vs }) fun _ _ => rfl).setLocal hLoc hLow1⟩
    (Locals.get_setLocal_same hLow1 hHigh1)

/-- The facts of `After` for other locals that agree below `base`. -/
theorem After.reframe {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap' : Heap} {store store' : Store Unit} {s s' s'' : Locals} {t : Ty}
    {mode : Mode} {v : t.denote} {ws : List Value}
    (a : After env slots L0 L base heap store s t mode v heap' store' s' ws)
    (f : Frame base s' s'') :
    After env slots L0 L base heap store s t mode v heap' store' s'' ws :=
  ⟨a.step, a.frame.trans f, a.holds.agree fun j hj => f.below j hj, a.rep,
    a.apart.agree a.holds fun j hj => f.below j hj⟩

/-- Facts about the live sets and trap flags of constructs with two parts, and of calls. -/
theorem trap_left : ∀ a b o : Bool, (a || o) = true → (a || b || o) = true := by decide

theorem trap_right : ∀ a b o : Bool, (b || o) = true → (a || b || o) = true := by decide

theorem live_right : ∀ a b c : Bool, (b || c) = true → (a || b || c) = true := by decide


theorem call_trap_args : ∀ a b c o : Bool, (c || o) = true → (a || b || c || o) = true := by
  decide

theorem call_trap_callee : ∀ a b c o : Bool, a = true → (a || b || c || o) = true := by decide

/-- The trap flag of a binding's body: the bound value is owned only when its code may trap or an
owned variable is in scope. -/
theorem let_trap_body : ∀ v b m o : Bool, (m = true → (v || o) = true) →
    (b || (m || o)) = true → (v || b || o) = true := by decide

theorem live_build : ∀ a b c : Bool, (a || b) = true → (a || (c || b)) = true := by decide

theorem live_dup : ∀ a b : Bool, (a || b || b) = true → (a || b) = true := by decide

theorem live_assoc : ∀ a b c : Bool, (a || b || c) = true → (a || (b || c)) = true := by decide

/-- The live sets and trap flags of a loop: `a` for a variable live after it, `c`, `n`, and `b`
for its use in the count, the initial state, and the body, and `o` for an owned variable in
scope. -/
theorem loop_live_count : ∀ a n b c : Bool,
    (a || n || b || c) = true → (a || (c || n || b)) = true := by decide

theorem loop_live_init : ∀ a b n : Bool, (a || b || n) = true → (a || n || b) = true := by decide

theorem loop_live_state : ∀ a b c n : Bool, (a || b) = true → (a || (c || n || b)) = true := by
  decide

theorem loop_trap_count : ∀ c n b o : Bool, (c || o) = true → (c || n || b || o) = true := by
  decide

theorem loop_trap_init : ∀ c n b o : Bool, (n || o) = true → (c || n || b || o) = true := by
  decide

theorem loop_trap_body : ∀ c n b m z o : Bool, (m = true → (c || n || b || o) = true) →
    z = false → (b || (m || (z || o))) = true → (c || n || b || o) = true := by decide

/-- A loop's mode, the join of the initial state's mode and the body's mode for a borrowed
state, holds the body's value for a state in that mode. -/
theorem loop_mode {a : Mode} {f : Mode → Mode} (h : f (a.join (f .borrowed)) = .owned) :
    a.join (f .borrowed) = .owned := by
  cases hj : a.join (f .borrowed) with
  | owned => rfl
  | borrowed =>
    rw [hj] at h
    rw [h] at hj
    cases a <;> exact nomatch hj

theorem set_live_index : ∀ a b c d : Bool,
    (a || b || c || d) = true → (a || (b || d || c)) = true := by decide

/-- The trap flag of the body of a binding of a pair's components. -/
theorem let_trap_body2 : ∀ v b m o : Bool, (m = true → (v || o) = true) →
    (b || (m || (m || o))) = true → (v || b || o) = true := by decide

/-- The live sets of an `if`: `a` for a variable live after it, `c`, `t`, and `e` for its use
in the condition and the branches, and `b` for its use in the branch taken. -/
theorem ite_live_branch : ∀ a b t e : Bool, (b = true → (t || e) = true) →
    (a || b) = true → (a || t || e) = true := by decide

theorem ite_live_entry : ∀ a c t e : Bool, (a || t || e) = true → (a || (c || t || e)) = true := by
  decide

theorem ite_live_cond : ∀ a c t e : Bool,
    (a || t || e || c) = true → (a || (c || t || e)) = true := by decide

theorem ite_trap_cond : ∀ c t e o : Bool, (c || o) = true → (c || t || e || o) = true := by
  decide

/-- The variables live in `m` and not released, where the release selects those live in `m` and
not in `x ⊆ m`, are those in `x`. -/
theorem live_released : ∀ m x : Bool, (x = true → m = true) → (m && !(m && !x)) = x := by
  decide

/-- One branch of an `if`, after the condition: the releases of the owned variables that die at
its entry, its code, the coercion of its value to the `if`'s mode, and the store of its words,
which the code loads after the `if`. -/
theorem ite_branch (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} {c : Expr S Γ' .bool}
    {thenE elseE b : Expr S Γ' tTy}
    (bSpec : ∀ env slots live, CodeSpec m funs host b env slots live)
    {env : Env Γ'} {slots : List Slot} {live : Nat → Bool} {base : Nat} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit}
    (hVars : Holds env slots (fun i => live i || (Expr.ite c thenE elseE).uses i) base heap
      store s)
    (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoomB : base + tTy.width + max b.width (copyWidth tTy) ≤ s.params.length + s.locals.length)
    (hTrap : TrapOK ((Expr.ite c thenE elseE).aborts || slots.any (·.mode == .owned)) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots (fun i => live i || (Expr.ite c thenE elseE).uses i) live base heap store s
        tTy ((Expr.ite c thenE elseE).mode (slots.map Slot.mode))
        ((Expr.ite c thenE elseE).denote funs env) heap' store' s' ws →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host)
    {heap1 : Heap} {store1 : Store Unit} {s1 : Locals}
    (e1 : Evolves env slots (fun i => live i || (Expr.ite c thenE elseE).uses i)
      (fun i => live i || thenE.uses i || elseE.uses i) base heap store s heap1 store1
      { s1 with values := s.values })
    (hbPlace : b.placeArgs = true)
    (hbu : ∀ i, b.uses i = true → (thenE.uses i || elseE.uses i) = true)
    (hba : b.aborts = true → (Expr.ite c thenE elseE).aborts = true)
    (hval : b.denote funs env = (Expr.ite c thenE elseE).denote funs env)
    (hbm : b.mode (slots.map Slot.mode) = .owned →
      (Expr.ite c thenE elseE).mode (slots.map Slot.mode) = .owned)
    (Qb : Assertion Unit) (hQbTrap : ∀ st, Q (.Trap st "unreachable") → Qb (.Trap st "unreachable"))
    (hQb : ∀ st' s', wp m (loadCode base tTy.width ++ rest) Q st'
      { s' with values := s.values } host → Qb (.Fallthrough st' s')) :
    wp m (releaseWhere Γ' slots (fun i => (live i || thenE.uses i || elseE.uses i) &&
        !(live i || b.uses i)) ++
      (b.code slots (base + tTy.width) live ++
        (coerceCode tTy (b.mode (slots.map Slot.mode))
          ((Expr.ite c thenE elseE).mode (slots.map Slot.mode)) (base + tTy.width) ++
          storeCode base tTy.width))) Qb store1 { s1 with values := s.values } host := by
  have hp1 : s1.params = s.params := e1.frame.params
  have hl1 : s1.locals.length = s.locals.length := e1.frame.length
  have hTrapB : TrapOK ((Expr.ite c thenE elseE).aborts || slots.any (·.mode == .owned)) Qb :=
    hTrap.imp hQbTrap
  have hSubMid : ∀ i, (live i || b.uses i) = true →
      (live i || thenE.uses i || elseE.uses i) = true := fun i =>
    ite_live_branch _ _ _ _ (hbu i)
  refine wp_releaseWhere hm e1.holds e1.step.at_
    (fun i h => by simp only [Bool.and_eq_true] at h; exact h.1) fun heap2 store2 e2 => ?_
  have hEq : (fun i => (live i || thenE.uses i || elseE.uses i) &&
      !((live i || thenE.uses i || elseE.uses i) && !(live i || b.uses i))) =
      (fun i => live i || b.uses i) := by
    funext i
    exact live_released _ _ (hSubMid i)
  rw [hEq] at e2
  rw [← List.append_nil (storeCode base tTy.width)]
  refine bSpec env slots live (base + tTy.width) heap2 store2 { s1 with values := s.values }
    (e2.holds.mono (by omega)) e2.step.at_
    (by rw [e2.step.cap m, e1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base + tTy.width; rw [hp1]; omega)
    (by show base + tTy.width + b.width ≤ s1.params.length + s1.locals.length
        rw [hp1, hl1]; omega) hbPlace _ _ (hTrapB.of_imp fun h => by
          simp only [Bool.or_eq_true] at h ⊢; exact h.imp_left hba)
    fun heap3 store3 s3 ws3 a3 => ?_
  have hp3 : s3.params = s.params := a3.frame.params.trans hp1
  have hl3 : s3.locals.length = s.locals.length := a3.frame.length.trans hl1
  refine After.coerce hm a3 hbm le_rfl (by rw [hp3]; omega) (by rw [hp3, hl3]; omega)
    (by rw [a3.step.cap m, e2.step.cap m, e1.step.cap m]; exact hCap)
    (fun hs ht _ => (hTrapB.of_imp fun _ => by
      have := (Expr.ite c thenE elseE).mode_owned (slots.map Slot.mode) ht
      rw [Slot.any_map] at this; exact this))
    fun heap4 store4 s4 ws4 a4 => ?_
  have hp4 : s4.params = s.params := a4.frame.params.trans hp1
  have hl4 : s4.locals.length = s.locals.length := a4.frame.length.trans hl1
  have hl := a4.rep.length
  refine wp_storeCode ws4 base tTy.width s4 s.values hl (by rw [hp4]; omega)
    (by rw [hp4, hl4]; omega) fun s5 hp5 hl5 hold hout => ?_
  rw [wp_nil]
  refine hQb _ _ (wp_loadCode ws4 hl hold ?_)
  -- The `if`'s facts: the evolutions of the condition and the releases, then the branch.
  have hLower := a4.lower e2.holds (Nat.le_add_right _ _) (fun i h => by simp [h])
  have hEntry : ∀ i, (live i || thenE.uses i || elseE.uses i) = true →
      (live i || (Expr.ite c thenE elseE).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact ite_live_entry _ _ _ _ h
  have e12 := Evolves.trans hVars e1 e2 hSubMid hEntry
  have aAll := After.prepend hVars e12 hLower (fun i h => hEntry i (hSubMid i h))
    (fun i h => by simp [h])
  have hFrame : Frame base s { s5 with values := s.values } := by
    refine ⟨hp5.trans hp4, hl5.trans hl4, fun j hj => ?_⟩
    show s5.get j = s.get j
    rw [hout j (Or.inl hj)]
    exact aAll.frame.below j hj
  rw [hval] at aAll
  refine hNext heap4 store4 _ ws4 ⟨aAll.step, hFrame, ?_, aAll.rep, ?_⟩
  · exact aAll.holds.agree fun j hj => hout j (Or.inl hj)
  · intro u y hy hmo wy hwy hly b' hb' c' hc'
    have hwy' : LocalsHold s4 (slots.getD y.index default).loc wy := fun k hk => by
      rw [← hout _ (Or.inl (by have := (aAll.holds.get y hy).1; omega))]
      exact hwy k hk
    exact aAll.apart u y hy hmo wy hwy' hly b' hb' c' hc'

/-- An `if`: the condition, then each branch as `ite_branch` describes. -/
theorem spec_ite (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} {c : Expr S Γ' .bool}
    {thenE elseE : Expr S Γ' tTy}
    (cSpec : ∀ env slots live, CodeSpec m funs host c env slots live)
    (thenSpec : ∀ env slots live, CodeSpec m funs host thenE env slots live)
    (elseSpec : ∀ env slots live, CodeSpec m funs host elseE env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.ite c thenE elseE) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
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
  refine cSpec env slots _ base heap store s (hVars.live_mono hMid) hAt hCap hBase (by omega)
    hPlaceC _ _ (hTrap.of_imp fun h => by simp only [Expr.aborts]; exact ite_trap_cond _ _ _ _ h)
    fun heap1 store1 s1 ws1 a1 => ?_
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
  have hRoomT : base + tTy.width + max thenE.width (copyWidth tTy) ≤
      s.params.length + s.locals.length := by
    have := Nat.max_le.mpr ⟨ht.trans (Nat.le_max_left _ (copyWidth tTy)), Nat.le_max_right _ _⟩
    omega
  have hRoomE : base + tTy.width + max elseE.width (copyWidth tTy) ≤
      s.params.length + s.locals.length := by
    have := Nat.max_le.mpr ⟨he.trans (Nat.le_max_left _ (copyWidth tTy)), Nat.le_max_right _ _⟩
    omega
  cases hcv : c.denote funs env
  · simp (config := { decide := true }) only [↓reduceIte]
    exact ite_branch hm elseSpec hVars hCap hBase hRoomE hTrap hNext e1 hPlaceE
      (fun i h => by simp [h]) (fun h => by simp [Expr.aborts, h])
      (by simp [Expr.denote, hcv]) hModeE _ (fun _ h => h) fun _ _ h => by simpa using h
  · simp (config := { decide := true }) only [↓reduceIte]
    exact ite_branch hm thenSpec hVars hCap hBase hRoomT hTrap hNext e1 hPlaceT
      (fun i h => by simp [h]) (fun h => by simp [Expr.aborts, h])
      (by simp [Expr.denote, hcv]) hModeT _ (fun _ h => h) fun _ _ h => by simpa using h

/-- A `let` binding: the value's code, the store of its words from local `base` on, the release
of the value when it is owned and the body does not use it, and the body's code. -/
theorem spec_letE (hm : Runtime m) {Γ' : List Ty} {sTy tTy : Ty} {value : Expr S Γ' sTy}
    {body : Expr S (sTy :: Γ') tTy}
    (valueSpec : ∀ env slots live, CodeSpec m funs host value env slots live)
    (bodySpec : ∀ env slots live, CodeSpec m funs host body env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.letE value body) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hValueRoom : value.width ≤ max value.width body.width := Nat.le_max_left ..
  have hBodyRoom : body.width ≤ max value.width body.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  have hV : ∀ i, ((live i || body.uses (i + 1)) || value.uses i) = true →
      (live i || (Expr.letE value body).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  refine valueSpec env slots (fun i => live i || body.uses (i + 1)) (base + sTy.width) heap
    store s ((hVars.mono (by omega)).live_mono hV) hAt hCap (by omega) (by omega) hPlace.1 _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
    fun heap1 store1 s1 ws1 a1 => ?_
  have hp1 : s1.params = s.params := a1.frame.params
  have hl1 : s1.locals.length = s.locals.length := a1.frame.length
  have a1' := a1.lower (hVars.live_mono hV) (Nat.le_add_right _ _) fun i h => by simp [h]
  refine wp_storeCode ws1 base sTy.width s1 s.values a1.rep.length (by rw [hp1]; omega)
    (by rw [hp1, hl1]; omega) fun s2 hp2 hl2 hold hout => ?_
  have f2 : Frame base s1 { s2 with values := s.values } :=
    ⟨hp2, hl2, fun j hj => hout j (Or.inl hj)⟩
  have hold' : LocalsHold { s2 with values := s.values } base ws1 := hold
  -- The body's context: the value as variable 0, in the locals from `base` on.
  have hVarsB : Holds (Env.cons (value.denote funs env) env)
      (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => i == 0 || shift 1 live i || body.uses i) (base + sTy.width) heap1 store1
      { s2 with values := s.values } :=
    Holds.push ((a1'.holds.agree fun j hj => f2.below j hj).live_mono fun i h => by
        simpa using h)
      hold' a1.rep ((a1'.apart.agree a1'.holds fun j hj => f2.below j hj).live_mono
        fun i h => by simpa using h)
  have hRelease : (if value.mode (slots.map Slot.mode) = .owned ∧ body.uses 0 = false then
      releaseCode sTy base else []) =
      (if body.uses 0 = false then [0] else []).flatMap
        (releaseVar (sTy :: Γ') (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)) := by
    cases body.uses 0 <;> cases value.mode (slots.map Slot.mode) <;> simp [releaseVar]
  rw [hRelease]
  refine wp_releaseVars hm _ (by split <;> simp) hVarsB a1.step.at_ (by split <;> simp)
    fun heap2 store2 e2 => ?_
  have e2' := e2.mono (live' := fun i => shift 1 live i || body.uses i) fun i h => by
    cases i with
    | zero =>
      have h0 : body.uses 0 = true := by simpa [shift] using h
      simp [h0]
    | succ k => split <;> simpa using h
  refine bodySpec _ _ (shift 1 live) (base + sTy.width) heap2 store2
    { s2 with values := s.values } e2'.holds e2'.step.at_
    (by rw [e2'.step.cap m, a1.step.cap m]; exact hCap)
    (by show s2.params.length ≤ base + sTy.width; rw [hp2, hp1]; omega)
    (by show base + sTy.width + body.width ≤ s2.params.length + s2.locals.length
        rw [hp2, hl2, hp1, hl1]; omega) hPlace.2 _ _
    (hTrap.of_imp fun h => by
      have hmo := value.mode_owned (slots.map Slot.mode)
      rw [Slot.any_map] at hmo
      simp only [List.any_cons, Expr.aborts] at h ⊢
      exact let_trap_body _ _ _ _ (fun hv => hmo (by simpa using hv)) h)
    fun heap3 store3 s3 ws3 aB => ?_
  have aB' := After.prepend hVarsB e2' aB (fun i h => live_right _ _ _ h) fun i h => by simp [h]
  exact hNext heap3 store3 s3 ws3
    ((After.bind (hVars.live_mono hV) a1' f2 hold' aB' (fun i h => by simpa using h)
      (fun i h => by simp [h]) fun i h => by simp [h]).liveIn hV)

/-- The code of a place, a variable or a pair of places, pushes the words that its variables
hold, which represent its value as borrowed, and changes nothing else. -/
theorem place_spec {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L : Nat → Bool} {base : Nat}
    {heap : Heap} {store : Store Unit} {s : Locals}
    (hVars : Holds env slots L base heap store s) :
    {t : Ty} → (e : Expr S Γ t) → e.isPlace = true → (∀ i, e.uses i = true → L i = true) →
    ∀ {rest : Program} {Q : Assertion Unit} {vs : List Value},
    (∀ ws, t.Rep .borrowed heap store ws (e.denote funs env) →
      wp m rest Q store { s with values := ws.reverse ++ vs } host) →
    wp m (e.placeCode slots ++ rest) Q store { s with values := vs } host
  | _, .var x, _, hL, _, _, _, hNext => by
    obtain ⟨-, ws, hold, hRep⟩ := hVars.1 _ x (hL _ (by simp [Expr.uses]))
    simp only [Expr.placeCode]
    exact wp_loadCode ws hRep.length hold (hNext ws hRep.borrow)
  | _, .pair a b, hp, hL, _, _, _, hNext => by
    simp only [Expr.isPlace, Bool.and_eq_true] at hp
    simp only [Expr.placeCode, List.append_assoc]
    refine place_spec hVars a hp.1 (fun i h => hL i (by simp [Expr.uses, h])) fun wa ha => ?_
    refine place_spec hVars b hp.2 (fun i h => hL i (by simp [Expr.uses, h])) fun wb hb => ?_
    have := hNext (wa ++ wb) ⟨wa, wb, rfl, ha, hb, fun h => nomatch h⟩
    simpa [List.reverse_append, List.append_assoc] using this
  | _, .word _, hp, _, _, _, _, _ | _, .bool _, hp, _, _, _, _, _
  | _, .bin _ _ _, hp, _, _, _, _, _ | _, .cmp _ _ _, hp, _, _, _, _, _
  | _, .not _, hp, _, _, _, _, _ | _, .and _ _, hp, _, _, _, _, _
  | _, .or _ _, hp, _, _, _, _, _ | _, .ite _ _ _, hp, _, _, _, _, _
  | _, .letE _ _, hp, _, _, _, _, _ | _, .call _ _, hp, _, _, _, _, _
  | _, .letPair _ _, hp, _, _, _, _, _ | _, .loop _ _ _, hp, _, _, _, _, _
  | _, .size _, hp, _, _, _, _, _ | _, .get _ _, hp, _, _, _, _, _ => by
    simp [Expr.isPlace] at hp

/-- The code of a call's arguments pushes words that represent their values as borrowed, in
order.  An argument without arrays runs its code with every variable that an argument uses live
after it, so that no argument consumes a variable, and an argument with arrays, a place, loads
its variables' words. -/
theorem args_spec (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {all : Nat → Bool} {base : Nat} :
    {ps : List Ty} → (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) →
    (∀ i env slots live, CodeSpec m funs host (args i) env slots live) →
    (∀ i k, (args i).uses k = true → all k = true) →
    (∀ i, (ps.get i).scalar = false → (args i).isPlace = true) →
    (∀ i, (args i).placeArgs = true) →
    ∀ (heap : Heap) (store : Store Unit) (s : Locals),
    Holds env slots all base heap store s → heap.At store → store.memoryCap m 0 ≤ 65535 →
    s.params.length ≤ base → (∀ i, base + (args i).width ≤ s.params.length + s.locals.length) →
    ∀ (rest : Program) (Q : Assertion Unit),
    TrapOK ((argsAny fun i => (args i).aborts) || slots.any (·.mode == .owned)) Q →
    (∀ heap' store' s' ws, Evolves env slots all all base heap store s heap' store' s' →
      Env.Rep .borrowed heap' store' ws (Env.ofFn fun i => (args i).denote funs env) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) →
    wp m (argsCode (fun i => if (ps.get i).scalar then (args i).code slots base all
      else (args i).placeCode slots) ++ rest) Q store s host
  | [], _, _, _, _, _, heap, store, s, hVars, hAt, _, _, _, _, _, _, hNext => by
    simpa [argsCode, Env.ofFn, Env.Rep] using
      hNext heap store s [] (Evolves.refl hAt hVars fun _ _ h => h) rfl
  | p :: ps, args, argsSpec, hUses, hPlace, hPlaceArgs, heap, store, s, hVars, hAt, hCap, hBase,
      hRoom, rest, Q, hTrap, hNext => by
    simp only [argsCode, List.append_assoc]
    -- The other arguments, from the state after the first.
    have hRest : ∀ heap1 store1 s1 ws1,
        Evolves env slots all all base heap store s heap1 store1 s1 →
        p.Rep .borrowed heap1 store1 ws1 ((args ⟨0, by simp⟩).denote funs env) →
        wp m (argsCode (fun i : Fin ps.length =>
            if ((p :: ps).get i.succ).scalar then (args i.succ).code slots base all
            else (args i.succ).placeCode slots) ++ rest) Q store1
          { s1 with values := ws1.reverse ++ s.values } host := by
      intro heap1 store1 s1 ws1 e1 hR1
      refine args_spec hm (fun i => args i.succ) (fun i => argsSpec i.succ)
        (fun i => hUses i.succ) (fun i => hPlace i.succ) (fun i => hPlaceArgs i.succ) heap1
        store1 { s1 with values := ws1.reverse ++ s.values } (e1.holds.agree fun _ _ => rfl)
        e1.step.at_ (by rw [e1.step.cap m]; exact hCap)
        (by show s1.params.length ≤ base; rw [e1.frame.params]; exact hBase)
        (fun i => by
          show base + (args i.succ).width ≤ s1.params.length + s1.locals.length
          rw [e1.frame.params, e1.frame.length]; exact hRoom _) _ _
        (hTrap.of_imp fun h => by simp only [argsAny]; exact trap_right _ _ _ h)
        fun heap2 store2 s2 ws2 e2 hR2 => ?_
      have e12 := Evolves.trans hVars (e1.values (ws1.reverse ++ s.values)) e2 (fun _ h => h)
        fun _ h => h
      have := hNext heap2 store2 s2 (ws1 ++ ws2) e12
        ⟨ws1, ws2, rfl, (hR1.step e2.step fun _ _ => Holds.KeepDying.none).1, hR2⟩
      simpa [List.reverse_append, List.append_assoc] using this
    by_cases hp : p.scalar = true
    · rw [ite_eq_left (show ((p :: ps).get ⟨0, by simp⟩).scalar = true from hp)]
      have hSub : ∀ k, (all k || (args ⟨0, by simp⟩).uses k) = true → all k = true :=
        fun k h => by
          simp only [Bool.or_eq_true] at h
          exact h.elim id (hUses _ k)
      refine argsSpec ⟨0, by simp⟩ env slots all base heap store s (hVars.live_mono hSub) hAt
        hCap hBase (hRoom _) (hPlaceArgs _) _ _
        (hTrap.of_imp fun h => by simp only [argsAny]; exact trap_left _ _ _ h)
        fun heap1 store1 s1 ws1 a1 => ?_
      exact hRest heap1 store1 s1 ws1 ((a1.liveIn hSub).toEvolves hp) a1.rep.borrow
    · rw [ite_eq_right (show ¬((p :: ps).get ⟨0, by simp⟩).scalar = true from hp)]
      exact place_spec hVars (args ⟨0, by simp⟩) (hPlace _ (by simpa using hp))
        (fun k h => hUses _ k h) fun ws1 hR1 =>
          hRest heap store s ws1 (Evolves.refl hAt hVars fun _ _ h => h) hR1

/-- A call: the arguments, the callee, whose theorem `Calls` gives, and the release of the owned
variables that the arguments use and that die at the call. -/
theorem spec_call (hm : Runtime m) (hCalls : Calls m funs) {sig : Sig} {Γ' : List Ty}
    (g : FVar S sig) (args : (i : Fin sig.params.length) → Expr S Γ' (sig.params.get i))
    (argsSpec : ∀ i env slots live, CodeSpec m funs host (args i) env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.call g args) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hRoom' : ∀ i, base + (args i).width ≤ s.params.length + s.locals.length := fun i =>
    (Nat.add_le_add_left (le_argsMax (fun i => (args i).width) i) base).trans hRoom
  simp only [Expr.placeArgs, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hPlace
  obtain ⟨hA, hB⟩ := hPlace
  have hPlace1 : ∀ i, (sig.params.get i).scalar = false → (args i).isPlace = true :=
    fun i hs => by
      cases hi : (args i).isPlace with
      | true => rfl
      | false =>
        have := le_argsAny (fun i => !(sig.params.get i).scalar && !(args i).isPlace) i
          (by simp only [hs, hi, Bool.not_false, Bool.and_self])
        rw [hA] at this
        exact nomatch this
  have hPlace2 : ∀ i, (args i).placeArgs = true := fun i => by
    cases hi : (args i).placeArgs with
    | true => rfl
    | false =>
      have := le_argsAny (fun i => !(args i).placeArgs) i (by simp [hi])
      rw [hB] at this
      exact nomatch this
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  refine args_spec hm args argsSpec (fun i k h => by
      simp only [Bool.or_eq_true]
      exact Or.inr (le_argsAny (fun j => (args j).uses k) i h))
    hPlace1 hPlace2 heap store s hVars hAt hCap hBase hRoom' _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts]; exact call_trap_args _ _ _ _ h)
    fun heap1 store1 s1 ws1 e1 hR1 => ?_
  obtain ⟨hImpl, fn, hfn, hnum⟩ := hCalls g
  have hRun := (hImpl host store1 heap1 ws1 (Env.ofFn fun i => (args i).denote funs env)
    e1.step.at_ trivial hR1 Separate.nil (by rw [e1.step.cap m]; exact hCap)).append_args
    (by simp [hm.imports]) (by simpa [hm.imports] using hfn) (by simp [hR1.length, hnum])
    s.values
  refine wp_call_runs hRun (hTrap.of_imp fun h => by
    simp only [Expr.aborts]; exact call_trap_callee _ _ _ _ h) fun st' vs hPost => ?_
  obtain ⟨out, rfl, heap', hAt', hOwned, hCaps, hRegions, -⟩ := hPost
  have hRep : sig.result.Rep ((Expr.call g args).mode (slots.map Slot.mode)) heap' st'
      out.reverse (funs.get g (Env.ofFn fun i => (args i).denote funs env)) := by
    simp only [Expr.mode]
    split
    · exact Ty.Rep.borrow hOwned
    · exact hOwned
  have hStep : Step heap1 store1 (fun _ => True) heap' st'
      (((Expr.call g args).mode (slots.map Slot.mode)).fresh st' sig.result out.reverse
        (funs.get g (Env.ofFn fun i => (args i).denote funs env))) :=
    ⟨hAt', hCaps, fun r hr hpos _ => by
      obtain ⟨hb, hreg, hout⟩ := hRegions r hr hpos Apart.nil
      exact ⟨hb, hreg, fun b hb' => hout b (Mode.fresh_sub hb')⟩⟩
  have aCall : After env slots (fun i => live i || (Expr.call g args).uses i)
      (fun i => live i || (Expr.call g args).uses i) base heap store s sig.result
      ((Expr.call g args).mode (slots.map Slot.mode))
      (funs.get g (Env.ofFn fun i => (args i).denote funs env)) heap' st' s1 out.reverse := by
    refine ⟨e1.step.trans hStep fun r hr => ⟨hr, fun _ => trivial⟩, e1.frame,
      e1.holds.step hStep fun _ _ _ _ _ _ _ _ => trivial, hRep, ?_⟩
    intro u y hy _ wy hwy hly b hb c hc
    obtain ⟨hSame, hFresh⟩ := e1.holds.regions_after hStep hy hwy hly fun _ _ => trivial
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
  refine After.release hm (s1 := s1) (live := live)
    (sel := fun i => (argsAny fun j => (args j).uses i) && !live i) hVars aCall (fun _ h => h)
    (fun i h => by
      simp only [Bool.and_eq_true] at h
      simp [Expr.uses, h.1]) (fun i h => by simp [h]) fun heap2 store2 a2 => ?_
  simpa using hNext heap2 store2 s1 out.reverse a2

/-- A pair: the code of each component, each followed by its coercion to the pair's mode. -/
theorem spec_pair (hm : Runtime m) {Γ' : List Ty} {sTy tTy : Ty} {first : Expr S Γ' sTy}
    {second : Expr S Γ' tTy}
    (firstSpec : ∀ env slots live, CodeSpec m funs host first env slots live)
    (secondSpec : ∀ env slots live, CodeSpec m funs host second env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.pair first second) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
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
  have hOwnedTrap : (Expr.pair first second).mode (slots.map Slot.mode) = .owned →
      TrapOK true Q := fun ht => hTrap.of_imp fun _ => by
    have := (Expr.pair first second).mode_owned (slots.map Slot.mode) ht
    rw [Slot.any_map] at this
    exact this
  refine firstSpec env slots (fun i => live i || second.uses i) base heap store s hVarsL hAt hCap
    hBase (by omega) hPlace.1 _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
    fun heap1 store1 s1 ws1 a1 => ?_
  refine After.coerce hm a1 (fun h => by simp [Mode.join, h]) le_rfl
    (by rw [a1.frame.params]; exact hBase) (by rw [a1.frame.params, a1.frame.length]; omega)
    (by rw [a1.step.cap m]; exact hCap) (fun _ ht _ => hOwnedTrap ht)
    fun heap1 store1 s1 ws1 a1 => ?_
  refine secondSpec env slots live base heap1 store1 { s1 with values := ws1.reverse ++ s.values }
    (a1.holds.agree fun _ _ => rfl) a1.step.at_ (by rw [a1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base; rw [a1.frame.params]; exact hBase)
    (by show base + second.width ≤ s1.params.length + s1.locals.length
        rw [a1.frame.params, a1.frame.length]; omega) hPlace.2 _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts]; exact trap_right _ _ _ h)
    fun heap2 store2 s2 ws2 a2 => ?_
  refine After.coerce hm a2 (fun h => by
      simp only [Mode.join, h]; cases first.mode (slots.map Slot.mode) <;> rfl) le_rfl
    (by rw [a2.frame.params, a1.frame.params]; exact hBase)
    (by rw [a2.frame.params, a2.frame.length, a1.frame.params, a1.frame.length]; omega)
    (by rw [a2.step.cap m, a1.step.cap m]; exact hCap) (fun _ ht _ => hOwnedTrap ht)
    fun heap2 store2 s2 ws2 a2 => ?_
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
  simpa [List.reverse_append, List.append_assoc] using hv

/-- A binding of a pair's components: the pair's code, the stores of its components' words, the
release of each component that is owned and that the body does not use, and the body's code. -/
theorem spec_letPair (hm : Runtime m) {Γ' : List Ty} {sTy tTy uTy : Ty}
    {e : Expr S Γ' (.pair sTy tTy)} {body : Expr S (tTy :: sTy :: Γ') uTy}
    (eSpec : ∀ env slots live, CodeSpec m funs host e env slots live)
    (bodySpec : ∀ env slots live, CodeSpec m funs host body env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.letPair e body) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hER : e.width ≤ max e.width body.width := Nat.le_max_left ..
  have hBR : body.width ≤ max e.width body.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  have hV : ∀ i, ((live i || body.uses (i + 2)) || e.uses i) = true →
      (live i || (Expr.letPair e body).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  refine eSpec env slots (fun i => live i || body.uses (i + 2)) (base + sTy.width + tTy.width)
    heap store s ((hVars.mono (by omega)).live_mono hV) hAt hCap (by omega) (by omega) hPlace.1
    _ _ (hTrap.of_imp fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
    fun heap1 store1 s1 ws a1 => ?_
  have hp1 : s1.params = s.params := a1.frame.params
  have hl1 : s1.locals.length = s.locals.length := a1.frame.length
  have a1' := a1.lower (hVars.live_mono hV) (by omega) fun i h => by simp [h]
  obtain ⟨wf, wsec, rfl, hRf, hRs, hDisj⟩ := a1.rep
  have hlf := hRf.length
  have hls := hRs.length
  rw [List.reverse_append, List.append_assoc]
  refine wp_storeCode wsec (base + sTy.width) tTy.width s1 (wf.reverse ++ s.values) hls
    (by rw [hp1]; omega) (by rw [hp1, hl1]; omega) fun s2 hp2 hl2 hold2 hout2 => ?_
  refine wp_storeCode wf base sTy.width s2 s.values hlf (by rw [hp2, hp1]; omega)
    (by rw [hp2, hl2, hp1, hl1]; omega) fun s3 hp3 hl3 hold1 hout3 => ?_
  have hold1' : LocalsHold { s3 with values := s.values } base wf := hold1
  have hold2' : LocalsHold { s3 with values := s.values } (base + sTy.width) wsec := fun k hk => by
    show s3.get (base + sTy.width + k) = _
    rw [hout3 _ (Or.inr (by omega))]
    exact hold2 k hk
  have f3 : Frame base s1 { s3 with values := s.values } :=
    ⟨hp3.trans hp2, hl3.trans hl2, fun j hj => by
      show s3.get j = s1.get j
      rw [hout3 j (Or.inl hj), hout2 j (Or.inl (by omega))]⟩
  -- The body's context: the second component as variable 0 and the first as variable 1.
  have hVars1 := (a1'.holds.agree fun j hj => f3.below j hj)
  have hApart := a1'.apart.agree a1'.holds fun j hj => f3.below j hj
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
  refine wp_releaseVars hm _ (by split <;> split <;> simp) hVarsB a1.step.at_
    (by split <;> split <;> simp) fun heap2 store2 e2 => ?_
  have e2' := e2.mono (live' := fun i => shift 2 live i || body.uses i) fun i h => by
    match i with
    | 0 =>
      have h0 : body.uses 0 = true := by simpa [shift] using h
      simp [h0]
    | 1 =>
      have h1 : body.uses 1 = true := by simpa [shift] using h
      simp [h1]
    | k + 2 => split <;> split <;> simpa using h
  refine bodySpec _ _ (shift 2 live) (base + sTy.width + tTy.width) heap2 store2
    { s3 with values := s.values } e2'.holds e2'.step.at_
    (by rw [e2'.step.cap m, a1.step.cap m]; exact hCap)
    (by show s3.params.length ≤ base + sTy.width + tTy.width; rw [hp3, hp2, hp1]; omega)
    (by show base + sTy.width + tTy.width + body.width ≤ s3.params.length + s3.locals.length
        rw [hp3, hl3, hp2, hl2, hp1, hl1]; omega) hPlace.2 _ _
    (hTrap.of_imp fun h => by
      have hmo := e.mode_owned (slots.map Slot.mode)
      rw [Slot.any_map] at hmo
      simp only [List.any_cons, Expr.aborts] at h ⊢
      exact let_trap_body2 _ _ _ _ (fun hv => hmo (by simpa using hv)) h)
    fun heap3 store3 s4 ws4 aB => ?_
  have aB' := After.prepend hVarsB e2' aB (fun i h => live_right _ _ _ h) fun i h => by simp [h]
  have hNew : ∀ r, (∀ b ∈ (e.mode (slots.map Slot.mode)).fresh store1 (.pair sTy tTy) (wf ++ wsec)
      (e.denote funs env), regionsDisjoint r b) →
      ((e.mode (slots.map Slot.mode)) = .owned → ∀ w,
        LocalsHold { s3 with values := s.values } (base + sTy.width) w → w.length = tTy.width →
        ∀ b ∈ tTy.blocks store1 w (e.denote funs env).2, regionsDisjoint r b) ∧
      ((e.mode (slots.map Slot.mode)) = .owned → ∀ w,
        LocalsHold { s3 with values := s.values } base w → w.length = sTy.width →
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

/-- The release of an array variable that a reader reads, when it is owned and dies there. -/
theorem read_release (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {live : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    {vals : List Value} {rest : Program} {Q : Assertion Unit} (x : Var Γ .array)
    (hVars : Holds env slots (fun k => live k || k == x.index) base heap store s)
    (hAt : heap.At store)
    (hNext : ∀ heap' store', Evolves env slots (fun k => live k || k == x.index) live base heap
      store s heap' store' s → wp m rest Q store' { s with values := vals } host) :
    wp m ((if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
        releaseCode .array (slots.getD x.index default).loc else []) ++ rest) Q store
      { s with values := vals } host := by
  have hCode : (if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
      releaseCode .array (slots.getD x.index default).loc else []) =
      (if live x.index = false then [x.index] else []).flatMap (releaseVar Γ slots) := by
    cases live x.index <;> simp [releaseVar, x.getElem?_index]
  rw [hCode]
  refine wp_releaseVars hm _ (by split <;> simp) (hVars.agree fun _ _ => rfl) hAt
    (by split <;> simp) fun heap' store' e => hNext heap' store' ?_
  have e' := e.mono (live' := live) fun k h => by
    split
    · next hx =>
      have hne : k ≠ x.index := fun he => by rw [he, hx] at h; exact nomatch h
      simp [h, hne]
    · simp [h]
  exact ⟨e'.step, ⟨e'.frame.params, e'.frame.length, e'.frame.below⟩,
    e'.holds.agree fun _ _ => rfl⟩

/-- The size of an array variable: the load of its length word, then the release of the variable
when it is owned and dies there. -/
theorem spec_size (hm : Runtime m) {Γ' : List Ty} (x : Var Γ' .array) :
    ∀ env slots live, CodeSpec m funs host (Expr.size (S := S) x) env slots live := by
  intro env slots live base heap store s hVars hAt _ _ _ _ rest Q _ hNext
  obtain ⟨-, ws, hold, hRep⟩ := hVars.1 _ x (by simp [Expr.uses])
  obtain ⟨ptr, rfl, hB⟩ := hRep
  have hA := hB.borrow.values
  have hLength := hA.lengthBound
  have hPtr : s.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    simpa using hold 0 (by simp)
  simp only [Expr.code, List.cons_append, List.nil_append]
  simp only [wp_localGet_cons, hPtr, wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead]
  refine read_release hm x hVars hAt fun heap' store' e => ?_
  exact hNext heap' store' s [.i64 (env.get x).size.toUInt64]
    (After.ofScalar rfl e.step rfl e.frame e.holds rfl)

/-- A read of an array variable: the position in local `base`, a comparison of it with the
length word, the load of the element or 0, and the release of the variable when it is owned and
dies there. -/
theorem spec_get (hm : Runtime m) {Γ' : List Ty} (x : Var Γ' .array) {i : Expr S Γ' .word}
    (iSpec : ∀ env slots live, CodeSpec m funs host i env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.get x i) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hi : i.width ≤ max i.width 1 := Nat.le_max_left ..
  have h1 : 1 ≤ max i.width 1 := Nat.le_max_right ..
  simp only [Expr.placeArgs] at hPlace
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  have hIn : ∀ k, ((live k || k == x.index) || i.uses k) = true →
      (live k || (Expr.get x i).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact live_assoc _ _ _ h
  refine iSpec env slots (fun k => live k || k == x.index) base heap store s (hVars.live_mono hIn)
    hAt hCap hBase (by omega) hPlace _ _ (hTrap.of_imp fun h => by simpa [Expr.aborts] using h)
    fun heap1 store1 s1 ws1 a1 => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  have e1 := a1.toEvolves rfl
  have hp1 : s1.params = s.params := e1.frame.params
  have hl1 : s1.locals.length = s.locals.length := e1.frame.length
  obtain ⟨hBelowX, wx, holdx, hRepx⟩ := e1.holds.1 _ x (by simp)
  obtain ⟨ptr, rfl, hBx⟩ := hRepx
  have hA := hBx.borrow.values
  have hLength := hA.lengthBound
  have hSize := hA.size_lt
  simp only [Ty.width] at hBelowX
  have hPtr1 : s1.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    simpa using holdx 0 (by simp)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  refine wp_localSet_local (by rw [hp1]; omega) (by rw [hp1, hl1]; omega) ?_
  let s1a := setLocal { s1 with values := s.values } base (.i64 (i.denote funs env))
  have hK : s1a.get base = some (.i64 (i.denote funs env)) :=
    Locals.get_setLocal_same (by show s1.params.length ≤ base; rw [hp1]; omega)
      (by show base < s1.params.length + s1.locals.length; rw [hp1, hl1]; omega)
  have hP : s1a.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne (by show s1.params.length ≤ base; rw [hp1]; omega) (by omega)]
    exact hPtr1
  have hFrame : Frame base s s1a := by
    refine ⟨hp1, by simp [s1a, setLocal, hl1], fun j hj => ?_⟩
    rw [Locals.get_setLocal_ne (by show s1.params.length ≤ base; rw [hp1]; omega) (by omega)]
    exact e1.frame.below j hj
  have hVars1 : Holds env slots (fun k => live k || k == x.index) base heap1 store1 s1a :=
    (e1.holds.agree (s' := { s1 with values := s.values }) fun _ _ => rfl).setLocal le_rfl
      (by show s1.params.length ≤ base; rw [hp1]; exact hBase)
  have hAfter : wp m ((if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
      releaseCode .array (slots.getD x.index default).loc else []) ++ rest) Q store1
      { s1a with values := .i64 (env.get x)[(i.denote funs env).toNat]! :: s.values } host := by
    refine read_release hm x hVars1 e1.step.at_ fun heap2 store2 e2 => ?_
    have e12 := Evolves.trans (hVars.live_mono hIn) ⟨e1.step, hFrame, hVars1⟩ e2
      (fun k h => by simp [h]) fun k h => by simp [h]
    exact hNext heap2 store2 s1a [.i64 (env.get x)[(i.denote funs env).toNat]!]
      ((After.ofScalar (t := .word) (mode := .borrowed) rfl e12.step rfl e12.frame e12.holds
        rfl).liveIn hIn)
  have hs1a : s1a.values = s.values := rfl
  show wp m _ Q store1 s1a host
  simp only [wp_localGet_cons, Locals.get_values, hK, hP, wp_wrapI64_cons, wp_load64_cons,
    wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead]
  simp only [wp_ltUI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have hLess : i.denote funs env < UInt64.ofNat (env.get x).size ↔
      (i.denote funs env).toNat < (env.get x).size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hSize]
  by_cases hk : (i.denote funs env).toNat < (env.get x).size
  · rw [ite_eq_left (by simp [hLess.mpr hk])]
    have hOffset := element_offset hk (by have := hA.1; omega)
    have hElement := hA.elementBound _ hk
    simp only [wp_localGet_cons, Locals.get_values, hK, hP, wp_constI64_cons, wp_addI64_cons,
      wp_mulI64_cons, wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32, UInt32.toNat_zero,
      Nat.add_zero, UInt32.add_zero, hOffset]
    rw [ite_eq_right (by omega), hA.elementRead _ hk,
      ← getElem!_pos (env.get x) (i.denote funs env).toNat hk]
    simpa [wp_nil, hs1a] using hAfter
  · rw [ite_eq_right (by simp [hLess, hk])]
    simp only [wp_constI64_cons, getElem!_neg (env.get x) (i.denote funs env).toNat hk] at hAfter ⊢
    simpa [wp_nil, hs1a, show (default : UInt64) = 0 from rfl] using hAfter

/-- `LeanExe.loop`: the count in local `base`, the initial state, coerced to the loop's mode,
from local `base + 2` on, and the index in local `base + 1`.  The invariant at the top of the
WebAssembly `loop` holds the count, the index `i`, and the state after `i` iterations, with the
facts of `After` for the outer variables live in the loop, those live after it or used by the
body.  Each iteration releases a state that the body does not use, runs the body, coerces its
value to the loop's mode, and stores it as the next state.  After the loop the outer variables
that only the body uses are released. -/
theorem spec_loop (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} {count : Expr S Γ' .word}
    {init : Expr S Γ' tTy} {body : Expr S (tTy :: .word :: Γ') tTy}
    (countSpec : ∀ env slots live, CodeSpec m funs host count env slots live)
    (initSpec : ∀ env slots live, CodeSpec m funs host init env slots live)
    (bodySpec : ∀ env slots live, CodeSpec m funs host body env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.loop count init body) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hc := Nat.le_max_left count.width (max (1 + max init.width (copyWidth tTy))
    (2 + tTy.width + max body.width (copyWidth tTy)))
  have hi := (Nat.le_max_left (1 + max init.width (copyWidth tTy))
    (2 + tTy.width + max body.width (copyWidth tTy))).trans (Nat.le_max_right count.width _)
  have hb := (Nat.le_max_right (1 + max init.width (copyWidth tTy))
    (2 + tTy.width + max body.width (copyWidth tTy))).trans (Nat.le_max_right count.width _)
  have hi1 := Nat.le_max_left init.width (copyWidth tTy)
  have hi2 := Nat.le_max_right init.width (copyWidth tTy)
  have hb1 := Nat.le_max_left body.width (copyWidth tTy)
  have hb2 := Nat.le_max_right body.width (copyWidth tTy)
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  obtain ⟨⟨hPc, hPi⟩, hPb⟩ := hPlace
  have hOwnedTrap : (Expr.loop count init body).mode (slots.map Slot.mode) = .owned →
      TrapOK true Q := fun ht => hTrap.of_imp fun _ => by
    have := (Expr.loop count init body).mode_owned (slots.map Slot.mode) ht
    rw [Slot.any_map] at this
    exact this
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The count, in local `base`.
  have hCountIn : ∀ i, ((live i || init.uses i || body.uses (i + 2)) || count.uses i) = true →
      (live i || (Expr.loop count init body).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact loop_live_count _ _ _ _ h
  refine countSpec env slots (fun i => live i || init.uses i || body.uses (i + 2)) base heap
    store s (hVars.live_mono hCountIn) hAt hCap hBase (by omega) hPc _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts]; exact loop_trap_count _ _ _ _ h)
    fun heap1 store1 s1 ws1 a1 => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  have e1 := a1.toEvolves rfl
  have hp1 : s1.params = s.params := e1.frame.params
  have hl1 : s1.locals.length = s.locals.length := e1.frame.length
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  refine wp_localSet_local (by rw [hp1]; omega) (by rw [hp1, hl1]; omega) ?_
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; exact hBase
  have hF2 : Frame base s
      (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) :=
    ⟨hp1, by simp [setLocal, hl1], fun j hj => by
      rw [Locals.get_setLocal_ne hLow1 (by omega)]
      exact e1.frame.below j hj⟩
  have hN2 : (setLocal { s1 with values := s.values } base
      (.i64 (count.denote funs env))).get base = some (.i64 (count.denote funs env)) :=
    Locals.get_setLocal_same hLow1
      (by show base < s1.params.length + s1.locals.length; rw [hp1, hl1]; omega)
  have e1' : Evolves env slots (fun i => (live i || init.uses i || body.uses (i + 2)) ||
      count.uses i) (fun i => live i || body.uses (i + 2) || init.uses i) base heap store s heap1
      store1 (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) :=
    (Evolves.mk e1.step hF2 ((e1.holds.agree (s' := { s1 with values := s.values })
      fun _ _ => rfl).setLocal le_rfl hLow1)).mono fun i h => loop_live_init _ _ _ h
  -- The initial state, coerced to the loop's mode, in the locals from `base + 2` on.
  refine initSpec env slots (fun i => live i || body.uses (i + 2)) (base + 1) heap1 store1 _
    (e1'.holds.mono (Nat.le_succ base)) e1'.step.at_ (by rw [e1'.step.cap m]; exact hCap)
    (by rw [hF2.params]; omega) (by rw [hF2.params, hF2.length]; omega) hPi _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts]; exact loop_trap_init _ _ _ _ h)
    fun heap2 store2 s3 ws0 a2 => ?_
  refine After.coerce hm a2 (fun h => by simp [Mode.join, h]) le_rfl
    (by rw [a2.frame.params, hF2.params]; omega)
    (by rw [a2.frame.params, a2.frame.length, hF2.params, hF2.length]; omega)
    (by rw [a2.step.cap m, e1'.step.cap m]; exact hCap) (fun _ ht _ => hOwnedTrap ht)
    fun heap2 store2 s3 ws0 a2 => ?_
  have hF3 : Frame base s s3 := hF2.trans (a2.frame.mono (Nat.le_succ base))
  have hN3 : s3.get base = some (.i64 (count.denote funs env)) :=
    (a2.frame.below base (by omega)).trans hN2
  have a0 := (After.prepend (hVars.live_mono hCountIn) e1'
    (a2.lower e1'.holds (Nat.le_succ base) fun i h => by simp [h]) (fun i h => by
      have := loop_live_init _ _ _ h
      simp only [Bool.or_eq_true] at this ⊢; exact Or.inl this) fun i h => by simp [h]).liveIn
    hCountIn
  refine wp_storeCode ws0 (base + 2) tTy.width s3 s.values a0.rep.length
    (by rw [hF3.params]; omega) (by rw [hF3.params, hF3.length]; omega)
    fun s4 hp4 hl4 hold4 hout4 => ?_
  -- The index, in local `base + 1`.
  simp only [wp_constI64_cons]
  refine wp_localSet_local (s := s4) (vs := s.values) (by rw [hp4, hF3.params]; omega)
    (by rw [hp4, hl4, hF3.params, hF3.length]; omega) ?_
  have hLow4 : ({ s4 with values := s.values } : Locals).params.length ≤ base + 1 := by
    show s4.params.length ≤ base + 1; rw [hp4, hF3.params]; omega
  have hF5 : Frame base s3 (setLocal { s4 with values := s.values } (base + 1) (.i64 0)) :=
    ⟨hp4, by simp [setLocal, hl4], fun j hj => by
      rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values,
        hout4 j (Or.inl (by omega))]⟩
  have hN5 : (setLocal { s4 with values := s.values } (base + 1) (.i64 0)).get base =
      some (.i64 (count.denote funs env)) := by
    rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values,
      hout4 base (Or.inl (by omega))]
    exact hN3
  have hI5 : (setLocal { s4 with values := s.values } (base + 1) (.i64 0)).get (base + 1) =
      some (.i64 0) :=
    Locals.get_setLocal_same hLow4
      (by show base + 1 < s4.params.length + s4.locals.length
          rw [hp4, hl4, hF3.params, hF3.length]; omega)
  have hold5 : LocalsHold (setLocal { s4 with values := s.values } (base + 1) (.i64 0))
      (base + 2) ws0 := fun k hk => by
    rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values]
    exact hold4 k hk
  -- The loop.  The invariant holds the count, the index `i`, and the state after `i`
  -- iterations, and the count less the index decreases.
  refine wp_block_cons ?_
  refine wp_loop_cons
    (fun st si => ∃ heapI wsI, ∃ i : UInt64, i ≤ count.denote funs env ∧
      si.get base = some (.i64 (count.denote funs env)) ∧ si.get (base + 1) = some (.i64 i) ∧
      LocalsHold si (base + 2) wsI ∧
      After env slots (fun i => live i || (Expr.loop count init body).uses i)
        (fun i => live i || body.uses (i + 2)) base heap store s tTy
        ((init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)))
        (loopState (init.denote funs env)
          (fun i acc => body.denote funs (.cons acc (.cons i env))) i.toNat) heapI st si wsI)
    (fun _ s' => match s'.get (base + 1) with
      | some (.i64 i) => (count.denote funs env).toNat - i.toNat
      | _ => 0)
    ⟨heap2, ws0, 0, UInt64.zero_le, hN5, hI5, hold5, a0.reframe hF5⟩ ?_
  rintro st si ⟨heapI, wsI, i, hiN, hNi, hii, holdi, aI⟩
  simp only [wp_localGet_cons, Locals.get_values, hii, hNi, wp_geUI64_cons, wp_br_if_cons]
  by_cases hge : count.denote funs env ≤ i
  · -- The index reached the count: the release of the outer variables that only the body
    -- uses, and the load of the state.
    simp (config := { decide := true }) only [ge_iff_le, hge, ↓reduceIte, List.take_zero,
      List.drop_zero, List.nil_append]
    rw [UInt64.le_antisymm hiN hge, loopState_eq] at aI
    refine After.release hm (s1 := si) (live := live)
      (sel := fun i => body.uses (i + 2) && !live i) hVars aI
      (fun i h => by simp only [Expr.uses]; exact loop_live_state _ _ _ _ h)
      (fun i h => by simp only [Bool.and_eq_true] at h; simp [h.1]) (fun i h => by simp [h])
      fun heap' store' a' => ?_
    refine wp_loadCode wsI a'.rep.length holdi ?_
    exact hNext heap' store' si wsI a'
  · -- One more iteration.
    have hlt : i < count.denote funs env := UInt64.not_le.mp hge
    have hsucc : (i + 1).toNat = i.toNat + 1 := by
      have := UInt64.lt_iff_toNat_lt.mp hlt
      have := (count.denote funs env).toNat_lt
      rw [UInt64.toNat_add]; simp; omega
    simp (config := { decide := true }) only [ge_iff_le, hge, ↓reduceIte]
    have holdIdx : LocalsHold si (base + 1) [.i64 i] := fun k hk => by
      obtain rfl : k = 0 := by simpa using hk
      simpa using hii
    have hRoomi : base + 2 + tTy.width + max body.width (copyWidth tTy) ≤
        si.params.length + si.locals.length := by
      rw [aI.frame.params, aI.frame.length]; omega
    -- The body's context: the state as variable 0 and the index as variable 1.
    have hIdx := Holds.push (t := .word) (v := i) (mode := .borrowed)
      (live' := fun j => decide (j + 1 < 2) ||
        shift 2 (fun i => live i || body.uses (i + 2)) (j + 1) || body.uses (j + 1))
      ((aI.holds.mono (Nat.le_add_right base 1)).live_mono fun j h => by simpa using h) holdIdx
      rfl
      (Holds.Apart.ofScalar rfl)
    have hVarsB : Holds (Env.cons (loopState (init.denote funs env)
          (fun i acc => body.denote funs (.cons acc (.cons i env))) i.toNat)
          (Env.cons (t := .word) i env))
        (⟨base + 2, (init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))⟩ ::
          ⟨base + 1, .borrowed⟩ :: slots)
        (fun j => decide (j < 2) ||
          shift 2 (fun i => live i || body.uses (i + 2)) j || body.uses j)
        (base + 2 + tTy.width) heapI st si :=
      Holds.push (hIdx.mono (base' := base + 2) (by simp [Ty.width])) holdi aI.rep
        (Holds.Apart.push (u := .word) (v := i) (mv := .borrowed)
          (live' := fun j => decide (j + 1 < 2) ||
            shift 2 (fun i => live i || body.uses (i + 2)) (j + 1) || body.uses (j + 1))
          (aI.apart.live_mono fun j h => by simpa using h) holdIdx rfl
          fun _ _ _ c hc => by simp [Ty.regions, Ty.reads] at hc)
    have hRelease : (if (init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)) = .owned ∧
          body.uses 0 = false then releaseCode tTy (base + 2) else []) =
        (if body.uses 0 = false then [0] else []).flatMap
          (releaseVar (tTy :: .word :: Γ') (⟨base + 2, (init.mode (slots.map Slot.mode)).join
            (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))⟩ ::
            ⟨base + 1, .borrowed⟩ :: slots)) := by
      cases body.uses 0 <;>
        cases (init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)) <;> simp [releaseVar]
    rw [hRelease]
    refine wp_releaseVars hm _ (by split <;> simp) hVarsB aI.step.at_ (by split <;> simp)
      fun heap2 store2 e2 => ?_
    have e2' := e2.mono
      (live' := fun j => shift 2 (fun i => live i || body.uses (i + 2)) j || body.uses j)
      fun j h => by
        match j with
        | 0 =>
          have h0 : body.uses 0 = true := by simpa [shift] using h
          simp [h0]
        | 1 => simp
        | k + 2 => split <;> simpa using h
    refine bodySpec _ _ (shift 2 fun i => live i || body.uses (i + 2)) (base + 2 + tTy.width)
      heap2 store2 si e2'.holds e2'.step.at_
      (by rw [e2'.step.cap m, aI.step.cap m]; exact hCap) (by rw [aI.frame.params]; omega)
      (by omega) hPb _ _
      ((hTrap.of_imp fun h => by
        have hmo := (Expr.loop count init body).mode_owned (slots.map Slot.mode)
        rw [Slot.any_map] at hmo
        simp only [List.any_cons, Expr.aborts] at h ⊢
        exact loop_trap_body _ _ _ _ _ _ (fun hv => hmo (beq_iff_eq.mp hv)) rfl h).imp
          fun _ h => h)
      fun heap6 store6 s6 ws6 aB => ?_
    have hp6 : s6.params = s.params := aB.frame.params.trans aI.frame.params
    have hl6 : s6.locals.length = s.locals.length := aB.frame.length.trans aI.frame.length
    refine After.coerce hm aB
      (fun h => loop_mode (f := fun md => body.mode (md :: .borrowed :: slots.map Slot.mode)) h)
      le_rfl (by rw [hp6]; omega) (by rw [hp6, hl6]; omega)
      (by rw [aB.step.cap m, e2'.step.cap m, aI.step.cap m]; exact hCap)
      (fun _ ht _ => (hOwnedTrap ht).imp fun _ h => h) fun heap6 store6 s6 ws6 aB => ?_
    have hp6 : s6.params = s.params := aB.frame.params.trans aI.frame.params
    have hl6 : s6.locals.length = s.locals.length := aB.frame.length.trans aI.frame.length
    refine wp_storeCode ws6 (base + 2) tTy.width s6 si.values aB.rep.length
      (by rw [hp6]; omega) (by rw [hp6, hl6]; omega) fun s7 hp7 hl7 hold7 hout7 => ?_
    have hp7' : s7.params = s.params := hp7.trans hp6
    have hl7' : s7.locals.length = s.locals.length := hl7.trans hl6
    have hget7 : ∀ j < base + 2, s7.get j = si.get j := fun j hj => by
      rw [hout7 j (Or.inl hj)]
      exact aB.frame.below j (by omega)
    -- The next index, in local `base + 1`.
    simp only [wp_localGet_cons, Locals.get_values, hget7 (base + 1) (by omega), hii,
      wp_constI64_cons, wp_addI64_cons]
    have hLow7 : ({ s7 with values := si.values } : Locals).params.length ≤ base + 1 := by
      show s7.params.length ≤ base + 1; rw [hp7']; omega
    refine wp_localSet_local (s := s7) (vs := si.values) (by rw [hp7']; omega)
      (by rw [hp7', hl7']; omega) ?_
    have hget8 : (setLocal { s7 with values := si.values } (base + 1) (.i64 (i + 1))).get
        (base + 1) = some (.i64 (i + 1)) :=
      Locals.get_setLocal_same hLow7
        (by show base + 1 < s7.params.length + s7.locals.length; rw [hp7', hl7']; omega)
    have hold8 : LocalsHold (setLocal { s7 with values := si.values } (base + 1)
        (.i64 (i + 1))) (base + 2) ws6 := fun k hk => by
      rw [Locals.get_setLocal_ne hLow7 (by omega), Locals.get_values]
      exact hold7 k hk
    -- The state after `i + 1` iterations: the facts of the body's code for the outer context.
    have aB' := After.prepend hVarsB e2' aB (fun j h => live_right _ _ _ h) fun j h => by
      simp [h]
    have hNew : ∀ r, (∀ b ∈ ((init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))).fresh st tTy wsI
          (loopState (init.denote funs env)
            (fun i acc => body.denote funs (.cons acc (.cons i env))) i.toNat),
          regionsDisjoint r b) →
        ((init.mode (slots.map Slot.mode)).join
            (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)) = .owned → ∀ w,
          LocalsHold si (base + 2) w → w.length = tTy.width →
          ∀ b ∈ tTy.blocks st w (loopState (init.denote funs env)
            (fun i acc => body.denote funs (.cons acc (.cons i env))) i.toNat),
          regionsDisjoint r b) ∧
        (Mode.borrowed = .owned → ∀ w, LocalsHold si (base + 1) w → w.length = Ty.word.width →
          ∀ b ∈ Ty.word.blocks st w i, regionsDisjoint r b) := by
      intro r hFresh
      refine ⟨fun hmo w hw hlw b hb => ?_, fun hmo => nomatch hmo⟩
      obtain rfl := LocalsHold.unique hw holdi (hlw.trans aI.rep.length.symm)
      rw [hmo] at hFresh
      exact hFresh b hb
    have aNext := After.bind2 hVars aI (Frame.refl base si) aB' (by omega) hNew
      (fun j h => by simpa using h)
      (fun j h => by simp only [Expr.uses]; exact loop_live_state _ _ _ _ h) fun _ h => h
    have hv : loopState (init.denote funs env)
        (fun i acc => body.denote funs (.cons acc (.cons i env))) (i + 1).toNat =
        body.denote funs (.cons (loopState (init.denote funs env)
          (fun i acc => body.denote funs (.cons acc (.cons i env))) i.toNat) (.cons i env)) := by
      rw [hsucc, loopState, UInt64.ofNat_toNat]
    rw [wp_br_cons]
    dsimp only
    refine ⟨⟨heap6, ws6, i + 1, UInt64.le_iff_toNat_le.mpr ?_, ?_, hget8, hold8, ?_⟩, ?_⟩
    · have := UInt64.lt_iff_toNat_lt.mp hlt
      omega
    · rw [Locals.get_setLocal_ne hLow7 (by omega), Locals.get_values, hget7 base (by omega)]
      exact hNi
    · rw [hv]
      refine aNext.reframe ⟨hp7, by simp [setLocal, hl7], fun j hj => ?_⟩
      show (setLocal { s7 with values := si.values } (base + 1) (.i64 (i + 1))).get j = s6.get j
      rw [Locals.get_setLocal_ne hLow7 (by omega), Locals.get_values,
        hout7 j (Or.inl (by omega))]
    · have := UInt64.lt_iff_toNat_lt.mp hlt
      simp only [hget8]
      omega

/-- `LeanExe.build`: the count in local `base`, a trap at `unreachable` when it is `2 ^ 29` or
more, a new owned array at the address in local `base + 1`, and the index in local `base + 2`.
The invariant at the top of the WebAssembly `loop` holds an owned array of the count's length
whose elements below the index are the built ones, with the facts of `After` for the outer
variables live in the loop.  Each iteration runs the element's code in the context with the
index, which keeps every region, and stores the element. -/
theorem spec_build (hm : Runtime m) {Γ' : List Ty} {count : Expr S Γ' .word}
    {elem : Expr S (.word :: Γ') .word}
    (countSpec : ∀ env slots live, CodeSpec m funs host count env slots live)
    (elemSpec : ∀ env slots live, CodeSpec m funs host elem env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.build count elem) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hc := Nat.le_max_left count.width (3 + elem.width)
  have he := Nat.le_max_right count.width (3 + elem.width)
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  have hTrapT : TrapOK true Q := hTrap.of_imp fun _ => by simp [Expr.aborts]
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The count, in local `base`.
  have hCountIn : ∀ i, ((live i || elem.uses (i + 1)) || count.uses i) = true →
      (live i || (Expr.build count elem).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  refine countSpec env slots (fun i => live i || elem.uses (i + 1)) base heap store s
    (hVars.live_mono hCountIn) hAt hCap hBase (by omega) hPlace.1 _ _
    (hTrapT.of_imp fun _ => rfl) fun heap1 store1 s1 ws1 a1 => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  have e1 := a1.toEvolves rfl
  have hp1 : s1.params = s.params := e1.frame.params
  have hl1 : s1.locals.length = s.locals.length := e1.frame.length
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  refine wp_localSet_local (by rw [hp1]; omega) (by rw [hp1, hl1]; omega) ?_
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; exact hBase
  have hF2 : Frame base s
      (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) :=
    ⟨hp1, by simp [setLocal, hl1], fun j hj => by
      rw [Locals.get_setLocal_ne hLow1 (by omega)]
      exact e1.frame.below j hj⟩
  have hN2 : (setLocal { s1 with values := s.values } base
      (.i64 (count.denote funs env))).get base = some (.i64 (count.denote funs env)) :=
    Locals.get_setLocal_same hLow1
      (by show base < s1.params.length + s1.locals.length; rw [hp1, hl1]; omega)
  -- The trap when the count is `2 ^ 29` or more.
  simp only [wp_localGet_cons, hN2, wp_constI64_cons, wp_geUI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  by_cases hBig : (536870912 : UInt64) ≤ count.denote funs env
  · simp (config := { decide := true }) only [ge_iff_le, hBig, ↓reduceIte]
    rw [wp_unreachable_cons]
    exact hTrapT _
  · simp (config := { decide := true }) only [ge_iff_le, hBig, ↓reduceIte]
    rw [wp_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    have hn : (count.denote funs env).toNat < 536870912 := by
      have := UInt64.not_le.mp hBig
      rw [UInt64.lt_iff_toNat_lt] at this
      exact this
    -- The new array, at the address in local `base + 1`.
    show wp m _ Q store1
      (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) host
    refine wp_allocArray hm e1.step.at_ (by rw [e1.step.cap m]; exact hCap) hTrapT hn hN2
      (by show s1.params.length ≤ base + 1; rw [hp1]; omega)
      (by show base + 1 < s1.params.length + (setLocal _ _ _).locals.length
          simp [setLocal, hp1, hl1]; omega) (by omega)
      fun heap2 store2 root words hSize hStepA hOwned => ?_
    have hLow2 : (setLocal { s1 with values := s.values } base
        (.i64 (count.denote funs env))).params.length ≤ base + 1 := by
      show s1.params.length ≤ base + 1; rw [hp1]; omega
    have hHigh2 : base + 1 < (setLocal { s1 with values := s.values } base
        (.i64 (count.denote funs env))).params.length + (setLocal { s1 with values := s.values }
        base (.i64 (count.denote funs env))).locals.length := by
      simp [setLocal, hp1, hl1]; omega
    have hF3 : Frame base s (setLocal (setLocal { s1 with values := s.values } base
        (.i64 (count.denote funs env))) (base + 1) (.i64 root)) :=
      hF2.trans ⟨rfl, by simp [setLocal], fun j hj => Locals.get_setLocal_ne hLow2 (by omega)⟩
    have hN3 : (setLocal (setLocal { s1 with values := s.values } base
        (.i64 (count.denote funs env))) (base + 1) (.i64 root)).get base =
        some (.i64 (count.denote funs env)) := by
      rw [Locals.get_setLocal_ne hLow2 (by omega)]; exact hN2
    have hRoot3 : (setLocal (setLocal { s1 with values := s.values } base
        (.i64 (count.denote funs env))) (base + 1) (.i64 root)).get (base + 1) =
        some (.i64 root) := Locals.get_setLocal_same hLow2 hHigh2
    -- The facts of `After` for the new array.
    have hVars1 : Holds env slots (fun i => live i || elem.uses (i + 1)) base heap1 store1
        (setLocal (setLocal { s1 with values := s.values } base
          (.i64 (count.denote funs env))) (base + 1) (.i64 root)) :=
      e1.holds.agree fun j hj => (hF3.below j hj).trans (e1.frame.below j hj).symm
    have a0 : After env slots (fun i => live i || (Expr.build count elem).uses i)
        (fun i => live i || elem.uses (i + 1)) base heap store s .array .owned words heap2 store2
        (setLocal (setLocal { s1 with values := s.values } base
          (.i64 (count.denote funs env))) (base + 1) (.i64 root)) [.i64 root] := by
      refine ⟨(e1.step.trans hStepA fun _ hr => ⟨hr, fun _ => trivial⟩).mono
        (fun _ hr => hr.mono fun i h1 h2 => ⟨hCountIn i h1, h2⟩) (fun _ h => h), hF3,
        hVars1.step hStepA (fun _ _ _ _ _ _ _ _ => trivial), ⟨root, rfl, hOwned⟩, ?_⟩
      intro u y hy _ wy hwy hly b hb c hc
      obtain ⟨hSame, hFresh⟩ := hVars1.regions_after hStepA hy hwy hly fun _ _ => trivial
      rw [hSame] at hc
      exact regionsDisjoint_symm (hFresh c hc b hb)
    -- The index, in local `base + 2`.
    simp only [wp_constI64_cons]
    have hLow3 : (setLocal (setLocal { s1 with values := s.values } base
        (.i64 (count.denote funs env))) (base + 1) (.i64 root)).params.length ≤ base + 2 := by
      show s1.params.length ≤ base + 2; rw [hp1]; omega
    have hHigh3 : base + 2 < (setLocal (setLocal { s1 with values := s.values } base
        (.i64 (count.denote funs env))) (base + 1) (.i64 root)).params.length +
        (setLocal (setLocal { s1 with values := s.values } base
        (.i64 (count.denote funs env))) (base + 1) (.i64 root)).locals.length := by
      simp [setLocal, hp1, hl1]; omega
    refine wp_localSet_local hLow3 hHigh3 ?_
    have hF4 : Frame base (setLocal (setLocal { s1 with values := s.values } base
        (.i64 (count.denote funs env))) (base + 1) (.i64 root))
        (setLocal (setLocal (setLocal { s1 with values := s.values } base
          (.i64 (count.denote funs env))) (base + 1) (.i64 root)) (base + 2) (.i64 0)) :=
      ⟨rfl, by simp [setLocal], fun j hj => Locals.get_setLocal_ne hLow3 (by omega)⟩
    have hN4 := (Locals.get_setLocal_ne (v := .i64 0) hLow3 (by omega : base ≠ base + 2)).trans
      hN3
    have hRoot4 := (Locals.get_setLocal_ne (v := .i64 0) hLow3
      (by omega : base + 1 ≠ base + 2)).trans hRoot3
    have hIdx4 := Locals.get_setLocal_same (v := .i64 0) hLow3 hHigh3
    -- The loop.  The invariant holds an array of the count's length whose elements below the
    -- index `k` are the built ones, and the count less the index decreases.
    refine wp_block_cons ?_
    refine wp_loop_cons
      (fun st si => ∃ heapI words, ∃ k : Nat, k ≤ (count.denote funs env).toNat ∧
        words.size = (count.denote funs env).toNat ∧
        (∀ j (hj : j < words.size), j < k →
          words[j] = elem.denote funs (.cons (UInt64.ofNat j) env)) ∧
        si.get base = some (.i64 (count.denote funs env)) ∧
        si.get (base + 1) = some (.i64 root) ∧ si.get (base + 2) = some (.i64 (UInt64.ofNat k)) ∧
        After env slots (fun i => live i || (Expr.build count elem).uses i)
          (fun i => live i || elem.uses (i + 1)) base heap store s .array .owned words heapI st si
          [.i64 root])
      (fun _ si => match si.get (base + 2) with
        | some (.i64 i) => (count.denote funs env).toNat - i.toNat
        | _ => 0)
      ⟨heap2, words, 0, Nat.zero_le _, hSize, fun _ _ h => absurd h (Nat.not_lt_zero _), hN4,
        hRoot4, hIdx4, a0.reframe hF4⟩ ?_
    rintro st si ⟨heapI, words, k, hk, hSize, hPrefix, hNi, hRooti, hIdxi, aI⟩
    have hk64 : (UInt64.ofNat k).toNat = k :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    simp only [wp_localGet_cons, Locals.get_values, hIdxi, hNi, wp_geUI64_cons, wp_br_if_cons]
    by_cases hDone : count.denote funs env ≤ UInt64.ofNat k
    · -- The array is complete: the release of the outer variables that only the element
      -- reads, and the array's address.
      have hkEq : k = (count.denote funs env).toNat := by
        rw [UInt64.le_iff_toNat_le, hk64] at hDone; omega
      simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte, List.take_zero,
        List.drop_zero, List.nil_append]
      have hWords : words = LeanExe.build (count.denote funs env)
          fun i => elem.denote funs (.cons i env) := by
        apply Array.ext
        · rw [hSize]; simp [LeanExe.build]
        · intro j hj _
          rw [hPrefix j hj (by omega)]
          simp [LeanExe.build]
      rw [hWords] at aI
      refine After.release hm (s1 := si) (live := live)
        (sel := fun i => elem.uses (i + 1) && !live i) hVars aI
        (fun i h => by simp only [Expr.uses]; exact live_build _ _ _ h)
        (fun i h => by simp only [Bool.and_eq_true] at h; simp [h.1]) (fun i h => by simp [h])
        fun heap' store' a' => ?_
      simp only [wp_localGet_cons, Locals.get_values, hRooti]
      simpa [setLocal] using hNext heap' store' si [.i64 root] a'
    · -- One more element.
      have hLess : k < (count.denote funs env).toNat := by
        rw [UInt64.le_iff_toNat_le, hk64] at hDone; omega
      simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte]
      simp only [hRooti, wp_constI64_cons, wp_addI64_cons, wp_mulI64_cons, wp_wrapI64_cons,
        wrap_toUInt32, element_address]
      have hk' : k < words.size := by omega
      -- The element, in the context with the index as variable 0.
      have holdIdx : LocalsHold si (base + 2) [.i64 (UInt64.ofNat k)] := fun j hj => by
        obtain rfl : j = 0 := by simpa using hj
        simpa using hIdxi
      have hLE : ∀ j, (shift 1 (fun i => live i || elem.uses (i + 1)) (j + 1) ||
          elem.uses (j + 1)) = true → (live j || elem.uses (j + 1)) = true := fun j h => by
        simp only [shift_add] at h; exact live_dup _ _ h
      have hVarsI : Holds env slots (fun i => live i || elem.uses (i + 1)) (base + 2) heapI st
          { si with values := .i32 (UInt64Array.wordAddress root (k + 1)) :: si.values } :=
        (aI.holds.mono (by omega)).agree fun _ _ => rfl
      have holdIdx' : LocalsHold
          { si with values := .i32 (UInt64Array.wordAddress root (k + 1)) :: si.values }
          (base + 2) [.i64 (UInt64.ofNat k)] := holdIdx
      have hVarsE := (Holds.push (t := .word) (v := UInt64.ofNat k) (mode := .borrowed)
        (live' := fun j => shift 1 (fun i => live i || elem.uses (i + 1)) j || elem.uses j)
        (hVarsI.live_mono hLE) holdIdx' rfl (Holds.Apart.ofScalar rfl)).mono
        (base' := base + 3) (by simp [Ty.width])
      refine elemSpec _ _ (shift 1 fun i => live i || elem.uses (i + 1)) (base + 3) heapI st
        { si with values := .i32 (UInt64Array.wordAddress root (k + 1)) :: si.values } hVarsE
        aI.step.at_ (by rw [aI.step.cap m]; exact hCap)
        (by show si.params.length ≤ base + 3; rw [aI.frame.params]; omega)
        (by show base + 3 + elem.width ≤ si.params.length + si.locals.length
            rw [aI.frame.params, aI.frame.length]; omega)
        hPlace.2 _ _ ((hTrapT.of_imp fun _ => rfl).imp fun _ h => h)
        fun heapE stE sE wsE aE => ?_
      have hRE := aE.rep
      simp only [Ty.rep_word] at hRE
      subst hRE
      -- The element's facts for the outer context, after the array's.
      have aE1 := After.bind (base := base + 2) hVarsI
        (After.refl (t := .word) (mode := .borrowed) (v := UInt64.ofNat k)
          (ws := [.i64 (UInt64.ofNat k)]) aI.step.at_ hVarsI (fun _ h => h) rfl rfl
          (Holds.Apart.ofScalar rfl))
        (Frame.refl _ _) holdIdx' aE hLE (fun _ h => h) fun _ h => h
      have aE2 := aE1.lower ((aI.holds.agree (s' := { si with
        values := .i32 (UInt64Array.wordAddress root (k + 1)) :: si.values }) fun _ _ => rfl))
        (by omega) fun _ h => h
      obtain ⟨hStep, hFrame, hRep1, hApart1, -⟩ := After.seq hVars aI aE2
        (fun i h => by simp only [Expr.uses]; exact live_build _ _ _ h) fun _ h => h
      have aI2 : After env slots (fun i => live i || (Expr.build count elem).uses i)
          (fun i => live i || elem.uses (i + 1)) base heap store s .array .owned words heapE stE
          sE [.i64 root] :=
        ⟨hStep.mono (fun _ h => h) fun b hb => List.mem_append_left _ hb, hFrame, aE2.holds,
          hRep1, hApart1⟩
      -- The store of the element.
      obtain ⟨p, hp, hOwned2⟩ := aI2.rep
      obtain rfl : p = root := by
        simp only [List.cons.injEq, Value.i64.injEq] at hp; exact hp.1.symm
      have hElement := hOwned2.values.elementBound k hk'
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
      rw [ite_eq_right (by rw [UInt64Array.wordAddress]; omega)]
      have aW := aI2.writeElement hk' (elem.denote funs (.cons (UInt64.ofNat k) env))
      -- The next index, in local `base + 2`.
      have hpE : sE.params = s.params := aE.frame.params.trans aI.frame.params
      have hlE : sE.locals.length = s.locals.length := aE.frame.length.trans aI.frame.length
      have hgetE : ∀ j < base + 3, sE.get j = si.get j := fun j hj => aE.frame.below j hj
      simp only [wp_localGet_cons, Locals.get_values, hgetE (base + 2) (by omega), hIdxi,
        wp_constI64_cons, wp_addI64_cons]
      have hLowE : ({ sE with values := si.values } : Locals).params.length ≤ base + 2 := by
        show sE.params.length ≤ base + 2; rw [hpE]; omega
      have hHighE : base + 2 < ({ sE with values := si.values } : Locals).params.length +
          ({ sE with values := si.values } : Locals).locals.length := by
        show base + 2 < sE.params.length + sE.locals.length; rw [hpE, hlE]; omega
      refine wp_localSet_local (s := sE) (vs := si.values) hLowE hHighE ?_
      have hSucc : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
        rw [UInt64.ofNat_add]; rfl
      have hSucc64 : (UInt64.ofNat (k + 1)).toNat = k + 1 :=
        UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
      have hIdx6 := Locals.get_setLocal_same (v := .i64 (UInt64.ofNat k + 1)) hLowE hHighE
      rw [wp_br_cons]
      dsimp only
      refine ⟨⟨heapE, words.set k _ hk', k + 1, by omega, by simp [hSize], fun j hj hjk => ?_,
        ?_, ?_, by rw [hIdx6, hSucc], aW.reframe ⟨rfl, by simp [setLocal], fun j hj => ?_⟩⟩, ?_⟩
      · rw [Array.getElem_set]
        split
        · next he => subst he; rfl
        · exact hPrefix j (by simpa using hj) (by omega)
      · rw [Locals.get_setLocal_ne hLowE (by omega), Locals.get_values, hgetE base (by omega)]
        exact hNi
      · rw [Locals.get_setLocal_ne hLowE (by omega), Locals.get_values,
          hgetE (base + 1) (by omega)]
        exact hRooti
      · show (setLocal { sE with values := si.values } (base + 2) _).get j = sE.get j
        rw [Locals.get_setLocal_ne hLowE (by omega), Locals.get_values]
      · rw [hIdx6]
        simp only [hSucc, hSucc64]
        omega

theorem Ty.copyScratch_le (t : Ty) : t.copyScratch ≤ copyWidth t := by
  unfold Ty.copyScratch copyWidth
  split <;> omega

/-- A variable in an owned position: its words as an owned value, which move it when it is owned
and dies, and a copy otherwise.  The copy may trap at `unreachable`. -/
theorem spec_ownedVar (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} (x : Var Γ' tTy)
    {env : Env Γ'} {slots : List Slot} {live : Nat → Bool} {base : Nat} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit}
    (hVars : Holds env slots (fun i => live i || i == x.index) base heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoom : base + copyWidth tTy ≤ s.params.length + s.locals.length) (hTrap : TrapOK true Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots (fun i => live i || i == x.index) live base heap store s tTy .owned
        (env.get x) heap' store' s' ws →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wp m (x.ownedCode slots base live ++ rest) Q store s host := by
  simp only [Var.ownedCode, List.append_assoc]
  have hScratch := tTy.copyScratch_le
  refine spec_var (S := []) (funs := .nil) hm x env slots live base heap store s hVars hAt hCap
    hBase (by simp only [Expr.width]; omega) rfl _ _ (hTrap.of_imp fun _ => rfl)
    fun heap1 store1 s1 ws1 a1 => ?_
  rw [show (Expr.var (S := []) x).mode (slots.map Slot.mode) = (slots.getD x.index default).mode
    from Slot.modes_getD slots x.index] at a1
  exact After.coerce hm a1 (fun _ => rfl) le_rfl (by rw [a1.frame.params]; exact hBase)
    (by rw [a1.frame.params, a1.frame.length]; omega) (by rw [a1.step.cap m]; exact hCap)
    (fun _ _ _ => hTrap) hNext

/-- `x.set! i.toNat v`: the position in local `base`, the value in local `base + 1`, the array as
owned in local `base + 2`, which is `x`'s own block when `x` is owned and dies, and the write of
the element when the position is below the length. -/
theorem spec_set (hm : Runtime m) {Γ' : List Ty} (x : Var Γ' .array) {i v : Expr S Γ' .word}
    (iSpec : ∀ env slots live, CodeSpec m funs host i env slots live)
    (vSpec : ∀ env slots live, CodeSpec m funs host v env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.set x i v) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hi := Nat.le_max_left i.width (max (1 + v.width) (2 + copyWidth .array))
  have hv := (Nat.le_max_left (1 + v.width) (2 + copyWidth .array)).trans
    (Nat.le_max_right i.width _)
  have hx := (Nat.le_max_right (1 + v.width) (2 + copyWidth .array)).trans
    (Nat.le_max_right i.width _)
  have hcw : copyWidth Ty.array = 4 := rfl
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  have hTrapT : TrapOK true Q := hTrap.of_imp fun _ => by simp [Expr.aborts]
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The position, in local `base`.
  have hIn : ∀ k, ((live k || k == x.index || v.uses k) || i.uses k) = true →
      (live k || (Expr.set x i v).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact set_live_index _ _ _ _ h
  refine iSpec env slots (fun k => live k || k == x.index || v.uses k) base heap store s
    (hVars.live_mono hIn) hAt hCap hBase (by omega) hPlace.1 _ _ (hTrapT.of_imp fun _ => rfl)
    fun heap1 store1 s1 ws1 a1 => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  refine After.storeWord a1 le_rfl hBase (by omega) fun e1 hI1 => ?_
  have hp1 := e1.frame.params
  have hl1 := e1.frame.length
  -- The value, in local `base + 1`.
  refine vSpec env slots (fun k => live k || k == x.index) (base + 1) heap1 store1 _
    (e1.holds.mono (Nat.le_succ base)) e1.step.at_ (by rw [e1.step.cap m]; exact hCap)
    (by rw [hp1]; omega) (by rw [hp1, hl1]; omega) hPlace.2 _ _ (hTrapT.of_imp fun _ => rfl)
    fun heap2 store2 s2 ws2 a2 => ?_
  have hR2 := a2.rep
  simp only [Ty.rep_word] at hR2
  subst hR2
  refine After.storeWord a2 le_rfl (by rw [hp1]; omega) (by rw [hp1, hl1]; omega)
    fun e2 hV2 => ?_
  have hp2 := e2.frame.params.trans hp1
  have hl2 := e2.frame.length.trans hl1
  have hI2 := (e2.frame.below base (by omega)).trans hI1
  -- The array as owned, in local `base + 2`.
  refine spec_ownedVar hm x ((e2.holds.mono (Nat.le_succ _)) : Holds env slots
      (fun k => live k || k == x.index) (base + 2) heap2 store2 _) e2.step.at_
    (by rw [e2.step.cap m, e1.step.cap m]; exact hCap) (by rw [hp2]; omega)
    (by rw [hp2, hl2]; omega) hTrapT fun heap3 store3 s3 ws3 a3 => ?_
  obtain ⟨p, hws, hOwned⟩ := a3.rep
  subst hws
  have hp3 := a3.frame.params.trans hp2
  have hl3 := a3.frame.length.trans hl2
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow3 : ({ s3 with values := (setLocal { s2 with values := (setLocal { s1 with
      values := s.values } base (.i64 (i.denote funs env))).values } (base + 1)
      (.i64 (v.denote funs env))).values } : Locals).params.length ≤ base + 2 := by
    show s3.params.length ≤ base + 2; rw [hp3]; omega
  have hHigh3 : base + 2 < ({ s3 with values := (setLocal { s2 with values := (setLocal
      { s1 with values := s.values } base (.i64 (i.denote funs env))).values } (base + 1)
      (.i64 (v.denote funs env))).values } : Locals).params.length +
      ({ s3 with values := (setLocal { s2 with values := (setLocal { s1 with
      values := s.values } base (.i64 (i.denote funs env))).values } (base + 1)
      (.i64 (v.denote funs env))).values } : Locals).locals.length := by
    show base + 2 < s3.params.length + s3.locals.length; rw [hp3, hl3]; omega
  refine wp_localSet_local hLow3 hHigh3 ?_
  set s4 : Locals := setLocal { s3 with values := (setLocal { s2 with values := (setLocal
    { s1 with values := s.values } base (.i64 (i.denote funs env))).values } (base + 1)
    (.i64 (v.denote funs env))).values } (base + 2) (.i64 p) with hs4
  have hP4 : s4.get (base + 2) = some (.i64 p) := Locals.get_setLocal_same hLow3 hHigh3
  have hI4 : s4.get base = some (.i64 (i.denote funs env)) :=
    (Locals.get_setLocal_ne (v := .i64 p) hLow3 (by omega : base ≠ base + 2)).trans
      ((a3.frame.below base (by omega)).trans hI2)
  have hV4 : s4.get (base + 1) = some (.i64 (v.denote funs env)) :=
    (Locals.get_setLocal_ne (v := .i64 p) hLow3 (by omega : base + 1 ≠ base + 2)).trans
      ((a3.frame.below (base + 1) (by omega)).trans hV2)
  have hValues4 : s4.values = s.values := rfl
  have hF4 : Frame (base + 2) s3 s4 := ⟨rfl, by simp [s4, setLocal], fun j hj => by
    rw [hs4, Locals.get_setLocal_ne (v := .i64 p) hLow3 (by omega), Locals.get_values]⟩
  have a4 := a3.reframe hF4
  -- The rest of the code, from the array after the write or without it.
  have hFinish : ∀ (store4 : Store Unit) (xs : Array UInt64),
      xs = (env.get x).set! (i.denote funs env).toNat (v.denote funs env) →
      After env slots (fun k => live k || k == x.index) live (base + 2) heap2 store2
        (setLocal { s2 with values := (setLocal { s1 with values := s.values } base
          (.i64 (i.denote funs env))).values } (base + 1) (.i64 (v.denote funs env))) .array
        .owned xs heap3 store4 s4 [.i64 p] →
      wp m rest Q store4 { s4 with values := .i64 p :: s4.values } host := by
    rintro store4 xs rfl aX
    have aX1 := (aX.lower e2.holds (Nat.le_succ _) fun k h => by simp [h])
    have aX2 := After.prepend (e1.holds.mono (Nat.le_succ base)) e2 aX1 (fun k h => by simp [h])
      fun k h => by simp [h]
    have aX3 := After.prepend (hVars.live_mono hIn) e1 (aX2.lower e1.holds (Nat.le_succ base)
      fun k h => by simp [h]) (fun k h => by simp [h]) fun k h => by simp [h]
    simpa [hValues4] using hNext heap3 store4 _ [.i64 p] (aX3.liveIn hIn)
  have hA := hOwned.values
  have hLength := hA.lengthBound
  have hSize := hA.size_lt
  simp only [wp_localGet_cons, Locals.get_values, hI4, hP4, wp_wrapI64_cons, wp_load64_cons,
    wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead]
  simp only [wp_ltUI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have hLess : i.denote funs env < UInt64.ofNat (env.get x).size ↔
      (i.denote funs env).toNat < (env.get x).size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hSize]
  by_cases hk : (i.denote funs env).toNat < (env.get x).size
  · -- The write of the element.
    rw [ite_eq_left (by simp [hLess.mpr hk])]
    have hOffset := element_offset hk (by have := hA.1; omega)
    have hElement := hA.elementBound _ hk
    simp only [wp_localGet_cons, Locals.get_values, hI4, hP4, hV4, wp_constI64_cons,
      wp_addI64_cons, wp_mulI64_cons, wp_wrapI64_cons, wrap_toUInt32, hOffset,
      wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
    rw [ite_eq_right (by omega), wp_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, hP4]
    exact hFinish (UInt64Array.writeElement store3 p _ (v.denote funs env))
      ((env.get x).set _ (v.denote funs env) hk) (by simp [Array.set!, Array.setIfInBounds, hk])
      (a4.writeElement hk (v.denote funs env))
  · rw [ite_eq_right (by simp [hLess, hk])]
    rw [wp_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, wp_localGet_cons, hP4]
    exact hFinish _ (env.get x) (by simp [Array.set!, Array.setIfInBounds, hk]) a4

end Cases

/-- The code of every expression meets its specification. -/
theorem Expr.code_spec {S : List Sig} (m : Module) (funs : Funs S) (host : HostEnv Unit)
    (hm : Runtime m) (hCalls : Calls m funs) {Γ : List Ty} {t : Ty}
    (expr : Expr S Γ t) : ∀ env slots live, CodeSpec m funs host expr env slots live := by
  induction expr with
  | word value => exact spec_word value
  | bool value => exact spec_bool value
  | var x => exact spec_var hm x
  | bin op left right leftSpec rightSpec => exact spec_bin op leftSpec rightSpec
  | cmp op left right leftSpec rightSpec => exact spec_cmp op leftSpec rightSpec
  | not e eSpec => exact spec_not eSpec
  | and left right leftSpec rightSpec => exact spec_and leftSpec rightSpec
  | or left right leftSpec rightSpec => exact spec_or leftSpec rightSpec
  | ite c thenE elseE cSpec thenSpec elseSpec => exact spec_ite hm cSpec thenSpec elseSpec
  | letE value body valueSpec bodySpec => exact spec_letE hm valueSpec bodySpec
  | call g args argsSpec => exact spec_call hm hCalls g args argsSpec
  | pair first second firstSpec secondSpec => exact spec_pair hm firstSpec secondSpec
  | letPair e body eSpec bodySpec => exact spec_letPair hm eSpec bodySpec
  | loop count init body countSpec initSpec bodySpec =>
    exact spec_loop hm countSpec initSpec bodySpec
  | size x => exact spec_size hm x
  | get x i iSpec => exact spec_get hm x iSpec
  | build count elem countSpec elemSpec => exact spec_build hm countSpec elemSpec
  | set x i v iSpec vSpec => exact spec_set hm x iSpec vSpec

/-- The position of a variable's first word among the words of the context's values. -/
def Var.offset : {Γ : List Ty} → {t : Ty} → Var Γ t → Nat
  | _ :: _, _, .here => 0
  | s :: _, _, .there y => s.width + y.offset

theorem paramSlots_getD {Γ : List Ty} {t : Ty} (x : Var Γ t) (loc : Nat) :
    (paramSlots Γ loc).getD x.index default = ⟨loc + x.offset, .borrowed⟩ := by
  induction x generalizing loc with
  | here => simp [paramSlots, Var.index, Var.offset]
  | @there Γ' t' s' y ih =>
    simp only [paramSlots, Var.index, Var.offset, List.getD_cons_succ, ih]
    congr 1
    omega

theorem paramSlots_mode : (ts : List Ty) → (loc i : Nat) →
    ((paramSlots ts loc).getD i default).mode = .borrowed
  | [], _, _ => by simp [paramSlots]; rfl
  | _ :: _, _, 0 => rfl
  | _ :: ts, _, i + 1 => by
    simp only [paramSlots, List.getD_cons_succ]; exact paramSlots_mode ts _ i

theorem paramSlots_any : (ts : List Ty) → (loc : Nat) →
    (paramSlots ts loc).any (·.mode == .owned) = false
  | [], _ => rfl
  | _ :: ts, loc => by simp [paramSlots, paramSlots_any ts]

theorem Var.offset_width {Γ : List Ty} {t : Ty} (x : Var Γ t) :
    x.offset + t.width ≤ widthSum Γ := by
  induction x with
  | here => simp [Var.offset, widthSum_cons]
  | @there Γ' t' s' y ih => simp only [Var.offset, widthSum_cons]; omega

/-- The words of a variable among the words of the context's values. -/
theorem Env.Rep.var {mode : Mode} {heap : Heap} {store : Store Unit} {Γ : List Ty} {t : Ty}
    (x : Var Γ t) : ∀ {ws : List Value} {env : Env Γ}, Env.Rep mode heap store ws env →
      t.Rep mode heap store ((ws.drop x.offset).take t.width) (env.get x) := by
  induction x with
  | here =>
    intro ws env h
    cases env with
    | cons v rest =>
      obtain ⟨first, rest', rfl, h1, -⟩ := h
      rw [Var.offset, List.drop_zero, List.take_left' h1.length]
      exact h1
  | @there Γ' t' s' y ih =>
    intro ws env h
    cases env with
    | cons v rest =>
      obtain ⟨first, rest', rfl, h1, h2⟩ := h
      rw [Var.offset, ← h1.length, List.drop_append, List.drop_eq_nil_of_le (by omega),
        List.nil_append, Nat.add_sub_cancel_left]
      exact ih h2

theorem FVar.index_lt {S : List Sig} {g : Sig} (f : FVar S g) :
    f.index < S.length := by
  induction f with
  | here => simp [FVar.index]
  | there g ih => simp [FVar.index]; omega

/-- A function's code from its entry: the body's code, with every parameter borrowed, followed by
the coercion of the body's value to an owned one. -/
theorem Func.code_spec {S : List Sig} (func : Func S) (funs : Funs S) (m : Module)
    (host : HostEnv Unit) (hm : Runtime m) (hCalls : Calls m funs) (args : Env func.params)
    (heap : Heap) (store : Store Unit) (s : Locals)
    (hVars : Holds args (paramSlots func.params 0) (fun i => false || func.body.uses i)
      (widthSum func.params) heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hBase : s.params.length ≤ widthSum func.params)
    (hRoom : widthSum func.params + func.body.width + copyWidth func.result ≤
      s.params.length + s.locals.length)
    (Q : Assertion Unit) (hTrap : TrapOK func.aborts Q)
    (hNext : ∀ heap' store' s' ws,
      After args (paramSlots func.params 0) (fun i => false || func.body.uses i) (fun _ => false)
        (widthSum func.params) heap store s func.result .owned (func.denote funs args) heap'
        store' s' ws →
      Q (.Fallthrough store' { s' with values := ws.reverse ++ s.values })) :
    wp m (func.body.code (paramSlots func.params 0) (widthSum func.params) (fun _ => false) ++
      (coerceCode func.result (func.body.mode ((paramSlots func.params 0).map Slot.mode)) .owned
        (widthSum func.params + func.body.width) ++ [])) Q store s host := by
  refine Expr.code_spec m funs host hm hCalls func.body args (paramSlots func.params 0)
    (fun _ => false) (widthSum func.params) heap store s hVars hAt hCap hBase (by omega)
    func.placeArgs _ _ (hTrap.of_imp fun h => by
      rw [paramSlots_any, Bool.or_false] at h
      simp [Func.aborts, h]) fun heap' store' s' ws a => ?_
  refine After.coerce hm a (fun _ => rfl) (Nat.le_add_right _ _) (by rw [a.frame.params]; omega)
    (by rw [a.frame.params, a.frame.length]; omega) (by rw [a.step.cap m]; exact hCap)
    (fun _ _ hs => hTrap.of_imp fun _ => by simp [Func.aborts, hs])
    fun heap'' store'' s'' ws'' a'' => ?_
  rw [wp_nil]
  exact hNext heap'' store'' s'' ws'' a''

/-- A function at position `pos` of a module whose functions at the call indices compute the
functions it calls computes `func.denote funs`. -/
theorem Func.correct {S : List Sig} (func : Func S) (funs : Funs S) (m : Module) (pos : Nat)
    (hm : Runtime m) (hFunc : m.funcs[pos]? = some (func.function pos))
    (hCalls : Calls m funs) :
    @ImplementsA _ _ (Env.represent func.params) (Ty.represent func.result) func.aborts m
      pos (func.denote funs) (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  intro host store heap params args hAt _ hArgs _ hCap
  have hArgs' : Env.Rep .borrowed heap store params args := hArgs
  have hLength : params.length = widthSum func.params := hArgs'.length
  apply Runs.of_wp_entry_for (f := func.function pos)
    (by rw [hm.imports, List.length_nil, Nat.sub_zero]; exact hFunc)
    (hImp := by simp [hm.imports])
  have hTake : (params.reverse.take (func.function pos).numParams).reverse = params := by
    rw [List.take_of_length_le (by simp [Func.function, Func.type, Function.numParams, hLength])]
    simp
  rw [hTake, show (func.function pos).body =
    func.body.code (paramSlots func.params 0) (widthSum func.params) (fun _ => false) ++
      (coerceCode func.result (func.body.mode ((paramSlots func.params 0).map Slot.mode)) .owned
        (widthSum func.params + func.body.width) ++ []) by simp [Func.function]]
  have hBorrowed : ∀ i, ((paramSlots func.params 0).getD i default).mode = .owned → False :=
    fun i h => by rw [paramSlots_mode] at h; exact nomatch h
  refine Func.code_spec func funs m host hm hCalls args heap store _
    ⟨fun t x _ => ?_, fun _ _ x _ _ _ _ hmo => (hBorrowed x.index hmo).elim⟩ hAt hCap
    (by simp [Function.toLocals, hLength])
    (by simp [Function.toLocals, Func.function, hLength]; omega) _
    (TrapOK.of_msg fun _ => Iff.rfl) fun heap' store' s' ws a => ?_
  · rw [paramSlots_getD x 0, Nat.zero_add]
    refine ⟨x.offset_width, _, fun k hk => ?_, hArgs'.var x⟩
    have hk' := hk
    simp only [List.length_take, List.length_drop] at hk'
    have hlt : x.offset + k < params.length := by omega
    simp only [Locals.get, Function.toLocals, hlt, ↓reduceIte, List.getElem_take,
      List.getElem_drop]
    simp [List.getElem?_eq_getElem hlt]
  · have hLen := a.rep.length
    have hValues : (ws.reverse ++ ((func.function pos).toLocals params).values).take
        (func.function pos).results.length ++ params.reverse.drop (func.function pos).numParams =
        ws.reverse := by
      simp [Func.function, Func.type, Function.numParams, Function.toLocals, hLen, hLength,
        List.take_of_length_le]
    simp only [hValues]
    refine ⟨heap', a.step.at_, ?_, a.step.caps, fun r hr hpos _ => ?_, trivial⟩
    · show func.result.Rep .owned heap' store' _ (func.body.denote funs args)
      rw [List.reverse_reverse]
      exact a.rep
    · obtain ⟨hb, hreg, hf⟩ := a.step.keeps r hr hpos
        fun _ x _ _ hmo => (hBorrowed x.index hmo).elim
      refine ⟨hb, hreg, fun b hb' => hf b ?_⟩
      rw [List.reverse_reverse] at hb'
      exact hb'

/-- Every function of a program, placed from position 2 of a module without imports, computes
its meaning. -/
theorem Prog.calls {S : List Sig} (prog : Prog S) (m : Module) (hm : Runtime m)
    (hFuncs : ∀ k < S.length, m.funcs[2 + k]? = prog.functions[k]?) : Calls m prog.funs := by
  induction prog with
  | nil => intro g fv; cases fv
  | @cons S' f rest ih =>
    have hRest : Calls m rest.funs := ih fun k hk => by
      rw [hFuncs k (by simp; omega)]
      simp [Prog.functions, List.getElem?_append_left (by rw [rest.functions_length]; exact hk)]
    intro g fv
    cases fv with
    | here =>
      have hpos : m.funcs[2 + S'.length]? = some (f.function (2 + S'.length)) := by
        rw [hFuncs _ (by simp)]
        simp [Prog.functions, rest.functions_length]
      refine ⟨?_, f.function (2 + S'.length), ?_, ?_⟩
      · simpa [FVar.callIndex, FVar.index, Funs.get, Prog.funs] using
          Func.correct f rest.funs m _ hm hpos hRest
      · simpa [FVar.callIndex, FVar.index] using hpos
      · simp [Func.function, Func.type, Function.numParams]
    | there g' =>
      obtain ⟨h1, fn, h2, h3⟩ := hRest g'
      have hidx : (FVar.there g' :
          FVar (⟨f.params, f.result, f.aborts⟩ :: S') g).callIndex = g'.callIndex := by
        have := g'.index_lt
        simp only [FVar.callIndex, FVar.index, List.length_cons]
        omega
      rw [hidx]
      exact ⟨by simpa [Funs.get, Prog.funs] using h1, fn, h2, h3⟩

/-- The correctness theorem.  Every function of a program's module, at its call index, computes
the function that the program gives it: it returns words that represent the value, with the
heap and store changed only as `ImplementsA` allows, and it traps only when it may allocate. -/
theorem Prog.correct {S : List Sig} (prog : Prog S) : Calls (compile prog) prog.funs :=
  prog.calls _ ⟨rfl, rfl, by simp [compile], by simp [compile]⟩ fun k _ => compile_funcs prog k

/-- A function's theorem for the verified compiler's representation gives the theorem for Lean
types whose representations agree with it. -/
theorem ImplementsA.comap {α β γ δ : Type} [Represent α] [Represent β] [Represent γ]
    [Represent δ] {aborts : Bool} {m : Module} {entry : Nat} {f : α → γ}
    (h : ImplementsA aborts m entry f (fun _ _ _ => True) (fun _ _ _ _ _ => True))
    (g : β → α) (k : γ → δ)
    (hArgs : ∀ heap store vs y, Represent.borrowed heap store vs y →
      Represent.borrowed heap store vs (g y))
    (hSep : ∀ store vs y,
      Separate store (Represent.moves store vs y) (Represent.reads store vs y) →
        Separate store (Represent.moves store vs (g y)) (Represent.reads store vs (g y)))
    (hMoves : ∀ store vs y, Represent.moves store vs (g y) = Represent.moves store vs y)
    (hResult : ∀ heap store vs z, Represent.owned heap store vs z →
      Represent.owned heap store vs (k z))
    (hBlocks : ∀ store vs z, Represent.blocks store vs (k z) = Represent.blocks store vs z) :
    ImplementsA aborts m entry (k ∘ f ∘ g) (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  intro env store heap vs y hAt _ hY hSep' hCap
  exact (h env store heap vs (g y) hAt trivial (hArgs _ _ _ _ hY) (hSep _ _ _ hSep') hCap).mono
    fun final values ⟨heap', hAt', hOwned, hCaps, hRegions, _⟩ =>
      ⟨heap', hAt', hResult _ _ _ _ hOwned, hCaps, fun r hr hpos hA => by
        obtain ⟨hb, hreg, hout⟩ := hRegions r hr hpos (by rw [hMoves]; exact hA)
        refine ⟨hb, hreg, ?_⟩
        simp only [Represent.outside, Function.comp_apply, hBlocks]
        exact hout, trivial⟩

/-- A function's theorem in the form of Lean's instances: for the Lean tuple of its arguments and
its result type, with the instances Lean synthesizes for them. -/
theorem ImplementsA.lean {ps : List Ty} {r : Ty} {aborts : Bool} {m : Module} {entry : Nat}
    {f : Env ps → r.denote}
    (h : @ImplementsA _ _ (Env.represent ps) (Ty.represent r) aborts m entry f
      (fun _ _ _ => True) (fun _ _ _ _ _ => True)) :
    @ImplementsA _ _ (argsInst ps) r.leanInst aborts m entry (fun y => f (Env.ofArgs ps y))
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  @ImplementsA.comap _ _ _ _ (Env.represent ps) (argsInst ps) (Ty.represent r) r.leanInst
    aborts m entry f h (Env.ofArgs ps) id
    (fun _ _ _ _ hy => (argsInst_borrowed ps).mp hy) (fun _ _ _ _ => Separate.nil)
    (fun _ _ _ => (argsInst_moves ps).symm)
    (fun _ _ _ _ hz => r.leanInst_owned.mpr hz) (fun _ _ _ => r.leanInst_blocks)

end Verified
