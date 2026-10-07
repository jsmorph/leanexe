import Verified.Heap
import LeanExe.ProofKit.F64Bits
import LeanExe.ProofKit.F64Convert
import LeanExe.ProofKit.F64Decoded

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
    @ImplementsA _ _ (Env.represent g.params g.modes) (Ty.represent g.result) g.aborts m
        f.callIndex
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

theorem argsAny_true : {n : Nat} → {b : (i : Fin n) → Bool} → argsAny b = true ↔ ∃ i, b i = true
  | 0, _ => by simp [argsAny]
  | _ + 1, b => by
    simp only [argsAny, Bool.or_eq_true]
    constructor
    · rintro (h | h)
      · exact ⟨0, h⟩
      · obtain ⟨i, hi⟩ := argsAny_true.mp h
        exact ⟨i.succ, hi⟩
    · rintro ⟨i, hi⟩
      cases i using Fin.cases with
      | zero => exact Or.inl hi
      | succ i => exact Or.inr (argsAny_true.mpr ⟨i, hi⟩)

/-- An owned parameter holds arrays. -/
theorem paramMode_owned : {ts : List Ty} → {ms : List Mode} → {i : Fin ts.length} →
    paramMode ts ms i = .owned → (ts.get i).scalar = false
  | t :: _, _, ⟨0, _⟩, h => by
    cases t <;> first | rfl | simp [paramMode, paramModes, Ty.paramMode] at h
  | _ :: ts, ms, ⟨i + 1, hi⟩, h =>
    paramMode_owned (ts := ts) (ms := ms.tail) (i := ⟨i, by simpa using hi⟩)
      (by simpa only [paramMode, paramModes, List.getD_cons_succ] using h)

/-- An expression at an owned parameter is a variable. -/
theorem Expr.exists_var {Γ : List Ty} {t : Ty} (e : Expr S Γ t)
    (h : e.varIndex?.isNone = false) : ∃ x : Var Γ t, e = .var x := by
  cases e with
  | var x => exact ⟨x, rfl⟩
  | _ => simp [Expr.varIndex?] at h

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

/-- A loop whose function keeps a state that fails `c` keeps it for every later pass. -/
theorem loopState_stop {α : Type} (init : α) (c : α → Bool) (f : UInt64 → α → α) {k : Nat}
    (h : c (loopState init (fun i s => bif c s then f i s else s) k) = false) :
    ∀ j, k ≤ j → loopState init (fun i s => bif c s then f i s else s) j =
      loopState init (fun i s => bif c s then f i s else s) k := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j _ ih => rw [loopState, ih, h]; rfl

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
represent its value: from any heap and store with the allocator invariant, in which the locals
have `h` positions, the variables live before the expression hold their values below position
`base`, and the positions from `base` on are free, the code ends as `After` states.  It may trap
at `unreachable` when the expression may trap or an owned variable is in scope, since only then
does it allocate. -/
def CodeSpec {S : List Sig} {Γ : List Ty} {t : Ty} (m : Module) (funs : Funs S)
    (host : HostEnv Unit) (e : Expr S Γ t) (env : Env Γ) (slots : List Slot)
    (live : Nat → Bool) : Prop :=
  ∀ (h base : Nat) (heap : Heap) (store : Store Unit) (s : Locals), s.half = h →
    Holds env slots (fun i => live i || e.uses i) base heap store s → heap.At store →
    store.memoryCap m 0 ≤ 65535 → s.params.length ≤ base → base + e.width ≤ h →
    e.placeArgs = true →
    ∀ (rest : Program) (Q : Assertion Unit),
    TrapOK (e.aborts || slots.any (·.mode == .owned)) Q →
    (∀ heap' store' s' ws,
      After env slots (fun i => live i || e.uses i) live base heap store s t
        (e.mode (slots.map Slot.mode)) (e.denote funs env) heap' store' s' ws →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) →
    wp m (e.code h slots base live ++ rest) Q store s host

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
  intro env slots live h base heap store s hh hVars hAt _ _ _ _ rest Q _ hNext
  simpa [Expr.code, Expr.denote] using
    hNext heap store s [.i64 value] (After.refl hAt hVars (by intro i h; simp [h]) rfl
      (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .word rfl] at hb; exact nomatch hb)

/-- A constant `Bool`. -/
theorem spec_bool {Γ : List Ty} (value : Bool) :
    ∀ env slots live,
      CodeSpec m funs host (Expr.bool (S := S) (Γ := Γ) value) env slots live := by
  intro env slots live h base heap store s hh hVars hAt _ _ _ _ rest Q _ hNext
  simpa [Expr.code, Expr.denote] using
    hNext heap store s [.i64 (boolWord value)] (After.refl hAt hVars (by intro i h; simp [h]) rfl
      (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .bool rfl] at hb; exact nomatch hb)

/-- A variable: read in place when borrowed, moved where it dies, and copied where it stays
live. -/
theorem spec_var (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} (x : Var Γ' tTy) :
    ∀ env slots live, CodeSpec m funs host (Expr.var (S := S) x) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom _ rest Q hTrap hNext
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
      (hTrap.of_imp fun _ => by simp [Slot.any_owned hOwned]) hh hRep hold hBelow hBase
      (by rw [hh]; simpa [Expr.width] using hRoom) fun heap' store' s' ws' hStep hRep' hF => ?_
    have hHolds := (hVars.live_mono hLiveIn).step hStep (fun _ _ _ _ _ _ _ _ => trivial)
    refine hNext heap' store' s' ws' ⟨?_, hF, hHolds.frame hF le_rfl, ?_, ?_⟩
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
      refine wp_loadCode ws hRep.typed hh hold (hNext heap store s ws (After.refl hAt hVars hLiveIn
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
      fun _ => Holds.KeepDying.transfer h0 a1.step a1.frame hL1
        (fun i h1 _ => h1) (hc.mono fun i h1 h2 => ⟨hL1 _ h1, h2⟩)⟩
  refine ⟨by rw [Mode.fresh_congr hSame1]; exact hStep, a1.frame.trans a2.frame.values, hRep1,
    ?_, fun x hx y hy => by rw [hSame1] at hx; exact hFresh1 x hx y hy⟩
  exact (a1.apart.live_mono hLive).transfer (a1.holds.live_mono hLive) a2.step
    a2.frame.values
    (fun w y hy wy hwy hly c hc => a1.holds.keepDying hLive hy hwy hly c hc) hSame1

/-- Two expressions in a row: the first's value stays on the stack below the second's, and the
facts of `After.seq` hold. -/
theorem seq_spec {Γ : List Ty} {t u : Ty} {l : Expr S Γ t} {r : Expr S Γ u}
    (lSpec : ∀ env slots live, CodeSpec m funs host l env slots live)
    (rSpec : ∀ env slots live, CodeSpec m funs host r env slots live)
    (env : Env Γ) (slots : List Slot) (live : Nat → Bool) (h base : Nat) (heap : Heap)
    (store : Store Unit) (s : Locals) (hh : s.half = h)
    (hVars : Holds env slots (fun i => live i || (l.uses i || r.uses i)) base heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoomL : base + l.width ≤ h) (hRoomR : base + r.width ≤ h)
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
    wp m (l.code h slots base (fun i => live i || r.uses i) ++ (r.code h slots base live ++ rest))
      Q store s host := by
  have hIn : ∀ i, (live i || r.uses i || l.uses i) = true →
      (live i || (l.uses i || r.uses i)) = true := fun i h => live_seq _ _ _ h
  have hVarsL := hVars.live_mono hIn
  refine lSpec env slots _ h base heap store s hh hVarsL hAt hCap hBase hRoomL hPlaceL _ _ hTrapL
    fun heap1 store1 s1 ws1 a1 => ?_
  refine rSpec env slots live h base heap1 store1 { s1 with values := ws1.reverse ++ s.values }
    (a1.frame.half.trans hh) (a1.holds.agree Frame.ofValues) a1.step.at_
    (by rw [a1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base; rw [a1.frame.params]; exact hBase) hRoomR hPlaceR _ _ hTrapR
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
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max op.scratch (max left.width right.width) :=
    (Nat.le_max_left ..).trans (Nat.le_max_right ..)
  have hR : right.width ≤ max op.scratch (max left.width right.width) :=
    (Nat.le_max_right ..).trans (Nat.le_max_right ..)
  have hS : op.scratch ≤ max op.scratch (max left.width right.width) := Nat.le_max_left ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_spec leftSpec rightSpec env slots live h base heap store s hh hVars hAt hCap hBase
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
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_spec leftSpec rightSpec env slots live h base heap store s hh hVars hAt hCap hBase
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

/-- A float constant, from its bit pattern. -/
theorem spec_float {Γ : List Ty} (bits : UInt64) :
    ∀ env slots live,
      CodeSpec m funs host (Expr.float (S := S) (Γ := Γ) bits) env slots live := by
  intro env slots live h base heap store s hh hVars hAt _ _ _ _ rest Q _ hNext
  simpa [Expr.code, Expr.denote, F64Bits.toBits_ofBits] using
    hNext heap store s [.f64 (Float.ofBits bits).toBits] (After.refl hAt hVars
      (by intro i h; simp [h]) rfl (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .float rfl] at hb; exact nomatch hb)

/-- An operation on floats. -/
theorem spec_fbin {Γ : List Ty} (op : FBinOp) {left right : Expr S Γ .float}
    (leftSpec : ∀ env slots live, CodeSpec m funs host left env slots live)
    (rightSpec : ∀ env slots live, CodeSpec m funs host right env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.fbin op left right) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_spec leftSpec rightSpec env slots live h base heap store s hh hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts, Bool.or_eq_true] at h ⊢; tauto)
    (hTrap.of_imp fun h => by simp only [Expr.aborts, Bool.or_eq_true] at h ⊢; tauto)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ => ?_
  have hR1' : ws1 = [.f64 (left.denote funs env).toBits] := hR1
  have hR2' : ws2 = [.f64 (right.denote funs env).toBits] := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext heap2 store2 s2 [.f64 ((Expr.fbin op left right).denote funs env).toBits]
    (After.ofScalar rfl hStep' rfl hF hH rfl)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hv ⊢
  cases op <;>
    simpa [FBinOp.instr, Expr.denote, FBinOp.apply, f64Add, f64Sub, f64Mul, f64Div,
      F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_div] using hv

/-- `After` for locals that differ from the starting ones only in the operand stack. -/
theorem After.ofValues {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap' : Heap} {store store' : Store Unit} {s s' : Locals} {t : Ty}
    {mode : Mode} {v : t.denote} {ws vs : List Value}
    (a : After env slots L0 L base heap store { s with values := vs } t mode v heap' store' s'
      ws) :
    After env slots L0 L base heap store s t mode v heap' store' s' ws :=
  ⟨a.step, a.frame.values, a.holds, a.rep, a.apart⟩

/-- An operation on one float.  The negation subtracts from negative zero, pushed first. -/
theorem spec_funary {Γ : List Ty} (op : FUnOp) {e : Expr S Γ .float}
    (eSpec : ∀ env slots live, CodeSpec m funs host e env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.funary op e) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  simp only [Expr.code]
  cases op with
  | neg =>
    simp only [FUnOp.code, List.cons_append, List.append_assoc, wp_f64Const_cons]
    refine eSpec env slots live h base heap store { s with values := .f64 0x8000000000000000 ::
      s.values } hh (hVars.agree Frame.ofValues) hAt hCap hBase hRoom hPlace _ _ hTrap
      fun heap1 store1 s1 ws a1 => ?_
    have hR : ws = [.f64 (e.denote funs env).toBits] := a1.rep
    subst hR
    have hStep := a1.step
    rw [Mode.fresh_scalar rfl] at hStep
    have hv := hNext heap1 store1 s1 [.f64 (-(e.denote funs env)).toBits]
      (After.ofValues (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl))
    simpa [Expr.denote, FUnOp.apply, f64Sub, F64Bits.toBits_neg] using hv
  | sqrt | abs =>
    simp only [FUnOp.code, List.append_assoc, List.cons_append, List.nil_append]
    refine eSpec env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace _ _ hTrap
      fun heap1 store1 s1 ws a1 => ?_
    have hR : ws = [.f64 (e.denote funs env).toBits] := a1.rep
    subst hR
    have hStep := a1.step
    rw [Mode.fresh_scalar rfl] at hStep
    have hv := hNext heap1 store1 s1 [.f64 ((Expr.funary _ e).denote funs env).toBits]
      (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
    simpa [Expr.denote, FUnOp.apply, f64Sqrt, f64Abs, F64Bits.toBits_sqrt, F64Bits.toBits_abs]
      using hv

/-- Adding negative zero to a float gives the canonical NaN for a NaN and leaves every other
float unchanged: a zero keeps its sign, and a finite nonzero float rounds to itself. -/
theorem add_negZero (x : UInt64) :
    IEEE64.add x 0x8000000000000000 = if IEEE64.isNaN x then IEEE64.canonicalNaN else x := by
  unfold IEEE64.add
  by_cases hn : IEEE64.isNaN x
  · simp [hn]
  have hz : IEEE64.isNaN 0x8000000000000000 = false := by decide
  have hzi : IEEE64.isInfinite 0x8000000000000000 = false := by decide
  have hzv : IEEE64.scaledValue 0x8000000000000000 = 0 := by decide
  have hzs : IEEE64.sign 0x8000000000000000 = true := by decide
  simp only [hn, hz, Bool.or_false, Bool.false_eq_true, ite_false, hzi, hzv, Int.add_zero, hzs,
    Bool.and_true]
  by_cases hi : IEEE64.isInfinite x
  · simp [hi]
  simp only [hi, Bool.false_eq_true, ite_false]
  have he : IEEE64.exponent x ≠ 2047 := by
    intro he
    simp only [IEEE64.isNaN, IEEE64.isInfinite, he] at hn hi
    simp_all
  by_cases hm : IEEE64.scaledMagnitude x = 0
  · have hx := F64Convert.zero_encoding x hm
    have hv : IEEE64.scaledValue x = 0 := by simp [IEEE64.scaledValue, hm]
    simp only [hv, beq_self_eq_true, ite_true]
    conv => rhs; rw [hx]
    cases IEEE64.sign x <;> rfl
  · have hm' : (IEEE64.scaledMagnitude x : Int) ≠ 0 := by exact_mod_cast hm
    have hv : IEEE64.scaledValue x ≠ 0 := by
      simp only [IEEE64.scaledValue]
      split <;> omega
    simp only [hv, beq_iff_eq, ite_false]
    have hneg : decide (IEEE64.scaledValue x < 0) = IEEE64.sign x := by
      simp only [IEEE64.scaledValue]
      split <;> simp_all; omega
    have habs : (IEEE64.scaledValue x).natAbs = IEEE64.scaledMagnitude x := by
      simp only [IEEE64.scaledValue]
      split <;> simp
    rw [hneg, habs]
    exact F64Decoded.roundScaled_value x he hm

/-- A conversion of a word to a float. -/
theorem spec_toFloat {Γ : List Ty} (op : ToFloat) {e : Expr S Γ .word}
    (eSpec : ∀ env slots live, CodeSpec m funs host e env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.toFloat op e) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  simp only [Expr.code, List.append_assoc]
  refine eSpec env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace _ _ hTrap
    fun heap1 store1 s1 ws a1 => ?_
  have hR : ws = [.i64 (e.denote funs env)] := a1.rep
  subst hR
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  have hv := hNext heap1 store1 s1 [.f64 ((Expr.toFloat op e).denote funs env).toBits]
    (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
  cases op <;>
    simpa [ToFloat.code, Expr.denote, ToFloat.apply, f64ConvertI64U, f64Add,
      F64Convert.toBits_toFloat, F64Bits.toBits_ofBits, add_negZero] using hv

/-- A conversion of a float to a word. -/
theorem spec_toWord {Γ : List Ty} (op : ToWord) {e : Expr S Γ .float}
    (eSpec : ∀ env slots live, CodeSpec m funs host e env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.toWord op e) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  simp only [Expr.code, List.append_assoc]
  refine eSpec env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace _ _ hTrap
    fun heap1 store1 s1 ws a1 => ?_
  have hR : ws = [.f64 (e.denote funs env).toBits] := a1.rep
  subst hR
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  have hv := hNext heap1 store1 s1 [.i64 ((Expr.toWord op e).denote funs env)]
    (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
  cases op <;>
    simpa [ToWord.instr, Expr.denote, ToWord.apply, i64TruncSatF64U, F64Convert.toUInt64_eq]
      using hv

/-- A comparison of floats. -/
theorem spec_fcmp {Γ : List Ty} (op : FCmpOp) {left right : Expr S Γ .float}
    (leftSpec : ∀ env slots live, CodeSpec m funs host left env slots live)
    (rightSpec : ∀ env slots live, CodeSpec m funs host right env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.fcmp op left right) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_spec leftSpec rightSpec env slots live h base heap store s hh hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts, Bool.or_eq_true] at h ⊢; tauto)
    (hTrap.of_imp fun h => by simp only [Expr.aborts, Bool.or_eq_true] at h ⊢; tauto)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ => ?_
  have hR1' : ws1 = [.f64 (left.denote funs env).toBits] := hR1
  have hR2' : ws2 = [.f64 (right.denote funs env).toBits] := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext heap2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hv ⊢
  cases op <;>
    simp only [FCmpOp.instr, wp_f64Lt_cons, wp_f64Le_cons, wp_f64Eq_cons, wp_extendUI32_cons]
  · cases hc : IEEE64.lt (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply, F64Bits.decide_lt, f64Lt, boolWord] using hv
  · cases hc : IEEE64.le (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply, F64Bits.decide_le, f64Le, boolWord] using hv
  · cases hc : IEEE64.eq (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply, F64Bits.beq_eq, f64Eq, boolWord] using hv

/-- The negation of a `Bool`. -/
theorem spec_not {Γ : List Ty} {e : Expr S Γ .bool}
    (eSpec : ∀ env slots live, CodeSpec m funs host e env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.not e) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  refine eSpec env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace _ _ hTrap
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
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_spec leftSpec rightSpec env slots live h base heap store s hh hVars hAt hCap hBase
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
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_spec leftSpec rightSpec env slots live h base heap store s hh hVars hAt hCap hBase
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
    {liveIn live : Nat → Bool} {h base base' : Nat} {heap : Heap} {store : Store Unit}
    {s : Locals} {t : Ty} {source target : Mode} {v : t.denote} {heap1 : Heap}
    {store1 : Store Unit} {s1 : Locals} {ws vs : List Value} {rest : Program}
    {Q : Assertion Unit}
    (a : After env slots liveIn live base heap store s t source v heap1 store1 s1 ws)
    (hTarget : source = .owned → target = .owned) (hBase' : base ≤ base')
    (hLow : s1.params.length ≤ base') (hh : s1.half = h) (hRoom : base' + copyWidth t ≤ h)
    (hCap : store1.memoryCap m 0 ≤ 65535)
    (hTrap : source = .borrowed → target = .owned → t.scalar = false → TrapOK true Q)
    (hNext : ∀ heap2 store2 s2 ws2,
      After env slots liveIn live base heap store s t target v heap2 store2 s2 ws2 →
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
    refine wp_copyCode hm t a.step.at_ hCap (hTrap rfl rfl hScalar) (hF2.half.trans hh) a.rep
      hold2 (le_refl _) (by rw [hF2.params]; omega)
      (by simp only [Locals.half_values, hF2.half, hh, Ty.copyScratch, hScalar,
        Bool.false_eq_true, ↓reduceIte]; omega)
      fun heap3 store3 s3 ws3 hStep3 hRep3 hF3 => ?_
    have hF13 : Frame base s1 s3 :=
      (hF2.mono hBase').trans (Frame.ofValues.trans (hF3.mono (by omega)))
    have hF : Frame base s s3 := a.frame.trans hF13
    have hStep0 := a.step
    simp only [Mode.fresh] at hStep0
    refine hNext heap3 store3 s3 ws3 ⟨?_, hF, ?_, hRep3, ?_⟩
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
        fun _ => Holds.KeepDying.transfer h0 e.step e.frame hL1
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
  | loop count init cond body _ ihI _ ihB =>
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
  | build _ _ _ _ | set _ _ _ _ _ | push _ _ _ | append _ _ => intro _ _; simp [Expr.aborts]
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
  ⟨e.step, ⟨e.frame.params, e.frame.length, e.frame.below⟩, e.holds.agree Frame.ofValues⟩

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
  refine wp_releaseWhere hm (a.holds.agree Frame.ofValues) a.step.at_ hSel
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
      fun _ => Holds.KeepDying.transfer h0 a.step a.frame hL1
        (fun i h1 _ => h1) (hr.mono fun i h1 h2 => ⟨hL1 _ h1, h2⟩)⟩
  refine hNext heap2 store2 ⟨hStep.mono (fun _ h => h) fun b hb => ?_, a.frame,
    e'.holds.agree Frame.ofValues, hRep, ?_⟩
  · rw [Mode.fresh_congr hSame] at hb
    exact List.mem_append_left _ hb
  · exact Holds.Apart.transfer (a.holds.live_mono hLiveL1) (a.apart.live_mono hLiveL1) e'.step
      Frame.ofValues (fun u y hy wy hwy hly => a.holds.keepDying hLiveL1 hy hwy hly) hSame

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
    (f2 : Frame base s1 s2) (hold : LocalsHold s2 base sTy.types ws1)
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
      Holds.KeepDying.transfer h0 a1.step a1.frame hL1
        (fun i h1 _ => h1) (hr.mono fun i h1 h2 => ⟨hL1 _ h1, h2⟩)
    intro t' x hx hxo hm wx hwx hlx b hb
    cases x with
    | here =>
      change mv = .owned at hm
      change LocalsHold s2 base sTy.types wx at hwx
      obtain rfl := LocalsHold.unique hwx hold (hlx.trans hl1.symm)
      subst hm
      exact hFresh b hb
    | there x =>
      change (slots.getD x.index default).mode = .owned at hm
      change LocalsHold s2 (slots.getD x.index default).loc t'.types wx at hwx
      have hx1 : L1 x.index = true := hLB _ hx
      have hxo' : live x.index = false := by simpa [Var.index] using hxo
      exact hr1 t' x hx1 hxo' hm wx
        ((a1.holds.hold_agree f2 hx1 hlx).mp hwx) hlx b hb
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
      (sl0.mode = .owned → ∀ w, LocalsHold s2 sl0.loc t0.types w → w.length = t0.width →
        ∀ b ∈ t0.blocks store1 w v0, regionsDisjoint r b) ∧
      (sl1.mode = .owned → ∀ w, LocalsHold s2 sl1.loc t1.types w → w.length = t1.width →
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
      Holds.KeepDying.transfer h0 a1.step a1.frame hL1
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
        change LocalsHold s2 (slots.getD x.index default).loc t'.types wx at hwx
        have hx1 : L1 x.index = true := hLB x.index hx
        have hxo' : live x.index = false := by
          simpa [Var.index, Nat.add_assoc] using hxo
        exact hr1 t' x hx1 hxo' hm wx
          ((a1.holds.hold_agree f2 hx1 hlx).mp hwx) hlx b hb
  · exact ((aB.holds.pop.pop).live_mono fun i h => by simpa [Nat.add_assoc] using h).lower h0
      fun i h => hL1 _ (hLive _ h)
  · exact aB.apart.pop.pop.live_mono fun i h => by simpa [Nat.add_assoc] using h

/-- Writes inside the block of an owned array value that leave it holding `words'`, within its
capacity: the value becomes `words'`, in the same block.  The writes keep every region apart from
the block, and the variables' regions lie apart from it. -/
theorem After.rewrite {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap1 : Heap} {store store1 store2 : Store Unit} {s s1 : Locals}
    {words words' : Array UInt64} {root : UInt64}
    (a : After env slots L0 L base heap store s (.array .word) .owned words heap1 store1 s1
      [.i64 root])
    (hWithin : WritesWithin store1 store2 root.toNat (capacityAt store1 root))
    (hCaps : store2.memoryCaps = store1.memoryCaps) (hValues : UInt64Array.At store2 root words')
    (hFit : 8 * (words'.size + 1) ≤ capacityAt store1 root) :
    After env slots L0 L base heap store s (.array .word) .owned words' heap1 store2 s1
      [.i64 root] := by
  obtain ⟨p, hp, hOwned⟩ := a.rep
  obtain rfl : p = root := by simp only [List.cons.injEq, Value.i64.injEq] at hp; exact hp.1.symm
  have hBase := hOwned.base
  obtain ⟨hOwned', hCapSame⟩ := hOwned.rewrite hWithin hValues hFit
  have hBlock : block store2 p = block store1 p := block_eq hCapSame
  have hW : Step heap1 store1 (fun r => regionsDisjoint r (block store1 p)) heap1 store2 [] :=
    ⟨Heap.At.writesOwned a.step.at_ hOwned hWithin, hCaps, fun r hr _ hd =>
      ⟨fun x hl hh => hWithin.bytes x (by simp only [block, regionsDisjoint] at hd; omega), hr,
        nofun⟩⟩
  -- The variables' regions lie apart from the block.
  have hKeep : ∀ (u : Ty) (y : Var Γ u), L y.index = true → ∀ wy,
      LocalsHold s1 (slots.getD y.index default).loc u.types wy → wy.length = u.width →
      ∀ c ∈ u.regions (slots.getD y.index default).mode store1 wy (env.get y),
        regionsDisjoint c (block store1 p) := fun u y hy wy hwy hly c hc =>
    regionsDisjoint_symm (a.apart u y hy (Or.inl rfl) wy hwy hly (block store1 p)
      (List.mem_singleton_self _) c hc)
  have hStep := a.step.transBoth (keep := Holds.KeepDying env slots L0 L store s) hW
    fun _ hr => ⟨hr, fun hf => hf _ (List.mem_singleton_self _)⟩
  have hSame : (Ty.array .word).regions .owned store2 [.i64 p] words =
      (Ty.array .word).regions .owned store1 [.i64 p] words := by
    show [block _ p] = [block _ p]
    rw [hBlock]
  refine ⟨hStep.mono (fun _ h => h) fun b hb => ?_, a.frame, a.holds.step hW hKeep,
    ⟨p, rfl, hOwned'⟩, ?_⟩
  · have hb' : b = block store1 p := by
      rw [← hBlock]; exact List.mem_singleton.mp hb
    exact List.mem_append_left _ (hb' ▸ List.mem_singleton_self _)
  · exact Holds.Apart.transfer (t := .array .word) (mode := .owned) (ws := [.i64 p]) (v := words)
      a.holds a.apart hW (Frame.refl base s1) hKeep hSame

/-- The write of element `k` of an owned array value: the array with that element replaced, in
the same block. -/
theorem After.writeElement {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap1 : Heap} {store store1 : Store Unit} {s s1 : Locals}
    {words : Array UInt64} {root : UInt64}
    (a : After env slots L0 L base heap store s (.array .word) .owned words heap1 store1 s1
      [.i64 root])
    {k : Nat} (hk : k < words.size) (v : UInt64) :
    After env slots L0 L base heap store s (.array .word) .owned (words.set k v hk) heap1
      (UInt64Array.writeElement store1 root k v) s1 [.i64 root] := by
  obtain ⟨p, hp, hOwned⟩ := a.rep
  replace hOwned : heap1.Owned store1 p words := hOwned
  obtain rfl : p = root := by simp only [List.cons.injEq, Value.i64.injEq] at hp; exact hp.1.symm
  have hA := hOwned.values
  have hCapacity := hOwned.capacity
  have hFrame := UInt64Array.writeElement_frame store1 p words.size k v hA.1 hk
  exact a.rewrite ⟨by rw [hFrame.1], hFrame.2.1, fun x hx => hFrame.2.2 x (by omega)⟩ rfl
    (hA.writeElement hk v) (by rw [Array.size_set]; exact hCapacity)

/-- An owned variable that dies: its words as an owned value, which consumes its blocks. -/
theorem After.move {Γ : List Ty} {env : Env Γ} {slots : List Slot} {live : Nat → Bool}
    {base : Nat} {heap : Heap} {store : Store Unit} {s : Locals} {t : Ty} (x : Var Γ t)
    (hVars : Holds env slots (fun i => live i || i == x.index) base heap store s)
    (hAt : heap.At store) (hOwned : (slots.getD x.index default).mode = .owned)
    (hDead : live x.index = false) {ws : List Value}
    (hold : LocalsHold s (slots.getD x.index default).loc t.types ws) (hl : ws.length = t.width) :
    After env slots (fun i => live i || i == x.index) live base heap store s t .owned (env.get x)
      heap store s ws := by
  have hx : (fun i => live i || i == x.index) x.index = true := by simp
  obtain ⟨-, ws', hold', hRep⟩ := hVars.get x hx
  obtain rfl := LocalsHold.unique hold' hold (hRep.length.trans hl.symm)
  rw [hOwned] at hRep
  refine ⟨⟨hAt, rfl, fun r hr _ hk => ⟨fun _ _ _ => rfl, hr,
    fun b hb => hk t x hx hDead hOwned ws' hold' hRep.length b hb⟩⟩, Frame.refl base s,
    hVars.live_mono fun i h => by simp [h], hRep, ?_⟩
  intro u y hy _ wy hwy hly b hb c hc
  have hne : x.index ≠ y.index := fun he => by rw [he, hy] at hDead; exact nomatch hDead
  exact hVars.2 t u x y hx (by simp [hy]) hne hOwned ws' wy hold' hRep.length hwy hly b hb c hc

/-- `After` for an array of element type `e` is `After` for the words that hold its elements. -/
theorem After.ofWords {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap' : Heap} {store store' : Store Unit} {s s' : Locals} {mode : Mode}
    {e : Elem} {v : Array e.denote} {ws : List Value}
    (a : After env slots L0 L base heap store s (.array .word) mode (e.words v) heap' store' s'
      ws) :
    After env slots L0 L base heap store s (.array e) mode v heap' store' s' ws :=
  ⟨a.step, a.frame, a.holds, a.rep, a.apart⟩

theorem After.toWords {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap' : Heap} {store store' : Store Unit} {s s' : Locals} {mode : Mode}
    {e : Elem} {v : Array e.denote} {ws : List Value}
    (a : After env slots L0 L base heap store s (.array e) mode v heap' store' s' ws) :
    After env slots L0 L base heap store s (.array .word) mode (e.words v) heap' store' s' ws :=
  ⟨a.step, a.frame, a.holds, a.rep, a.apart⟩

/-- A step that consumes the block of an owned array value and whose fresh block holds `v'`:
the value becomes `v'`, at the new address. -/
theorem After.replace {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap1 heap2 : Heap} {store store1 store2 : Store Unit} {s s1 : Locals}
    {v v' : Array UInt64} {p q : UInt64}
    (a : After env slots L0 L base heap store s (.array .word) .owned v heap1 store1 s1 [.i64 p])
    (hStep : Step heap1 store1 (fun r => regionsDisjoint r (block store1 p)) heap2 store2
      [block store2 q])
    (hOwned : heap2.Owned store2 q v') :
    After env slots L0 L base heap store s (.array .word) .owned v' heap2 store2 s1 [.i64 q] := by
  have hKeep : ∀ (u : Ty) (y : Var Γ u), L y.index = true → ∀ wy,
      LocalsHold s1 (slots.getD y.index default).loc u.types wy → wy.length = u.width →
      ∀ c ∈ u.regions (slots.getD y.index default).mode store1 wy (env.get y),
        regionsDisjoint c (block store1 p) := fun u y hy wy hwy hly c hc =>
    regionsDisjoint_symm (a.apart u y hy (Or.inl rfl) wy hwy hly (block store1 p)
      (List.mem_singleton_self _) c hc)
  have hStep2 := a.step.transBoth (keep := Holds.KeepDying env slots L0 L store s) hStep
    fun _ hr => ⟨hr, fun hf => hf _ (List.mem_singleton_self _)⟩
  refine ⟨hStep2.mono (fun _ h => h) fun b hb => List.mem_append_right _ hb, a.frame,
    a.holds.step hStep hKeep, ⟨q, rfl, hOwned⟩, ?_⟩
  intro u y hy _ wy hwy hly b hb c hc
  obtain ⟨hSame, hFresh⟩ := a.holds.regions_after hStep hy hwy hly (hKeep u y hy wy hwy hly)
  rw [hSame] at hc
  exact regionsDisjoint_symm (hFresh c hc b hb)

/-- The store of a word value into local `loc`, at or above `base`: the facts of `After` as an
evolution to the locals with the word. -/
theorem After.storeWord {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap1 : Heap} {store store1 : Store Unit} {s s1 : Locals} {mode : Mode}
    {v : UInt64} {vs : List Value} {loc : Nat} {rest : Program} {Q : Assertion Unit}
    (a : After env slots L0 L base heap store s .word mode v heap1 store1 s1 [.i64 v])
    (hLoc : base ≤ loc) (hLow : s.params.length ≤ loc) (hHigh : loc < s.half)
    (hNext : Evolves env slots L0 L base heap store s heap1 store1
        (setLocal { s1 with values := vs } loc (.i64 v)) →
      (setLocal { s1 with values := vs } loc (.i64 v)).get loc = some (.i64 v) →
      wp m rest Q store1 (setLocal { s1 with values := vs } loc (.i64 v)) host) :
    wp m (.localSet loc :: rest) Q store1 { s1 with values := [.i64 v].reverse ++ vs } host := by
  have hLow1 : ({ s1 with values := vs } : Locals).params.length ≤ loc := by
    show s1.params.length ≤ loc; rw [a.frame.params]; exact hLow
  have hHigh1 : loc < ({ s1 with values := vs } : Locals).half := by
    rw [Locals.half_values, a.frame.half]; exact hHigh
  refine wp_localSet_local hLow1 (Locals.lt_total hHigh1) ?_
  have e := a.toEvolves rfl
  have f : Frame base s1 (setLocal { s1 with values := vs } loc (.i64 v)) :=
    Frame.setValues hLow1 hLoc hHigh1
  exact hNext ⟨e.step, e.frame.trans f, e.holds.agree f⟩
    (Locals.get_setLocal_same hLow1 (Locals.lt_total hHigh1))

theorem wp_ofWordCode {st : Store Unit} {env' : HostEnv Unit} {s : Locals} {vs : List Value}
    {rest : Program} {Q : Assertion Unit} (ty : ValueType) (w : UInt64) :
    wp m (ofWordCode ty ++ rest) Q st { s with values := .i64 w :: vs } env' ↔
      wp m rest Q st { s with values := typedValue ty w :: vs } env' := by
  cases ty <;> simp [ofWordCode, typedValue]

theorem wp_toWordCode {st : Store Unit} {env' : HostEnv Unit} {s : Locals} {vs : List Value}
    {rest : Program} {Q : Assertion Unit} (ty : ValueType) (w : UInt64) :
    wp m (toWordCode ty ++ rest) Q st { s with values := typedValue ty w :: vs } env' ↔
      wp m rest Q st { s with values := .i64 w :: vs } env' := by
  cases ty <;> simp [toWordCode, typedValue]

theorem wordCount_toNat (k : Nat) : (wordCount k).toNat = min k 536870912 :=
  UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)

theorem wordCount_ne_zero {k : Nat} (hk : 0 < k) : wordCount k ≠ 0 := by
  intro h
  have := wordCount_toNat k
  rw [h] at this
  simp at this
  omega

theorem wp_scaleCode {st : Store Unit} {env' : HostEnv Unit} {s : Locals} {vs : List Value}
    {rest : Program} {Q : Assertion Unit} (k : Nat) (x : UInt64) :
    wp m (scaleCode k ++ rest) Q st { s with values := .i64 x :: vs } env' ↔
      wp m rest Q st { s with values := .i64 (x * wordCount k) :: vs } env' := by
  unfold scaleCode
  split
  · next hk => subst hk; simp [wordCount]
  · simp [wp_constI64_cons, wp_mulI64_cons]

theorem wp_divCode {st : Store Unit} {env' : HostEnv Unit} {s : Locals} {vs : List Value}
    {rest : Program} {Q : Assertion Unit} {k : Nat} (hk : 0 < k) (x : UInt64) :
    wp m (divCode k ++ rest) Q st { s with values := .i64 x :: vs } env' ↔
      wp m rest Q st { s with values := .i64 (x / wordCount k) :: vs } env' := by
  unfold divCode
  split
  · next hk => subst hk; simp [wordCount]
  · simp [wp_constI64_cons, wp_divUI64_cons, wordCount_ne_zero hk]

/-- The word count of an array of `n` elements of `k` words, divided by the code's word count, is
`n`. -/
theorem words_div {n k : Nat} (hk : 0 < k) (hnk : n * k < 536870912) :
    UInt64.ofNat (n * k) / wordCount k = UInt64.ofNat n := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div, wordCount_toNat, UInt64.toNat_ofNat_of_lt' (by
      rw [show UInt64.size = 18446744073709551616 from rfl]; omega),
    UInt64.toNat_ofNat_of_lt' (by
      rw [show UInt64.size = 18446744073709551616 from rfl]
      have := Nat.le_mul_of_pos_right n hk; omega)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : k < 536870912 := by have := Nat.le_mul_of_pos_left k hn; omega
    rw [Nat.min_eq_left (by omega), Nat.mul_div_cancel _ hk]

/-- The first word of element `i` of an array of elements of `k` words, when the array holds the
element, is word `i * k`. -/
theorem words_scale {i k : Nat} (hk0 : 0 < k) (hik : i * k < 536870912) :
    UInt64.ofNat i * wordCount k = UInt64.ofNat (i * k) := by
  have hi : i ≤ i * k := Nat.le_mul_of_pos_right i hk0
  apply UInt64.toNat_inj.mp
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  have hk : k < 536870912 := by have := Nat.le_mul_of_pos_left k hpos; omega
  rw [UInt64.toNat_mul, wordCount_toNat, Nat.min_eq_left (by omega),
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega),
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- A count below the limit of `build` gives fewer than `2 ^ 29` words. -/
theorem build_limit {c k : Nat} (hk : 0 < k) (hc : c < (536870912 + k - 1) / k) :
    c * k < 536870912 := by
  have := (Nat.le_div_iff_mul_le hk).mp (Nat.succ_le_of_lt hc)
  rw [Nat.succ_mul] at this
  omega

/-- The offset of word `w + j` of an array, as the code computes it. -/
theorem word_offset {w : UInt64} {j size : Nat} (hw : w.toNat + j < size)
    (hSize : 8 * (size + 1) ≤ 4294967296) :
    (w + UInt64.ofNat (j + 1)) * 8 = UInt64.ofNat (8 * (w.toNat + j + 1)) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

/-- The loads of words `w + j` on of the array at `p`, each under the flag: the array's words
when the flag is 1, and zeros when it is 0.  `w` is the word in local `w0`. -/
theorem wp_loadWordsCode {store : Store Unit} {env' : HostEnv Unit} {ptr w0 flag : Nat}
    {p w : UInt64} {ws : Array UInt64} {rest : Program} {Q : Assertion Unit} (b : Bool)
    (hA : b = true → UInt64Array.At store p ws) :
    (j : Nat) → (tys : List ValueType) → (s : Locals) → (vals : List UInt64) →
    s.get ptr = some (.i64 p) → s.get w0 = some (.i64 w) →
    s.get flag = some (.i64 (boolWord b)) → vals.length = tys.length →
    (b = true → w.toNat + j + tys.length ≤ ws.size ∧
      ∀ i, i < vals.length → ws[w.toNat + j + i]! = vals[i]!) →
    (b = false → vals = List.replicate tys.length 0) →
    wp m rest Q store
      { s with values := (List.zipWith typedValue tys vals).reverse ++ s.values } env' →
    wp m (loadWordsCode ptr w0 flag j tys ++ rest) Q store s env'
  | _, [], s, vals, _, _, _, hl, _, _, hk => by
    obtain rfl : vals = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simpa [loadWordsCode] using hk
  | j, ty :: tys, s, v :: vals, hP, hW, hF, hl, hT, hZ, hk => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [loadWordsCode, List.append_assoc, List.cons_append, List.nil_append]
    simp only [wp_localGet_cons, hF, wp_wrapI64_cons]
    rw [wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    have hNext : wp m (ofWordCode ty ++ loadWordsCode ptr w0 flag (j + 1) tys ++ rest) Q store
        { s with values := .i64 v :: s.values } env' := by
      rw [List.append_assoc, wp_ofWordCode]
      refine wp_loadWordsCode b hA (j + 1) tys { s with values := typedValue ty v :: s.values } vals
        hP hW hF hl (fun hb => ?_) (fun hb => ?_) ?_
      · obtain ⟨hFit, hRead⟩ := hT hb
        refine ⟨by simp only [List.length_cons] at hFit; omega, fun i hi => ?_⟩
        have := hRead (i + 1) (by simp; omega)
        rw [show w.toNat + (j + 1) + i = w.toNat + j + (i + 1) by omega, this]
        rfl
      · have := hZ hb
        simp only [List.length_cons, List.replicate_succ, List.cons.injEq] at this
        exact this.2
      · simpa [List.zipWith_cons_cons, List.reverse_cons, List.append_assoc] using hk
    cases b with
    | false =>
      have hv : v = 0 := by
        have := hZ rfl
        simp only [List.length_cons, List.replicate_succ, List.cons.injEq] at this
        exact this.1
      subst hv
      simp only [boolWord, Bool.cond_false]
      simpa [wp_constI64_cons, wp_nil] using hNext
    | true =>
      obtain ⟨hFit, hRead⟩ := hT rfl
      have hAt := hA rfl
      simp only [List.length_cons] at hFit
      have hn : w.toNat + j < ws.size := by omega
      have hv : ws[w.toNat + j]! = v := by simpa using hRead 0 (by simp)
      have hOffset := word_offset hn (by have := hAt.1; omega)
      have hElement := hAt.elementBound _ hn
      simp (config := { decide := true }) only [boolWord, Bool.cond_true, ↓reduceIte]
      simp only [wordAddrCode, List.cons_append, List.nil_append, wp_localGet_cons,
        Locals.get_values, hP, hW, wp_constI64_cons, wp_addI64_cons, wp_mulI64_cons,
        wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero,
        UInt32.add_zero, hOffset]
      rw [ite_eq_right (by omega), hAt.elementRead _ hn, ← getElem!_pos ws _ hn, hv]
      simpa [wp_nil] using hNext

/-- The writes of the words of types `tys` at positions `src` on as the words `w + j` on of an
owned array value at `p`: the array with those words replaced, in the same block.  `w` is the word
in local `w0`. -/
theorem wp_storeWordsCode {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap1 : Heap} {store0 : Store Unit} {s0 : Locals} {h ptr w0 : Nat}
    {p w : UInt64} {rest : Program} {Q : Assertion Unit} :
    (j src : Nat) → (tys : List ValueType) → (words : List UInt64) → (ws : Array UInt64) →
    (store1 : Store Unit) → (s : Locals) →
    After env slots L0 L base heap store0 s0 (.array .word) .owned ws heap1 store1 s [.i64 p] →
    s.half = h → s.get ptr = some (.i64 p) → s.get w0 = some (.i64 w) →
    LocalsHold s src tys (List.zipWith typedValue tys words) → words.length = tys.length →
    w.toNat + j + tys.length ≤ ws.size →
    (∀ store2, After env slots L0 L base heap store0 s0 (.array .word) .owned
        (writeWords ws (w.toNat + j) words) heap1 store2 s [.i64 p] →
      wp m rest Q store2 s host) →
    wp m (storeWordsCode h ptr w0 j src tys ++ rest) Q store1 s host
  | _, _, [], words, ws, store1, s, a, _, _, _, _, hl, _, hk => by
    obtain rfl : words = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simpa [storeWordsCode, writeWords] using hk store1 a
  | j, src, ty :: tys, v :: words, ws, store1, s, a, hh, hP, hW, hold, hl, hFit, hk => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [List.length_cons] at hFit
    have hn : w.toNat + j < ws.size := by omega
    obtain ⟨q, hq, hOwned⟩ := a.rep
    replace hOwned : heap1.Owned store1 q ws := hOwned
    obtain rfl : q = p := by simp only [List.cons.injEq, Value.i64.injEq] at hq; exact hq.1.symm
    have hA := hOwned.values
    have hOffset := word_offset hn (by have := hA.1; omega)
    have hElement := hA.elementBound _ hn
    have hv : s.get (slotIndex h src ty) = some (typedValue ty v) := by
      have := hold 0 (by simp)
      simpa [hh, List.zipWith_cons_cons] using this
    have holdRest : LocalsHold s (src + 1) tys (List.zipWith typedValue tys words) := by
      intro k hk'
      have := hold (k + 1) (by simp only [List.zipWith_cons_cons, List.length_cons]; omega)
      simpa [List.zipWith_cons_cons, Nat.add_assoc, Nat.add_comm 1 k] using this
    simp only [storeWordsCode, wordAddrCode, List.append_assoc, List.cons_append,
      List.nil_append, wp_localGet_cons, Locals.get_values, hP, hW, wp_constI64_cons,
      wp_addI64_cons, wp_mulI64_cons, wp_wrapI64_cons, wrap_toUInt32, hOffset, hv]
    rw [wp_toWordCode]
    simp only [wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
    rw [ite_eq_right (by omega)]
    refine wp_storeWordsCode (j + 1) (src + 1) tys words _ _ s (a.writeElement hn v) hh hP hW
      holdRest hl (by rw [Array.size_set]; omega) fun store2 a2 => hk store2 ?_
    have hSet : ws.set (w.toNat + j) v hn = ws.set! (w.toNat + j) v := by
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hn]
    rw [hSet, show w.toNat + (j + 1) = w.toNat + j + 1 by omega] at a2
    exact a2

/-- The facts of `After` for other locals that agree below `base`. -/
theorem After.reframe {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap' : Heap} {store store' : Store Unit} {s s' s'' : Locals} {t : Ty}
    {mode : Mode} {v : t.denote} {ws : List Value}
    (a : After env slots L0 L base heap store s t mode v heap' store' s' ws)
    (f : Frame base s' s'') :
    After env slots L0 L base heap store s t mode v heap' store' s'' ws :=
  ⟨a.step, a.frame.trans f, a.holds.agree f, a.rep,
    a.apart.agree a.holds f⟩

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

theorem append_live : ∀ a xb yb : Bool,
    (a || yb || xb) = true → (a || (xb || yb)) = true := by decide

theorem live_dup : ∀ a b : Bool, (a || b || b) = true → (a || b) = true := by decide

theorem live_assoc : ∀ a b c : Bool, (a || b || c) = true → (a || (b || c)) = true := by decide

/-- The live sets and trap flags of a loop: `a` for a variable live after it, `c`, `n`, `d`, and
`b` for its use in the count, the initial state, the condition, and the body, and `o` for an
owned variable in scope. -/
theorem loop_live_count : ∀ a d b n c : Bool,
    (a || d || b || n || c) = true → (a || (c || n || d || b)) = true := by decide

theorem loop_live_state : ∀ a d b c n : Bool,
    (a || d || b) = true → (a || (c || n || d || b)) = true := by decide

theorem loop_sel : ∀ a d b : Bool, (d || b) = true → (a || d || b) = true := by decide

theorem loop_trap_count : ∀ c n d b o : Bool, (c || o) = true → (c || n || d || b || o) = true := by
  decide

theorem loop_trap_init : ∀ c n d b o : Bool, (n || o) = true → (c || n || d || b || o) = true := by
  decide

theorem loop_trap_cond : ∀ c n d b o : Bool, (d || o) = true → (c || n || d || b || o) = true := by
  decide

theorem loop_trap_body : ∀ c n d b m z o : Bool, (m = true → (c || n || d || b || o) = true) →
    z = false → (b || (m || (z || o))) = true → (c || n || d || b || o) = true := by decide

/-- The condition's live sets: the state, variable 0, and the outer variables of `all`, which
hold every outer variable that the condition uses. -/
theorem cond_live (all d : Nat → Bool) (hd : ∀ i, d (i + 1) = true → all i = true) :
    ∀ j, ((j == 0 || shift 1 all j) || d j) = true → (j == 0 || shift 1 all j) = true
  | 0, _ => rfl
  | k + 1, h => by
    have hk : ¬ k + 1 < 1 := by omega
    simp only [shift, hk, if_false, Nat.add_sub_cancel] at h ⊢
    have : (k + 1 == 0) = false := rfl
    rw [this, Bool.false_or] at h ⊢
    cases hd' : d (k + 1)
    · simpa [hd'] using h
    · exact hd k hd'

theorem cond_live_outer (all d : Nat → Bool) (hd : ∀ i, d (i + 1) = true → all i = true)
    (j : Nat) (h : ((j + 1 == 0 || shift 1 all (j + 1)) || d (j + 1)) = true) : all j = true := by
  have := cond_live all d hd (j + 1) h
  have hk : ¬ j + 1 < 1 := by omega
  simpa [shift, hk] using this

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
    {env : Env Γ'} {slots : List Slot} {live : Nat → Bool} {h base : Nat} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit} (hh : s.half = h)
    (hVars : Holds env slots (fun i => live i || (Expr.ite c thenE elseE).uses i) base heap
      store s)
    (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoomB : base + tTy.width + max b.width (copyWidth tTy) ≤ h)
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
  rw [← List.append_nil (storeCode h base tTy.types)]
  have hbw := Nat.le_max_left b.width (copyWidth tTy)
  have hcw := Nat.le_max_right b.width (copyWidth tTy)
  refine bSpec env slots live h (base + tTy.width) heap2 store2 { s1 with values := s.values }
    hh1 (e2.holds.mono (by omega)) e2.step.at_
    (by rw [e2.step.cap m, e1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base + tTy.width; rw [hp1]; omega)
    (by omega) hbPlace _ _ (hTrapB.of_imp fun h => by
          simp only [Bool.or_eq_true] at h ⊢; exact h.imp_left hba)
    fun heap3 store3 s3 ws3 a3 => ?_
  have hp3 : s3.params = s.params := a3.frame.params.trans hp1
  have hh3 : s3.half = h := a3.frame.half.trans hh1
  refine After.coerce hm a3 hbm le_rfl (by rw [hp3]; omega) hh3 (by omega)
    (by rw [a3.step.cap m, e2.step.cap m, e1.step.cap m]; exact hCap)
    (fun hs ht _ => (hTrapB.of_imp fun _ => by
      have := (Expr.ite c thenE elseE).mode_owned (slots.map Slot.mode) ht
      rw [Slot.any_map] at this; exact this))
    fun heap4 store4 s4 ws4 a4 => ?_
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
  exact aAll.apart.agree aAll.holds hF45

/-- An `if`: the condition, then each branch as `ite_branch` describes. -/
theorem spec_ite (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} {c : Expr S Γ' .bool}
    {thenE elseE : Expr S Γ' tTy}
    (cSpec : ∀ env slots live, CodeSpec m funs host c env slots live)
    (thenSpec : ∀ env slots live, CodeSpec m funs host thenE env slots live)
    (elseSpec : ∀ env slots live, CodeSpec m funs host elseE env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.ite c thenE elseE) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
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
  refine cSpec env slots _ h base heap store s hh (hVars.live_mono hMid) hAt hCap hBase
    (by omega) hPlaceC _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts]; exact ite_trap_cond _ _ _ _ h)
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
  have hRoomT : base + tTy.width + max thenE.width (copyWidth tTy) ≤ h := by
    have := Nat.max_le.mpr ⟨ht.trans (Nat.le_max_left _ (copyWidth tTy)), Nat.le_max_right _ _⟩
    omega
  have hRoomE : base + tTy.width + max elseE.width (copyWidth tTy) ≤ h := by
    have := Nat.max_le.mpr ⟨he.trans (Nat.le_max_left _ (copyWidth tTy)), Nat.le_max_right _ _⟩
    omega
  cases hcv : c.denote funs env
  · simp (config := { decide := true }) only [↓reduceIte]
    exact ite_branch hm elseSpec hh hVars hCap hBase hRoomE hTrap hNext e1 hPlaceE
      (fun i h => by simp [h]) (fun h => by simp [Expr.aborts, h])
      (by simp [Expr.denote, hcv]) hModeE _ (fun _ h => h) fun _ _ h => by simpa using h
  · simp (config := { decide := true }) only [↓reduceIte]
    exact ite_branch hm thenSpec hh hVars hCap hBase hRoomT hTrap hNext e1 hPlaceT
      (fun i h => by simp [h]) (fun h => by simp [Expr.aborts, h])
      (by simp [Expr.denote, hcv]) hModeT _ (fun _ h => h) fun _ _ h => by simpa using h

/-- A `let` binding: the value's code, the store of its words from local `base` on, the release
of the value when it is owned and the body does not use it, and the body's code. -/
theorem spec_letE (hm : Runtime m) {Γ' : List Ty} {sTy tTy : Ty} {value : Expr S Γ' sTy}
    {body : Expr S (sTy :: Γ') tTy}
    (valueSpec : ∀ env slots live, CodeSpec m funs host value env slots live)
    (bodySpec : ∀ env slots live, CodeSpec m funs host body env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.letE value body) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
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
    store s hh ((hVars.mono (by omega)).live_mono hV) hAt hCap (by omega) (by omega) hPlace.1 _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
    fun heap1 store1 s1 ws1 a1 => ?_
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
  refine wp_releaseVars hm _ (by split <;> simp) hVarsB a1.step.at_ (by split <;> simp)
    fun heap2 store2 e2 => ?_
  have e2' := e2.mono (live' := fun i => shift 1 live i || body.uses i) fun i h => by
    cases i with
    | zero =>
      have h0 : body.uses 0 = true := by simpa [shift] using h
      simp [h0]
    | succ k => split <;> simpa using h
  refine bodySpec _ _ (shift 1 live) h (base + sTy.width) heap2 store2
    { s2 with values := s.values } hh2 e2'.holds e2'.step.at_
    (by rw [e2'.step.cap m, a1.step.cap m]; exact hCap)
    (by show s2.params.length ≤ base + sTy.width; rw [hp2]; omega)
    (by omega) hPlace.2 _ _
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

theorem Ty.copyScratch_le (t : Ty) : t.copyScratch ≤ copyWidth t := by
  unfold Ty.copyScratch copyWidth
  split <;> omega

/-- A variable in an owned position: its words as an owned value, which move it when it is owned
and dies, and a copy otherwise.  The copy may trap at `unreachable`. -/
theorem spec_ownedVar (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} (x : Var Γ' tTy)
    {env : Env Γ'} {slots : List Slot} {live : Nat → Bool} {h base : Nat} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit} (hh : s.half = h)
    (hVars : Holds env slots (fun i => live i || i == x.index) base heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoom : base + copyWidth tTy ≤ h) (hTrap : TrapOK true Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots (fun i => live i || i == x.index) live base heap store s tTy .owned
        (env.get x) heap' store' s' ws →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wp m (x.ownedCode h slots base live ++ rest) Q store s host := by
  simp only [Var.ownedCode, List.append_assoc]
  have hScratch := tTy.copyScratch_le
  refine spec_var (S := []) (funs := .nil) hm x env slots live h base heap store s hh hVars hAt
    hCap hBase (by simp only [Expr.width]; omega) rfl _ _ (hTrap.of_imp fun _ => rfl)
    fun heap1 store1 s1 ws1 a1 => ?_
  rw [show (Expr.var (S := []) x).mode (slots.map Slot.mode) = (slots.getD x.index default).mode
    from Slot.modes_getD slots x.index] at a1
  exact After.coerce hm a1 (fun _ => rfl) le_rfl (by rw [a1.frame.params]; exact hBase)
    (a1.frame.half.trans hh) (by omega) (by rw [a1.step.cap m]; exact hCap)
    (fun _ _ _ => hTrap) hNext

/-- The region `r` lies apart from the regions of the variables that `sel` selects. -/
def Holds.ApartFrom {Γ : List Ty} (env : Env Γ) (slots : List Slot) (sel : Nat → Bool)
    (store : Store Unit) (s : Locals) (r : Nat × Nat) : Prop :=
  ∀ (u : Ty) (y : Var Γ u), sel y.index = true → ∀ wy,
    LocalsHold s (slots.getD y.index default).loc u.types wy → wy.length = u.width →
    ∀ c ∈ u.regions (slots.getD y.index default).mode store wy (env.get y), regionsDisjoint r c

namespace Holds

variable {Γ : List Ty} {env : Env Γ} {slots : List Slot} {live sel : Nat → Bool} {base : Nat}
  {heap heap' : Heap} {store store' : Store Unit} {s s' : Locals} {fresh : List (Nat × Nat)}

theorem ApartFrom.mono {r : Nat × Nat} (h : ApartFrom env slots sel store s r)
    {sel' : Nat → Bool} (hSel : ∀ i, sel' i = true → sel i = true) :
    ApartFrom env slots sel' store s r :=
  fun u y hy => h u y (hSel _ hy)

/-- A region apart from the regions of the owned variables that die lies apart from their
blocks. -/
theorem ApartFrom.keepDying {r : Nat × Nat} (h : ApartFrom env slots sel store s r)
    {liveIn liveOut : Nat → Bool}
    (hSub : ∀ i, liveIn i = true → liveOut i = false → sel i = true) :
    KeepDying env slots liveIn liveOut store s r := by
  intro t x hx hxo hm wx hwx hlx b hb
  refine h t x (hSub _ hx hxo) wx hwx hlx b ?_
  rw [hm]
  exact hb

/-- `ApartFrom` holds in either state of a step that keeps every region, for live variables. -/
theorem ApartFrom.iff (h : Holds env slots live base heap store s)
    (hStep : Step heap store (fun _ => True) heap' store' fresh)
    (hs : Frame base s s') (hSel : ∀ i, sel i = true → live i = true)
    {r : Nat × Nat} : ApartFrom env slots sel store' s' r ↔ ApartFrom env slots sel store s r := by
  constructor
  · intro hA u y hy wy hwy hly c hc
    have hSame := (h.regions_after hStep (hSel _ hy) hwy hly fun _ _ => trivial).1
    exact hA u y hy wy ((h.hold_agree hs (hSel _ hy) hly).mpr hwy) hly c (hSame ▸ hc)
  · intro hA u y hy wy hwy hly c hc
    have hwy' := (h.hold_agree hs (hSel _ hy) hly).mp hwy
    rw [(h.regions_after hStep (hSel _ hy) hwy' hly fun _ _ => trivial).1] at hc
    exact hA u y hy wy hwy' hly c hc

/-- The blocks of a live owned variable lie apart from the variables other than it. -/
theorem ApartFrom.owned (h : Holds env slots live base heap store s) {t : Ty} {x : Var Γ t}
    (hx : live x.index = true) (hm : (slots.getD x.index default).mode = .owned)
    {wx : List Value} (hwx : LocalsHold s (slots.getD x.index default).loc t.types wx)
    (hlx : wx.length = t.width) (hSel : ∀ i, sel i = true → live i = true ∧ i ≠ x.index) :
    ∀ b ∈ t.blocks store wx (env.get x), ApartFrom env slots sel store s b :=
  fun b hb u y hy wy hwy hly c hc =>
    h.2 t u x y hx (hSel _ hy).1 (fun he => (hSel _ hy).2 he.symm) hm wx wy hwx hlx hwy hly b hb c
      hc

end Holds

theorem Apart.append {store : Store Unit} {l1 l2 : List UInt64} {r : Nat × Nat}
    (h1 : Apart store l1 r) (h2 : Apart store l2 r) : Apart store (l1 ++ l2) r := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact h1 q hq
  · exact h2 q hq

/-- The code of a place, a variable or a pair of places, pushes the words that its variables
hold, which represent its value as borrowed, and changes nothing else.  A region apart from the
regions of its variables lies apart from its arrays' words. -/
theorem place_spec {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L : Nat → Bool}
    {h base : Nat} {heap : Heap} {store : Store Unit} {s : Locals} (hh : s.half = h)
    (hVars : Holds env slots L base heap store s) :
    {t : Ty} → (e : Expr S Γ t) → e.isPlace = true → (∀ i, e.uses i = true → L i = true) →
    ∀ {rest : Program} {Q : Assertion Unit} {vs : List Value},
    (∀ ws, t.Rep .borrowed heap store ws (e.denote funs env) →
      (∀ r, Holds.ApartFrom env slots e.uses store s r →
        ∀ c ∈ t.reads ws (e.denote funs env), regionsDisjoint r c) →
      wp m rest Q store { s with values := ws.reverse ++ vs } host) →
    wp m (e.placeCode h slots ++ rest) Q store { s with values := vs } host
  | _, .var x, _, hL, _, _, _, hNext => by
    obtain ⟨-, ws, hold, hRep⟩ := hVars.1 _ x (hL _ (by simp [Expr.uses]))
    simp only [Expr.placeCode]
    exact wp_loadCode ws hRep.typed hh hold (hNext ws hRep.borrow fun r hr =>
      hRep.reads_apart r (hr _ x (by simp [Expr.uses]) ws hold hRep.length))
  | _, .pair a b, hp, hL, _, _, _, hNext => by
    simp only [Expr.isPlace, Bool.and_eq_true] at hp
    simp only [Expr.placeCode, List.append_assoc]
    refine place_spec hh hVars a hp.1 (fun i h => hL i (by simp [Expr.uses, h]))
      fun wa ha hra => ?_
    refine place_spec hh hVars b hp.2 (fun i h => hL i (by simp [Expr.uses, h]))
      fun wb hb hrb => ?_
    have := hNext (wa ++ wb) ⟨wa, wb, rfl, ha, hb, fun h => nomatch h⟩ fun r hr c hc => by
      rw [Ty.reads_append ha.length] at hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hra r (hr.mono fun i h => by simp [Expr.uses, h]) c hc
      · exact hrb r (hr.mono fun i h => by simp [Expr.uses, h]) c hc
    simpa [List.reverse_append, List.append_assoc] using this
  | _, .word _, hp, _, _, _, _, _ | _, .bool _, hp, _, _, _, _, _
  | _, .bin _ _ _, hp, _, _, _, _, _ | _, .cmp _ _ _, hp, _, _, _, _, _
  | _, .not _, hp, _, _, _, _, _ | _, .and _ _, hp, _, _, _, _, _
  | _, .or _ _, hp, _, _, _, _, _ | _, .ite _ _ _, hp, _, _, _, _, _
  | _, .letE _ _, hp, _, _, _, _, _ | _, .call _ _, hp, _, _, _, _, _
  | _, .letPair _ _, hp, _, _, _, _, _ | _, .loop _ _ _ _, hp, _, _, _, _, _
  | _, .size _, hp, _, _, _, _, _ | _, .get _ _, hp, _, _, _, _, _
  | _, .build _ _, hp, _, _, _, _, _ | _, .set _ _ _, hp, _, _, _, _, _
  | _, .push _ _, hp, _, _, _, _, _ | _, .append _ _, hp, _, _, _, _, _
  | _, .float _, hp, _, _, _, _, _ | _, .fbin _ _ _, hp, _, _, _, _, _
  | _, .funary _ _, hp, _, _, _, _, _ | _, .fcmp _ _ _, hp, _, _, _, _, _
  | _, .toFloat _ _, hp, _, _, _, _, _ | _, .toWord _ _, hp, _, _, _, _, _ => by
    simp [Expr.isPlace] at hp

theorem args_trap_first : ∀ a d b o : Bool, (a || o) = true → (a || d || b || o) = true := by
  decide

/-- The words of an owned variable in an owned position, where it dies: its own words. -/
theorem Var.ownedCode_move {Γ : List Ty} {t : Ty} (x : Var Γ t) {slots : List Slot}
    {base : Nat} {live : Nat → Bool} (hm : (slots.getD x.index default).mode = .owned)
    (hx : live x.index = false) {h : Nat} :
    x.ownedCode h slots base live = loadCode h (slots.getD x.index default).loc t.types := by
  simp only [Var.ownedCode, Var.code, hm, hx, Bool.false_eq_true, and_false, ↓reduceIte,
    coerceCode, reduceCtorEq, false_and, List.append_nil]

/-- The code of a variable in an owned position depends only on whether the variable is live. -/
theorem Var.ownedCode_live {Γ : List Ty} {t : Ty} (x : Var Γ t) {slots : List Slot}
    {h base : Nat} {live live' : Nat → Bool} (hl : live x.index = live' x.index) :
    x.ownedCode h slots base live = x.ownedCode h slots base live' := by
  simp [Var.ownedCode, Var.code, hl]

/-- The code of a call's arguments pushes words that represent their values in the modes
`modes`, in order.  An argument without arrays runs its code with the variables `all` live after
it, so that no argument consumes a variable.  A borrowed argument with arrays, a place, loads its
variables' words.  An owned argument, a variable, loads its words when it is owned and not in
`kept`, which moves it into the call, and is copied otherwise.  The copies are the fresh blocks
`F` of the arguments' step.  The owned arguments' blocks lie apart from one another and from the
borrowed arguments' arrays, and a region apart from `F` and from the blocks of the moved
variables lies apart from the owned arguments' blocks.  A region apart from the variables that
the arguments with arrays read lies apart from the borrowed arguments' arrays. -/
theorem args_spec (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {all kept : Nat → Bool} {h base : Nat} :
    {ps : List Ty} → (modes : Nat → Mode) →
    (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) →
    (∀ i env slots live, CodeSpec m funs host (args i) env slots live) →
    (∀ i k, (args i).uses k = true → all k = true) → (∀ k, kept k = true → all k = true) →
    (∀ i : Fin ps.length, modes i = .owned → (ps.get i).scalar = false) →
    (∀ i, (ps.get i).scalar = false → modes i = .borrowed → (args i).isPlace = true) →
    (∀ i : Fin ps.length, modes i = .owned → ∃ x : Var Γ (ps.get i), args i = .var x ∧
      (kept x.index = false → (slots.getD x.index default).mode = .owned ∧
        ∀ j : Fin ps.length, j ≠ i → (ps.get j).scalar = false →
          (args j).uses x.index = false)) →
    (∀ i, (args i).placeArgs = true) →
    ∀ (heap : Heap) (store : Store Unit) (s : Locals), s.half = h →
    Holds env slots all base heap store s → heap.At store → store.memoryCap m 0 ≤ 65535 →
    s.params.length ≤ base →
    (∀ i : Fin ps.length,
      base + (if modes i = .owned then copyWidth (ps.get i) else (args i).width) ≤ h) →
    ∀ (rest : Program) (Q : Assertion Unit),
    TrapOK ((argsAny fun i => (args i).aborts || modes i == .owned) ||
      slots.any (·.mode == .owned)) Q →
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
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) →
    wp m (argsCode (fun i => if (ps.get i).scalar then (args i).code h slots base all
      else if modes i = .owned then (args i).ownedCode h slots base kept
      else (args i).placeCode h slots) ++ rest) Q store s host
  | [], _, _, _, _, _, _, _, _, _, heap, store, s, _, hVars, hAt, _, _, _, rest, Q, _, hNext => by
    simpa [argsCode, Env.ofFn, Env.Rep, Env.moves, Env.reads] using
      hNext heap store s [] [] (Step.refl hAt _) (Frame.refl base s) hVars rfl Separate.nil
        (fun _ _ _ => Apart.nil) fun _ _ _ h => nomatch h
  | p :: ps, modes, args, argsSpec, hUses, hKept, hArray, hPlace, hOwned, hPlaceArgs, heap,
      store, s, hh, hVars, hAt, hCap, hBase, hRoom, rest, Q, hTrap, hNext => by
    simp only [argsCode, List.append_assoc]
    -- The other arguments, from the state after the first, and the facts of all of them.
    have hRest : ∀ heap1 store1 s1 ws0 F0,
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
      intro heap1 store1 s1 ws0 F0 hStep1 hF1 hH1 hR1 h5a h5c h6b
      have hl0 := hR1.length
      have hAllUses : ∀ (i : Fin ps.length) k, (args i.succ).uses k = true → all k = true :=
        fun i => hUses i.succ
      refine args_spec hm (fun i => modes (i + 1)) (fun i => args i.succ)
        (fun i => argsSpec i.succ) hAllUses hKept (fun i => hArray i.succ)
        (fun i => hPlace i.succ) (fun i hmo => ?_) (fun i => hPlaceArgs i.succ) heap1
        store1 { s1 with values := ws0.reverse ++ s.values } (hF1.half.trans hh)
        (hH1.agree Frame.ofValues) hStep1.at_ (by rw [hStep1.cap m]; exact hCap)
        (by show s1.params.length ≤ base; rw [hF1.params]; exact hBase)
        (fun i => hRoom i.succ) _ _
        (hTrap.of_imp fun h => by simp only [argsAny]; exact trap_right _ _ _ h)
        fun heap2 store2 s2 ws2 F2 hStep2 hF2 hH2 hRep2 hSep2 hX2 hY2 => ?_
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
      refine argsSpec ⟨0, by simp⟩ env slots all h base heap store s hh (hVars.live_mono hSub)
        hAt hCap hBase hRoom0 (hPlaceArgs _) _ _
        (hTrap.of_imp fun h => by simp only [argsAny]; exact args_trap_first _ _ _ _ h)
        fun heap1 store1 s1 ws1 a1 => ?_
      have hStep := a1.step
      rw [Mode.fresh_scalar (show ((p :: ps).get ⟨0, by simp⟩).scalar = true from hp)] at hStep
      refine hRest heap1 store1 s1 ws1 [] (hStep.mono (fun _ _ => (Holds.KeepDying.none).mono
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
          refine wp_loadCode ws hRep.typed hh hold (hRest heap store s ws [] (Step.refl hAt _)
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
          refine spec_ownedVar hm x hh (hVars.live_mono fun i h => by
              simp only [Bool.or_eq_true, beq_iff_eq] at h
              exact h.elim id fun he => he ▸ hAllX) hAt hCap hBase hRoom0
            (hTrap.of_imp fun _ => by simp [argsAny, hmd]) fun heap1 store1 s1 ws1 a1 => ?_
          have hStep := a1.step
          simp only [Mode.fresh] at hStep
          refine hRest heap1 store1 s1 ws1 (p.blocks store1 ws1 (env.get x))
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
            hRest heap store s ws1 [] (Step.refl hAt _) (Frame.refl base s) hVars
              (by rw [hmd]; exact hR1) (fun _ _ _ q hq => by rw [hmd] at hq; exact nomatch hq)
              (fun q hq => by rw [hmd] at hq; exact nomatch hq)
              fun r hr c hc => by
                rw [hmd] at hc
                exact hReads1 r (hr.mono fun k h => by
                  rw [Bool.and_eq_true]; exact ⟨by simpa using hp, h⟩) c hc

/-- A call: the arguments, the callee, whose theorem `Calls` gives, and the release of the owned
variables that the arguments use and that die at the call, other than those that the call
consumes. -/
theorem spec_call (hm : Runtime m) (hCalls : Calls m funs) {sig : Sig} {Γ' : List Ty}
    (g : FVar S sig) (args : (i : Fin sig.params.length) → Expr S Γ' (sig.params.get i))
    (argsSpec : ∀ i env slots live, CodeSpec m funs host (args i) env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.call g args) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
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
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  refine args_spec hm (all := fun i => live i || argsAny fun j => (args j).uses i)
    (kept := fun i => (live i || argsAny fun j => (args j).uses i) &&
      !(argsAny fun j => callMoves slots live args j && (args j).uses i)) sig.mode args argsSpec
    (fun i k h => by
      simp only [Bool.or_eq_true]
      exact Or.inr (le_argsAny (fun j => (args j).uses k) i h))
    (fun k h => by simp only [Bool.and_eq_true] at h; exact h.1)
    (fun i hmo => ?_) hPlace1 (fun i hmo => ?_) hPlace2 heap store s hh hVars hAt hCap hBase hRoom'
    _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts]; exact call_trap_args _ _ _ _ h)
    fun heap1 store1 s1 ws1 F hStep1 hF1 hH1 hRep1 hSep1 hX1 hY1 => ?_
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
  -- The callee, from the arguments' state.
  obtain ⟨hImpl, fn, hfn, hnum⟩ := hCalls g
  have hRun := (hImpl host store1 heap1 ws1 (Env.ofFn fun i => (args i).denote funs env)
    hStep1.at_ trivial hRep1 hSep1 (by rw [hStep1.cap m]; exact hCap)).append_args
    (by simp [hm.imports]) (by simpa [hm.imports] using hfn) (by simp [hRep1.length, hnum])
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
  refine After.release hm (s1 := s1) (live := live)
    (sel := fun i => ((live i || argsAny fun j => (args j).uses i) &&
      !(argsAny fun j => callMoves slots live args j && (args j).uses i)) && !live i) hVars aCall
    hKeptAll (fun i h => by simp only [Bool.and_eq_true] at h ⊢; exact h.1) (fun i h => ?_)
    fun heap2 store2 a2 => ?_
  · have hk : (argsAny fun j => callMoves slots live args j && (args j).uses i) = false := by
      cases hm' : argsAny fun j => callMoves slots live args j && (args j).uses i with
      | false => rfl
      | true =>
        obtain ⟨_, _, _, _, _, _, hl, _⟩ := hMoved i hm'
        rw [hl] at h
        exact nomatch h
    simp [h, hk]
  · simpa using hNext heap2 store2 s1 out.reverse a2

/-- A pair: the code of each component, each followed by its coercion to the pair's mode. -/
theorem spec_pair (hm : Runtime m) {Γ' : List Ty} {sTy tTy : Ty} {first : Expr S Γ' sTy}
    {second : Expr S Γ' tTy}
    (firstSpec : ∀ env slots live, CodeSpec m funs host first env slots live)
    (secondSpec : ∀ env slots live, CodeSpec m funs host second env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.pair first second) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
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
  refine firstSpec env slots (fun i => live i || second.uses i) h base heap store s hh hVarsL hAt
    hCap hBase (by omega) hPlace.1 _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
    fun heap1 store1 s1 ws1 a1 => ?_
  refine After.coerce hm a1 (fun h => by simp [Mode.join, h]) le_rfl
    (by rw [a1.frame.params]; exact hBase) (a1.frame.half.trans hh) (by omega)
    (by rw [a1.step.cap m]; exact hCap) (fun _ ht _ => hOwnedTrap ht)
    fun heap1 store1 s1 ws1 a1 => ?_
  refine secondSpec env slots live h base heap1 store1
    { s1 with values := ws1.reverse ++ s.values } (a1.frame.half.trans hh)
    (a1.holds.agree Frame.ofValues) a1.step.at_ (by rw [a1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base; rw [a1.frame.params]; exact hBase) (by omega) hPlace.2 _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts]; exact trap_right _ _ _ h)
    fun heap2 store2 s2 ws2 a2 => ?_
  refine After.coerce hm a2 (fun h => by
      simp only [Mode.join, h]; cases first.mode (slots.map Slot.mode) <;> rfl) le_rfl
    (by rw [a2.frame.params, a1.frame.params]; exact hBase)
    (a2.frame.half.trans (a1.frame.half.trans hh)) (by omega)
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
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
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
    (base + sTy.width + tTy.width) heap store s hh ((hVars.mono (by omega)).live_mono hV) hAt hCap
    (by omega) (by omega) hPlace.1
    _ _ (hTrap.of_imp fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
    fun heap1 store1 s1 ws a1 => ?_
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
  refine bodySpec _ _ (shift 2 live) h (base + sTy.width + tTy.width) heap2 store2
    { s3 with values := s.values } (f3.half.trans hh1) e2'.holds e2'.step.at_
    (by rw [e2'.step.cap m, a1.step.cap m]; exact hCap)
    (by show s3.params.length ≤ base + sTy.width + tTy.width; rw [hp3]; omega)
    (by omega) hPlace.2 _ _
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

/-- The release of an array variable that a reader reads, when it is owned and dies there. -/
theorem read_release (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {live : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    {vals : List Value} {rest : Program} {Q : Assertion Unit} {e : Elem} (x : Var Γ (.array e))
    (hVars : Holds env slots (fun k => live k || k == x.index) base heap store s)
    (hAt : heap.At store)
    (hNext : ∀ heap' store', Evolves env slots (fun k => live k || k == x.index) live base heap
      store s heap' store' s → wp m rest Q store' { s with values := vals } host) :
    wp m ((if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
        releaseCode (.array e) (slots.getD x.index default).loc else []) ++ rest) Q store
      { s with values := vals } host := by
  have hCode : (if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
      releaseCode (.array e) (slots.getD x.index default).loc else []) =
      (if live x.index = false then [x.index] else []).flatMap (releaseVar Γ slots) := by
    cases live x.index <;> simp [releaseVar, x.getElem?_index]
  rw [hCode]
  refine wp_releaseVars hm _ (by split <;> simp) (hVars.agree Frame.ofValues) hAt
    (by split <;> simp) fun heap' store' e => hNext heap' store' ?_
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
theorem spec_size (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e)) :
    ∀ env slots live, CodeSpec m funs host (Expr.size (S := S) x) env slots live := by
  intro env slots live h base heap store s hh hVars hAt _ _ _ _ rest Q _ hNext
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
  refine read_release hm x hVars hAt fun heap' store' ev => ?_
  exact hNext heap' store' s [.i64 (env.get x).size.toUInt64]
    (After.ofScalar rfl ev.step rfl ev.frame ev.holds rfl)

/-- A read of an array variable: the position in local `base`, a comparison of it with the
array's size as a flag in local `base + 1`, the position of the element's first word in local
`base`, the loads of its words under the flag, and the release of the variable when it is owned and
dies there. -/
theorem spec_get (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {i : Expr S Γ' .word}
    (iSpec : ∀ env slots live, CodeSpec m funs host i env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.get x i) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hi : i.width ≤ max i.width 2 := Nat.le_max_left ..
  have h2 : 2 ≤ max i.width 2 := Nat.le_max_right ..
  simp only [Expr.placeArgs] at hPlace
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  have hIn : ∀ k, ((live k || k == x.index) || i.uses k) = true →
      (live k || (Expr.get x i).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact live_assoc _ _ _ h
  refine iSpec env slots (fun k => live k || k == x.index) h base heap store s hh
    (hVars.live_mono hIn) hAt hCap hBase (by omega) hPlace _ _
    (hTrap.of_imp fun h => by simpa [Expr.aborts] using h) fun heap1 store1 s1 ws1 a1 => ?_
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
    refine read_release hm x hVars1 e1.step.at_ fun heap2 store2 e2 => ?_
    have e12 := Evolves.trans (hVars.live_mono hIn) ⟨e1.step, hFrame, hVars1⟩ e2
      (fun k h => by simp [h]) fun k h => by simp [h]
    exact hNext heap2 store2 s1c (e.values (env.get x)[(i.denote funs env).toNat]!)
      ((After.ofScalar (t := .elem e) (mode := .borrowed) rfl e12.step rfl e12.frame e12.holds
        rfl).liveIn hIn)

/-- A tuple of two elements: the code of each, in order. -/
theorem spec_mk {Γ : List Ty} {a b : Elem} {first : Expr S Γ (.elem a)}
    {second : Expr S Γ (.elem b)}
    (firstSpec : ∀ env slots live, CodeSpec m funs host first env slots live)
    (secondSpec : ∀ env slots live, CodeSpec m funs host second env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.mk first second) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : first.width ≤ max first.width second.width := Nat.le_max_left ..
  have hR : second.width ≤ max first.width second.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_spec firstSpec secondSpec env slots live h base heap store s hh hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts, Bool.or_eq_true] at h ⊢; tauto)
    (hTrap.of_imp fun h => by simp only [Expr.aborts, Bool.or_eq_true] at h ⊢; tauto)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ => ?_
  have hR1' : ws1 = a.values (first.denote funs env) := hR1
  have hR2' : ws2 = b.values (second.denote funs env) := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext heap2 store2 s2
    (a.values (first.denote funs env) ++ b.values (second.denote funs env))
    (After.ofScalar rfl hStep' rfl hF hH rfl)
  simpa [List.reverse_append, List.append_assoc] using hv

/-- A component of a tuple variable: the loads of the words that hold it. -/
theorem spec_proj {Γ' : List Ty} {e e' : Elem} (x : Var Γ' (.elem e)) (p : Path e e') :
    ∀ env slots live, CodeSpec m funs host (Expr.proj (S := S) x p) env slots live := by
  intro env slots live h base heap store s hh hVars hAt _ _ _ _ rest Q _ hNext
  obtain ⟨-, ws, hold, hRep⟩ := hVars.1 _ x (by simp [Expr.uses])
  have hRep' : ws = e.values (env.get x) := hRep
  subst hRep'
  simp only [Expr.code]
  exact wp_loadCode _ (by rw [e'.values_length, e'.types_length]) hh (p.holds hold)
    (hNext heap store s _ (After.refl hAt hVars (by intro i h; simp [Expr.uses, h]) rfl rfl
      (Holds.Apart.ofScalar rfl)))

/-- A value apart from the live variables in its mode is apart from them read borrowed. -/
theorem Holds.Apart.borrow {Γ : List Ty} {env : Env Γ} {slots : List Slot} {live : Nat → Bool}
    {heap : Heap} {store : Store Unit} {s : Locals} {t : Ty} {mode : Mode} {ws : List Value}
    {v : t.denote} (h : Holds.Apart env slots live store s t mode ws v)
    (hRep : t.Rep mode heap store ws v) : Holds.Apart env slots live store s t .borrowed ws v := by
  intro u y hy hm wy hwy hly b hb c hc
  have hyo : (slots.getD y.index default).mode = .owned := hm.resolve_left nofun
  exact regionsDisjoint_symm (hRep.reads_apart c
    (fun b' hb' => regionsDisjoint_symm (h u y hy (Or.inr hyo) wy hwy hly b' hb' c hc)) b hb)

/-- A test of a value: the facts of the value's code, then the facts of a test's code in the
context with the value as variable 0, in which no variable dies, give the facts of the value's
code at the test's heap and locals. -/
theorem After.test {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L LC LC' : Nat → Bool}
    {base base' : Nat} {heap heap1 heap2 : Heap} {store store1 store2 : Store Unit}
    {s s1 s2 : Locals} {t u : Ty} {mode m2 : Mode} {sl : Slot} {v : t.denote} {c : u.denote}
    {ws wc : List Value}
    (a1 : After env slots L0 L base heap store s t mode v heap1 store1 s1 ws)
    (aC : After (Env.cons v env) (sl :: slots) LC LC' base' heap1 store1 s1 u m2 c heap2 store2
      s2 wc)
    (hBase : base ≤ base') (hLC : ∀ i, LC i = true → LC' i = true) (hScalar : u.scalar = true) :
    After env slots L0 L base heap store s t mode v heap2 store2 s2 ws := by
  have hKeep : ∀ r, Holds.KeepDying (Env.cons v env) (sl :: slots) LC LC' store1 s1 r :=
    fun r t' x hx hxo => by rw [hLC _ hx] at hxo; exact nomatch hxo
  obtain ⟨hRep, hSame, -⟩ := a1.rep.step aC.step fun r _ => hKeep r
  have hStep := a1.step.transBoth (keep := Holds.KeepDying env slots L0 L store s) aC.step
    fun r hr => ⟨hr, fun _ => hKeep r⟩
  rw [Mode.fresh_scalar hScalar, List.append_nil, ← Mode.fresh_congr hSame] at hStep
  have hF : Frame base s1 s2 := aC.frame.mono hBase
  exact ⟨hStep, a1.frame.trans hF,
    (a1.holds.step aC.step fun _ _ _ _ _ _ c _ => hKeep c).frame hF le_rfl, hRep,
    a1.apart.transfer a1.holds aC.step hF (fun _ _ _ _ _ _ c _ => hKeep c) hSame⟩

/-- `LeanExe.loop` with a condition: the count in local `base`, the initial state, coerced to the
loop's mode, from local `base + 2` on, and the index in local `base + 1`.  The invariant at the top
of the WebAssembly `loop` holds the count, the index `i`, and the state after `i` passes, with the
facts of `After` for the outer variables live in the loop, those live after it or used by the
condition or the body.  Each pass leaves at the count, then runs the condition with the state as a
borrowed variable, in which no variable dies, so `After.test` keeps the invariant at its heap.  A
false condition leaves with the state, which `loopState_stop` shows is the loop's value.
Otherwise the pass releases a state that the body does not use, runs the body, coerces its value
to the loop's mode, and stores it as the next state.  After the loop the outer variables that only
the condition or the body uses are released. -/
theorem spec_loop (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} {count : Expr S Γ' .word}
    {init : Expr S Γ' tTy} {cond : Expr S (tTy :: Γ') .bool}
    {body : Expr S (tTy :: .word :: Γ') tTy}
    (countSpec : ∀ env slots live, CodeSpec m funs host count env slots live)
    (initSpec : ∀ env slots live, CodeSpec m funs host init env slots live)
    (condSpec : ∀ env slots live, CodeSpec m funs host cond env slots live)
    (bodySpec : ∀ env slots live, CodeSpec m funs host body env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.loop count init cond body) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hc := Nat.le_max_left count.width (max (1 + max init.width (copyWidth tTy))
    (2 + tTy.width + max (max cond.width body.width) (copyWidth tTy)))
  have hi := (Nat.le_max_left (1 + max init.width (copyWidth tTy))
    (2 + tTy.width + max (max cond.width body.width) (copyWidth tTy))).trans
    (Nat.le_max_right count.width _)
  have hb := (Nat.le_max_right (1 + max init.width (copyWidth tTy))
    (2 + tTy.width + max (max cond.width body.width) (copyWidth tTy))).trans
    (Nat.le_max_right count.width _)
  have hi1 := Nat.le_max_left init.width (copyWidth tTy)
  have hi2 := Nat.le_max_right init.width (copyWidth tTy)
  have hb1 := Nat.le_max_left (max cond.width body.width) (copyWidth tTy)
  have hb2 := Nat.le_max_right (max cond.width body.width) (copyWidth tTy)
  have hcd := Nat.le_max_left cond.width body.width
  have hbd := Nat.le_max_right cond.width body.width
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  obtain ⟨⟨⟨hPc, hPi⟩, hPcd⟩, hPb⟩ := hPlace
  have hOwnedTrap : (Expr.loop count init cond body).mode (slots.map Slot.mode) = .owned →
      TrapOK true Q := fun ht => hTrap.of_imp fun _ => by
    have := (Expr.loop count init cond body).mode_owned (slots.map Slot.mode) ht
    rw [Slot.any_map] at this
    exact this
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The count, in local `base`.
  have hCountIn : ∀ i, ((live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) ||
      count.uses i) = true → (live i || (Expr.loop count init cond body).uses i) = true :=
    fun i h => by simp only [Expr.uses]; exact loop_live_count _ _ _ _ _ h
  refine countSpec env slots
    (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) h base heap
    store s hh (hVars.live_mono hCountIn) hAt hCap hBase (by omega) hPc _ _
    (hTrap.of_imp fun h => by simp only [Expr.aborts]; exact loop_trap_count _ _ _ _ _ h)
    fun heap1 store1 s1 ws1 a1 => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  have e1 := a1.toEvolves rfl
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.half = h := e1.frame.half.trans hh
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; exact hBase
  have hHigh1 : base < s1.half := by rw [hh1]; omega
  refine wp_localSet_local hLow1 (Locals.lt_total hHigh1) ?_
  have f2 : Frame base s1
      (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) :=
    Frame.setValues hLow1 le_rfl hHigh1
  have hF2 : Frame base s
      (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) :=
    e1.frame.trans f2
  have hN2 : (setLocal { s1 with values := s.values } base
      (.i64 (count.denote funs env))).get base = some (.i64 (count.denote funs env)) :=
    Locals.get_setLocal_same hLow1 (Locals.lt_total hHigh1)
  have e1' : Evolves env slots
      (fun i => (live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) || count.uses i)
      (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) base heap store s
      heap1 store1
      (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) :=
    Evolves.mk e1.step hF2 (e1.holds.agree f2)
  -- The initial state, coerced to the loop's mode, in the locals from `base + 2` on.
  refine initSpec env slots (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) h
    (base + 1) heap1 store1 _ (hF2.half.trans hh) (e1'.holds.mono (Nat.le_succ base))
    e1'.step.at_ (by rw [e1'.step.cap m]; exact hCap) (by rw [hF2.params]; omega) (by omega) hPi
    _ _ (hTrap.of_imp fun h => by simp only [Expr.aborts]; exact loop_trap_init _ _ _ _ _ h)
    fun heap2 store2 s3 ws0 a2 => ?_
  refine After.coerce hm a2 (fun h => by simp [Mode.join, h]) le_rfl
    (by rw [a2.frame.params, hF2.params]; omega) (a2.frame.half.trans (hF2.half.trans hh))
    (by omega) (by rw [a2.step.cap m, e1'.step.cap m]; exact hCap) (fun _ ht _ => hOwnedTrap ht)
    fun heap2 store2 s3 ws0 a2 => ?_
  have hF3 : Frame base s s3 := hF2.trans (a2.frame.mono (Nat.le_succ base))
  have hh3 : s3.half = h := hF3.half.trans hh
  have hN3 : s3.get base = some (.i64 (count.denote funs env)) :=
    (a2.frame.below base (by omega)).1.trans hN2
  have a0 := (After.prepend (hVars.live_mono hCountIn) e1'
    (a2.lower e1'.holds (Nat.le_succ base) fun i h => by simp [h]) (fun i h => by simp [h])
    fun i h => by simp [h]).liveIn hCountIn
  refine wp_storeCode ws0 h (base + 2) tTy.types s3 s.values a0.rep.typed hh3
    (by rw [hF3.params]; omega) (by rw [Ty.types_length, hh3]; omega)
    fun s4 hF4 hold4 _ => ?_
  -- The index, in local `base + 1`.
  simp only [wp_constI64_cons]
  have hh4 : s4.half = h := hF4.half.trans hh3
  have hLow4 : ({ s4 with values := s.values } : Locals).params.length ≤ base + 1 := by
    show s4.params.length ≤ base + 1; rw [hF4.params, hF3.params]; omega
  have hHigh4 : base + 1 < s4.half := by rw [hh4]; omega
  refine wp_localSet_local (s := s4) (vs := s.values) hLow4 (Locals.lt_total hHigh4) ?_
  have f5 : Frame (base + 1) s4 (setLocal { s4 with values := s.values } (base + 1) (.i64 0)) :=
    Frame.setValues hLow4 le_rfl hHigh4
  have hF5 : Frame base s3 (setLocal { s4 with values := s.values } (base + 1) (.i64 0)) :=
    (hF4.mono (base := base) (by omega)).trans (f5.mono (base := base) (by omega))
  have hN5 : (setLocal { s4 with values := s.values } (base + 1) (.i64 0)).get base =
      some (.i64 (count.denote funs env)) := by
    rw [(((hF4.mono (base := base + 1) (by omega)).trans f5).below base (by omega)).1]
    exact hN3
  have hI5 : (setLocal { s4 with values := s.values } (base + 1) (.i64 0)).get (base + 1) =
      some (.i64 0) :=
    Locals.get_setLocal_same hLow4 (Locals.lt_total hHigh4)
  have hold5 : LocalsHold (setLocal { s4 with values := s.values } (base + 1) (.i64 0))
      (base + 2) tTy.types ws0 :=
    hold4.keep (lo := base + 2) (by simp)
      (fun j hj _ => ⟨by rw [Locals.get_setLocal_ne hLow4 (by omega)]; rfl,
        by rw [Locals.get_setLocal_ne hLow4 (by omega)]; rfl⟩) le_rfl
      (by rw [a0.rep.length, hh4]; omega)
  -- The exit at either test: the release of the outer variables that only the loop uses, and the
  -- load of the state.
  have hExit : ∀ heapX stX sX wsX (vals : List Value), vals = s.values →
      LocalsHold sX (base + 2) tTy.types wsX →
      After env slots (fun i => live i || (Expr.loop count init cond body).uses i)
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) base heap store s tTy
        ((init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)))
        ((Expr.loop count init cond body).denote funs env) heapX stX sX wsX →
      wp m (releaseWhere Γ' slots (fun i => (cond.uses (i + 1) || body.uses (i + 2)) && !live i) ++
        (loadCode h (base + 2) tTy.types ++ rest)) Q stX { sX with values := vals } host := by
    intro heapX stX sX wsX vals hv holdX aX
    subst hv
    refine After.release hm (live := live)
      (sel := fun i => (cond.uses (i + 1) || body.uses (i + 2)) && !live i) hVars aX
      (fun i h => by simp only [Expr.uses]; exact loop_live_state _ _ _ _ _ h)
      (fun i h => by simp only [Bool.and_eq_true] at h; exact loop_sel _ _ _ h.1)
      (fun i h => by simp [h]) fun heap' store' a' => ?_
    refine wp_loadCode wsX a'.rep.typed (aX.frame.half.trans hh) holdX ?_
    exact hNext heap' store' sX wsX a'
  -- The loop.  The invariant holds the count, the index `i`, and the state after `i` passes, and
  -- the count less the index decreases.
  refine wp_block_cons ?_
  refine wp_loop_cons
    (fun st si => ∃ heapI wsI, ∃ i : UInt64, i ≤ count.denote funs env ∧
      si.get base = some (.i64 (count.denote funs env)) ∧ si.get (base + 1) = some (.i64 i) ∧
      LocalsHold si (base + 2) tTy.types wsI ∧
      After env slots (fun i => live i || (Expr.loop count init cond body).uses i)
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) base heap store s tTy
        ((init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)))
        (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) heapI st si wsI)
    (fun _ s' => match s'.get (base + 1) with
      | some (.i64 i) => (count.denote funs env).toNat - i.toNat
      | _ => 0)
    ⟨heap2, ws0, 0, UInt64.zero_le, hN5, hI5, hold5, a0.reframe hF5⟩ ?_
  rintro st si ⟨heapI, wsI, i, hiN, hNi, hii, holdi, aI⟩
  simp only [wp_localGet_cons, Locals.get_values, hii, hNi, wp_geUI64_cons, wp_br_if_cons]
  by_cases hge : count.denote funs env ≤ i
  · -- The index reached the count.
    simp (config := { decide := true }) only [ge_iff_le, hge, ↓reduceIte, List.take_zero,
      List.drop_zero, List.nil_append]
    rw [UInt64.le_antisymm hiN hge, loopState_eq] at aI
    exact hExit _ _ _ _ _ rfl holdi aI
  -- One more pass, if the condition holds.
  have hlt : i < count.denote funs env := UInt64.not_le.mp hge
  have hsucc : (i + 1).toNat = i.toNat + 1 := by
    have := UInt64.lt_iff_toNat_lt.mp hlt
    have := (count.denote funs env).toNat_lt
    rw [UInt64.toNat_add]; simp; omega
  simp (config := { decide := true }) only [ge_iff_le, hge, ↓reduceIte]
  have hhi : si.half = h := aI.frame.half.trans hh
  -- The condition's context: the state, borrowed, as variable 0.
  have hdAll : ∀ j, cond.uses (j + 1) = true →
      (live j || cond.uses (j + 1) || body.uses (j + 2)) = true := fun j h => by simp [h]
  have hVarsC : Holds (Env.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
          body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) env)
      (⟨base + 2, .borrowed⟩ :: slots)
      (fun j => (j == 0 ||
        shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j) || cond.uses j)
      (base + 2 + tTy.width) heapI st si :=
    Holds.push ((aI.holds.mono (by omega)).live_mono fun j hj => cond_live_outer _ _ hdAll j hj)
      holdi aI.rep.borrow
      ((aI.apart.borrow aI.rep).live_mono fun j hj => cond_live_outer _ _ hdAll j hj)
  refine condSpec _ (⟨base + 2, .borrowed⟩ :: slots)
    (fun j => j == 0 || shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j) h
    (base + 2 + tTy.width) heapI st si hhi hVarsC aI.step.at_ (by rw [aI.step.cap m]; exact hCap)
    (by rw [aI.frame.params]; omega) (by omega) hPcd _ _
    ((hTrap.of_imp fun h => by
      have h' : (cond.aborts || slots.any (·.mode == .owned)) = true := by
        simpa [List.any_cons] using h
      simp only [Expr.aborts]; exact loop_trap_cond _ _ _ _ _ h').imp fun _ h => h)
    fun heapC stC sC wsC aC => ?_
  have hRC := aC.rep
  simp only [Ty.rep_bool] at hRC
  subst hRC
  have aI2 := After.test aI aC (by omega) (cond_live _ _ hdAll) rfl
  have hiiC : sC.get (base + 1) = some (.i64 i) :=
    (aC.frame.below (base + 1) (by omega)).1.trans hii
  have hNiC : sC.get base = some (.i64 (count.denote funs env)) :=
    (aC.frame.below base (by omega)).1.trans hNi
  have holdC : LocalsHold sC (base + 2) tTy.types wsI :=
    (LocalsHold.frame aC.frame (by rw [aI.rep.length, Ty.types_length])
      (by rw [Ty.types_length])).mpr holdi
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_eqzI64_cons, wp_br_if_cons]
  cases hcv : cond.denote funs (Env.cons (loopState (init.denote funs env)
      (fun i acc => bif cond.denote funs (.cons acc env) then
        body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) env)
  · -- The condition fails: the state stays for the remaining passes.
    simp (config := { decide := true }) only [↓reduceIte, List.take_zero, List.drop_zero,
      List.nil_append]
    have hStop := loopState_stop (init.denote funs env)
      (fun acc => cond.denote funs (.cons acc env))
      (fun i acc => body.denote funs (.cons acc (.cons i env))) hcv _
      (UInt64.le_iff_toNat_le.mp hiN)
    rw [← hStop, loopState_eq] at aI2
    exact hExit _ _ _ _ _ rfl holdC aI2
  simp (config := { decide := true }) only [↓reduceIte]
  -- The condition holds: the pass runs the body.
  set sB : Locals := { sC with values := si.values }
  have aB0 := aI2.reframe (Frame.ofValues (s := sC) (values := si.values))
  have holdB : LocalsHold sB (base + 2) tTy.types wsI := holdC
  have hiiB : sB.get (base + 1) = some (.i64 i) := hiiC
  have hNiB : sB.get base = some (.i64 (count.denote funs env)) := hNiC
  have holdIdx : LocalsHold sB (base + 1) Ty.word.types [.i64 i] := fun k hk => by
    obtain rfl : k = 0 := by simpa using hk
    simpa [Ty.types, slotIndex] using hiiB
  have hhB : sB.half = h := aB0.frame.half.trans hh
  have hRoomi : base + 2 + tTy.width + max body.width (copyWidth tTy) ≤ h := by omega
  -- The body's context: the state as variable 0 and the index as variable 1.
  have hIdx := Holds.push (t := .word) (v := i) (mode := .borrowed)
    (live' := fun j => decide (j + 1 < 2) ||
      shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) (j + 1) ||
        body.uses (j + 1))
    ((aB0.holds.mono (Nat.le_add_right base 1)).live_mono fun j h => by simpa using h) holdIdx
    rfl
    (Holds.Apart.ofScalar rfl)
  have hVarsB : Holds (Env.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat)
        (Env.cons (t := .word) i env))
      (⟨base + 2, (init.mode (slots.map Slot.mode)).join
        (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))⟩ ::
        ⟨base + 1, .borrowed⟩ :: slots)
      (fun j => decide (j < 2) ||
        shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j || body.uses j)
      (base + 2 + tTy.width) heapC stC sB :=
    Holds.push (hIdx.mono (base' := base + 2) (by simp [Ty.width])) holdB aB0.rep
      (Holds.Apart.push (u := .word) (v := i) (mv := .borrowed)
        (live' := fun j => decide (j + 1 < 2) ||
          shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) (j + 1) ||
            body.uses (j + 1))
        (aB0.apart.live_mono fun j h => by simpa using h) holdIdx rfl
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
  refine wp_releaseVars hm _ (by split <;> simp) hVarsB aB0.step.at_ (by split <;> simp)
    fun heap2 store2 e2 => ?_
  have e2' := e2.mono
    (live' := fun j =>
      shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j || body.uses j)
    fun j h => by
      match j with
      | 0 =>
        have h0 : body.uses 0 = true := by simpa [shift] using h
        simp [h0]
      | 1 => simp
      | k + 2 => split <;> simpa using h
  refine bodySpec _ _ (shift 2 fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) h
    (base + 2 + tTy.width) heap2 store2 sB hhB e2'.holds e2'.step.at_
    (by rw [e2'.step.cap m, aB0.step.cap m]; exact hCap) (by rw [aB0.frame.params]; omega)
    (by omega) hPb _ _
    ((hTrap.of_imp fun h => by
      have hmo := (Expr.loop count init cond body).mode_owned (slots.map Slot.mode)
      rw [Slot.any_map] at hmo
      simp only [List.any_cons, Expr.aborts] at h ⊢
      exact loop_trap_body _ _ _ _ _ _ _ (fun hv => hmo (beq_iff_eq.mp hv)) rfl h).imp
        fun _ h => h)
    fun heap6 store6 s6 ws6 aB => ?_
  have hp6 : s6.params = s.params := aB.frame.params.trans aB0.frame.params
  refine After.coerce hm aB
    (fun h => loop_mode (f := fun md => body.mode (md :: .borrowed :: slots.map Slot.mode)) h)
    le_rfl (by rw [hp6]; omega) (aB.frame.half.trans hhB) (by omega)
    (by rw [aB.step.cap m, e2'.step.cap m, aB0.step.cap m]; exact hCap)
    (fun _ ht _ => (hOwnedTrap ht).imp fun _ h => h) fun heap6 store6 s6 ws6 aB => ?_
  have hp6 : s6.params = s.params := aB.frame.params.trans aB0.frame.params
  have hh6 : s6.half = h := aB.frame.half.trans hhB
  refine wp_storeCode ws6 h (base + 2) tTy.types s6 si.values aB.rep.typed hh6
    (by rw [hp6]; omega) (by rw [Ty.types_length, hh6]; omega) fun s7 hF7 hold7 _ => ?_
  have hp7' : s7.params = s.params := hF7.params.trans hp6
  have hh7 : s7.half = h := hF7.half.trans hh6
  have hget7 : ∀ j < base + 2, s7.get j = sB.get j := fun j hj => by
    rw [(hF7.below j hj).1]
    exact (aB.frame.below j (by omega)).1
  -- The next index, in local `base + 1`.
  simp only [wp_localGet_cons, Locals.get_values, hget7 (base + 1) (by omega), hiiB,
    wp_constI64_cons, wp_addI64_cons]
  have hLow7 : ({ s7 with values := si.values } : Locals).params.length ≤ base + 1 := by
    show s7.params.length ≤ base + 1; rw [hp7']; omega
  have hHigh7 : base + 1 < s7.half := by rw [hh7]; omega
  refine wp_localSet_local (s := s7) (vs := si.values) hLow7 (Locals.lt_total hHigh7) ?_
  have hget8 : (setLocal { s7 with values := si.values } (base + 1) (.i64 (i + 1))).get
      (base + 1) = some (.i64 (i + 1)) :=
    Locals.get_setLocal_same hLow7 (Locals.lt_total hHigh7)
  have hold8 : LocalsHold (setLocal { s7 with values := si.values } (base + 1)
      (.i64 (i + 1))) (base + 2) tTy.types ws6 :=
    hold7.keep (lo := base + 2) (by simp)
      (fun j hj _ => ⟨by rw [Locals.get_setLocal_ne hLow7 (by omega)]; rfl,
        by rw [Locals.get_setLocal_ne hLow7 (by omega)]; rfl⟩) le_rfl
      (by rw [aB.rep.length, hh7]; omega)
  -- The state after `i + 1` iterations: the facts of the body's code for the outer context.
  have aB' := After.prepend hVarsB e2' aB (fun j h => live_right _ _ _ h) fun j h => by
    simp [h]
  have hNew : ∀ r, (∀ b ∈ ((init.mode (slots.map Slot.mode)).join
        (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))).fresh stC tTy wsI
        (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat),
        regionsDisjoint r b) →
      ((init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)) = .owned → ∀ w,
        LocalsHold sB (base + 2) tTy.types w → w.length = tTy.width →
        ∀ b ∈ tTy.blocks stC w (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat),
        regionsDisjoint r b) ∧
      (Mode.borrowed = .owned → ∀ w, LocalsHold sB (base + 1) Ty.word.types w →
        w.length = Ty.word.width →
        ∀ b ∈ Ty.word.blocks stC w i, regionsDisjoint r b) := by
    intro r hFresh
    refine ⟨fun hmo w hw hlw b hb => ?_, fun hmo => nomatch hmo⟩
    obtain rfl := LocalsHold.unique hw holdB (hlw.trans aB0.rep.length.symm)
    rw [hmo] at hFresh
    exact hFresh b hb
  have aNext := After.bind2 hVars aB0 (Frame.refl base sB) aB' (by omega) hNew
    (fun j h => by simpa using h)
    (fun j h => by simp only [Expr.uses]; exact loop_live_state _ _ _ _ _ h) fun _ h => h
  have hv : loopState (init.denote funs env)
      (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) (i + 1).toNat =
      body.denote funs (.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) (.cons i env)) := by
    rw [hsucc, loopState, UInt64.ofNat_toNat]
    simp only [hcv, Bool.cond_true]
  rw [wp_br_cons]
  dsimp only
  refine ⟨⟨heap6, ws6, i + 1, UInt64.le_iff_toNat_le.mpr ?_, ?_, hget8, hold8, ?_⟩, ?_⟩
  · have := UInt64.lt_iff_toNat_lt.mp hlt
    omega
  · rw [Locals.get_setLocal_ne hLow7 (by omega), Locals.get_values, hget7 base (by omega)]
    exact hNiB
  · rw [hv]
    exact aNext.reframe ((hF7.mono (base := base) (by omega)).trans
      ((Frame.setValues (s := s7) (vs := si.values) (base := base + 1) hLow7 le_rfl
        hHigh7).mono (base := base)
        (by omega)))
  · have := UInt64.lt_iff_toNat_lt.mp hlt
    simp only [hget8]
    omega

/-- `LeanExe.build`: the count in local `base`, a trap at `unreachable` when it is `2 ^ 29` or
more, a new owned array at the address in local `base + 1`, and the index in local `base + 2`.
The invariant at the top of the WebAssembly `loop` holds an owned array of the count's length
whose elements below the index are the built ones, with the facts of `After` for the outer
variables live in the loop.  Each iteration runs the element's code in the context with the
index, which keeps every region, and stores the element. -/
theorem spec_build (hm : Runtime m) {Γ' : List Ty} {e : Elem} {count : Expr S Γ' .word}
    {elem : Expr S (.word :: Γ') (.elem e)}
    (countSpec : ∀ env slots live, CodeSpec m funs host count env slots live)
    (elemSpec : ∀ env slots live, CodeSpec m funs host elem env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.build count elem) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hc := Nat.le_max_left count.width (3 + max elem.width (e.width + 1))
  have he := Nat.le_max_right count.width (3 + max elem.width (e.width + 1))
  have he1 := Nat.le_max_left elem.width (e.width + 1)
  have he2 := Nat.le_max_right elem.width (e.width + 1)
  have hk := e.width_pos
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  have hTrapT : TrapOK true Q := hTrap.of_imp fun _ => by simp [Expr.aborts]
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The count, in local `base`.
  have hCountIn : ∀ i, ((live i || elem.uses (i + 1)) || count.uses i) = true →
      (live i || (Expr.build count elem).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  refine countSpec env slots (fun i => live i || elem.uses (i + 1)) h base heap store s hh
    (hVars.live_mono hCountIn) hAt hCap hBase (by omega) hPlace.1 _ _
    (hTrapT.of_imp fun _ => rfl) fun heap1 store1 s1 ws1 a1 => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  have e1 := a1.toEvolves rfl
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.half = h := e1.frame.half.trans hh
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; exact hBase
  have hHigh1 : base < s1.half := by rw [hh1]; omega
  refine wp_localSet_local hLow1 (Locals.lt_total hHigh1) ?_
  set s2 := setLocal { s1 with values := s.values } base (.i64 (count.denote funs env)) with hs2
  have f2 : Frame base s1 s2 := Frame.setValues hLow1 le_rfl hHigh1
  have hN2 : s2.get base = some (.i64 (count.denote funs env)) :=
    Locals.get_setLocal_same hLow1 (Locals.lt_total hHigh1)
  have hh2 : s2.half = h := by simp only [hs2, Locals.half_setLocal, Locals.half_values, hh1]
  -- The trap when the count's words would be `2 ^ 29` or more.
  simp only [wp_localGet_cons, hN2, wp_constI64_cons, wp_geUI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  by_cases hBig : UInt64.ofNat ((536870912 + e.width - 1) / e.width) ≤ count.denote funs env
  · simp (config := { decide := true }) only [ge_iff_le, hBig, ↓reduceIte]
    rw [wp_unreachable_cons]
    exact hTrapT _
  simp (config := { decide := true }) only [ge_iff_le, hBig, ↓reduceIte]
  rw [wp_nil]
  dsimp only
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  have hLim : (536870912 + e.width - 1) / e.width < UInt64.size := by
    rw [show UInt64.size = 18446744073709551616 from rfl]
    have hd : (536870912 + e.width - 1) / e.width ≤ 536870912 :=
      Nat.div_le_of_le_mul (by omega)
    omega
  have hcLim : (count.denote funs env).toNat < (536870912 + e.width - 1) / e.width := by
    have := UInt64.not_le.mp hBig
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hLim] at this
    exact this
  have hck := build_limit hk hcLim
  have hcSmall : (count.denote funs env).toNat ≤ (count.denote funs env).toNat * e.width :=
    Nat.le_mul_of_pos_right _ hk
  -- The count of words, in local `base + 2`.
  show wp m _ Q store1 s2 host
  simp only [wp_localGet_cons, hN2]
  rw [wp_scaleCode, show count.denote funs env = UInt64.ofNat (count.denote funs env).toNat by simp,
    words_scale hk hck]
  have hLowT : ({ s2 with values := s.values } : Locals).params.length ≤ base + 2 := by
    show s1.params.length ≤ base + 2; rw [hp1]; omega
  have hHighT : base + 2 < ({ s2 with values := s.values } : Locals).half := by
    simp only [Locals.half_values, hh2]; omega
  refine wp_localSet_local hLowT (Locals.lt_total hHighT) ?_
  set s3 := setLocal { s2 with values := s.values } (base + 2)
    (.i64 (UInt64.ofNat ((count.denote funs env).toNat * e.width))) with hs3
  have hT3 : s3.get (base + 2) =
      some (.i64 (UInt64.ofNat ((count.denote funs env).toNat * e.width))) :=
    Locals.get_setLocal_same hLowT (Locals.lt_total hHighT)
  have hN3 : s3.get base = some (.i64 (count.denote funs env)) := by
    rw [Locals.get_setLocal_ne hLowT (by omega), Locals.get_values]; exact hN2
  have f3 : Frame base s2 s3 := Frame.setValues hLowT (by omega) (by simpa using hHighT)
  have hh3 : s3.half = h := by simp only [hs3, Locals.half_setLocal, Locals.half_values, hh2]
  have hp3 : s3.params = s.params := by
    simp only [hs3, hs2, setLocal]; exact hp1
  -- The new array, at the address in local `base + 1`.
  have hTn : (UInt64.ofNat ((count.denote funs env).toNat * e.width)).toNat =
      (count.denote funs env).toNat * e.width :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hLow4 : s3.params.length ≤ base + 1 := by rw [hp3]; omega
  have hHigh4' : base + 1 < s3.half := by rw [hh3]; omega
  have hHigh4 := Locals.lt_total hHigh4'
  refine wp_allocArray hm e1.step.at_ (by rw [e1.step.cap m]; exact hCap) hTrapT
    (by rw [hTn]; exact hck) hT3 hLow4 hHigh4 (by omega)
    fun heap2 store2 root words hSize hStepA hOwned => ?_
  rw [hTn] at hSize
  set s4 := setLocal { s3 with values := s3.values } (base + 1) (.i64 root) with hs4
  have f4 : Frame base s3 s4 := Frame.setValues hLow4 (by omega) hHigh4'
  have hF4 : Frame base s s4 := e1.frame.trans (f2.trans (f3.trans f4))
  have hN4 : s4.get base = some (.i64 (count.denote funs env)) := by
    rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values]; exact hN3
  have hRoot4 : s4.get (base + 1) = some (.i64 root) := Locals.get_setLocal_same hLow4 hHigh4
  have hh4 : s4.half = h := by simp only [hs4, Locals.half_setLocal, Locals.half_values, hh3]
  have hp4 : s4.params = s.params := by simp only [hs4, setLocal]; exact hp3
  -- The facts of `After` for the new array.
  have hVars1 : Holds env slots (fun i => live i || elem.uses (i + 1)) base heap1 store1 s4 :=
    e1.holds.agree (f2.trans (f3.trans f4))
  have a0 : After env slots (fun i => live i || (Expr.build count elem).uses i)
      (fun i => live i || elem.uses (i + 1)) base heap store s (.array .word) .owned words heap2
      store2 s4 [.i64 root] := by
    refine ⟨(e1.step.trans hStepA fun _ hr => ⟨hr, fun _ => trivial⟩).mono
      (fun _ hr => hr.mono fun i h1 h2 => ⟨hCountIn i h1, h2⟩) (fun _ h => h), hF4,
      hVars1.step hStepA (fun _ _ _ _ _ _ _ _ => trivial), ⟨root, rfl, hOwned⟩, ?_⟩
    intro u y hy _ wy hwy hly b hb c hc
    obtain ⟨hSame, hFresh⟩ := hVars1.regions_after hStepA hy hwy hly fun _ _ => trivial
    rw [hSame] at hc
    exact regionsDisjoint_symm (hFresh c hc b hb)
  -- The index, in local `base + 2`.
  simp only [wp_constI64_cons]
  have hLow5 : ({ s4 with values := s4.values } : Locals).params.length ≤ base + 2 := by
    show s4.params.length ≤ base + 2; rw [hp4]; omega
  have hHigh5' : base + 2 < s4.half := by rw [hh4]; omega
  have hHigh5 := Locals.lt_total (s := { s4 with values := s4.values }) hHigh5'
  refine wp_localSet_local hLow5 hHigh5 ?_
  set s5 := setLocal { s4 with values := s4.values } (base + 2) (.i64 0) with hs5
  have hF5 : Frame base s4 s5 := Frame.setValues hLow5 (by omega) hHigh5'
  have hN5 : s5.get base = some (.i64 (count.denote funs env)) := by
    rw [Locals.get_setLocal_ne hLow5 (by omega), Locals.get_values]; exact hN4
  have hRoot5 : s5.get (base + 1) = some (.i64 root) := by
    rw [Locals.get_setLocal_ne hLow5 (by omega), Locals.get_values]; exact hRoot4
  have hIdx5 : s5.get (base + 2) = some (.i64 0) := Locals.get_setLocal_same hLow5 hHigh5
  -- The loop.  The invariant holds an array of the count's elements' words whose elements below
  -- the index `i` hold the built ones, and the count less the index decreases.
  refine wp_block_cons ?_
  refine wp_loop_cons
    (fun st si => ∃ heapI words, ∃ i : Nat, i ≤ (count.denote funs env).toNat ∧
      words.size = (count.denote funs env).toNat * e.width ∧
      (∀ i', i' < i → ∀ j, j < e.width → words[i' * e.width + j]! =
        (e.toWords (elem.denote funs (.cons (UInt64.ofNat i') env)))[j]!) ∧
      si.get base = some (.i64 (count.denote funs env)) ∧
      si.get (base + 1) = some (.i64 root) ∧ si.get (base + 2) = some (.i64 (UInt64.ofNat i)) ∧
      After env slots (fun i => live i || (Expr.build count elem).uses i)
        (fun i => live i || elem.uses (i + 1)) base heap store s (.array .word) .owned words heapI
        st si [.i64 root])
    (fun _ si => match si.get (base + 2) with
      | some (.i64 i) => (count.denote funs env).toNat - i.toNat
      | _ => 0)
    ⟨heap2, words, 0, Nat.zero_le _, hSize, fun _ h => absurd h (Nat.not_lt_zero _), hN5,
      hRoot5, hIdx5, a0.reframe hF5⟩ ?_
  rintro st si ⟨heapI, words, i, hi, hSize, hPrefix, hNi, hRooti, hIdxi, aI⟩
  have hi64 : (UInt64.ofNat i).toNat = i :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  simp only [wp_localGet_cons, Locals.get_values, hIdxi, hNi, wp_geUI64_cons, wp_br_if_cons]
  by_cases hDone : count.denote funs env ≤ UInt64.ofNat i
  · -- The array is complete: the release of the outer variables that only the element reads,
    -- and the array's address.
    have hiEq : i = (count.denote funs env).toNat := by
      rw [UInt64.le_iff_toNat_le, hi64] at hDone; omega
    simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte, List.take_zero,
      List.drop_zero, List.nil_append]
    have hWords : words = e.words (LeanExe.build (count.denote funs env)
        fun i => elem.denote funs (.cons i env)) := by
      refine Elem.words_ext e (by rw [hSize]; simp [LeanExe.build]) fun i' hi' j hj => ?_
      have hi'' : i' < (count.denote funs env).toNat := by simpa [LeanExe.build] using hi'
      rw [hPrefix i' (by omega) j hj, getElem!_pos (LeanExe.build (count.denote funs env)
        fun i => elem.denote funs (.cons i env)) i' hi']
      simp [LeanExe.build]
    rw [hWords] at aI
    refine After.release hm (s1 := si) (live := live)
      (sel := fun i => elem.uses (i + 1) && !live i) hVars (After.ofWords aI)
      (fun i h => by simp only [Expr.uses]; exact live_build _ _ _ h)
      (fun i h => by simp only [Bool.and_eq_true] at h; simp [h.1]) (fun i h => by simp [h])
      fun heap' store' a' => ?_
    simp only [wp_localGet_cons, Locals.get_values, hRooti]
    simpa [setLocal, hs2] using hNext heap' store' si [.i64 root] a'
  -- One more element.
  have hLess : i < (count.denote funs env).toNat := by
    rw [UInt64.le_iff_toNat_le, hi64] at hDone; omega
  simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte]
  -- The element, in the context with the index as variable 0.
  have holdIdx : LocalsHold si (base + 2) Ty.word.types [.i64 (UInt64.ofNat i)] :=
    fun j hj => by
      obtain rfl : j = 0 := by simpa using hj
      simpa [Ty.types, slotIndex] using hIdxi
  have hhi : si.half = h := aI.frame.half.trans hh
  have hLE : ∀ j, (shift 1 (fun i => live i || elem.uses (i + 1)) (j + 1) ||
      elem.uses (j + 1)) = true → (live j || elem.uses (j + 1)) = true := fun j h => by
    simp only [shift_add] at h; exact live_dup _ _ h
  have hVarsI : Holds env slots (fun i => live i || elem.uses (i + 1)) (base + 2) heapI st si :=
    aI.holds.mono (by omega)
  have hVarsE := (Holds.push (t := .word) (v := UInt64.ofNat i) (mode := .borrowed)
    (live' := fun j => shift 1 (fun i => live i || elem.uses (i + 1)) j || elem.uses j)
    (hVarsI.live_mono hLE) holdIdx rfl (Holds.Apart.ofScalar rfl)).mono
    (base' := base + 3) (by simp [Ty.width])
  refine elemSpec _ _ (shift 1 fun i => live i || elem.uses (i + 1)) h (base + 3) heapI st si hhi
    hVarsE aI.step.at_ (by rw [aI.step.cap m]; exact hCap)
    (by show si.params.length ≤ base + 3; rw [aI.frame.params]; omega) (by omega)
    hPlace.2 _ _ ((hTrapT.of_imp fun _ => rfl).imp fun _ h => h)
    fun heapE stE sE wsE aE => ?_
  have hRE := Ty.rep_elem.mp aE.rep
  subst hRE
  -- The element's facts for the outer context, after the array's.
  have aE1 := After.bind (base := base + 2) hVarsI
    (After.refl (t := .word) (mode := .borrowed) (v := UInt64.ofNat i)
      (ws := [.i64 (UInt64.ofNat i)]) aI.step.at_ hVarsI (fun _ h => h) rfl rfl
      (Holds.Apart.ofScalar rfl))
    (Frame.refl _ _) holdIdx aE hLE (fun _ h => h) fun _ h => h
  have aE2 := aE1.lower aI.holds (by omega) fun _ h => h
  obtain ⟨hStep, hFrame, hRep1, hApart1, -⟩ := After.seq hVars aI aE2
    (fun i h => by simp only [Expr.uses]; exact live_build _ _ _ h) fun _ h => h
  have aI2 : After env slots (fun i => live i || (Expr.build count elem).uses i)
      (fun i => live i || elem.uses (i + 1)) base heap store s (.array .word) .owned words heapE
      stE sE [.i64 root] :=
    ⟨hStep.mono (fun _ h => h) fun b hb => List.mem_append_left _ hb, hFrame, aE2.holds,
      hRep1, hApart1⟩
  have hpE : sE.params = s.params := aE.frame.params.trans aI.frame.params
  have hhE : sE.half = h := aE.frame.half.trans hhi
  have hgetE : ∀ j < base + 3, sE.get j = si.get j := fun j hj => (aE.frame.below j hj).1
  -- The element's words, from local `base + 3` on.
  refine wp_storeCode (e.values (elem.denote funs (.cons (UInt64.ofNat i) env))) h (base + 3)
    e.types sE si.values (by rw [e.values_length, e.types_length]) hhE
    (by rw [hpE]; omega) (by rw [e.types_length, hhE]; omega)
    fun s6 f6 hold6 _ => ?_
  have hp6 : s6.params = s.params := f6.params.trans hpE
  have hh6 : s6.half = h := f6.half.trans hhE
  have hget6 : ∀ j < base + 3, s6.get j = si.get j := fun j hj =>
    (f6.below j hj).1.trans (hgetE j hj)
  -- The position of the element's first word, in local `base + 3 + k`.
  simp only [wp_localGet_cons, Locals.get_values, hget6 (base + 2) (by omega), hIdxi]
  rw [wp_scaleCode, words_scale hk
    (lt_of_le_of_lt (Nat.mul_le_mul_right e.width (Nat.le_of_lt hLess)) hck)]
  have hLow7 : ({ s6 with values := si.values } : Locals).params.length ≤ base + 3 + e.width := by
    show s6.params.length ≤ _; rw [hp6]; omega
  have hHigh7' : base + 3 + e.width < s6.half := by rw [hh6]; omega
  have hHigh7 := Locals.lt_total (s := { s6 with values := si.values }) hHigh7'
  refine wp_localSet_local hLow7 hHigh7 ?_
  set s7 := setLocal { s6 with values := si.values } (base + 3 + e.width)
    (.i64 (UInt64.ofNat (i * e.width))) with hs7
  have f7 : Frame (base + 3) s6 s7 := Frame.setValues hLow7 (by omega) hHigh7'
  have hW7 : s7.get (base + 3 + e.width) = some (.i64 (UInt64.ofNat (i * e.width))) :=
    Locals.get_setLocal_same hLow7 hHigh7
  have hget7 : ∀ j < base + 3, s7.get j = si.get j := fun j hj =>
    (f7.below j hj).1.trans (hget6 j hj)
  have hh7 : s7.half = h := f7.half.trans hh6
  have hold7 : LocalsHold s7 (base + 3) e.types
      (List.zipWith typedValue e.types
        (e.toWords (elem.denote funs (.cons (UInt64.ofNat i) env)))) := by
    rw [e.values_typed]
    intro j hj
    have := hold6 j hj
    rw [e.values_length] at hj
    rw [show s7.half = s6.half from f7.half]
    rw [← this]
    simp only [hs7]
    rw [Locals.get_setLocal_ne hLow7, Locals.get_values]
    cases hty : e.types.getD j .i64 <;> simp only [slotIndex] <;> omega
  -- The writes of the element's words.
  have hik : i * e.width + e.width ≤ words.size := by
    rw [hSize]; have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hLess)
    rw [Nat.succ_mul] at this; exact this
  have hik64 : (UInt64.ofNat (i * e.width)).toNat = i * e.width :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  refine wp_storeWordsCode 0 (base + 3) e.types
    (e.toWords (elem.denote funs (.cons (UInt64.ofNat i) env))) words stE s7
    (aI2.reframe ((f6.mono (by omega)).trans (f7.mono (by omega)))) hh7
    (by rw [hget7 (base + 1) (by omega)]; exact hRooti) hW7 hold7
    (by rw [e.toWords_length, e.types_length]) (by rw [hik64, e.types_length]; omega)
    fun store8 a8 => ?_
  rw [hik64, Nat.add_zero] at a8
  -- The next index, in local `base + 2`.
  simp only [wp_localGet_cons, hget7 (base + 2) (by omega), hIdxi, wp_constI64_cons,
    wp_addI64_cons]
  have hLow9 : ({ s7 with values := s7.values } : Locals).params.length ≤ base + 2 := by
    show s7.params.length ≤ base + 2; rw [f7.params, hp6]; omega
  have hHigh9' : base + 2 < s7.half := by rw [hh7]; omega
  have hHigh9 := Locals.lt_total (s := { s7 with values := s7.values }) hHigh9'
  refine wp_localSet_local (s := s7) (vs := s7.values) hLow9 hHigh9 ?_
  have hSucc : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by
    rw [UInt64.ofNat_add]; rfl
  have hSucc64 : (UInt64.ofNat (i + 1)).toNat = i + 1 :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hIdx9 := Locals.get_setLocal_same (v := .i64 (UInt64.ofNat i + 1)) hLow9 hHigh9
  rw [wp_br_cons]
  dsimp only
  have hfit : i * e.width + (e.toWords (elem.denote funs (.cons (UInt64.ofNat i) env))).length ≤
      words.size := by rw [e.toWords_length]; exact hik
  refine ⟨⟨heapE, _, i + 1, by omega, by rw [writeWords_size, hSize], fun i' hi' j hj => ?_,
    ?_, ?_, by rw [hIdx9, hSucc],
    a8.reframe (Frame.setValues hLow9 (by omega) hHigh9')⟩, ?_⟩
  · rw [writeWords_getElem! _ _ _ hfit, e.toWords_length]
    by_cases hii : i' = i
    · subst hii
      rw [if_pos (by omega), show i' * e.width + j - i' * e.width = j by omega]
    · have hlt : i' < i := by omega
      have hout : ¬(i * e.width ≤ i' * e.width + j ∧ i' * e.width + j < i * e.width + e.width) := by
        intro ⟨h1, _⟩
        have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hlt)
        rw [Nat.succ_mul] at this; omega
      rw [if_neg hout]
      exact hPrefix i' hlt j hj
  · rw [Locals.get_setLocal_ne hLow9 (by omega), Locals.get_values, hget7 base (by omega)]
    exact hNi
  · rw [Locals.get_setLocal_ne hLow9 (by omega), Locals.get_values, hget7 (base + 1) (by omega)]
    exact hRooti
  · rw [hIdx9]
    simp only [hSucc, hSucc64]
    omega

/-- `x.set! i.toNat v`: the position in local `base`, the value's words from local `base + 1` on,
the array as owned in local `base + 1 + k`, which is `x`'s own block when `x` is owned and dies,
and, when the position is below the size, the position of the element's first word in local
`base + 2 + k` and the writes of the element's words. -/
theorem spec_set (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {i : Expr S Γ' .word} {v : Expr S Γ' (.elem e)}
    (iSpec : ∀ env slots live, CodeSpec m funs host i env slots live)
    (vSpec : ∀ env slots live, CodeSpec m funs host v env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.set x i v) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hi := Nat.le_max_left i.width (max (1 + v.width) (1 + e.width + copyWidth (.array e)))
  have hv := (Nat.le_max_left (1 + v.width) (1 + e.width + copyWidth (.array e))).trans
    (Nat.le_max_right i.width _)
  have hx := (Nat.le_max_right (1 + v.width) (1 + e.width + copyWidth (.array e))).trans
    (Nat.le_max_right i.width _)
  have hcw : copyWidth (Ty.array e) = 4 := rfl
  have hk := e.width_pos
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  have hTrapT : TrapOK true Q := hTrap.of_imp fun _ => by simp [Expr.aborts]
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The position, in local `base`.
  have hIn : ∀ k, ((live k || k == x.index || v.uses k) || i.uses k) = true →
      (live k || (Expr.set x i v).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact set_live_index _ _ _ _ h
  refine iSpec env slots (fun k => live k || k == x.index || v.uses k) h base heap store s hh
    (hVars.live_mono hIn) hAt hCap hBase (by omega) hPlace.1 _ _ (hTrapT.of_imp fun _ => rfl)
    fun heap1 store1 s1 ws1 a1 => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  refine After.storeWord a1 le_rfl hBase (by rw [hh]; omega) fun e1 hI1 => ?_
  have hp1 := e1.frame.params
  have hh1 := e1.frame.half.trans hh
  -- The value's words, from local `base + 1` on.
  refine vSpec env slots (fun k => live k || k == x.index) h (base + 1) heap1 store1 _ hh1
    (e1.holds.mono (Nat.le_succ base)) e1.step.at_ (by rw [e1.step.cap m]; exact hCap)
    (by rw [hp1]; omega) (by omega) hPlace.2 _ _ (hTrapT.of_imp fun _ => rfl)
    fun heap2 store2 s2 ws2 a2 => ?_
  have hR2 := Ty.rep_elem.mp a2.rep
  subst hR2
  have e2a := a2.toEvolves rfl
  have hp2a : s2.params = s.params := e2a.frame.params.trans hp1
  have hh2a : s2.half = h := e2a.frame.half.trans hh1
  refine wp_storeCode (e.values (v.denote funs env)) h (base + 1) e.types s2 s.values
    (by rw [e.values_length, e.types_length]) hh2a (by rw [hp2a]; omega)
    (by rw [e.types_length, hh2a]; omega) fun s2' f2 hold2 _ => ?_
  have f2' : Frame (base + 1) s2 { s2' with values := s.values } := f2.trans Frame.ofValues
  have e2 : Evolves env slots (fun k => (live k || k == x.index) || v.uses k)
      (fun k => live k || k == x.index) (base + 1) heap1 store1 _ heap2 store2
      { s2' with values := s.values } :=
    ⟨e2a.step, e2a.frame.trans f2', e2a.holds.agree f2'⟩
  have hp2 : s2'.params = s.params := f2.params.trans hp2a
  have hh2 : s2'.half = h := f2.half.trans hh2a
  have hI2 : s2'.get base = some (.i64 (i.denote funs env)) :=
    (e2.frame.below base (by omega)).1.trans hI1
  -- The array as owned, in local `base + 1 + k`.
  refine spec_ownedVar hm x (s := { s2' with values := s.values }) hh2
    ((e2.holds.mono (by omega)) : Holds env slots
      (fun k => live k || k == x.index) (base + 1 + e.width) heap2 store2 _) e2.step.at_
    (by rw [e2.step.cap m, e1.step.cap m]; exact hCap)
    (by show s2'.params.length ≤ _; rw [hp2]; omega)
    (by omega) hTrapT fun heap3 store3 s3 ws3 a3 => ?_
  obtain ⟨p, hws, hOwned⟩ := a3.rep
  subst hws
  have hp3 : s3.params = s.params := a3.frame.params.trans hp2
  have hh3 : s3.half = h := a3.frame.half.trans hh2
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow3 : ({ s3 with values := s.values } : Locals).params.length ≤ base + 1 + e.width := by
    show s3.params.length ≤ _; rw [hp3]; omega
  have hHigh3' : base + 1 + e.width < s3.half := by rw [hh3]; omega
  have hHigh3 := Locals.lt_total (s := { s3 with values := s.values }) hHigh3'
  refine wp_localSet_local hLow3 hHigh3 ?_
  set s4 : Locals := setLocal { s3 with values := s.values } (base + 1 + e.width) (.i64 p)
    with hs4
  have hP4 : s4.get (base + 1 + e.width) = some (.i64 p) := Locals.get_setLocal_same hLow3 hHigh3
  have hF4 : Frame (base + 1 + e.width) s3 s4 := Frame.setValues hLow3 le_rfl hHigh3'
  have hI4 : s4.get base = some (.i64 (i.denote funs env)) :=
    (hF4.below base (by omega)).1.trans ((a3.frame.below base (by omega)).1.trans hI2)
  have hold4 : LocalsHold s4 (base + 1) e.types (e.values (v.denote funs env)) :=
    (LocalsHold.frame (Frame.ofValues.trans (a3.frame.trans hF4))
      (by rw [e.values_length, e.types_length]) (by rw [e.types_length])).mpr hold2
  have hh4 : s4.half = h := hF4.half.trans hh3
  have hp4 : s4.params = s.params := hF4.params.trans hp3
  have hValues4 : s4.values = s.values := rfl
  have a4 := a3.reframe hF4
  -- The rest of the code, from the array after the writes or without them.
  have hFinish : ∀ (store4 : Store Unit) (s' : Locals) (ws : Array UInt64),
      Frame (base + 1 + e.width) s4 s' → s'.values = s.values →
      ws = e.words ((env.get x).set! (i.denote funs env).toNat (v.denote funs env)) →
      After env slots (fun k => live k || k == x.index) live (base + 1 + e.width) heap2 store2
        { s2' with values := s.values } (.array .word) .owned ws heap3 store4 s' [.i64 p] →
      wp m rest Q store4 { s' with values := .i64 p :: s'.values } host := by
    rintro store4 s' ws _ hv' rfl aX
    have aX1 := (After.ofWords aX).lower e2.holds (by omega) fun k h => by simp [h]
    have aX2 := After.prepend (e1.holds.mono (Nat.le_succ base)) e2 aX1
      (fun k h => by simp [h]) fun k h => by simp [h]
    have aX3 := After.prepend (hVars.live_mono hIn) e1 (aX2.lower e1.holds (Nat.le_succ base)
      fun k h => by simp [h]) (fun k h => by simp [h]) fun k h => by simp [h]
    simpa [hv'] using hNext heap3 store4 _ [.i64 p] (aX3.liveIn hIn)
  have hA := hOwned.values
  have hLength := hA.lengthBound
  have hnk : (env.get x).size * e.width < 536870912 := by
    have := hA.1; rw [Elem.words_size] at this; omega
  have hn64 : (env.get x).size < UInt64.size := by
    have := Nat.le_mul_of_pos_right (env.get x).size hk
    rw [show UInt64.size = 18446744073709551616 from rfl]; omega
  show wp m _ Q store3 s4 host
  simp only [wp_localGet_cons, Locals.get_values, hI4, hP4, wp_wrapI64_cons, wp_load64_cons,
    wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead, Elem.words_size, wp_divCode hk, words_div hk hnk]
  simp only [wp_ltUI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have hLess : i.denote funs env < UInt64.ofNat (env.get x).size ↔
      (i.denote funs env).toNat < (env.get x).size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hn64]
  by_cases hc : (i.denote funs env).toNat < (env.get x).size
  · -- The writes of the element's words.
    rw [ite_eq_left (by simp [hLess.mpr hc])]
    have hik : (i.denote funs env).toNat * e.width < 536870912 :=
      lt_of_le_of_lt (Nat.mul_le_mul_right e.width (Nat.le_of_lt hc)) hnk
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, Locals.get_values, hI4]
    have hs := words_scale hk hik
    rw [UInt64.ofNat_toNat] at hs
    rw [wp_scaleCode, hs]
    have hLow5 : ({ s4 with values := s4.values } : Locals).params.length ≤
        base + 2 + e.width := by
      show s4.params.length ≤ _; rw [hp4]; omega
    have hHigh5' : base + 2 + e.width < s4.half := by rw [hh4]; omega
    have hHigh5 := Locals.lt_total (s := { s4 with values := s4.values }) hHigh5'
    refine wp_localSet_local hLow5 hHigh5 ?_
    set s5 : Locals := setLocal { s4 with values := s4.values } (base + 2 + e.width)
      (.i64 (UInt64.ofNat ((i.denote funs env).toNat * e.width))) with hs5
    have hF5 : Frame (base + 2 + e.width) s4 s5 := Frame.setValues hLow5 le_rfl hHigh5'
    have hW5 : s5.get (base + 2 + e.width) =
        some (.i64 (UInt64.ofNat ((i.denote funs env).toNat * e.width))) :=
      Locals.get_setLocal_same hLow5 hHigh5
    have hP5 : s5.get (base + 1 + e.width) = some (.i64 p) :=
      (hF5.below _ (by omega)).1.trans hP4
    have hold5 : LocalsHold s5 (base + 1) e.types
        (List.zipWith typedValue e.types (e.toWords (v.denote funs env))) := by
      rw [e.values_typed]
      exact (LocalsHold.frame hF5 (by rw [e.values_length, e.types_length])
        (by rw [e.types_length]; omega)).mpr hold4
    have hik64 : (UInt64.ofNat ((i.denote funs env).toNat * e.width)).toNat =
        (i.denote funs env).toNat * e.width :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    rw [← List.append_nil (storeWordsCode h (base + 1 + e.width) (base + 2 + e.width) 0 (base + 1)
      e.types)]
    refine wp_storeWordsCode 0 (base + 1) e.types (e.toWords (v.denote funs env))
      (e.words (env.get x)) store3 s5 (a4.toWords.reframe (hF5.mono (by omega)))
      (hF5.half.trans hh4) hP5 hW5 hold5 (by rw [e.toWords_length, e.types_length])
      (by rw [hik64, e.types_length, Elem.words_size]
          have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hc)
          rw [Nat.succ_mul] at this; omega)
      fun store6 a6 => ?_
    rw [hik64] at a6
    simp only [Nat.add_zero] at a6
    rw [Elem.words_set e hc] at a6
    rw [wp_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, wp_localGet_cons, hP5]
    exact hFinish store6 s5 _ (hF5.mono (by omega)) rfl rfl a6
  · rw [ite_eq_right (by simp [hLess, hc])]
    rw [wp_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, wp_localGet_cons, hP4]
    exact hFinish _ s4 (e.words (env.get x)) (Frame.refl _ _) rfl
      (by simp [Array.set!, Array.setIfInBounds, hc]) a4.toWords

/-- `Var.roomCode`: an owned array, at the address in local `b + 4`, whose first elements are
those of `x`, whose length is `x`'s length plus the word `e` in local `ext`, and whose block has
room for that length.  An owned `x` that dies is consumed; any other `x` is read. -/
theorem spec_room (hm : Runtime m) {Γ' : List Ty} {el : Elem} (x : Var Γ' (.array el))
    {env : Env Γ'}
    {slots : List Slot} {live : Nat → Bool} {b ext : Nat} {e : UInt64} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit}
    (hVars : Holds env slots (fun i => live i || i == x.index) b heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ b)
    (hRoom : b + 6 ≤ s.half) (hExt : s.get ext = some (.i64 e))
    (hExtB : ext < b) (he : e.toNat ≤ 536870912) (hTrap : TrapOK true Q)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (q : UInt64)
      (words : Array UInt64), words.size = (el.words (env.get x)).size + e.toNat →
      (∀ j (hj : j < (el.words (env.get x)).size), words[j]! = (el.words (env.get x))[j]) →
      After env slots (fun i => live i || i == x.index) live b heap store s (.array .word) .owned
        words heap' store' s' [.i64 q] →
      s'.get (b + 1) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size)) →
      s'.get (b + 4) = some (.i64 q) → s'.values = s.values → wp m rest Q store' s' host) :
    wp m (x.roomCode slots b live ext ++ rest) Q store s host := by
  have hTot : 2 * s.half ≤ s.params.length + s.locals.length := by
    simp only [Locals.half]; omega
  obtain ⟨hBelowX, ws, hold, hRep⟩ := hVars.get x (by simp)
  obtain ⟨p, rfl, hArr⟩ := hRep
  have hB := hArr.borrow
  have hA := hB.values
  have hLenB := hA.lengthBound
  have hFitA := hA.1
  have hn : (el.words (env.get x)).size < 536870912 := by omega
  have hN : (UInt64.ofNat (el.words (env.get x)).size).toNat = (el.words (env.get x)).size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hP : s.get (slots.getD x.index default).loc = some (.i64 p) := by
    exact LocalsHold.word hold
  simp only [Var.roomCode, List.append_assoc, List.cons_append, List.nil_append]
  -- The address, in local `b`.
  simp only [wp_localGet_cons, hP]
  refine wp_localSet_local hBase (by omega) ?_
  have hLow0 : ({ s with values := s.values } : Locals).params.length ≤ b := hBase
  let s1 := setLocal { s with values := s.values } b (.i64 p)
  have hP1 : s1.get b = some (.i64 p) := Locals.get_setLocal_same hLow0 (by omega)
  have hExt1 : s1.get ext = some (.i64 e) := by
    rw [Locals.get_setLocal_ne hLow0 (by omega)]; exact hExt
  -- The length, in local `b + 1`.
  show wp m _ Q store s1 host
  simp only [wp_localGet_cons, hP1, wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead]
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ b + 1 := by
    show s.params.length ≤ b + 1; omega
  have hHigh1 : b + 1 < ({ s1 with values := s.values } : Locals).params.length +
      ({ s1 with values := s.values } : Locals).locals.length := by
    show b + 1 < s.params.length + (setLocal _ _ _).locals.length; simp [setLocal]; omega
  refine wp_localSet_local hLow1 hHigh1 ?_
  let s2 := setLocal { s1 with values := s.values } (b + 1)
    (.i64 (UInt64.ofNat (el.words (env.get x)).size))
  have hN2 : s2.get (b + 1) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size)) :=
    Locals.get_setLocal_same hLow1 hHigh1
  have hP2 : s2.get b = some (.i64 p) := by
    rw [Locals.get_setLocal_ne hLow1 (by omega)]; exact hP1
  have hExt2 : s2.get ext = some (.i64 e) := by
    rw [Locals.get_setLocal_ne hLow1 (by omega)]; exact hExt1
  -- The new length, in local `b + 2`.
  show wp m _ Q store s2 host
  simp only [wp_localGet_cons, Locals.get_values, hN2, hExt2, wp_addI64_cons]
  have hLow2 : ({ s2 with values := s.values } : Locals).params.length ≤ b + 2 := by
    show s.params.length ≤ b + 2; omega
  have hHigh2 : b + 2 < ({ s2 with values := s.values } : Locals).params.length +
      ({ s2 with values := s.values } : Locals).locals.length := by
    show b + 2 < s.params.length + (setLocal _ _ _).locals.length; simp [s1, setLocal]; omega
  refine wp_localSet_local hLow2 hHigh2 ?_
  let s3 := setLocal { s2 with values := s.values } (b + 2)
    (.i64 (UInt64.ofNat (el.words (env.get x)).size + e))
  have hT3 : s3.get (b + 2) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size + e)) :=
    Locals.get_setLocal_same hLow2 hHigh2
  have hN3 : s3.get (b + 1) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size)) := by
    rw [Locals.get_setLocal_ne hLow2 (by omega)]; exact hN2
  have hP3 : s3.get b = some (.i64 p) := by
    rw [Locals.get_setLocal_ne hLow2 (by omega)]; exact hP2
  have hTotal : (UInt64.ofNat (el.words (env.get x)).size + e).toNat =
      (el.words (env.get x)).size + e.toNat := by
    rw [UInt64.toNat_add, hN]; omega
  -- The trap when the new length is `2 ^ 29` or more.
  show wp m _ Q store s3 host
  simp only [wp_localGet_cons, hT3, wp_constI64_cons, wp_geUI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  by_cases hBig : (536870912 : UInt64) ≤ UInt64.ofNat (el.words (env.get x)).size + e
  · simp (config := { decide := true }) only [ge_iff_le, hBig, ↓reduceIte]
    rw [wp_unreachable_cons]
    exact hTrap _
  simp (config := { decide := true }) only [ge_iff_le, hBig, ↓reduceIte]
  rw [wp_nil]
  dsimp only
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  have hTotalLt : (el.words (env.get x)).size + e.toNat < 536870912 := by
    have := UInt64.not_le.mp hBig
    rw [UInt64.lt_iff_toNat_lt, hTotal] at this
    exact this
  have hT3' : ({ s3 with values := s3.values } : Locals).get (b + 2) =
      some (.i64 (UInt64.ofNat (el.words (env.get x)).size + e)) := hT3
  have hFrame3 : ∀ j < b, s3.get j = s.get j ∧ s3.get (j + s.half) = s.get (j + s.half) :=
    fun j hj => ⟨by
      rw [Locals.get_setLocal_ne hLow2 (by omega), Locals.get_values,
        Locals.get_setLocal_ne hLow1 (by omega), Locals.get_values,
        Locals.get_setLocal_ne hLow0 (by omega), Locals.get_values], by
      rw [Locals.get_setLocal_ne hLow2 (by omega), Locals.get_values,
        Locals.get_setLocal_ne hLow1 (by omega), Locals.get_values,
        Locals.get_setLocal_ne hLow0 (by omega), Locals.get_values]⟩
  have hh3 : s3.half = s.half := by simp [s3, s2, s1]
  have hp3 : s3.params = s.params := rfl
  have hl3 : s3.locals.length = s.locals.length := by simp [s3, s2, s1, setLocal]
  have hv3 : s3.values = s.values := rfl
  by_cases hMove : (slots.getD x.index default).mode = .owned ∧ live x.index = false
  swap
  · -- A copy into a block with room.
    rw [ite_eq_right hMove]
    simp only [List.cons_append, List.append_assoc, wp_localGet_cons, hT3', wp_constI64_cons,
      wp_addI64_cons, wp_mulI64_cons]
    have hBytes : ((UInt64.ofNat (el.words (env.get x)).size + e + 1) * 8).toNat =
        8 * ((UInt64.ofNat (el.words (env.get x)).size + e).toNat + 1) := by
      simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.reduceToNat] at hTotal ⊢
      omega
    refine wp_allocCopy hm hAt hCap hTrap hB (by rw [hTotal]; exact hTotalLt) (by omega)
      (by rw [hBytes]) (by rw [hBytes, hTotal]; omega) hP3 hT3 hN3
      (by show s.params.length ≤ b + 4; omega) (by rw [hp3, hl3]; omega)
      (by show s.params.length ≤ b + 5; omega) (by rw [hp3, hl3]; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      fun heap1 store1 s4 q words hSize hPrefix hStep hOwnedQ _ hp4 hl4 hOther4 hQ4 hv4 => ?_
    have hF4 : Frame b s s4 := ⟨hp4.trans hp3, hl4.trans hl3, fun j hj =>
      ⟨by rw [hOther4 j (by omega) (by omega), (hFrame3 j hj).1],
        by rw [hOther4 _ (by omega) (by omega), (hFrame3 j hj).2]⟩⟩
    have hVarsL := hVars.live_mono (live' := live) fun i h => by simp [h]
    refine hNext heap1 store1 s4 q words (by rw [hSize, hTotal]) hPrefix ⟨?_, hF4, ?_,
      ⟨q, rfl, hOwnedQ⟩, ?_⟩ (by rw [hOther4 _ (by omega) (by omega)]; exact hN3) hQ4
      (by rw [hv4, hv3])
    · exact hStep.mono (fun _ _ => trivial) fun _ h => h
    · exact (hVarsL.step hStep fun _ _ _ _ _ _ _ _ => trivial).frame hF4 le_rfl
    · intro u y hy _ wy hwy hly c hc d hd
      have hwy' := (hVarsL.hold_agree hF4 hy hly).mp hwy
      obtain ⟨hSame, hFresh⟩ := hVarsL.regions_after hStep hy hwy' hly fun _ _ => trivial
      rw [hSame] at hd
      exact regionsDisjoint_symm (hFresh d hd c hc)
  -- An owned `x` that dies: its block, extended in place or replaced by a larger one.
  obtain ⟨hOwnedX, hDead⟩ := hMove
  rw [ite_eq_left (show (slots.getD x.index default).mode = .owned ∧ live x.index = false from
    ⟨hOwnedX, hDead⟩)]
  have hOwned : heap.Owned store p (el.words (env.get x)) := by rw [hOwnedX] at hArr; exact hArr
  have hBaseP := hOwned.base
  have hAddrP := hOwned.address
  have hBelowP := hOwned.below
  have hTop := hAt.top
  have hCapacityP := hOwned.capacity
  have a0 := (After.move x hVars hAt hOwnedX hDead hold rfl).reframe
    ⟨hp3, hl3, fun j hj => hFrame3 j hj⟩
  have hP3' : ({ s3 with values := s3.values } : Locals).get b = some (.i64 p) := hP3
  have hCapAddr : (p - 32).toUInt32.toNat = p.toNat - 32 :=
    headerAddress_toNat (by simp only [UInt64.reduceToNat]; omega) (by omega)
  -- The capacity, in local `b + 3`.
  simp only [List.cons_append, List.nil_append, wp_localGet_cons, hP3', wp_constI64_cons,
    wp_subI64_cons, wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by rw [hCapAddr]; omega)]
  have hLow3 : ({ s3 with values := s3.values } : Locals).params.length ≤ b + 3 := by
    show s.params.length ≤ b + 3; omega
  have hHigh3 : b + 3 < ({ s3 with values := s3.values } : Locals).params.length +
      ({ s3 with values := s3.values } : Locals).locals.length := by
    show b + 3 < s3.params.length + s3.locals.length; rw [hp3, hl3]; omega
  refine wp_localSet_local hLow3 hHigh3 ?_
  let s4 := setLocal { s3 with values := s3.values } (b + 3)
    (.i64 (store.mem.read64 (p - 32).toUInt32))
  have hC4 : s4.get (b + 3) = some (.i64 (store.mem.read64 (p - 32).toUInt32)) :=
    Locals.get_setLocal_same hLow3 hHigh3
  have hT4 : s4.get (b + 2) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size + e)) := by
    rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values]; exact hT3
  have hN4 : s4.get (b + 1) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size)) := by
    rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values]; exact hN3
  have hP4 : s4.get b = some (.i64 p) := by
    rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values]; exact hP3
  have hp4 : s4.params = s.params := rfl
  have hl4 : s4.locals.length = s.locals.length := by simp [s4, setLocal, hl3]
  have hF4 : Frame b s3 s4 := ⟨rfl, by simp [s4, setLocal], fun j hj =>
    ⟨by rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values],
      by rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values]⟩⟩
  have hh4 : s4.half = s.half := by simp [s4, hh3]
  have hcN : (store.mem.read64 (p - 32).toUInt32).toNat = capacityAt store p := rfl
  -- The room test.
  show wp m _ Q store s4 host
  simp only [wp_localGet_cons, Locals.get_values, hT4, hC4, wp_constI64_cons, wp_addI64_cons,
    wp_mulI64_cons, wp_leUI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have hNeed : ((UInt64.ofNat (el.words (env.get x)).size + e + 1) * 8).toNat =
      8 * ((el.words (env.get x)).size + e.toNat + 1) := by
    simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.reduceToNat] at hTotal ⊢
    omega
  by_cases hFits : (UInt64.ofNat (el.words (env.get x)).size + e + 1) * 8 ≤
    store.mem.read64 (p - 32).toUInt32
  · -- Room in the block: the new length, in place.
    simp (config := { decide := true }) only [hFits, ↓reduceIte]
    rw [UInt64.le_iff_toNat_le, hNeed, hcN] at hFits
    have hP4' : ({ s4 with values := s4.values } : Locals).get b = some (.i64 p) := hP4
    simp only [wp_localGet_cons, hP4']
    have hLow4 : ({ s4 with values := s4.values } : Locals).params.length ≤ b + 4 := by
      show s.params.length ≤ b + 4; omega
    have hHigh4 : b + 4 < ({ s4 with values := s4.values } : Locals).params.length +
        ({ s4 with values := s4.values } : Locals).locals.length := by
      show b + 4 < s4.params.length + s4.locals.length; rw [hp4, hl4]; omega
    refine wp_localSet_local hLow4 hHigh4 ?_
    let s5 := setLocal { s4 with values := s4.values } (b + 4) (.i64 p)
    have hQ5 : s5.get (b + 4) = some (.i64 p) := Locals.get_setLocal_same hLow4 hHigh4
    have hT5 : s5.get (b + 2) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size + e)) := by
      rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values]; exact hT4
    have hN5 : s5.get (b + 1) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size)) := by
      rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values]; exact hN4
    have hF5 : Frame b s4 s5 := ⟨rfl, by simp [s5, setLocal], fun j hj =>
      ⟨by rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values],
        by rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values]⟩⟩
    show wp m _ _ store s5 host
    have hP32 : p.toUInt32.toNat = p.toNat := by rw [Memory.toUInt32_toNat]; omega
    simp only [wp_localGet_cons, Locals.get_values, hQ5, hT5, wp_wrapI64_cons, wrap_toUInt32,
      wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
    rw [ite_eq_right (by rw [hP32]; omega), wp_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    -- The block holds the new length, the elements of `x`, and what memory held after them.
    let store' : Store Unit :=
      { store with
        mem := store.mem.write64 p.toUInt32 (UInt64.ofNat (el.words (env.get x)).size + e) }
    let words : Array UInt64 :=
      Array.ofFn (n := (UInt64.ofNat (el.words (env.get x)).size + e).toNat) fun j =>
        if j.val < (el.words (env.get x)).size then (el.words (env.get x))[j.val]!
        else store'.mem.read64 (UInt64Array.wordAddress p (j.val + 1))
    have hSize : words.size = (UInt64.ofNat (el.words (env.get x)).size + e).toNat :=
      Array.size_ofFn
    have hValues : UInt64Array.At store' p words := by
      refine ⟨by rw [hSize, hTotal]; omega, ?_, ?_, fun j hj => ?_⟩
      · rw [hSize, hTotal]; simp only [store', Wasm.Mem.write64_pages]; omega
      · rw [hSize, UInt64.ofNat_toNat]; exact Memory.read64_write64 ..
      · simp only [words, Array.getElem_ofFn]
        rw [hSize, hTotal] at hj
        split
        · next hjn =>
          rw [getElem!_pos _ j hjn, ← hA.elementRead j hjn]
          refine Memory.read64_write64_disjoint _ _ _ _ (Or.inr ?_)
          rw [hP32, ← UInt64Array.wordAddress, UInt64Array.wordAddress_toNat hFitA (by omega)]
          omega
        · rfl
    have hWrites : Memory.WritesRange store store' p.toNat (p.toNat + 8) :=
      Memory.WritesRange.write64 _ p.toUInt32 _ _ _ (by omega) (by omega)
    have hWithin : WritesWithin store store' p.toNat (capacityAt store p) :=
      ⟨by rw [hWrites.1], hWrites.2.1, fun a ha => hWrites.2.2 a (by omega)⟩
    have aW := ((a0.toWords.reframe hF4).reframe hF5).rewrite hWithin (by rw [hWrites.1]) hValues
      (by rw [hSize, hTotal]; omega)
    refine hNext heap store' _ p words (by rw [hSize, hTotal]) (fun j hj => ?_) aW hN5 hQ5 rfl
    rw [getElem!_pos words j (by rw [hSize, hTotal]; omega)]
    simp only [words, Array.getElem_ofFn]
    rw [ite_eq_left hj, getElem!_pos _ j hj]
  · -- No room: a block of at least twice the capacity, then the release of the old one.
    simp (config := { decide := true }) only [hFits, ↓reduceIte]
    have hT4' : ({ s4 with values := s4.values } : Locals).get (b + 2) =
        some (.i64 (UInt64.ofNat (el.words (env.get x)).size + e)) := hT4
    have hC4' : ({ s4 with values := s4.values } : Locals).get (b + 3) =
        some (.i64 (store.mem.read64 (p - 32).toUInt32)) := hC4
    refine wp_requestCode hT4' hC4' (by rw [hTotal]; exact hTotalLt) (by rw [hcN]; omega)
      fun r hr1 hr2 => ?_
    refine wp_allocCopy hm hAt hCap (hTrap.imp fun _ h => h) hOwned.borrowed
      (by rw [hTotal]; exact hTotalLt) (by rw [hTotal]; omega) hr1 hr2 hP4 hT4 hN4
      (by show s.params.length ≤ b + 4; omega) (by rw [hp4, hl4]; omega)
      (by show s.params.length ≤ b + 5; omega) (by rw [hp4, hl4]; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      fun heap1 store1 s5 q words hSize hPrefix hStep1 hOwnedQ _ hp5 hl5 hOther5 hQ5 hv5 => ?_
    have hP5 : s5.get b = some (.i64 p) := by rw [hOther5 b (by omega) (by omega)]; exact hP4
    simp only [wp_localGet_cons, hP5]
    obtain ⟨⟨hOwnedP1, hCapP1⟩, hApartPQ⟩ := hStep1.owned hOwned trivial
    refine wp_release hm hStep1.at_ hOwnedP1 ?_
    rw [wp_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    have hRel := releaseStep hStep1.at_ hOwnedP1
    have hPQ : regionsDisjoint (block store1 q) (block store1 p) := by
      rw [block_eq hCapP1]
      exact regionsDisjoint_symm (hApartPQ _ (List.mem_singleton_self _))
    obtain ⟨⟨hOwnedQ2, hCapQ2⟩, -⟩ := hRel.owned hOwnedQ hPQ
    have hStepG := hStep1.transBoth hRel (keep := fun r => regionsDisjoint r (block store p))
      fun _ hr => ⟨trivial, fun _ => by rw [block_eq hCapP1]; exact hr⟩
    have aG := (a0.toWords.reframe hF4).replace (hStepG.mono (fun _ h => h) fun c hc => by
      rw [List.mem_singleton.mp hc, block_eq hCapQ2]
      exact List.mem_append_left _ (List.mem_singleton_self _)) hOwnedQ2
    have hF5 : Frame b s4 { s5 with values := s4.values } := ⟨hp5, hl5, fun j hj =>
      ⟨by show s5.get j = s4.get j; exact hOther5 j (by omega) (by omega),
        by show s5.get _ = s4.get _; exact hOther5 _ (by omega) (by omega)⟩⟩
    exact hNext _ _ _ q words (by rw [hSize, hTotal]) hPrefix (aG.reframe hF5)
      (by show s5.get (b + 1) = _; rw [hOther5 _ (by omega) (by omega)]; exact hN4) hQ5 rfl

/-- `x.push v`: the value's words from local `base` on, the array taken with room for one more
element by `Var.roomCode` from local `base + k + 1` on, and the writes of the element's words
after the array's words. -/
theorem spec_push (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {v : Expr S Γ' (.elem e)}
    (vSpec : ∀ env slots live, CodeSpec m funs host v env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.push x v) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hv := Nat.le_max_left v.width (e.width + 7)
  have h8 := Nat.le_max_right v.width (e.width + 7)
  have hk := e.width_pos
  simp only [Expr.placeArgs] at hPlace
  have hTrapT : TrapOK true Q := hTrap.of_imp fun _ => by simp [Expr.aborts]
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The value's words, from local `base` on.
  have hIn : ∀ k, ((live k || k == x.index) || v.uses k) = true →
      (live k || (Expr.push x v).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact live_assoc _ _ _ h
  refine vSpec env slots (fun k => live k || k == x.index) h base heap store s hh
    (hVars.live_mono hIn) hAt hCap hBase (by omega) hPlace _ _ (hTrapT.of_imp fun _ => rfl)
    fun heap1 store1 s1 ws1 a1 => ?_
  have hR1 := Ty.rep_elem.mp a1.rep
  subst hR1
  have e1a := a1.toEvolves rfl
  have hp1a : s1.params = s.params := e1a.frame.params
  have hh1a : s1.half = h := e1a.frame.half.trans hh
  refine wp_storeCode (e.values (v.denote funs env)) h base e.types s1 s.values
    (by rw [e.values_length, e.types_length]) hh1a (by rw [hp1a]; omega)
    (by rw [e.types_length, hh1a]; omega) fun s1' f1 hold1 _ => ?_
  have f1' : Frame base s1 { s1' with values := s.values } := f1.trans Frame.ofValues
  have e1 : Evolves env slots (fun k => (live k || k == x.index) || v.uses k)
      (fun k => live k || k == x.index) base heap store s heap1 store1
      { s1' with values := s.values } :=
    ⟨e1a.step, e1a.frame.trans f1', e1a.holds.agree f1'⟩
  have hp1 : s1'.params = s.params := f1.params.trans hp1a
  have hh1 : s1'.half = h := f1.half.trans hh1a
  -- The count of new words, in local `base + k`.
  simp only [wp_constI64_cons]
  have hLowK : ({ s1' with values := s.values } : Locals).params.length ≤ base + e.width := by
    show s1'.params.length ≤ _; rw [hp1]; omega
  have hHighK' : base + e.width < ({ s1' with values := s.values } : Locals).half := by
    simp only [Locals.half_values, hh1]; omega
  have hHighK := Locals.lt_total hHighK'
  refine wp_localSet_local hLowK hHighK ?_
  set s2 := setLocal { s1' with values := s.values } (base + e.width) (.i64 (wordCount e.width))
    with hs2
  have hK2 : s2.get (base + e.width) = some (.i64 (wordCount e.width)) :=
    Locals.get_setLocal_same hLowK hHighK
  have hF2 : Frame (base + e.width) { s1' with values := s.values } s2 :=
    Frame.setValues (s := { s1' with values := s.values }) (vs := s.values) hLowK le_rfl hHighK'
  have hold2 : LocalsHold s2 base e.types (e.values (v.denote funs env)) :=
    (LocalsHold.frame (Frame.ofValues.trans hF2) (by rw [e.values_length, e.types_length])
      (by rw [e.types_length])).mpr hold1
  have e2 : Evolves env slots (fun k => (live k || k == x.index) || v.uses k)
      (fun k => live k || k == x.index) base heap store s heap1 store1 s2 :=
    ⟨e1.step, e1.frame.trans (hF2.mono (by omega)), e1.holds.agree (hF2.mono (by omega))⟩
  have hp2 : s2.params = s.params := e2.frame.params
  have hh2 : s2.half = h := e2.frame.half.trans hh
  -- The array, with room for one more element, from local `base + k + 1` on.
  refine spec_room hm x (b := base + e.width + 1) (ext := base + e.width) (e := wordCount e.width)
    (s := s2) (e2.holds.mono (by omega))
    e2.step.at_ (by rw [e2.step.cap m]; exact hCap) (by rw [hp2]; omega)
    (by rw [hh2]; omega) hK2 (by omega) (by rw [wordCount_toNat]; omega) hTrapT
    fun heap2 store2 s3 q words hSize hPrefix aR hN3 hQ3 hv3 => ?_
  obtain ⟨p, hp, hOwnedQ⟩ := aR.rep
  replace hOwnedQ : heap2.Owned store2 p words := hOwnedQ
  obtain rfl : p = q := by simp only [List.cons.injEq, Value.i64.injEq] at hp; exact hp.1.symm
  have hFitQ := hOwnedQ.values.1
  have hkw : (wordCount e.width).toNat = e.width := by
    rw [wordCount_toNat] at hSize ⊢; omega
  rw [hkw, Elem.words_size] at hSize
  have hL64 : (UInt64.ofNat (e.words (env.get x)).size).toNat = (env.get x).size * e.width := by
    rw [Elem.words_size]
    exact UInt64.toNat_ofNat_of_lt'
      (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hold3 : LocalsHold s3 base e.types
      (List.zipWith typedValue e.types (e.toWords (v.denote funs env))) := by
    rw [e.values_typed]
    exact (LocalsHold.frame (aR.frame.mono (base := base + e.width) (by omega))
      (by rw [e.values_length, e.types_length]) (by rw [e.types_length])).mpr hold2
  -- The writes of the element's words after the array's words.
  refine wp_storeWordsCode 0 base e.types (e.toWords (v.denote funs env)) words store2 s3 aR
    (aR.frame.half.trans hh2) hQ3 hN3 hold3 (by rw [e.toWords_length, e.types_length])
    (by rw [hL64, e.types_length, hSize]; omega) fun store4 a4 => ?_
  rw [hL64] at a4
  simp only [Nat.add_zero] at a4
  rw [Elem.words_push_into e (v.denote funs env) hSize (fun w hw => by
    rw [getElem!_pos (e.words (env.get x)) w (by rw [Elem.words_size]; exact hw)]
    exact hPrefix w (by rw [Elem.words_size]; exact hw))] at a4
  have aFin := After.prepend (hVars.live_mono hIn) e2 ((After.ofWords a4).lower e2.holds (by omega)
    fun k h => by simp [h]) (fun k h => by simp [h]) fun k h => by simp [h]
  simp only [wp_localGet_cons, hQ3]
  simpa [hv3, hs2, setLocal] using hNext heap2 store4 s3 [.i64 p] (aFin.liveIn hIn)

/-- `x ++ y`: the length of `y` in local `base`, the array `x` taken with room for `y`'s elements
by `Var.roomCode` from local `base + 1` on, with `y` live, the copy of `y`'s elements after `x`'s,
and the release of `y` when it is owned and dies there. -/
theorem spec_append (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x y : Var Γ' (.array e)) :
    ∀ env slots live, CodeSpec m funs host (Expr.append (S := S) x y) env slots live := by
  intro env slots live h base heap store s hh hVars hAt hCap hBase hRoom _ rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hTrapT : TrapOK true Q := hTrap.of_imp fun _ => by simp [Expr.aborts]
  have hTot : 2 * s.half ≤ s.params.length + s.locals.length := by
    simp only [Locals.half]; omega
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The length of `y`, in local `base`.
  obtain ⟨hBelowY, wy, holdy, hRepY⟩ := hVars.get y (by simp [Expr.uses])
  obtain ⟨py, rfl, hArrY⟩ := hRepY
  have hYB : (slots.getD y.index default).loc < base := by
    have := hBelowY; simp only [Ty.width] at this; omega
  have hBY := hArrY.borrow
  have hAY := hBY.values
  have hLenY := hAY.lengthBound
  have hFitY := hAY.1
  have hmY : (e.words (env.get y)).size < 536870912 := by omega
  have hMY : (UInt64.ofNat (e.words (env.get y)).size).toNat = (e.words (env.get y)).size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hPY : s.get (slots.getD y.index default).loc = some (.i64 py) := by
    exact LocalsHold.word holdy
  simp only [wp_localGet_cons, hPY, wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hAY.lengthRead]
  refine wp_localSet_local hBase (by omega) ?_
  have hLow0 : ({ s with values := s.values } : Locals).params.length ≤ base := hBase
  set s1 := setLocal { s with values := s.values } base
    (.i64 (UInt64.ofNat (e.words (env.get y)).size))
    with hs1
  have hM1 : s1.get base = some (.i64 (UInt64.ofNat (e.words (env.get y)).size)) :=
    Locals.get_setLocal_same hLow0 (by omega)
  have hF1 : Frame base s s1 := by
    rw [hs1]; exact Frame.setValues hLow0 le_rfl (by rw [hh]; omega)
  have hh1' : s1.half = s.half := hF1.half
  -- The array `x` with room, from local `base + 1` on, with `y` live.
  have hIn : ∀ k, ((live k || k == y.index) || k == x.index) = true →
      (live k || (Expr.append (S := S) x y).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact append_live _ _ _ h
  have hVars1 : Holds env slots (fun k => (live k || k == y.index) || k == x.index) (base + 1)
      heap store s1 :=
    ((hVars.live_mono hIn).agree hF1).mono (by omega)
  refine spec_room hm x (b := base + 1) (ext := base) (e := UInt64.ofNat (e.words (env.get y)).size)
    (s := s1) hVars1 hAt hCap (by show s.params.length ≤ base + 1; omega)
    (by rw [hh1', hh]; omega)
    hM1 (by omega) (by rw [hMY]; exact Nat.le_of_lt hmY) hTrapT
    fun heap1 store1 s2 q words hSize hPrefix aR hN2 hQ2 hv2 => ?_
  rw [hMY] at hSize
  have hp2 : s2.params = s.params := aR.frame.params
  have hl2 : s2.locals.length = s.locals.length := by rw [aR.frame.length]; simp [s1, setLocal]
  have hM2 : s2.get base = some (.i64 (UInt64.ofNat (e.words (env.get y)).size)) :=
    (aR.frame.below base (by omega)).1.trans hM1
  have hh2' : s2.half = s.half := aR.frame.half.trans hh1'
  -- `y` stays readable, apart from the new array.
  obtain ⟨-, wy', holdy', hRepY'⟩ := aR.holds.get y (by simp)
  have hAgree2 : ∀ j < base, s2.get j = s.get j := fun j hj =>
    (aR.frame.below j (by omega)).1.trans (hF1.below j hj).1
  have holdy2 : LocalsHold s2 (slots.getD y.index default).loc (Ty.array e).types [.i64 py] :=
    (LocalsHold.frame (hF1.trans (aR.frame.mono (base := base) (by omega))) rfl
      (by simp only [Ty.types, List.length_singleton]; omega)).mpr holdy
  obtain rfl := LocalsHold.unique holdy' holdy2 (by rw [hRepY'.length]; rfl)
  obtain ⟨py', hpy, hArrY1⟩ := hRepY'
  obtain rfl : py = py' := by simp only [List.cons.injEq, Value.i64.injEq] at hpy; exact hpy.1
  have hBY1 := hArrY1.borrow
  obtain ⟨p, hp, hOwnedQ⟩ := aR.rep
  replace hOwnedQ : heap1.Owned store1 p words := hOwnedQ
  obtain rfl : p = q := by simp only [List.cons.injEq, Value.i64.injEq] at hp; exact hp.1.symm
  have hCapQ := hOwnedQ.capacity
  have hBaseQ := hOwnedQ.base
  have hApartQY : py.toNat + 8 * ((e.words (env.get y)).size + 1) ≤ p.toNat ∨
      p.toNat + 8 * (words.size + 1) ≤ py.toNat := by
    have hD := aR.apart _ y (by simp) (Or.inl rfl) [.i64 py] holdy2 rfl (block store1 p)
      (List.mem_singleton_self _)
    cases hmy : (slots.getD y.index default).mode
    · rw [hmy] at hD
      have := hD _ (List.mem_singleton_self _)
      simp only [block, regionsDisjoint] at this
      omega
    · rw [hmy] at hD hArrY1
      have hOwnedY : heap1.Owned store1 py (e.words (env.get y)) := hArrY1
      have := hD (block store1 py) (List.mem_singleton_self _)
      have := hOwnedY.capacity
      have := hOwnedY.base
      simp only [block, regionsDisjoint] at *
      omega
  -- The address of element `n` of the new array, in local `base + 4`.
  have h8n : UInt64.ofNat (e.words (env.get x)).size * 8 =
      UInt64.ofNat (8 * (e.words (env.get x)).size) := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  simp only [wp_localGet_cons, Locals.get_values, hQ2, hN2, wp_constI64_cons, wp_mulI64_cons,
    wp_addI64_cons, h8n]
  have hLow2 : ({ s2 with values := s2.values } : Locals).params.length ≤ base + 4 := by
    show s2.params.length ≤ base + 4; rw [hp2]; omega
  have hHigh2 : base + 4 < ({ s2 with values := s2.values } : Locals).params.length +
      ({ s2 with values := s2.values } : Locals).locals.length := by
    show base + 4 < s2.params.length + s2.locals.length; rw [hp2, hl2]; omega
  refine wp_localSet_local hLow2 hHigh2 ?_
  set s3 := setLocal { s2 with values := s2.values } (base + 4)
    (.i64 (p + UInt64.ofNat (8 * (e.words (env.get x)).size))) with hs3
  have hD3 : s3.get (base + 4) = some (.i64 (p + UInt64.ofNat (8 * (e.words (env.get x)).size))) :=
    Locals.get_setLocal_same hLow2 hHigh2
  have hGet3 : ∀ j, j ≠ base + 4 → s3.get j = s2.get j := fun j hj => by
    rw [hs3, Locals.get_setLocal_ne hLow2 hj, Locals.get_values]
  have hp3 : s3.params = s.params := hp2
  have hl3 : s3.locals.length = s.locals.length := by simp [s3, setLocal, hl2]
  -- The copy of `y`'s elements after `x`'s.
  refine wp_copyInto (k := (e.words (env.get x)).size) hBY1.values hOwnedQ.values (by omega)
    hApartQY
    (by rw [hGet3 _ (by omega), hAgree2 _ hYB]; exact hPY) hD3
    (by rw [hGet3 _ (by omega)]; exact hM2) (by omega) (by omega)
    (by omega) (by rw [hp3]; omega) (by rw [hp3, hl3]; omega)
    fun store2 s4 hW hA2 hp4 hl4 hOther4 hv4 => ?_
  have hWords : overlay words (e.words (env.get y)) (e.words (env.get x)).size
      (e.words (env.get y)).size = e.words (env.get x ++ env.get y) := by
    rw [Elem.words_append]
    apply Array.ext (by simp [overlay_size, hSize]) fun j h1 h2 => ?_
    simp only [overlay, Array.getElem_ofFn]
    rw [overlay_size] at h1
    by_cases hj : j < (e.words (env.get x)).size
    · rw [ite_eq_right (by omega), Array.getElem_append_left hj, ← hPrefix j hj,
        getElem!_pos words j h1]
    · rw [ite_eq_left (by omega), Array.getElem_append_right (by omega),
        getElem!_pos _ _ (by omega)]
  rw [hWords] at hA2
  have hWithin : WritesWithin store1 store2 p.toNat (capacityAt store1 p) :=
    ⟨by rw [hW.1], hW.2.1, fun a ha => hW.2.2 a (by omega)⟩
  have aW := aR.rewrite hWithin (by rw [hW.1]) hA2
    (by rw [Elem.words_append, Array.size_append]; omega)
  have hF4 : Frame (base + 1) s2 s4 := ⟨hp4.trans rfl, by rw [hl4]; simp [s3, setLocal],
    fun j hj => ⟨by rw [hOther4 j (by omega), hGet3 j (by omega)],
      by rw [hOther4 _ (by omega), hGet3 _ (by omega)]⟩⟩
  -- The release of `y` when it is owned and dies here.
  refine After.release hm (s1 := s4) (live := live)
    (sel := fun k => k == y.index && !live k) hVars1 (After.ofWords (aW.reframe hF4))
    (fun k h => by simp [h]) (fun k h => by
      simp only [Bool.and_eq_true, beq_iff_eq] at h; simp [h.1])
    (fun k h => by simp [h]) fun heap2 store3 a' => ?_
  have hQ4 : s4.get (base + 5) = some (.i64 p) := by
    rw [hOther4 _ (by omega), hGet3 _ (by omega)]; exact hQ2
  simp only [wp_localGet_cons, hQ4]
  have e0 : Evolves env slots (fun i => live i || (Expr.append (S := S) x y).uses i)
      (fun k => (live k || k == y.index) || k == x.index) base heap store s heap store s1 :=
    ⟨Step.refl hAt _, hF1, (hVars.live_mono hIn).agree hF1⟩
  have aFin := After.prepend hVars e0 (a'.lower ((hVars.live_mono hIn).agree
    hF1) (by omega) fun k h => by simp [h]) hIn fun k h => by simp [h]
  have hv3 : s3.values = s.values := by rw [hs3]; exact hv2
  simpa [hv4, hv3] using hNext heap2 store3 s4 [.i64 p] aFin

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
  | loop count init cond body countSpec initSpec condSpec bodySpec =>
    exact spec_loop hm countSpec initSpec condSpec bodySpec
  | size x => exact spec_size hm x
  | get x i iSpec => exact spec_get hm x iSpec
  | build count elem countSpec elemSpec => exact spec_build hm countSpec elemSpec
  | set x i v iSpec vSpec => exact spec_set hm x iSpec vSpec
  | push x v vSpec => exact spec_push hm x vSpec
  | append x y => exact spec_append hm x y
  | float bits => exact spec_float bits
  | fbin op left right leftSpec rightSpec => exact spec_fbin op leftSpec rightSpec
  | funary op e eSpec => exact spec_funary op eSpec
  | fcmp op left right leftSpec rightSpec => exact spec_fcmp op leftSpec rightSpec
  | toFloat op e eSpec => exact spec_toFloat op eSpec
  | toWord op e eSpec => exact spec_toWord op eSpec
  | mk first second firstSpec secondSpec => exact spec_mk firstSpec secondSpec
  | proj x p => exact spec_proj x p

/-- The position of a variable's first word among the words of the context's values. -/
def Var.offset : {Γ : List Ty} → {t : Ty} → Var Γ t → Nat
  | _ :: _, _, .here => 0
  | s :: _, _, .there y => s.width + y.offset

theorem paramSlots_getD {Γ : List Ty} {t : Ty} (x : Var Γ t) (ms : List Mode) (loc : Nat) :
    (paramSlots Γ ms loc).getD x.index default = ⟨loc + x.offset, paramMode Γ ms x.index⟩ := by
  induction x generalizing ms loc with
  | here => simp [paramSlots, Var.index, Var.offset, paramMode, paramModes]
  | @there Γ' t' s' y ih =>
    simp only [paramSlots, Var.index, Var.offset, List.getD_cons_succ, ih, paramMode, paramModes]
    congr 1
    omega

theorem paramSlots_modes : (ts : List Ty) → (ms : List Mode) → (loc : Nat) →
    (paramSlots ts ms loc).map Slot.mode = paramModes ts ms
  | [], _, _ => rfl
  | _ :: ts, ms, loc => by simp [paramSlots, paramModes, paramSlots_modes ts]

theorem Var.offset_width {Γ : List Ty} {t : Ty} (x : Var Γ t) :
    x.offset + t.width ≤ widthSum Γ := by
  induction x with
  | here => simp [Var.offset, widthSum_cons]
  | @there Γ' t' s' y ih => simp only [Var.offset, widthSum_cons]; omega

theorem flatMap_types_length : (ts : List Ty) → (ts.flatMap Ty.types).length = widthSum ts
  | [] => rfl
  | t :: ts => by simp [widthSum_cons, t.types_length, flatMap_types_length ts]

/-- The type of a variable's word among the types of the context's words. -/
theorem Var.types_getD {Γ : List Ty} {t : Ty} (x : Var Γ t) {k : Nat} (hk : k < t.width) :
    (Γ.flatMap Ty.types).getD (x.offset + k) .i64 = t.types.getD k .i64 := by
  induction x with
  | here =>
    simp only [List.flatMap_cons, Var.offset, Nat.zero_add, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by rw [Ty.types_length]; exact hk)]
  | @there Γ' t' s' y ih =>
    simp only [List.flatMap_cons, Var.offset, List.getD_eq_getElem?_getD] at ih ⊢
    rw [List.getElem?_append_right (by rw [Ty.types_length]; omega), Ty.types_length,
      show s'.width + y.offset + k - s'.width = y.offset + k by omega]
    exact ih hk

theorem Var.words_there {s : Ty} {first rest : List Value} (h : first.length = s.width)
    {Γ : List Ty} {t : Ty} (y : Var Γ t) :
    ((first ++ rest).drop (Var.offset (Var.there (s := s) y))).take t.width =
      (rest.drop y.offset).take t.width := by
  rw [Var.offset, ← h, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    Nat.add_sub_cancel_left]

/-- The words of a variable among the words of the context's values. -/
theorem Env.Rep.var {heap : Heap} {store : Store Unit} {Γ : List Ty} {t : Ty} (x : Var Γ t) :
    ∀ {modes : Nat → Mode} {ws : List Value} {env : Env Γ}, Env.Rep modes heap store ws env →
      t.Rep (modes x.index) heap store ((ws.drop x.offset).take t.width) (env.get x) := by
  induction x with
  | here =>
    intro modes ws env h
    cases env with
    | cons v rest =>
      obtain ⟨first, rest', rfl, h1, -⟩ := h
      rw [Var.offset, List.drop_zero, List.take_left' h1.length]
      exact h1
  | @there Γ' t' s' y ih =>
    intro modes ws env h
    cases env with
    | cons v rest =>
      obtain ⟨first, rest', rfl, h1, h2⟩ := h
      rw [Var.words_there h1.length]
      exact ih h2

/-- The addresses of an owned variable's arrays are among those that the call consumes. -/
theorem Env.moves_var {heap : Heap} {store : Store Unit} {Γ : List Ty} {t : Ty} (x : Var Γ t) :
    ∀ {modes : Nat → Mode} {ws : List Value} {env : Env Γ}, Env.Rep modes heap store ws env →
      modes x.index = .owned → ∀ q ∈ t.pointers ((ws.drop x.offset).take t.width),
        q ∈ Env.moves modes ws env := by
  induction x with
  | here =>
    intro modes ws env h hm q hq
    cases env with
    | cons v rest =>
      obtain ⟨first, rest', rfl, h1, -⟩ := h
      rw [Var.offset, List.drop_zero, List.take_left' h1.length] at hq
      rw [Env.moves_cons h1.length]
      simp only [Var.index] at hm
      rw [hm]
      exact List.mem_append_left _ hq
  | @there Γ' t' s' y ih =>
    intro modes ws env h hm q hq
    cases env with
    | cons v rest =>
      obtain ⟨first, rest', rfl, h1, h2⟩ := h
      rw [Var.words_there h1.length] at hq
      rw [Env.moves_cons h1.length]
      exact List.mem_append_right _ (ih h2 hm q hq)

/-- The regions of a borrowed variable's arrays are among those that the call reads. -/
theorem Env.reads_var {heap : Heap} {store : Store Unit} {Γ : List Ty} {t : Ty} (x : Var Γ t) :
    ∀ {modes : Nat → Mode} {ws : List Value} {env : Env Γ}, Env.Rep modes heap store ws env →
      modes x.index = .borrowed → ∀ c ∈ t.reads ((ws.drop x.offset).take t.width) (env.get x),
        c ∈ Env.reads modes ws env := by
  induction x with
  | here =>
    intro modes ws env h hm c hc
    cases env with
    | cons v rest =>
      obtain ⟨first, rest', rfl, h1, -⟩ := h
      rw [Var.offset, List.drop_zero, List.take_left' h1.length] at hc
      rw [Env.reads_cons h1.length]
      simp only [Var.index] at hm
      rw [hm]
      exact List.mem_append_left _ hc
  | @there Γ' t' s' y ih =>
    intro modes ws env h hm c hc
    cases env with
    | cons v rest =>
      obtain ⟨first, rest', rfl, h1, h2⟩ := h
      rw [Var.words_there h1.length] at hc
      rw [Env.reads_cons h1.length]
      exact List.mem_append_right _ (ih h2 hm c hc)

/-- Arguments whose owned blocks lie apart from one another and from the borrowed arrays: the
blocks of each owned argument lie apart from the regions of every other argument. -/
theorem Env.Rep.apart {heap : Heap} {store : Store Unit} {Γ : List Ty} {t : Ty} (x : Var Γ t) :
    ∀ {modes : Nat → Mode} {ws : List Value} {env : Env Γ}, Env.Rep modes heap store ws env →
    Separate store (Env.moves modes ws env) (Env.reads modes ws env) →
    ∀ {u : Ty} (y : Var Γ u), x.index ≠ y.index → modes x.index = .owned →
    ∀ b ∈ t.blocks store ((ws.drop x.offset).take t.width) (env.get x),
    ∀ c ∈ u.regions (modes y.index) store ((ws.drop y.offset).take u.width) (env.get y),
      regionsDisjoint b c := by
  induction x with
  | here =>
    intro modes ws env h hSep u y hne hm b hb c hc
    cases env with
    | cons v rest =>
      obtain ⟨first, rest', rfl, h1, h2⟩ := h
      rw [Env.moves_cons h1.length, Env.reads_cons h1.length] at hSep
      simp only [Var.index] at hm
      rw [hm] at hSep
      rw [Var.offset, List.drop_zero, List.take_left' h1.length, Ty.blocks_pointers] at hb
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
      cases y with
      | here => exact absurd rfl hne
      | there y' =>
        rw [Var.words_there h1.length] at hc
        simp only [Var.index] at hc
        cases hmy : modes (y'.index + 1) with
        | owned =>
          rw [hmy] at hc
          simp only [Ty.regions, Ty.blocks_pointers] at hc
          obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hc
          have := hSep.1
          rw [List.map_append] at this
          exact (List.pairwise_append.mp this).2.2 _ (List.mem_map_of_mem hq) _
            (List.mem_map_of_mem (Env.moves_var y' h2 hmy q' hq'))
        | borrowed =>
          rw [hmy] at hc
          exact regionsDisjoint_symm (hSep.2 c (List.mem_append_right _
            (Env.reads_var y' h2 hmy c hc)) q (List.mem_append_left _ hq))
  | @there Γ' t' s' x' ih =>
    intro modes ws env h hSep u y hne hm b hb c hc
    cases env with
    | cons v rest =>
      obtain ⟨first, rest', rfl, h1, h2⟩ := h
      rw [Env.moves_cons h1.length, Env.reads_cons h1.length] at hSep
      rw [Var.words_there h1.length] at hb
      cases y with
      | here =>
        rw [Ty.blocks_pointers] at hb
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
        have hq' := Env.moves_var x' h2 hm q hq
        rw [Var.offset, List.drop_zero, List.take_left' h1.length] at hc
        simp only [Var.index] at hc
        cases hmy : modes 0 with
        | owned =>
          rw [hmy] at hc hSep
          simp only [Ty.regions, Ty.blocks_pointers] at hc
          obtain ⟨q', hq'', rfl⟩ := List.mem_map.mp hc
          have := hSep.1
          rw [List.map_append] at this
          exact regionsDisjoint_symm ((List.pairwise_append.mp this).2.2 _
            (List.mem_map_of_mem hq'') _ (List.mem_map_of_mem hq'))
        | borrowed =>
          rw [hmy] at hc hSep
          exact regionsDisjoint_symm (hSep.2 c (List.mem_append_left _ hc) q
            (List.mem_append_right _ hq'))
      | there y' =>
        rw [Var.words_there h1.length] at hc
        have hSep' : Separate store (Env.moves (fun i => modes (i + 1)) rest' rest)
            (Env.reads (fun i => modes (i + 1)) rest' rest) := by
          refine ⟨?_, fun r hr q hq => hSep.2 r (List.mem_append_right _ hr) q
            (List.mem_append_right _ hq)⟩
          have := hSep.1
          rw [List.map_append] at this
          exact (List.pairwise_append.mp this).2.1
        exact ih h2 hSep' y' (fun he => hne (by simp [Var.index, he])) hm b hb c hc

theorem FVar.index_lt {S : List Sig} {g : Sig} (f : FVar S g) :
    f.index < S.length := by
  induction f with
  | here => simp [FVar.index]
  | there g ih => simp [FVar.index]; omega

/-- A function's code from its entry: the release of the owned parameters that the body does not
use, the body's code, and the coercion of the body's value to an owned one. -/
theorem Func.code_spec {S : List Sig} (func : Func S) (funs : Funs S) (m : Module)
    (host : HostEnv Unit) (hm : Runtime m) (hCalls : Calls m funs) (args : Env func.params)
    (heap : Heap) (store : Store Unit) (s : Locals) (hh : s.half = func.positions)
    (hVars : Holds args (paramSlots func.params func.modes 0) (fun _ => true)
      (widthSum func.params) heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hBase : s.params.length ≤ widthSum func.params)
    (Q : Assertion Unit) (hTrap : TrapOK func.aborts Q)
    (hNext : ∀ heap' store' s' ws,
      After args (paramSlots func.params func.modes 0) (fun _ => true) (fun _ => false)
        (widthSum func.params) heap store s func.result .owned (func.denote funs args) heap'
        store' s' ws →
      Q (.Fallthrough store' { s' with values := ws.reverse ++ s.values })) :
    wp m (releaseWhere func.params (paramSlots func.params func.modes 0)
        (fun i => !func.body.uses i) ++
      (func.body.code func.positions (paramSlots func.params func.modes 0) (widthSum func.params)
        (fun _ => false) ++
      (coerceCode func.positions func.result
        (func.body.mode ((paramSlots func.params func.modes 0).map Slot.mode)) .owned
        (widthSum func.params + func.body.width) ++ []))) Q store s host := by
  have hPos : func.positions = widthSum func.params + func.body.width + copyWidth func.result :=
    rfl
  refine wp_releaseWhere hm hVars hAt (fun _ _ => rfl) fun heap1 store1 e => ?_
  have e' := e.mono (live' := fun i => false || func.body.uses i) fun i h => by simpa using h
  refine Expr.code_spec m funs host hm hCalls func.body args
    (paramSlots func.params func.modes 0) (fun _ => false) func.positions (widthSum func.params)
    heap1 store1 s hh e'.holds e'.step.at_ (by rw [e'.step.cap m]; exact hCap) hBase (by omega)
    func.placeArgs _ _
    (hTrap.of_imp fun h => by
      rw [← Slot.any_map, paramSlots_modes] at h
      simp only [Func.aborts]
      exact trap_left _ _ _ h) fun heap' store' s' ws a => ?_
  have a' := After.prepend hVars e' a (fun _ _ => rfl) fun _ h => nomatch h
  refine After.coerce hm a' (fun _ => rfl) (Nat.le_add_right _ _)
    (by rw [a'.frame.params]; omega) (a'.frame.half.trans hh) (by omega)
    (by rw [a'.step.cap m]; exact hCap) (fun _ _ hs => hTrap.of_imp fun _ => by
      simp [Func.aborts, hs]) fun heap'' store'' s'' ws'' a'' => ?_
  rw [wp_nil]
  exact hNext heap'' store'' s'' ws'' a''

/-- A function at position `pos` of a module whose functions at the call indices compute the
functions it calls computes `func.denote funs`. -/
theorem Func.correct {S : List Sig} (func : Func S) (funs : Funs S) (m : Module) (pos : Nat)
    (hm : Runtime m) (hFunc : m.funcs[pos]? = some (func.function pos))
    (hCalls : Calls m funs) :
    @ImplementsA _ _ (Env.represent func.params func.modes) (Ty.represent func.result)
      func.aborts m pos (func.denote funs) (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  intro host store heap params args hAt _ hArgs hSep hCap
  have hArgs' : Env.Rep (paramMode func.params func.modes) heap store params args := hArgs
  have hSep' : Separate store (Env.moves (paramMode func.params func.modes) params args)
      (Env.reads (paramMode func.params func.modes) params args) := hSep
  have hLength : params.length = widthSum func.params := hArgs'.length
  apply Runs.of_wp_entry_for (f := func.function pos)
    (by rw [hm.imports, List.length_nil, Nat.sub_zero]; exact hFunc)
    (hImp := by simp [hm.imports])
  have hNum : (func.function pos).numParams = widthSum func.params := by
    simp only [Func.function, Func.type, Function.numParams]
    exact flatMap_types_length _
  have hTake : (params.reverse.take (func.function pos).numParams).reverse = params := by
    rw [List.take_of_length_le (by rw [hNum, List.length_reverse, hLength])]
    simp
  rw [hTake, show (func.function pos).body =
    paramCopyCode func.positions 0 (func.params.flatMap Ty.types) ++
    (releaseWhere func.params (paramSlots func.params func.modes 0)
        (fun i => !func.body.uses i) ++
      (func.body.code func.positions (paramSlots func.params func.modes 0) (widthSum func.params)
        (fun _ => false) ++
      (coerceCode func.positions func.result
        (func.body.mode ((paramSlots func.params func.modes 0).map Slot.mode)) .owned
        (widthSum func.params + func.body.width) ++ []))) by simp [Func.function]]
  have hPos : func.positions = widthSum func.params + func.body.width + copyWidth func.result :=
    rfl
  have hLocals : ((func.function pos).toLocals params).params.length +
      ((func.function pos).toLocals params).locals.length = func.positions + func.positions := by
    simp [Function.toLocals, Func.function, hLength, hPos]; omega
  refine wp_paramCopyCode (func.params.flatMap Ty.types) 0
    (by simp only [Function.toLocals, Nat.zero_add]; rw [flatMap_types_length, hLength])
    (by simp [Function.toLocals, hLength, hPos]; omega) (by rw [hLocals])
    fun s1 hp1 hl1 hv1 hlow1 hcopy1 => ?_
  have hh1 : s1.half = func.positions := by
    simp only [Locals.half, hp1, hl1, hLocals]; omega
  have hParam : ∀ j (hj : j < params.length),
      ((func.function pos).toLocals params).get j = some params[j] := by
    intro j hj
    simp [Locals.get, Function.toLocals, hj]
  -- The locals after the copy hold each parameter's words.
  have hHold : ∀ {t : Ty} (x : Var func.params t),
      LocalsHold s1 x.offset t.types ((params.drop x.offset).take t.width) := by
    intro t x k hk
    have hk' := hk
    simp only [List.length_take, List.length_drop] at hk'
    have hlt : x.offset + k < params.length := by have := x.offset_width; omega
    have hkw : k < t.width := by have := x.offset_width; omega
    rw [List.getElem_take, List.getElem_drop, hh1]
    by_cases hf : t.types.getD k .i64 = .f64
    · rw [hf]
      show s1.get (x.offset + k + func.positions) = _
      rw [hcopy1 (x.offset + k) (Nat.zero_le _)
        (by rw [Nat.zero_add, flatMap_types_length]; exact hLength ▸ hlt)
        (by rw [Nat.sub_zero, x.types_getD hkw, hf])]
      exact hParam _ hlt
    · have hIdx : slotIndex func.positions (x.offset + k) (t.types.getD k .i64) =
          x.offset + k := by
        cases hty : t.types.getD k .i64 <;> simp_all [slotIndex]
      rw [hIdx, hlow1 _ (by omega)]
      exact hParam _ hlt
  have hWords : ∀ {t : Ty} (x : Var func.params t),
      ((params.drop x.offset).take t.width).length = t.width := by
    intro t x
    have := x.offset_width
    simp only [List.length_take, List.length_drop]
    omega
  refine Func.code_spec func funs m host hm hCalls args heap store s1 hh1
    ⟨fun t x _ => ?_, fun t u x y _ _ hxy hmo wx wy hwx hlx hwy hly => ?_⟩ hAt hCap
    (by rw [hp1]; simp [Function.toLocals, hLength]) _
    (TrapOK.of_msg fun _ => Iff.rfl) fun heap' store' s' ws a => ?_
  · rw [paramSlots_getD x, Nat.zero_add]
    exact ⟨x.offset_width, _, hHold x, hArgs'.var x⟩
  · rw [paramSlots_getD x, Nat.zero_add] at hwx hmo
    rw [paramSlots_getD y, Nat.zero_add] at hwy ⊢
    obtain rfl := LocalsHold.unique hwx (hHold x) (by rw [hlx, hWords])
    obtain rfl := LocalsHold.unique hwy (hHold y) (by rw [hly, hWords])
    exact hArgs'.apart x hSep' y hxy hmo
  · have hLen := a.rep.length
    have hValues : (ws.reverse ++ s1.values).take
        (func.function pos).results.length ++ params.reverse.drop (func.function pos).numParams =
        ws.reverse := by
      rw [hv1, hNum]
      simp [Func.function, Func.type, Function.toLocals, hLen, hLength, Ty.types_length,
        List.take_of_length_le]
    simp only [hValues]
    refine ⟨heap', a.step.at_, ?_, a.step.caps, fun r hr hpos hA => ?_, trivial⟩
    · show func.result.Rep .owned heap' store' _ (func.body.denote funs args)
      rw [List.reverse_reverse]
      exact a.rep
    · obtain ⟨hb, hreg, hf⟩ := a.step.keeps r hr hpos fun t x _ _ hmo wx hwx hlx b hb => by
        rw [paramSlots_getD x, Nat.zero_add] at hwx hmo
        obtain rfl := LocalsHold.unique hwx (hHold x) (by rw [hlx, hWords x])
        rw [Ty.blocks_pointers] at hb
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
        exact hA q (Env.moves_var x hArgs' hmo q hq)
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
      · simp only [Func.function, Func.type, Function.numParams]
        exact flatMap_types_length _
    | there g' =>
      obtain ⟨h1, fn, h2, h3⟩ := hRest g'
      have hidx : (FVar.there g' :
          FVar (⟨f.params, f.result, f.aborts, f.modes⟩ :: S') g).callIndex = g'.callIndex := by
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

/-- A function's theorem for the verified compiler's representation gives the theorem for a Lean
function `F` on types whose representations agree with it: each argument `y` is represented as
`g y` is, and the result of `f` at `g y` represents `F y`. -/
theorem ImplementsA.transfer {α β γ δ : Type} {_ : Represent α} [Represent β] {_ : Represent γ}
    [Represent δ] {aborts : Bool} {m : Module} {entry : Nat} {f : α → γ}
    (h : ImplementsA aborts m entry f (fun _ _ _ => True) (fun _ _ _ _ _ => True))
    (g : β → α) (F : β → δ)
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
    ImplementsA aborts m entry F (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  intro env store heap vs y hAt _ hY hSep' hCap
  exact (h env store heap vs (g y) hAt trivial (hArgs _ _ _ _ hY) (hSep _ _ _ _ hY hSep')
    hCap).mono fun final values ⟨heap', hAt', hOwned, hCaps, hRegions, _⟩ =>
      ⟨heap', hAt', hResult _ _ _ _ hOwned, hCaps, fun r hr hpos hA => by
        obtain ⟨hb, hreg, hout⟩ := hRegions r hr hpos (by rw [hMoves _ _ _ _ hY]; exact hA)
        refine ⟨hb, hreg, ?_⟩
        simp only [Represent.outside, hBlocks]
        exact hout, trivial⟩

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
    {f : α → γ} (h : ImplementsA aborts m entry f (fun _ _ _ => True) (fun _ _ _ _ _ => True))
    (g : β → α) (r : δ → γ) (F : β → δ) (hF : ∀ y, f (g y) = r (F y)) (hArgs : Agree ib ia g)
    (hResult : Agree id ic r) :
    ImplementsA aborts m entry F (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  ImplementsA.transfer h g F (fun _ _ _ _ hy => (hArgs.borrowed _ _ _ _).mp hy)
    (fun _ _ _ _ _ hs => by rw [← hArgs.moves, ← hArgs.reads]; exact hs)
    (fun _ _ _ _ _ => (hArgs.moves _ _ _).symm)
    (fun _ _ _ y hy => (hResult.owned _ _ _ _).mpr (hF y ▸ hy))
    (fun _ _ y => by rw [hF]; exact hResult.blocks _ _ _)

/-- A function's theorem for the verified compiler's representation gives the theorem for Lean
types whose representations agree with it. -/
theorem ImplementsA.comap {α β γ δ : Type} [Represent α] [Represent β] [Represent γ]
    [Represent δ] {aborts : Bool} {m : Module} {entry : Nat} {f : α → γ}
    (h : ImplementsA aborts m entry f (fun _ _ _ => True) (fun _ _ _ _ _ => True))
    (g : β → α) (k : γ → δ)
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
    ImplementsA aborts m entry (k ∘ f ∘ g) (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  ImplementsA.transfer h g (k ∘ f ∘ g) hArgs hSep hMoves (fun _ _ _ _ hz => hResult _ _ _ _ hz)
    (fun _ _ _ => hBlocks _ _ _)

/-- A function's theorem in the form of Lean's instances: for the Lean tuple of its arguments and
its result type, with the instances Lean synthesizes for them. -/
theorem ImplementsA.lean {ps : List Ty} {ms : List Mode} {r : Ty} {aborts : Bool} {m : Module}
    {entry : Nat} {f : Env ps → r.denote}
    (h : @ImplementsA _ _ (Env.represent ps ms) (Ty.represent r) aborts m entry f
      (fun _ _ _ => True) (fun _ _ _ _ _ => True)) :
    @ImplementsA _ _ (argsInst ps ms) r.leanInst aborts m entry
      (fun y => f (Env.ofArgs ps ms y)) (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  @ImplementsA.comap _ _ _ _ (Env.represent ps ms) (argsInst ps ms) (Ty.represent r) r.leanInst
    aborts m entry f h (Env.ofArgs ps ms) id
    (fun _ _ _ _ hy => (argsInst_borrowed ps ms).mp hy)
    (fun _ _ _ _ hy hS => by
      have hl := ((argsInst_borrowed ps ms).mp hy).length
      rw [argsInst_moves ps ms hl, argsInst_reads ps ms hl] at hS
      exact hS)
    (fun _ _ _ _ hy => (argsInst_moves ps ms ((argsInst_borrowed ps ms).mp hy).length).symm)
    (fun _ _ _ _ hz => r.leanInst_owned.mpr hz) (fun _ _ _ => r.leanInst_blocks)

end Verified
