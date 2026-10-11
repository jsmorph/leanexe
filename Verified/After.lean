import Verified.Heap
import LeanExe.Pipeline.FlatRecords
import LeanExe.ProofKit.F64Bits
import LeanExe.ProofKit.F64Convert
import LeanExe.ProofKit.F64Decoded

/-! The facts that the correctness proof of `Correct.lean` shares: `After`, which states what holds
after the code of an expression, the facts about the variables that stay live, the liveness and
trap facts of each construct, the specifications of the code that converts, scales, loads, and
stores words, and the facts about a function's parameters. -/

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

/-- The call depth in the arguments of a function whose code takes it. -/
def Env.depthOf {Γ : List Ty} : Env (.word :: Γ) → UInt64
  | .cons d _ => d

/-- The meaning of a function whose code takes the call depth, at its code's arguments: its
meaning at its own arguments, which follow the depth. -/
def depthMeaning {Γ : List Ty} {t : Ty} (F : Env Γ → t.denote) : Env (.word :: Γ) → t.denote
  | .cons _ args => F args

theorem paramMode_succ (t : Ty) (ts : List Ty) (mo : Mode) (ms : List Mode) (i : Nat) :
    paramMode (t :: ts) (mo :: ms) (i + 1) = paramMode ts ms i := by
  simp [paramMode, paramModes]

/-- The words of a call's arguments after the call depth. -/
theorem Env.rep_depth {ts : List Ty} {ms : List Mode} {heap : Heap} {store : Store Unit}
    {vs : List Value} {d : UInt64} {args : Env ts} :
    Env.Rep (paramMode (.word :: ts) (.borrowed :: ms)) heap store vs (.cons (t := .word) d args) ↔
      ∃ ws, vs = .i64 d :: ws ∧ Env.Rep (paramMode ts ms) heap store ws args := by
  constructor
  · rintro ⟨first, ws, rfl, h1, h2⟩
    have h1' : first = [.i64 d] := h1
    subst h1'
    exact ⟨ws, rfl, by simpa only [paramMode_succ] using h2⟩
  · rintro ⟨ws, rfl, h⟩
    exact ⟨[.i64 d], ws, rfl, rfl, by simpa only [paramMode_succ] using h⟩

theorem Env.moves_depth {ts : List Ty} {ms : List Mode} {ws : List Value} {d : UInt64}
    {args : Env ts} :
    Env.moves (paramMode (.word :: ts) (.borrowed :: ms)) (.i64 d :: ws)
        (.cons (t := .word) d args) =
      Env.moves (paramMode ts ms) ws args := by
  rw [show (.i64 d :: ws : List Value) = [.i64 d] ++ ws from rfl, Env.moves_cons rfl,
    show (fun i => paramMode (.word :: ts) (.borrowed :: ms) (i + 1)) = paramMode ts ms from
      funext fun i => paramMode_succ _ _ _ _ i]
  rfl

theorem Env.reads_depth {ts : List Ty} {ms : List Mode} {ws : List Value} {d : UInt64}
    {args : Env ts} :
    Env.reads (paramMode (.word :: ts) (.borrowed :: ms)) (.i64 d :: ws)
        (.cons (t := .word) d args) =
      Env.reads (paramMode ts ms) ws args := by
  rw [show (.i64 d :: ws : List Value) = [.i64 d] ++ ws from rfl, Env.reads_cons rfl,
    show (fun i => paramMode (.word :: ts) (.borrowed :: ms) (i + 1)) = paramMode ts ms from
      funext fun i => paramMode_succ _ _ _ _ i]
  rfl

/-- The code before a call's arguments: the call depth after the frame's, from local 0, when the
callee's code takes it. -/
theorem wp_depthCode {m : Module} {host : HostEnv Unit} {Q : Assertion Unit} {store : Store Unit}
    {s : Locals} {rest : Program} (depth : Bool) {d0 : UInt64}
    (hd : depth = true → s.params.head? = some (.i64 d0))
    (h : wp m rest Q store { s with values := (if depth then [.i64 (d0 + 1)] else []) ++ s.values }
      host) :
    wp m ((if depth then [.localGet 0, .constI64 1, .addI64] else []) ++ rest) Q store s host := by
  cases depth
  · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append] at h ⊢
    exact h
  · have h0 : s.get 0 = some (.i64 d0) := by
      have := hd rfl
      cases hp : s.params with
      | nil => rw [hp] at this; exact nomatch this
      | cons v vs =>
        rw [hp] at this
        simp only [List.head?_cons, Option.some.injEq] at this
        simp [Locals.get, hp, this]
    simp only [↓reduceIte, List.cons_append, List.nil_append, wp_localGet_cons, h0,
      wp_constI64_cons, wp_addI64_cons] at h ⊢
    exact h

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

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {host : HostEnv Unit} {pv : List Value}

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

/-- `After` for locals that differ from the starting ones only in the operand stack. -/
theorem After.ofValues {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap' : Heap} {store store' : Store Unit} {s s' : Locals} {t : Ty}
    {mode : Mode} {v : t.denote} {ws vs : List Value}
    (a : After env slots L0 L base heap store { s with values := vs } t mode v heap' store' s'
      ws) :
    After env slots L0 L base heap store s t mode v heap' store' s' ws :=
  ⟨a.step, a.frame.values, a.holds, a.rep, a.apart⟩

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
  | build _ _ _ _ | set _ _ _ _ _ | push _ _ _ | append _ _ | insertAt _ _ _ _ _
  | eraseAt _ _ _ => intro _ _; simp [Expr.aborts]
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

/-- The write of element `k` of an owned array keeps the capacity in its header. -/
theorem capacityAt_writeElement {heap : Heap} {store : Store Unit} {p : UInt64}
    {words : Array UInt64} (hOwned : heap.Owned store p words) {k : Nat} (hk : k < words.size)
    (v : UInt64) : capacityAt (UInt64Array.writeElement store p k v) p = capacityAt store p := by
  have hA := hOwned.values
  have hCapacity := hOwned.capacity
  have hFrame := UInt64Array.writeElement_frame store p words.size k v hA.1 hk
  exact (hOwned.rewrite ⟨by rw [hFrame.1], hFrame.2.1, fun x hx => hFrame.2.2 x (by omega)⟩
    (hA.writeElement hk v) (by rw [Array.size_set]; exact hCapacity)).2

/-- Writes inside the words of an owned array value that leave it holding `words'`, no longer than
`words`: the value becomes `words'`, in the same block. -/
theorem After.rewriteRange {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap1 : Heap} {store store1 store2 : Store Unit} {s s1 : Locals}
    {words words' : Array UInt64} {root : UInt64}
    (a : After env slots L0 L base heap store s (.array .word) .owned words heap1 store1 s1
      [.i64 root])
    (hW : Memory.WritesRange store1 store2 root.toNat (root.toNat + 8 * (words.size + 1)))
    (hValues : UInt64Array.At store2 root words') (hLe : words'.size ≤ words.size) :
    After env slots L0 L base heap store s (.array .word) .owned words' heap1 store2 s1
      [.i64 root] := by
  obtain ⟨p, hp, hOwned⟩ := a.rep
  replace hOwned : heap1.Owned store1 p words := hOwned
  obtain rfl : p = root := by simp only [List.cons.injEq, Value.i64.injEq] at hp; exact hp.1.symm
  have hCapacity := hOwned.capacity
  exact a.rewrite ⟨by rw [hW.1], hW.2.1, fun x hx => hW.2.2 x (by omega)⟩ (by rw [hW.1])
    hValues (by omega)

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

theorem wordCount_eq {k : Nat} (hk : k < 536870912) : wordCount k = UInt64.ofNat k := by
  simp only [wordCount, Nat.min_eq_left (Nat.le_of_lt hk)]

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
      capacityAt store2 p = capacityAt store1 p → wp m rest Q store2 s host) →
    wp m (storeWordsCode h ptr w0 j src tys ++ rest) Q store1 s host
  | _, _, [], words, ws, store1, s, a, _, _, _, _, hl, _, hk => by
    obtain rfl : words = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simpa [storeWordsCode, writeWords] using hk store1 a rfl
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
      holdRest hl (by rw [Array.size_set]; omega) fun store2 a2 hc =>
        hk store2 ?_ (hc.trans (capacityAt_writeElement hOwned hn v))
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

theorem Ty.copyScratch_le (t : Ty) : t.copyScratch ≤ copyWidth t := by
  unfold Ty.copyScratch copyWidth
  split <;> omega

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
  | _, .insertAt _ _ _, hp, _, _, _, _, _ | _, .eraseAt _ _, hp, _, _, _, _, _
  | _, .float _, hp, _, _, _, _, _ | _, .fbin _ _ _, hp, _, _, _, _, _
  | _, .funary _ _, hp, _, _, _, _, _ | _, .fcmp _ _ _, hp, _, _, _, _, _
  | _, .toFloat _ _, hp, _, _, _, _, _ | _, .toWord _ _, hp, _, _, _, _, _ => by
    simp [Expr.isPlace] at hp

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

theorem Holds.keepDying_values {Γ' : List Ty} {env : Env Γ'} {slots : List Slot}
    {liveIn liveOut : Nat → Bool} {store : Store Unit} {s : Locals} {values : List Value}
    {r : Nat × Nat} :
    Holds.KeepDying env slots liveIn liveOut store { s with values } r ↔
      Holds.KeepDying env slots liveIn liveOut store s r := Iff.rfl

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

end Cases

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

/-- The test of the call depth `d` in local 0, when the code takes it: a trap at `unreachable`
when the depth has reached the limit, and the rest of the code otherwise. -/
theorem wp_guardCode {m : Module} {host : HostEnv Unit} {Q : Assertion Unit} {store : Store Unit}
    {s : Locals} {rest : Program} (depth : Bool) {d : UInt64}
    (h0 : depth = true → s.get 0 = some (.i64 d))
    (hTrap : depth = true → ¬d < depthLimit → ∀ st, Q (.Trap st "unreachable"))
    (hNext : (depth = true → d < depthLimit) → wp m rest Q store s host) :
    wp m ((if depth then guardCode else []) ++ rest) Q store s host := by
  cases depth
  · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    exact hNext nofun
  · simp only [↓reduceIte, guardCode, List.cons_append, List.nil_append, wp_localGet_cons,
      h0 rfl, wp_constI64_cons, wp_geUI64_cons]
    rw [wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    by_cases hd : depthLimit ≤ d
    · simp (config := { decide := true }) only [ge_iff_le, hd, ↓reduceIte]
      rw [wp_unreachable_cons]
      exact hTrap rfl (UInt64.not_lt.mpr hd) _
    · simp (config := { decide := true }) only [ge_iff_le, hd, ↓reduceIte]
      rw [wp_nil]
      dsimp only
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      exact hNext fun _ => UInt64.not_le.mp hd

theorem bodyFunction_numParams {S : List Sig} {params : List Ty} {result : Ty}
    (modes : List Mode) (body : Expr S params result) (depth : Bool) (typeIdx : Nat) :
    (bodyFunction modes body depth typeIdx).numParams =
      (if depth then 1 else 0) + widthSum params := by
  simp only [bodyFunction, codeParams, Function.numParams, List.length_append,
    flatMap_types_length]
  cases depth <;> rfl

theorem FVar.callIndex_here {S : List Sig} {g : Sig} :
    (FVar.here : FVar (g :: S) g).callIndex = 2 + S.length := by
  simp [FVar.callIndex, FVar.index]

theorem FVar.callIndex_there {S : List Sig} {g h : Sig} (f : FVar S g) :
    (FVar.there f : FVar (h :: S) g).callIndex = f.callIndex := by
  have := f.index_lt
  simp only [FVar.callIndex, FVar.index, List.length_cons]
  omega

end Verified
