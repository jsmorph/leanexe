import Verified.Compile
import LeanExe.Pipeline.Allocation
import LeanExe.TalosCompat

/-! The states of the verified compiler's proof: how locals hold words, how words represent values
in a heap and store, the steps that a heap and store take, and `Holds`, the facts about the
variables in scope. -/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

/-- `after` agrees with `before` on the parameters, the number of locals, and every local below
`base`: the code of an expression with scratch from `base` on changes nothing else. -/
structure Frame (base : Nat) (before after : Locals) : Prop where
  params : after.params = before.params
  length : after.locals.length = before.locals.length
  below : ∀ j < base, after.get j = before.get j

theorem Frame.refl (base : Nat) (s : Locals) : Frame base s s := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem Frame.trans {base : Nat} {s1 s2 s3 : Locals} (h1 : Frame base s1 s2)
    (h2 : Frame base s2 s3) : Frame base s1 s3 :=
  ⟨h2.params.trans h1.params, h2.length.trans h1.length,
    fun j hj => (h2.below j hj).trans (h1.below j hj)⟩

/-- The operand stack plays no part in a frame. -/
theorem Frame.values {base : Nat} {s s' : Locals} {values : List Value}
    (h : Frame base { s with values } s') : Frame base s s' :=
  ⟨h.params, h.length, h.below⟩

theorem Frame.mono {base base' : Nat} {s s' : Locals} (h : Frame base' s s') (hb : base ≤ base') :
    Frame base s s' :=
  ⟨h.params, h.length, fun j hj => h.below j (by omega)⟩

@[simp] theorem Locals.get_values (s : Locals) (vs : List Value) (i : Nat) :
    ({ s with values := vs } : Locals).get i = s.get i := rfl

/-- Local `i`, past the parameters, after a store of `v`. -/
def setLocal (s : Locals) (i : Nat) (v : Value) : Locals :=
  { s with locals := s.locals.set (i - s.params.length) v }

theorem Locals.set?_local {s : Locals} {i : Nat} (v : Value) (hLow : s.params.length ≤ i)
    (hHigh : i < s.params.length + s.locals.length) :
    s.set? i v = some (setLocal s i v) := by
  simp [Locals.set?, setLocal, Nat.not_lt.mpr hLow, hHigh]

theorem Locals.get_setLocal_same {s : Locals} {i : Nat} {v : Value}
    (hLow : s.params.length ≤ i) (hHigh : i < s.params.length + s.locals.length) :
    (setLocal s i v).get i = some v := by
  simp [Locals.get, setLocal, Nat.not_lt.mpr hLow, hHigh,
    List.getElem?_set_self (show i - s.params.length < s.locals.length by omega)]

theorem Locals.get_setLocal_ne {s : Locals} {i j : Nat} {v : Value}
    (hLow : s.params.length ≤ i) (hne : j ≠ i) : (setLocal s i v).get j = s.get j := by
  simp only [Locals.get, setLocal, List.length_set]
  split
  · rfl
  · split
    · rw [List.getElem?_set_ne (by omega)]
    · rfl

/-- A store of `v` to local `i`, past the parameters. -/
theorem wp_localSet_local {m : Module} {rest : Program} {Q : Assertion α} {store : Store α}
    {env : HostEnv α} {s : Locals} {i : Nat} {v : Value} {vs : List Value}
    (hLow : s.params.length ≤ i) (hHigh : i < s.params.length + s.locals.length)
    (h : wp m rest Q store (setLocal { s with values := vs } i v) env) :
    wp m (.localSet i :: rest) Q store { s with values := v :: vs } env := by
  rw [wp_localSet_cons]
  simp only
  rw [Locals.set?_local (s := { s with values := v :: vs }) v hLow hHigh]
  exact h

/-- Locals `loc` to `loc + vals.length - 1` hold `vals`. -/
def LocalsHold (s : Locals) (loc : Nat) (vals : List Value) : Prop :=
  ∀ k (hk : k < vals.length), s.get (loc + k) = some vals[k]

/-- Loading locals that hold `vals` pushes `vals` in order. -/
theorem wp_loadCode {m : Module} {Q : Assertion α} {store : Store α} {host : HostEnv α}
    (vals : List Value) {loc w : Nat} {s : Locals} {rest : Program} (hw : vals.length = w)
    (hold : LocalsHold s loc vals)
    (h : wp m rest Q store { s with values := vals.reverse ++ s.values } host) :
    wp m (loadCode loc w ++ rest) Q store s host := by
  induction vals generalizing loc w s with
  | nil => subst hw; simpa [loadCode] using h
  | cons v vs ih =>
    subst hw
    have h0 : s.get loc = some v := by
      have := hold 0 (by simp)
      rw [Nat.add_zero] at this
      exact this
    simp only [loadCode, List.length_cons, List.cons_append, wp_localGet_cons, h0]
    refine ih rfl (fun k hk => ?_) ?_
    · have := hold (k + 1) (by simp; omega)
      rw [show loc + (k + 1) = loc + 1 + k by omega] at this
      simpa [-Locals.get] using this
    · simpa [List.append_assoc] using h

/-- Storing the top words `vals` of the stack in locals from `loc` on leaves them there and
changes no other local. -/
theorem wp_storeCode {m : Module} {Q : Assertion α} {store : Store α} {host : HostEnv α}
    {rest : Program} (vals : List Value) (loc w : Nat) (s : Locals) (vs : List Value)
    (hw : vals.length = w) (hLow : s.params.length ≤ loc)
    (hHigh : loc + w ≤ s.params.length + s.locals.length)
    (hNext : ∀ s', s'.params = s.params → s'.locals.length = s.locals.length →
      LocalsHold s' loc vals → (∀ j, j < loc ∨ loc + w ≤ j → s'.get j = s.get j) →
      wp m rest Q store { s' with values := vs } host) :
    wp m (storeCode loc w ++ rest) Q store { s with values := vals.reverse ++ vs } host := by
  induction vals generalizing loc w s vs rest with
  | nil =>
    subst hw
    exact hNext s rfl rfl (fun k hk => absurd hk (by simp)) fun _ _ => rfl
  | cons v vals ih =>
    subst hw
    simp only [storeCode, List.length_cons, List.append_assoc, List.reverse_cons,
      List.cons_append, List.nil_append]
    refine ih (loc + 1) _ s (v :: vs) rfl (by omega) (by simp at hHigh ⊢; omega)
      fun s1 hp1 hl1 hold1 hout1 => ?_
    refine wp_localSet_local (by rw [hp1]; omega) (by rw [hp1, hl1]; simp at hHigh; omega) ?_
    refine hNext (setLocal { s1 with values := vs } loc v) hp1 (by simp [setLocal, hl1])
      (fun k hk => ?_) fun j hj => ?_
    · cases k with
      | zero =>
        simpa [-Locals.get] using Locals.get_setLocal_same (s := { s1 with values := vs }) (v := v)
          (by show s1.params.length ≤ loc; rw [hp1]; omega)
          (by show loc < s1.params.length + s1.locals.length
              rw [hp1, hl1]; simp at hHigh; omega)
      | succ k =>
        rw [Locals.get_setLocal_ne (by show s1.params.length ≤ loc; rw [hp1]; omega) (by omega)]
        have := hold1 k (by simp at hk; omega)
        rw [show loc + 1 + k = loc + (k + 1) by omega] at this
        simpa [-Locals.get] using this
    · rw [Locals.get_setLocal_ne (by show s1.params.length ≤ loc; rw [hp1]; omega)
        (by simp at hj; omega)]
      exact hout1 j (by simp at hj; omega)


/-- The array `xs` at `ptr` in `heap` at `store`, borrowed or owned. -/
def Mode.array : Mode → Heap → Store Unit → UInt64 → Array UInt64 → Prop
  | .borrowed, heap, store, ptr, xs => heap.Borrowed store ptr xs
  | .owned, heap, store, ptr, xs => heap.Owned store ptr xs

/-- The words `ws` represent the value `v` of type `t` in `heap` at `store`, with the arrays that
the value contains held in mode `mode`: a word as itself, a `Bool` as 1 or 0, a pair as its first
component's words followed by its second's, and an array as its address. -/
def Ty.Rep (mode : Mode) (heap : Heap) (store : Store Unit) :
    (t : Ty) → List Value → t.denote → Prop
  | .word, ws, v => ws = [.i64 v]
  | .bool, ws, b => ws = [.i64 (boolWord b)]
  | .pair a b, ws, p =>
    ∃ first second, ws = first ++ second ∧ a.Rep mode heap store first p.1 ∧
      b.Rep mode heap store second p.2
  | .array, ws, xs => ∃ ptr, ws = [.i64 ptr] ∧ mode.array heap store ptr xs

theorem Mode.array.borrow {mode : Mode} {heap : Heap} {store : Store Unit} {ptr : UInt64}
    {xs : Array UInt64} (h : mode.array heap store ptr xs) : heap.Borrowed store ptr xs := by
  cases mode
  · exact h
  · exact Heap.Owned.borrowed h

@[simp] theorem Ty.rep_word {mode : Mode} {heap : Heap} {store : Store Unit} {ws : List Value}
    {v : UInt64} : Ty.Rep mode heap store .word ws v ↔ ws = [.i64 v] := Iff.rfl

@[simp] theorem Ty.rep_bool {mode : Mode} {heap : Heap} {store : Store Unit} {ws : List Value}
    {b : Bool} : Ty.Rep mode heap store .bool ws b ↔ ws = [.i64 (boolWord b)] := Iff.rfl

theorem Ty.Rep.length {mode : Mode} {heap : Heap} {store : Store Unit} :
    {t : Ty} → {ws : List Value} → {v : t.denote} → t.Rep mode heap store ws v →
      ws.length = t.width
  | .word, _, _, h | .bool, _, _, h => by subst h; rfl
  | .pair _ _, _, _, ⟨_, _, h, h1, h2⟩ => by
    subst h; simp [Ty.width, h1.length, h2.length]
  | .array, _, _, ⟨_, h, _⟩ => by subst h; rfl

/-- A value read where a borrowed one suffices. -/
theorem Ty.Rep.borrow {mode : Mode} {heap : Heap} {store : Store Unit} :
    {t : Ty} → {ws : List Value} → {v : t.denote} → t.Rep mode heap store ws v →
      t.Rep .borrowed heap store ws v
  | .word, _, _, h | .bool, _, _, h => h
  | .pair _ _, _, _, ⟨first, second, h, h1, h2⟩ => ⟨first, second, h, h1.borrow, h2.borrow⟩
  | .array, _, _, ⟨ptr, h, ha⟩ => ⟨ptr, h, ha.borrow⟩

/-- A value whose type holds no arrays has the same words in either mode. -/
theorem Ty.Rep.owned {mode : Mode} {heap : Heap} {store : Store Unit} :
    {t : Ty} → t.scalar = true → {ws : List Value} → {v : t.denote} →
      t.Rep mode heap store ws v → t.Rep .owned heap store ws v
  | .word, _, _, _, h | .bool, _, _, _, h => h
  | .pair _ _, hs, _, _, ⟨first, second, h, h1, h2⟩ =>
    ⟨first, second, h, h1.owned (by simp [Ty.scalar] at hs; exact hs.1),
      h2.owned (by simp [Ty.scalar] at hs; exact hs.2)⟩
  | .array, hs, _, _, _ => absurd hs (by decide)

/-- The words of the values of a context, in order. -/
def Env.Rep (mode : Mode) (heap : Heap) (store : Store Unit) :
    {Γ : List Ty} → List Value → Env Γ → Prop
  | _, ws, .nil => ws = []
  | _, ws, .cons (t := t) v env =>
    ∃ first rest, ws = first ++ rest ∧ t.Rep mode heap store first v ∧
      Env.Rep mode heap store rest env

theorem widthSum_cons (t : Ty) (ts : List Ty) : widthSum (t :: ts) = t.width + widthSum ts := by
  simp [widthSum]

theorem Env.Rep.length {mode : Mode} {heap : Heap} {store : Store Unit} :
    {Γ : List Ty} → {ws : List Value} → {env : Env Γ} → Env.Rep mode heap store ws env →
      ws.length = widthSum Γ
  | _, _, .nil, h => by subst h; rfl
  | _, _, .cons _ _, h => by
    obtain ⟨_, _, h, h1, h2⟩ := h
    subst h; simp [widthSum_cons, h1.length, h2.length]

/-- How the verified compiler passes arguments: borrowed, as the words of their values. -/
@[instance_reducible] def Env.represent (Γ : List Ty) : Represent (Env Γ) where
  width _ := widthSum Γ
  borrowed heap store vs env := Env.Rep .borrowed heap store vs env
  owned heap store vs env := Env.Rep .owned heap store vs env
  blocks _ _ _ := []
  reads _ _ _ := []
  moves _ _ _ := []

/-- How the verified compiler returns a value: as its words, owned by the caller. -/
@[instance_reducible] def Ty.represent (t : Ty) : Represent t.denote where
  width _ := t.width
  borrowed heap store vs v := t.Rep .borrowed heap store vs v
  owned heap store vs v := t.Rep .owned heap store vs v
  blocks _ _ _ := []
  reads _ _ _ := []
  moves _ _ _ := []

/-- A step from `heap` at `store` to `heap'` at `store'`: the allocator invariant holds after it,
the memory caps are unchanged, and every region of `heap` keeps its bytes and is a region of
`heap'`. -/
structure Step (heap : Heap) (store : Store Unit) (heap' : Heap) (store' : Store Unit) : Prop where
  at_ : heap'.At store'
  caps : store'.memoryCaps = store.memoryCaps
  keeps : heap.Keeps store [] heap' store' []

theorem Step.refl {heap : Heap} {store : Store Unit} (h : heap.At store) :
    Step heap store heap store :=
  ⟨h, rfl, Heap.Keeps.refl heap store []⟩

theorem Step.trans {heap heap1 heap2 : Heap} {store store1 store2 : Store Unit}
    (h1 : Step heap store heap1 store1) (h2 : Step heap1 store1 heap2 store2) :
    Step heap store heap2 store2 :=
  ⟨h2.at_, h2.caps.trans h1.caps, h1.keeps.trans h2.keeps fun _ _ _ _ hb => nomatch hb⟩

theorem Step.cap {heap heap' : Heap} {store store' : Store Unit} (h : Step heap store heap' store')
    (m : Module) : store'.memoryCap m 0 = store.memoryCap m 0 := by
  simp [Store.memoryCap, h.caps]

theorem Mode.array.step {mode : Mode} {heap heap' : Heap} {store store' : Store Unit}
    {ptr : UInt64} {xs : Array UInt64} (hStep : Step heap store heap' store')
    (h : mode.array heap store ptr xs) : mode.array heap' store' ptr xs := by
  cases mode
  · exact (hStep.keeps.borrowed hStep.at_ h fun _ hb => nomatch hb).1
  · exact ((hStep.keeps.owned hStep.at_ h fun _ hb => nomatch hb).1).1

/-- A value's words represent it after a step. -/
theorem Ty.Rep.step {mode : Mode} {heap heap' : Heap} {store store' : Store Unit}
    (hStep : Step heap store heap' store') :
    {t : Ty} → {ws : List Value} → {v : t.denote} → t.Rep mode heap store ws v →
      t.Rep mode heap' store' ws v
  | .word, _, _, h | .bool, _, _, h => h
  | .pair _ _, _, _, ⟨first, second, h, h1, h2⟩ =>
    ⟨first, second, h, h1.step hStep, h2.step hStep⟩
  | .array, _, _, ⟨ptr, h, ha⟩ => ⟨ptr, h, ha.step hStep⟩

/-- Each variable `x` live in `live` starts at local `(slots.getD x.index default).loc`, its
words end below `base`, and its locals hold words that represent its value in `heap` at
`store`, in the variable's mode. -/
def Holds {Γ : List Ty} (env : Env Γ) (slots : List Slot) (live : Nat → Bool) (base : Nat)
    (heap : Heap) (store : Store Unit) (s : Locals) : Prop :=
  ∀ (t : Ty) (x : Var Γ t), live x.index = true →
    (slots.getD x.index default).loc + t.width ≤ base ∧
    ∃ ws, LocalsHold s (slots.getD x.index default).loc ws ∧
      t.Rep (slots.getD x.index default).mode heap store ws (env.get x)

namespace Holds

variable {Γ : List Ty} {env : Env Γ} {slots : List Slot} {live : Nat → Bool} {base : Nat}
  {heap : Heap} {store : Store Unit} {s : Locals}

/-- `Holds` for fewer variables. -/
theorem live_mono (h : Holds env slots live base heap store s) {live' : Nat → Bool}
    (hLive : ∀ i, live' i = true → live i = true) : Holds env slots live' base heap store s :=
  fun t x hx => h t x (hLive _ hx)

theorem mono (h : Holds env slots live base heap store s) {base' : Nat} (hb : base ≤ base') :
    Holds env slots live base' heap store s :=
  fun t x hx => ⟨by have := (h t x hx).1; omega, (h t x hx).2⟩

/-- `Holds` depends only on the locals below `base`. -/
theorem agree (h : Holds env slots live base heap store s) {s' : Locals}
    (hs : ∀ j < base, s'.get j = s.get j) : Holds env slots live base heap store s' := by
  intro t x hx
  obtain ⟨hBelow, ws, hold, hRep⟩ := h t x hx
  refine ⟨hBelow, ws, fun k hk => ?_, hRep⟩
  rw [hs _ (by have := hRep.length; omega)]
  exact hold k hk

theorem frame (h : Holds env slots live base heap store s) {base' : Nat} {s' : Locals}
    (hf : Frame base' s s') (hb : base ≤ base') : Holds env slots live base heap store s' :=
  h.agree fun j hj => hf.below j (by omega)

theorem setLocal (h : Holds env slots live base heap store s) {i : Nat} {v : Value}
    (hi : base ≤ i) (hLow : s.params.length ≤ i) :
    Holds env slots live base heap store (Verified.setLocal s i v) :=
  h.agree fun j hj => Locals.get_setLocal_ne hLow (by omega)

theorem step (h : Holds env slots live base heap store s) {heap' : Heap} {store' : Store Unit}
    (hStep : Step heap store heap' store') : Holds env slots live base heap' store' s := by
  intro t x hx
  obtain ⟨hBelow, ws, hold, hRep⟩ := h t x hx
  exact ⟨hBelow, ws, hold, hRep.step hStep⟩

/-- A binding adds its value, in the locals from `base` on in mode `mode`, as variable 0. -/
theorem push {t : Ty} {v : t.denote} {mode : Mode} {live' : Nat → Bool}
    (h : Holds env slots (fun i => live' (i + 1)) base heap store s) {ws : List Value}
    (hold : LocalsHold s base ws) (hRep : t.Rep mode heap store ws v) :
    Holds (Env.cons v env) (⟨base, mode⟩ :: slots) live' (base + t.width) heap store s := by
  intro t' x hx
  cases x with
  | here => exact ⟨by simp [Var.index], ws, by simpa [Var.index] using hold, by simpa [Var.index,
      Env.get] using hRep⟩
  | there y =>
    simp only [Var.index, Env.get, List.getD_cons_succ]
    obtain ⟨hBelow, rest⟩ := h _ y hx
    exact ⟨by omega, rest⟩

end Holds


/-! The instances that Lean synthesizes for the source types, rebuilt by recursion over `Ty`, and
their agreement with the verified compiler's representation.  A function's theorem for Lean's
types follows from them, for every signature, without a proof per signature. -/

theorem Ty.scalar_pair {a b : Ty} (h : (Ty.pair a b).scalar = true) :
    a.scalar = true ∧ b.scalar = true := by
  simpa [Ty.scalar] using h

/-- The `Scalar` instance that Lean synthesizes for a type without arrays. -/
@[instance_reducible] def Ty.scalarInst : (t : Ty) → t.scalar = true → Scalar t.denote
  | .word, _ => instScalarUInt64
  | .bool, _ => @instScalarOfFlat Bool UInt64 instFlatBoolUInt64 instScalarUInt64
  | .pair a b, h => @instScalarProd a.denote b.denote (a.scalarInst (Ty.scalar_pair h).1)
      (b.scalarInst (Ty.scalar_pair h).2)
  | .array, h => absurd h (by decide)

/-- The `Represent` instance that Lean synthesizes for a type: the one from `Scalar` for a type
without arrays, and the instances for pairs and arrays otherwise. -/
@[instance_reducible] def Ty.leanInst : (t : Ty) → Represent t.denote
  | .word => @instRepresentOfScalar UInt64 instScalarUInt64
  | .bool => @instRepresentOfScalar Bool
      (@instScalarOfFlat Bool UInt64 instFlatBoolUInt64 instScalarUInt64)
  | .pair a b =>
    if h : (Ty.pair a b).scalar = true then
      @instRepresentOfScalar _ ((Ty.pair a b).scalarInst h)
    else @instRepresentProd _ _ a.leanInst b.leanInst
  | .array => instRepresentArrayUInt64

/-- The words of a value of a type without arrays. -/
theorem Ty.scalar_rep {mode : Mode} {heap : Heap} {store : Store Unit} :
    (t : Ty) → (h : t.scalar = true) → {ws : List Value} → {v : t.denote} →
      (ws = @Scalar.values _ (t.scalarInst h) v ↔ t.Rep mode heap store ws v)
  | .word, _, _, _ | .bool, _, _, _ => Iff.rfl
  | .pair a b, h, ws, p => by
    constructor
    · rintro rfl
      exact ⟨_, _, rfl, (a.scalar_rep (Ty.scalar_pair h).1).mp rfl,
        (b.scalar_rep (Ty.scalar_pair h).2).mp rfl⟩
    · rintro ⟨first, second, rfl, h1, h2⟩
      rw [(a.scalar_rep (Ty.scalar_pair h).1).mpr h1, (b.scalar_rep (Ty.scalar_pair h).2).mpr h2]
      rfl
  | .array, h, _, _ => absurd h (by decide)

theorem Ty.leanInst_scalar : (t : Ty) → (h : t.scalar = true) →
    t.leanInst = @instRepresentOfScalar _ (t.scalarInst h)
  | .word, _ | .bool, _ => rfl
  | .pair _ _, h => by rw [Ty.leanInst, dite_eq_left h]
  | .array, h => absurd h (by decide)

/-- Lean's instance agrees with the verified compiler's representation of a borrowed value. -/
theorem Ty.leanInst_borrowed {heap : Heap} {store : Store Unit} :
    (t : Ty) → {ws : List Value} → {v : t.denote} →
      (@Represent.borrowed _ t.leanInst heap store ws v ↔ t.Rep .borrowed heap store ws v)
  | .word, _, _ | .bool, _, _ | .array, _, _ => Iff.rfl
  | .pair a b, ws, p => by
    by_cases h : (Ty.pair a b).scalar = true
    · rw [(Ty.pair a b).leanInst_scalar h]
      exact (Ty.pair a b).scalar_rep h
    · rw [Ty.leanInst, dite_eq_right h]
      constructor
      · rintro ⟨first, second, rfl, h1, h2⟩
        exact ⟨first, second, rfl, a.leanInst_borrowed.mp h1, b.leanInst_borrowed.mp h2⟩
      · rintro ⟨first, second, rfl, h1, h2⟩
        exact ⟨first, second, rfl, a.leanInst_borrowed.mpr h1, b.leanInst_borrowed.mpr h2⟩

/-- Lean's instance agrees with the verified compiler's representation of an owned value whose
type holds no arrays. -/
theorem Ty.leanInst_owned {heap : Heap} {store : Store Unit} (t : Ty) (h : t.scalar = true)
    {ws : List Value} {v : t.denote} :
    @Represent.owned _ t.leanInst heap store ws v ↔ t.Rep .owned heap store ws v := by
  rw [t.leanInst_scalar h]
  exact t.scalar_rep h

theorem Ty.leanInst_blocks {store : Store Unit} (t : Ty) (h : t.scalar = true) {ws : List Value}
    {v : t.denote} : @Represent.blocks _ t.leanInst store ws v = [] := by
  rw [t.leanInst_scalar h]
  rfl

theorem Ty.leanInst_moves {store : Store Unit} :
    (t : Ty) → {ws : List Value} → {v : t.denote} → @Represent.moves _ t.leanInst store ws v = []
  | .word, _, _ | .bool, _, _ | .array, _, _ => rfl
  | .pair a b, ws, p => by
    by_cases h : (Ty.pair a b).scalar = true
    · rw [(Ty.pair a b).leanInst_scalar h]
      rfl
    · rw [Ty.leanInst, dite_eq_right h]
      show @Represent.moves _ a.leanInst store _ p.1 ++ @Represent.moves _ b.leanInst store _ p.2 = []
      rw [a.leanInst_moves, b.leanInst_moves]
      rfl

/-- The Lean type of a function's arguments: `Unit` for none, the parameter's type for one, and
the right-nested product of the parameters' types for more. -/
abbrev argsTy : List Ty → Type
  | [] => Unit
  | [t] => t.denote
  | t :: u :: ts => t.denote × argsTy (u :: ts)

/-- The `Scalar` instance that Lean synthesizes for arguments without arrays. -/
@[instance_reducible] def argsScalarInst : (ps : List Ty) → ps.all Ty.scalar = true →
    Scalar (argsTy ps)
  | [], _ => instScalarUnit
  | [t], h => t.scalarInst (by simpa using h)
  | t :: u :: ts, h => @instScalarProd t.denote (argsTy (u :: ts))
      (t.scalarInst (by simp at h; exact h.1))
      (argsScalarInst (u :: ts) (by simp at h ⊢; exact h.2))

/-- The `Represent` instance that Lean synthesizes for a function's arguments. -/
@[instance_reducible] def argsInst : (ps : List Ty) → Represent (argsTy ps)
  | [] => @instRepresentOfScalar Unit instScalarUnit
  | [t] => t.leanInst
  | t :: u :: ts =>
    if h : (t :: u :: ts).all Ty.scalar = true then
      @instRepresentOfScalar _ (argsScalarInst (t :: u :: ts) h)
    else @instRepresentProd _ _ t.leanInst (argsInst (u :: ts))

/-- The values of a function's arguments, from Lean's argument tuple. -/
def Env.ofArgs : (ps : List Ty) → argsTy ps → Env ps
  | [], _ => .nil
  | [_], x => .cons x .nil
  | _ :: u :: ts, x => .cons x.1 (Env.ofArgs (u :: ts) x.2)

theorem argsScalar_rep {mode : Mode} {heap : Heap} {store : Store Unit} :
    (ps : List Ty) → (h : ps.all Ty.scalar = true) → {ws : List Value} → {y : argsTy ps} →
      (ws = @Scalar.values _ (argsScalarInst ps h) y ↔
        Env.Rep mode heap store ws (Env.ofArgs ps y))
  | [], _, _, _ => Iff.rfl
  | [t], h, ws, y => by
    rw [show (@Scalar.values _ (argsScalarInst [t] h) y) =
      @Scalar.values _ (t.scalarInst (by simpa using h)) y from rfl, t.scalar_rep]
    constructor
    · intro hy; exact ⟨ws, [], by simp, hy, rfl⟩
    · rintro ⟨first, rest, rfl, h1, rfl⟩; simpa using h1
  | t :: u :: ts, h, ws, y => by
    constructor
    · rintro rfl
      exact ⟨_, _, rfl, (t.scalar_rep _).mp rfl, (argsScalar_rep (u :: ts) _).mp rfl⟩
    · rintro ⟨first, rest, rfl, h1, h2⟩
      rw [(t.scalar_rep _).mpr h1, (argsScalar_rep (u :: ts) _).mpr h2]
      rfl

theorem argsInst_scalar : (ps : List Ty) → (h : ps.all Ty.scalar = true) →
    argsInst ps = @instRepresentOfScalar _ (argsScalarInst ps h)
  | [], _ => rfl
  | [t], h => t.leanInst_scalar (by simpa using h)
  | _ :: _ :: _, h => by rw [argsInst, dite_eq_left h]

/-- Lean's instance for the arguments agrees with the verified compiler's representation. -/
theorem argsInst_borrowed {heap : Heap} {store : Store Unit} :
    (ps : List Ty) → {ws : List Value} → {y : argsTy ps} →
      (@Represent.borrowed _ (argsInst ps) heap store ws y ↔
        Env.Rep .borrowed heap store ws (Env.ofArgs ps y))
  | [], _, _ => Iff.rfl
  | [t], ws, y => by
    rw [show (@Represent.borrowed _ (argsInst [t]) heap store ws y) =
      @Represent.borrowed _ t.leanInst heap store ws y from rfl, t.leanInst_borrowed]
    constructor
    · intro hy; exact ⟨ws, [], by simp, hy, rfl⟩
    · rintro ⟨first, rest, rfl, h1, rfl⟩; simpa using h1
  | t :: u :: ts, ws, y => by
    by_cases h : (t :: u :: ts).all Ty.scalar = true
    · rw [argsInst_scalar _ h]
      exact argsScalar_rep _ h
    · rw [argsInst, dite_eq_right h]
      constructor
      · rintro ⟨first, rest, rfl, h1, h2⟩
        exact ⟨first, rest, rfl, t.leanInst_borrowed.mp h1, (argsInst_borrowed (u :: ts)).mp h2⟩
      · rintro ⟨first, rest, rfl, h1, h2⟩
        exact ⟨first, rest, rfl, t.leanInst_borrowed.mpr h1,
          (argsInst_borrowed (u :: ts)).mpr h2⟩

theorem argsInst_moves {store : Store Unit} :
    (ps : List Ty) → {ws : List Value} → {y : argsTy ps} →
      @Represent.moves _ (argsInst ps) store ws y = []
  | [], _, _ => rfl
  | [t], _, _ => t.leanInst_moves
  | t :: u :: ts, ws, y => by
    by_cases h : (t :: u :: ts).all Ty.scalar = true
    · rw [argsInst_scalar _ h]
      rfl
    · rw [argsInst, dite_eq_right h]
      show @Represent.moves _ t.leanInst store _ y.1 ++
        @Represent.moves _ (argsInst (u :: ts)) store _ y.2 = []
      rw [t.leanInst_moves, argsInst_moves (u :: ts)]
      rfl

end Verified
