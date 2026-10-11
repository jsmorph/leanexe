import Verified.After

/-! The potential of owned arrays, which pays for the moves of an array that grows.  An owned
array of `n` words at `p` has the potential `4u ∸ 2c`, with `u = 8 (n + 1)` the bytes of its length
word and words and `c` the capacity of its block.  The block holds the array, so `c ≥ u` and the
potential is at most `2u`.  A growth of an array whose potential is counted, a paid array, raises
`top` and the potential together by at most `48` plus four times the added bytes, since a move
requests twice the capacity.  `Env.pot` sums the potential of the variables that a selection
picks, from their words at their slots. -/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

/-- The words of types `tys` at the positions from `loc` on. -/
def _root_.Wasm.Locals.read (s : Locals) (loc : Nat) (tys : List ValueType) : List Value :=
  (List.range tys.length).map fun k =>
    (s.get (slotIndex s.half (loc + k) (tys.getD k .i64))).getD (.i64 0)

theorem _root_.Wasm.Locals.read_length (s : Locals) (loc : Nat) (tys : List ValueType) :
    (s.read loc tys).length = tys.length := by
  simp [Locals.read]

/-- Positions that hold words of given types hold the words that `Locals.read` reads. -/
theorem LocalsHold.read_eq {s : Locals} {loc : Nat} {tys : List ValueType} {ws : List Value}
    (h : LocalsHold s loc tys ws) (hl : ws.length = tys.length) : s.read loc tys = ws := by
  apply List.ext_getElem (by rw [Locals.read_length, hl])
  intro k hk1 hk2
  simp only [Locals.read, List.getElem_map, List.getElem_range]
  rw [h k hk2]
  rfl

/-- The potential of an owned array of `n` words at `ptr`. -/
def arrayPot (store : Store Unit) (ptr : UInt64) (n : Nat) : Nat :=
  4 * (8 * (n + 1)) - 2 * capacityAt store ptr

/-- The potential of the arrays of a value with the words `ws`. -/
def Ty.pot (store : Store Unit) : (t : Ty) → List Value → t.denote → Nat
  | .elem _, _, _ => 0
  | .pair a b, ws, p => a.pot store (ws.take a.width) p.1 + b.pot store (ws.drop a.width) p.2
  | .array e, ws, xs => match ws with
    | [.i64 ptr] => arrayPot store ptr (e.words xs).size
    | _ => 0

/-- The potential of variable `x`, from its words at its slot. -/
def Env.potOf (store : Store Unit) (s : Locals) {Γ : List Ty} (env : Env Γ) (slots : List Slot)
    {t : Ty} (x : Var Γ t) : Nat :=
  t.pot store (s.read (slots.getD x.index default).loc t.types) (env.get x)

/-- The potential of the variables that `sel` picks, from their words at their slots. -/
def Env.pot (store : Store Unit) (s : Locals) :
    {Γ : List Ty} → Env Γ → List Slot → (Nat → Bool) → Nat
  | [], .nil, _, _ => 0
  | t :: _, .cons v rest, slots, sel =>
    (if sel 0 then t.pot store (s.read (slots.getD 0 default).loc t.types) v else 0) +
      rest.pot store s slots.tail (fun i => sel (i + 1))

theorem Ty.blocks_length (store store' : Store Unit) :
    (t : Ty) → (ws : List Value) → (v : t.denote) →
    (t.blocks store' ws v).length = (t.blocks store ws v).length
  | .elem _, _, _ => rfl
  | .pair a b, _, _ => by
    simp [Ty.blocks, Ty.blocks_length store store' a, Ty.blocks_length store store' b]
  | .array _, ws, _ => by
    simp only [Ty.blocks]
    split <;> rfl

/-- A change of store that keeps a value's blocks keeps its potential, since the blocks hold the
capacities. -/
theorem Ty.pot_of_blocks {store store' : Store Unit} :
    (t : Ty) → (ws : List Value) → (v : t.denote) →
    t.blocks store' ws v = t.blocks store ws v → t.pot store' ws v = t.pot store ws v
  | .elem _, _, _, _ => rfl
  | .pair a b, _, _, h => by
    simp only [Ty.blocks] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (Ty.blocks_length store store' a _ _)
    simp only [Ty.pot, Ty.pot_of_blocks a _ _ h1, Ty.pot_of_blocks b _ _ h2]
  | .array _, ws, _, h => by
    simp only [Ty.blocks] at h
    simp only [Ty.pot]
    split at h
    · simp only [List.cons.injEq, block, Prod.mk.injEq, and_true] at h
      simp only [arrayPot]
      omega
    · split <;> simp_all

theorem getD_tail {α : Type} (l : List α) (i : Nat) (d : α) :
    l.tail.getD i d = l.getD (i + 1) d := by
  cases l <;> simp

namespace Env

variable {store store' : Store Unit} {s s' : Locals}

theorem pot_congr : {Γ : List Ty} → (env : Env Γ) → (slots slots' : List Slot) →
    (sel : Nat → Bool) →
    (∀ (t : Ty) (x : Var Γ t), sel x.index = true →
      env.potOf store s slots x = env.potOf store' s' slots' x) →
    env.pot store s slots sel = env.pot store' s' slots' sel
  | [], .nil, _, _, _, _ => rfl
  | t :: _, .cons v rest, slots, slots', sel, h => by
    simp only [Env.pot]
    have h0 : (if sel 0 then t.pot store (s.read (slots.getD 0 default).loc t.types) v else 0) =
        (if sel 0 then t.pot store' (s'.read (slots'.getD 0 default).loc t.types) v else 0) := by
      split
      · next h0 => exact h t .here h0
      · rfl
    rw [h0, pot_congr rest slots.tail slots'.tail _ fun u x hx => by
      have := h u (.there x) hx
      simpa [Env.potOf, Var.index, Env.get, getD_tail] using this]

theorem pot_ext : {Γ : List Ty} → (env : Env Γ) → (slots : List Slot) → (sel sel' : Nat → Bool) →
    (∀ i < Γ.length, sel i = sel' i) → env.pot store s slots sel = env.pot store s slots sel'
  | [], .nil, _, _, _, _ => rfl
  | _ :: _, .cons _ rest, slots, sel, sel', h => by
    simp only [Env.pot]
    rw [h 0 (by simp), pot_ext rest slots.tail _ _ fun i hi => h (i + 1) (by simp; omega)]

theorem pot_or : {Γ : List Ty} → (env : Env Γ) → (slots : List Slot) → (sel1 sel2 : Nat → Bool) →
    (∀ i, sel1 i = true → sel2 i = false) →
    env.pot store s slots (fun i => sel1 i || sel2 i) =
      env.pot store s slots sel1 + env.pot store s slots sel2
  | [], .nil, _, _, _, _ => rfl
  | _ :: _, .cons _ rest, slots, sel1, sel2, h => by
    simp only [Env.pot]
    rw [pot_or rest slots.tail _ _ fun i hi => h (i + 1) hi]
    have h0 := h 0
    cases h1 : sel1 0 <;> cases h2 : sel2 0 <;> simp_all <;> omega

theorem pot_mono : {Γ : List Ty} → (env : Env Γ) → (slots : List Slot) → (sel sel' : Nat → Bool) →
    (∀ i, sel i = true → sel' i = true) →
    env.pot store s slots sel ≤ env.pot store s slots sel'
  | [], .nil, _, _, _, _ => le_rfl
  | _ :: _, .cons _ rest, slots, sel, sel', h => by
    simp only [Env.pot]
    have := pot_mono rest slots.tail _ _ fun i hi => h (i + 1) hi
    have h0 := h 0
    cases h1 : sel 0 <;> cases h2 : sel' 0 <;> simp_all
    omega

theorem pot_none : {Γ : List Ty} → (env : Env Γ) → (slots : List Slot) → (sel : Nat → Bool) →
    (∀ i, sel i = false) → env.pot store s slots sel = 0
  | [], .nil, _, _, _ => rfl
  | _ :: _, .cons _ rest, slots, sel, h => by
    simp only [Env.pot, h 0, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact pot_none rest slots.tail _ fun i => h (i + 1)

theorem pot_single : {Γ : List Ty} → {t : Ty} → (env : Env Γ) → (slots : List Slot) →
    (x : Var Γ t) → env.pot store s slots (fun i => i == x.index) = env.potOf store s slots x
  | _ :: _, _, .cons _ rest, slots, .here => by
    simp only [Env.pot, Var.index, beq_self_eq_true, ↓reduceIte, Env.potOf, Env.get]
    rw [pot_none rest slots.tail _ fun i => by simp]
    rfl
  | _ :: _, _, .cons _ rest, slots, .there x => by
    have ih := pot_single rest slots.tail x
    have hf : (fun i => i + 1 == x.index + 1) = (fun i => i == x.index) := by funext i; simp
    simp only [Env.pot, Var.index, hf, ih]
    simp [Env.potOf, Var.index, Env.get]

/-- The potential of variables that stay live and owned across a step that keeps the regions apart
from the variables that die, with the locals kept below `base`, is unchanged: their words stay in
their slots, and the step keeps their blocks. -/
theorem pot_step {Γ : List Ty} {env : Env Γ} {slots : List Slot} {liveIn live : Nat → Bool}
    {base : Nat} {heap heap' : Heap} {fresh : List (Nat × Nat)}
    (h : Holds env slots liveIn base heap store s)
    (hStep : Step heap store (Holds.KeepDying env slots liveIn live store s) heap' store' fresh)
    (hFrame : Frame base s s')
    (hLive : ∀ i, live i = true → liveIn i = true) (sel : Nat → Bool)
    (hSel : ∀ i, sel i = true → live i = true ∧ (slots.getD i default).mode = .owned) :
    env.pot store' s' slots sel = env.pot store s slots sel := by
  refine pot_congr env slots slots sel fun u x hx => ?_
  obtain ⟨hxLive, hxOwned⟩ := hSel _ hx
  obtain ⟨hBelow, wx, hold, hRep⟩ := h.get x (hLive _ hxLive)
  have hl : wx.length = u.width := hRep.length
  have hold' := (h.hold_agree hFrame (hLive _ hxLive) hl).mpr hold
  have hSame := (h.regions_after hStep (hLive _ hxLive) hold hl
    (h.keepDying hLive hxLive hold hl)).1
  simp only [Ty.regions, hxOwned] at hSame
  simp only [Env.potOf, hold.read_eq (by rw [hl, Ty.types_length]),
    hold'.read_eq (by rw [hl, Ty.types_length])]
  exact Ty.pot_of_blocks u wx _ hSame

theorem pot_values {Γ : List Ty} (env : Env Γ) (slots : List Slot) (sel : Nat → Bool)
    (vs : List Value) :
    env.pot store { s with values := vs } slots sel = env.pot store s slots sel :=
  pot_congr env slots slots sel fun _ _ _ => by simp [Env.potOf, Locals.read]

end Env

/-- The potential of the paid owned variables live in `liveIn` and not in `liveOut`, those that
die between the two. -/
def dyingPot {Γ : List Ty} (store : Store Unit) (s : Locals) (env : Env Γ) (slots : List Slot)
    (paid : List Bool) (liveIn liveOut : Nat → Bool) : Nat :=
  env.pot store s slots fun i =>
    liveIn i && !liveOut i && paidAt paid i && (slots.getD i default).mode == .owned

section Dying

variable {Γ : List Ty} {store store' : Store Unit} {s s' : Locals} {env : Env Γ}
  {slots : List Slot} {paid : List Bool}

/-- The variables that die across two codes in a row are those that die in the first and those
that die in the second, for the live sets `L0 ⊇ L1 ⊇ L2` before, between, and after them. -/
theorem dyingPot_split (L0 L1 L2 : Nat → Bool) (h01 : ∀ i, L1 i = true → L0 i = true)
    (h12 : ∀ i, L2 i = true → L1 i = true) :
    dyingPot store s env slots paid L0 L2 =
      dyingPot store s env slots paid L0 L1 + dyingPot store s env slots paid L1 L2 := by
  simp only [dyingPot]
  rw [← Env.pot_or env slots _ _ fun i h1 => by
    have := h12 i
    cases h0 : L0 i <;> cases hl1 : L1 i <;> cases hl2 : L2 i <;> simp_all]
  refine Env.pot_ext env slots _ _ fun i _ => ?_
  have := h01 i
  have := h12 i
  cases h0 : L0 i <;> cases hl1 : L1 i <;> cases hl2 : L2 i <;> simp_all

theorem dyingPot_congr {L0 L0' L1 L1' : Nat → Bool} (h0 : ∀ i, L0 i = L0' i)
    (h1 : ∀ i, L1 i = L1' i) :
    dyingPot store s env slots paid L0 L1 = dyingPot store s env slots paid L0' L1' := by
  simp only [dyingPot]
  exact Env.pot_ext env slots _ _ fun i _ => by rw [h0, h1]

theorem dyingPot_values (L0 L1 : Nat → Bool) (vs : List Value) :
    dyingPot store { s with values := vs } env slots paid L0 L1 =
      dyingPot store s env slots paid L0 L1 :=
  Env.pot_values env slots _ vs

theorem dyingPot_le (L0 L1 : Nat → Bool) (L0' L1' : Nat → Bool)
    (h : ∀ i, L0 i = true → L1 i = false → L0' i = true ∧ L1' i = false) :
    dyingPot store s env slots paid L0 L1 ≤ dyingPot store s env slots paid L0' L1' := by
  simp only [dyingPot]
  refine Env.pot_mono env slots _ _ fun i hi => ?_
  have := h i
  cases hl0 : L0 i <;> cases hl1 : L1 i <;> simp_all

/-- More variables die between a larger live set before and a smaller one after. -/
theorem dyingPot_mono {L0 L1 L0' L1' : Nat → Bool} (h0 : ∀ i, L0 i = true → L0' i = true)
    (h1 : ∀ i, L1' i = true → L1 i = true) :
    dyingPot store s env slots paid L0 L1 ≤ dyingPot store s env slots paid L0' L1' :=
  dyingPot_le _ _ _ _ fun i hi hl => ⟨h0 i hi, by
    cases h : L1' i
    · rfl
    · rw [h1 i h] at hl; exact hl⟩

/-- A step that keeps the regions apart from the variables that die in it keeps the potential of
the variables live after it. -/
theorem dyingPot_step {liveIn live : Nat → Bool} {base : Nat} {heap heap' : Heap}
    {fresh : List (Nat × Nat)} (h : Holds env slots liveIn base heap store s)
    (hStep : Step heap store (Holds.KeepDying env slots liveIn live store s) heap' store' fresh)
    (hFrame : Frame base s s') (hLive : ∀ i, live i = true → liveIn i = true)
    (L1 L2 : Nat → Bool) (hL1 : ∀ i, L1 i = true → live i = true) :
    dyingPot store' s' env slots paid L1 L2 = dyingPot store s env slots paid L1 L2 :=
  Env.pot_step h hStep hFrame hLive _ fun i hi => by
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hi
    exact ⟨hL1 i hi.1.1.1, hi.2⟩

/-- `dyingPot_step` for a code with the facts of `After`. -/
theorem dyingPot_after {liveIn live : Nat → Bool} {base : Nat} {heap heap' : Heap} {t : Ty}
    {mode : Mode} {v : t.denote} {ws : List Value}
    (h : Holds env slots liveIn base heap store s)
    (a : After env slots liveIn live base heap store s t mode v heap' store' s' ws)
    (hLive : ∀ i, live i = true → liveIn i = true) (L1 L2 : Nat → Bool)
    (hL1 : ∀ i, L1 i = true → live i = true) :
    dyingPot store' s' env slots paid L1 L2 = dyingPot store s env slots paid L1 L2 :=
  dyingPot_step h a.step a.frame hLive L1 L2 hL1

/-- `dyingPot_step` for a code with the facts of `Evolves`. -/
theorem dyingPot_evolves {liveIn live : Nat → Bool} {base : Nat} {heap heap' : Heap}
    (h : Holds env slots liveIn base heap store s)
    (e : Evolves env slots liveIn live base heap store s heap' store' s')
    (hLive : ∀ i, live i = true → liveIn i = true) (L1 L2 : Nat → Bool)
    (hL1 : ∀ i, L1 i = true → live i = true) :
    dyingPot store' s' env slots paid L1 L2 = dyingPot store s env slots paid L1 L2 :=
  dyingPot_step h e.step e.frame hLive L1 L2 hL1

/-- A paid owned variable that dies is among those whose potential `dyingPot` counts. -/
theorem dyingPot_var {liveIn liveOut : Nat → Bool} {t : Ty} (x : Var Γ t)
    (hIn : liveIn x.index = true) (hOut : liveOut x.index = false)
    (hPaid : paidAt paid x.index = true) (hOwned : (slots.getD x.index default).mode = .owned) :
    env.potOf store s slots x ≤ dyingPot store s env slots paid liveIn liveOut := by
  rw [← Env.pot_single env slots x]
  exact Env.pot_mono env slots _ _ fun i hi => by
    simp only [beq_iff_eq] at hi
    subst hi
    simp only [hIn, hOut, hPaid, hOwned, Bool.not_false, Bool.and_self, beq_self_eq_true]

/-- The potential of the variables of a context with one more variable, the new variable 0
first. -/
theorem dyingPot_cons {t : Ty} (v : t.denote) (sl : Slot) (p : Bool) (L0 L1 : Nat → Bool) :
    dyingPot store s (Env.cons v env) (sl :: slots) (p :: paid) L0 L1 =
      (if (L0 0 && !L1 0 && p && sl.mode == .owned) = true then
          t.pot store (s.read sl.loc t.types) v else 0) +
        dyingPot store s env slots paid (fun i => L0 (i + 1)) (fun i => L1 (i + 1)) := by
  simp only [dyingPot, Env.pot, paidAt]
  rfl

/-- No variable dies between a live set and a larger one. -/
theorem dyingPot_eq_zero {L0 L1 : Nat → Bool} (h : ∀ i, L0 i = true → L1 i = true) :
    dyingPot store s env slots paid L0 L1 = 0 :=
  Env.pot_none env slots _ fun i => by
    cases h0 : L0 i
    · simp
    · simp [h i h0]

/-- No paid variable dies when each variable that dies is unpaid. -/
theorem dyingPot_eq_zero_unpaid {L0 L1 : Nat → Bool}
    (h : ∀ i, L0 i = true → L1 i = false → paidAt paid i = false) :
    dyingPot store s env slots paid L0 L1 = 0 :=
  Env.pot_none env slots _ fun i => by
    cases h0 : L0 i
    · simp
    · cases h1 : L1 i
      · simp [h i h0 h1]
      · simp

/-- No variable is paid without flags. -/
theorem dyingPot_nil (L0 L1 : Nat → Bool) : dyingPot store s env slots [] L0 L1 = 0 :=
  Env.pot_none env slots _ fun i => by simp [paidAt]

end Dying

end Verified
