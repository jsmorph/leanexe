import LeanExe.TalosCompat

namespace Verified

open Wasm

/-- The local that holds a word of type `ty` at position `p` of a function with `h` positions:
local `p` for an i64, `p + h` for an f64, and `p + 2 * h` for an f32.  Each bank
has one local per position, with the parameters occupying the beginning of the first bank. -/
def slotIndex (h p : Nat) : ValueType → Nat
  | .f64 => p + h
  | .f32 => p + 2 * h
  | _ => p

/-- The number of positions in the i64, f64, and f32 local banks. -/
def _root_.Wasm.Locals.positions (s : Locals) : Nat := (s.params.length + s.locals.length) / 3

/-- `after` agrees with `before` on the parameters, the number of locals, and all three locals of every
position below `base`: the code of an expression with scratch from `base` on changes nothing
else. -/
structure Frame (base : Nat) (before after : Locals) : Prop where
  params : after.params = before.params
  length : after.locals.length = before.locals.length
  below : ∀ j < base,
    after.get j = before.get j ∧ after.get (j + before.positions) = before.get (j + before.positions)
  below32 : ∀ j < base,
    after.get (j + 2 * before.positions) = before.get (j + 2 * before.positions)

theorem Frame.positions {base : Nat} {s s' : Locals} (h : Frame base s s') : s'.positions = s.positions := by
  simp [Locals.positions, h.params, h.length]

theorem Frame.refl (base : Nat) (s : Locals) : Frame base s s :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩

theorem Frame.trans {base : Nat} {s1 s2 s3 : Locals} (h1 : Frame base s1 s2)
    (h2 : Frame base s2 s3) : Frame base s1 s3 :=
  ⟨h2.params.trans h1.params, h2.length.trans h1.length, fun j hj =>
    ⟨(h2.below j hj).1.trans (h1.below j hj).1, by
      have := (h2.below j hj).2
      rw [h1.positions] at this
      exact this.trans (h1.below j hj).2⟩, fun j hj => by
        have h := h2.below32 j hj
        rw [h1.positions] at h
        exact h.trans (h1.below32 j hj)⟩

/-- The operand stack plays no part in a frame. -/
theorem Frame.values {base : Nat} {s s' : Locals} {values : List Value}
    (h : Frame base { s with values } s') : Frame base s s' :=
  ⟨h.params, h.length, h.below, h.below32⟩

theorem Frame.ofValues {base : Nat} {s : Locals} {values : List Value} :
    Frame base s { s with values } :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩

theorem Frame.mono {base base' : Nat} {s s' : Locals} (h : Frame base' s s') (hb : base ≤ base') :
    Frame base s s' :=
  ⟨h.params, h.length, fun j hj => h.below j (by omega),
    fun j hj => h.below32 j (by omega)⟩

theorem Frame.slot {base p : Nat} {s s' : Locals} (h : Frame base s s')
    (hp : p < base) (ty : ValueType) :
    s'.get (slotIndex s.positions p ty) = s.get (slotIndex s.positions p ty) := by
  cases ty <;> simp only [slotIndex] <;>
    first | exact (h.below p hp).1 | exact (h.below p hp).2 | exact h.below32 p hp

@[simp] theorem Locals.get_values (s : Locals) (vs : List Value) (i : Nat) :
    ({ s with values := vs } : Locals).get i = s.get i := rfl

@[simp] theorem Locals.positions_values (s : Locals) (vs : List Value) :
    ({ s with values := vs } : Locals).positions = s.positions := rfl

/-- Local `i`, past the parameters, after a store of `v`. -/
def setLocal (s : Locals) (i : Nat) (v : Value) : Locals :=
  { s with locals := s.locals.set (i - s.params.length) v }

@[simp] theorem Locals.positions_setLocal (s : Locals) (i : Nat) (v : Value) :
    (setLocal s i v).positions = s.positions := by
  simp [Locals.positions, setLocal]

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

/-- A store to an i64 local of a position at or above `base` keeps the frame below `base`. -/
theorem Frame.set {base : Nat} {s : Locals} {i : Nat} {v : Value}
    (hLow : s.params.length ≤ i) (hBase : base ≤ i) (hHigh : i < s.positions) :
    Frame base s (setLocal s i v) :=
  ⟨rfl, by simp [Verified.setLocal], fun j hj =>
    ⟨Locals.get_setLocal_ne hLow (by omega), Locals.get_setLocal_ne hLow (by omega)⟩,
    fun j hj => Locals.get_setLocal_ne hLow (by omega)⟩

/-- A store, with a new operand stack, to an i64 local of a position at or above `base`. -/
theorem Frame.setValues {base : Nat} {s : Locals} {vs : List Value} {i : Nat} {v : Value}
    (hLow : s.params.length ≤ i) (hBase : base ≤ i) (hHigh : i < s.positions) :
    Frame base s (setLocal { s with values := vs } i v) :=
  Frame.ofValues.trans (@Frame.set base { s with values := vs } i v hLow hBase hHigh)

/-- Locals that differ from `s` at most in local `index`, at or above `base` and below the position bound,
agree with `s` below `base`. -/
theorem Frame.ofOthers {base index : Nat} {s s' : Locals} (hp : s'.params = s.params)
    (hl : s'.locals.length = s.locals.length) (hOther : ∀ j, j ≠ index → s'.get j = s.get j)
    (hBase : base ≤ index) (hHalf : index < s.positions) : Frame base s s' :=
  ⟨hp, hl, fun j hj => ⟨hOther j (by omega), hOther _ (by omega)⟩,
    fun j hj => hOther _ (by omega)⟩

theorem Frame.setSlot {base p : Nat} {s : Locals} {v : Value} (ty : ValueType)
    (hLow : s.params.length ≤ slotIndex s.positions p ty) (hBase : base ≤ p)
    (hHigh : p < s.positions) : Frame base s (setLocal s (slotIndex s.positions p ty) v) := by
  refine ⟨rfl, by simp [setLocal], (fun j hj => ⟨?_, ?_⟩), (fun j hj => ?_)⟩ <;>
    apply Locals.get_setLocal_ne hLow <;> cases ty <;> simp only [slotIndex] <;> omega

/-- A position below the position bound has its i64 local among the locals. -/
theorem Locals.lt_total {s : Locals} {i : Nat} (h : i < s.positions) :
    i < s.params.length + s.locals.length := by
  simp only [Locals.positions] at h; omega

/-- The local of position `p` for a word of type `ty` lies past the parameters and among the
locals when the position does. -/
theorem slotIndex_bounds {s : Locals} {p : Nat} (ty : ValueType) (hLow : s.params.length ≤ p)
    (hHigh : p < s.positions) :
    s.params.length ≤ slotIndex s.positions p ty ∧
      slotIndex s.positions p ty < s.params.length + s.locals.length := by
  have : 3 * s.positions ≤ s.params.length + s.locals.length := by
    simp only [Locals.positions]; omega
  cases ty <;> simp only [slotIndex] <;> omega

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

theorem wrap_toUInt32 (a : UInt64) : UInt32.ofNat (a.toNat % 2 ^ 32) = a.toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp [UInt64.toNat_toUInt32]

theorem wrap_toUInt32_num (a : UInt64) :
    UInt32.ofNat (a.toNat % 4294967296) = a.toUInt32 := wrap_toUInt32 a


end Verified
