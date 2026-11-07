import LeanExe.M7.Proof.Memory
import LeanExe.M7.Gen
import LeanExe.ProofKit.Typed
import Interpreter.Wasm.Semantics

/-!
The relation of the simulation proof between a Talos frame and a state of the Cortex-M7 model, at
a point of a function's code whose operand stack has a known height.  Every value lies in a slot
of 8 bytes relative to SP, its low word first: the value at height `h`, counted from the bottom,
in the operand slot of `h`, a parameter in the caller's outgoing area above the frame, and a
declared local that the body names in its slot of the frame.  `SlotRel` relates a Talos value to
the slot's words: an `i32` in the low word with a high word of 0, an `i64` as its low and high
words.  A declared local that the body never names has no slot, and the relation says nothing of
it.  `FrameOk` states that SP is a multiple of 4, that the frame and the parameters above it are
`Ram` below 2^32, and that the stack's limit lies from 4096 up to SP with `Ram` from it to SP.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit

/-! ## Slots -/

/-- The words `lo` and `hi` of a slot hold the Talos value `v`. -/
def SlotRel : Value → UInt32 → UInt32 → Prop
  | .i32 x, lo, hi => lo = x ∧ hi = 0
  | .i64 x, lo, hi => lo = x.toUInt32 ∧ hi = (x >>> 32).toUInt32
  | _, _, _ => False

/-- The slot at the offset `o` from SP holds `v`. -/
def ValAt (s : State) (o : Nat) (v : Value) : Prop :=
  SlotRel v (load32 s.mem (s.sp + UInt32.ofNat o)) (load32 s.mem (s.sp + UInt32.ofNat (o + 4)))

/-- The two words of the slot at the offset `o` from SP have in `t` the values that they have in
`s`, where `t` has the SP of `s`. -/
def SlotSame (s t : State) (o : Nat) : Prop :=
  load32 t.mem (s.sp + UInt32.ofNat o) = load32 s.mem (s.sp + UInt32.ofNat o) ∧
    load32 t.mem (s.sp + UInt32.ofNat (o + 4)) = load32 s.mem (s.sp + UInt32.ofNat (o + 4))

theorem ValAt.congr {s t : State} {o : Nat} {v : Value} (h : ValAt s o v) (hsp : t.sp = s.sp)
    (hs : SlotSame s t o) : ValAt t o v := by
  unfold ValAt
  rw [hsp, hs.1, hs.2]
  exact h

theorem SlotSame.refl (s : State) (o : Nat) : SlotSame s s o := ⟨rfl, rfl⟩

theorem SlotSame.trans {s t u : State} {o : Nat} (h1 : SlotSame s t o) (h2 : SlotSame t u o)
    (hsp : t.sp = s.sp) : SlotSame s u o := by
  unfold SlotSame at *
  rw [hsp] at h2
  exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem slotRel_zero {t : ValueType} (ht : intType t = true) : SlotRel t.zero 0 0 := by
  cases t <;> simp [intType] at ht <;> exact ⟨rfl, rfl⟩

theorem hasType_zero {t : ValueType} (ht : intType t = true) : HasType t t.zero := by
  cases t <;> simp [intType] at ht <;> trivial

/-! ## Addresses -/

/-- The distance between two offsets from SP, modulo 2^32. -/
theorem toNat_sub_offsets (sp : UInt32) {x o : Nat} (hx : x < 4294967296) (ho : o < 4294967296) :
    (sp + UInt32.ofNat o - (sp + UInt32.ofNat x)).toNat = (o + 4294967296 - x) % 4294967296 := by
  have := toNat_lt32 sp
  rw [UInt32.toNat_sub, UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_ofNat',
    UInt32.toNat_ofNat']
  simp only [Nat.reducePow]
  omega

/-- A word store at the offset `x` from SP leaves the word at the offset `o` when their four
bytes do not overlap. -/
theorem load32_store32_off {m : UInt32 → UInt8} {sp v : UInt32} {x o : Nat}
    (hx : x + 4 ≤ 4294967296) (ho : o + 4 ≤ 4294967296) (hd : o + 4 ≤ x ∨ x + 4 ≤ o) :
    load32 (store32 m (sp + UInt32.ofNat x) v) (sp + UInt32.ofNat o) =
      load32 m (sp + UInt32.ofNat o) := by
  apply load32_store32_far <;> rw [toNat_sub_offsets sp (by omega) (by omega)] <;> omega

/-- Stores of two words at the offsets `x` and `x + 4` from SP leave the slot at the offset `o`
when the two slots do not overlap. -/
theorem slotSame_store2 {s t : State} {x o : Nat} {w0 w1 : UInt32}
    (hmem : t.mem = store32 (store32 s.mem (s.sp + UInt32.ofNat x) w0)
      (s.sp + UInt32.ofNat (x + 4)) w1)
    (hx : x + 8 ≤ 4294967296) (ho : o + 8 ≤ 4294967296) (hd : o + 8 ≤ x ∨ x + 8 ≤ o) :
    SlotSame s t o := by
  unfold SlotSame
  rw [hmem]
  constructor <;>
    rw [load32_store32_off (by omega) (by omega) (by omega),
      load32_store32_off (by omega) (by omega) (by omega)]

/-- Stores of two words at the offsets `x` and `x + 4` from SP give the slot at `x` those words. -/
theorem valAt_store2 {s t : State} {x : Nat} {w0 w1 : UInt32} {v : Value} (hsp : t.sp = s.sp)
    (hmem : t.mem = store32 (store32 s.mem (s.sp + UInt32.ofNat x) w0)
      (s.sp + UInt32.ofNat (x + 4)) w1)
    (hx : x + 8 ≤ 4294967296) (hv : SlotRel v w0 w1) : ValAt t x v := by
  unfold ValAt
  rw [hsp, hmem, load32_store32, load32_store32_off (by omega) (by omega) (by omega),
    load32_store32]
  exact hv

theorem toNat_add_ofNat {a : UInt32} {k : Nat} (h : a.toNat + k < 4294967296) :
    (a + UInt32.ofNat k).toNat = a.toNat + k := by
  rw [UInt32.toNat_add, UInt32.toNat_ofNat']
  simp only [Nat.reducePow]
  omega

/-- A word whose four bytes keep their values keeps its value. -/
theorem load32_congr {m m' : UInt32 → UInt8} {a : UInt32}
    (h : ∀ k < 4, m' (a + UInt32.ofNat k) = m (a + UInt32.ofNat k)) : load32 m' a = load32 m a := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  rw [show UInt32.ofNat 0 = 0 from rfl, UInt32.add_zero] at h0
  rw [show UInt32.ofNat 1 = 1 from rfl] at h1
  rw [show UInt32.ofNat 2 = 2 from rfl] at h2
  rw [show UInt32.ofNat 3 = 3 from rfl] at h3
  unfold load32
  rw [h0, h1, h2, h3]

/-! ## Frames -/

/-- The offset from SP of the operand slot of height `h`. -/
def Frame.opAt (fr : Frame) (h : Nat) : Nat := 8 * (fr.out + fr.named.length + h)

theorem Frame.opOff_eq {fr : Frame} {h o : Nat} (e : fr.opOff h = some o) :
    h < fr.height ∧ o = fr.opAt h := by
  unfold Frame.opOff at e
  split at e
  · cases e; exact ⟨by assumption, rfl⟩
  · cases e

theorem Frame.lrOff_eq (fr : Frame) : fr.lrOff = 8 * (fr.out + fr.named.length + fr.height) :=
  rfl

theorem Frame.size_eq (fr : Frame) : fr.size = fr.lrOff + 8 := by
  simp only [Frame.size, Frame.lrOff]; omega

/-- The offset of a local's slot is a parameter's above the frame or a named local's below the
operand slots. -/
theorem Frame.localOff_eq {fr : Frame} {i o : Nat} (e : fr.localOff i = some o) :
    (i < fr.params ∧ o = fr.size + 8 * i) ∨
      ∃ j, j < fr.named.length ∧ fr.named[j]? = some i ∧ o = 8 * (fr.out + j) := by
  unfold Frame.localOff at e
  split at e
  · cases e; exact .inl ⟨by assumption, rfl⟩
  · simp only [Option.map_eq_some_iff] at e
    obtain ⟨j, hj, rfl⟩ := e
    obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.mp hj
    exact .inr ⟨j, hlt, by rw [List.getElem?_eq_getElem hlt, heq], rfl⟩

/-- The frame at SP of a function whose layout `fr` gives, below the stack's limit `lim`. -/
structure FrameOk (P : Platform) (fr : Frame) (lim : UInt32) (s : State) : Prop where
  aligned : s.sp % 4 = 0
  ram : ∀ j < fr.size + 8 * fr.params, Ram P (s.sp + UInt32.ofNat j)
  fits : s.sp.toNat + fr.size + 8 * fr.params ≤ 4294967296
  limit : 4096 ≤ lim.toNat ∧ lim.toNat ≤ s.sp.toNat
  below : ∀ j < s.sp.toNat - lim.toNat, Ram P (lim + UInt32.ofNat j)

theorem FrameOk.congr {P : Platform} {fr : Frame} {lim : UInt32} {s t : State}
    (h : FrameOk P fr lim s) (hsp : t.sp = s.sp) : FrameOk P fr lim t := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨hsp ▸ h1, hsp ▸ h2, hsp ▸ h3, hsp ▸ h4, hsp ▸ h5⟩

/-- A load or store of the word at the offset `o` of the frame or the parameters passes the
checks. -/
theorem FrameOk.word {P : Platform} {fr : Frame} {lim : UInt32} {s : State}
    (h : FrameOk P fr lim s) {o : Nat} (ho : o % 4 = 0) (hn : o + 4 ≤ fr.size + 8 * fr.params) :
    WordOk P (s.sp + UInt32.ofNat o) :=
  wordOk_of_ram h.ram h.aligned ho hn

/-- The relation at a point of a function whose frame, locals' types, and shared addresses `E`
gives, with an operand stack of the types `σs`, top first: the operand slots hold the values of
the stack, the slots of the parameters and of the named locals hold their values, which have
their types, and the frame satisfies `FrameOk`. -/
structure Inv (P : Platform) (E : Env) (σs : List ValueType) (sl : Locals) (s : State) :
    Prop where
  height : sl.values.length ≤ E.frame.height
  stack : ∀ h v, sl.values.reverse[h]? = some v → ValAt s (E.frame.opAt h) v
  count : (sl.params ++ sl.locals).length = E.localTypes.length
  locals : ∀ i v o, (sl.params ++ sl.locals)[i]? = some v → E.frame.localOff i = some o →
    ValAt s o v
  ltypes : ∀ i v t o, (sl.params ++ sl.locals)[i]? = some v → E.localTypes[i]? = some t →
    E.frame.localOff i = some o → HasType t v
  frame : FrameOk P E.frame E.limit s
  types : Typed σs sl.values

theorem Inv.len {P : Platform} {E : Env} {σs : List ValueType} {sl : Locals} {s : State}
    (h : Inv P E σs sl s) : sl.values.length = σs.length := h.types.length.symm

/-! ## What code keeps -/

/-- The word of the LR slot and every byte from the end of the parameters up keep in `t` their
values in `s`, for the frame `fr` at `sp`. -/
structure BodyKeeps (fr : Frame) (sp : UInt32) (s t : State) : Prop where
  lr : load32 t.mem (sp + UInt32.ofNat fr.lrOff) = load32 s.mem (sp + UInt32.ofNat fr.lrOff)
  above : ∀ a : UInt32, sp.toNat + fr.size + 8 * fr.params ≤ a.toNat → t.mem a = s.mem a

theorem BodyKeeps.refl (fr : Frame) (sp : UInt32) (s : State) : BodyKeeps fr sp s s :=
  ⟨rfl, fun _ _ => rfl⟩

theorem BodyKeeps.trans {fr : Frame} {sp : UInt32} {s t u : State} (h1 : BodyKeeps fr sp s t)
    (h2 : BodyKeeps fr sp t u) : BodyKeeps fr sp s u :=
  ⟨h2.lr.trans h1.lr, fun a ha => (h2.above a ha).trans (h1.above a ha)⟩

theorem BodyKeeps.of_mem {fr : Frame} {sp : UInt32} {s t : State} (h : t.mem = s.mem) :
    BodyKeeps fr sp s t :=
  ⟨by rw [h], fun _ _ => by rw [h]⟩

/-- The operand slots of the heights below `b` keep in `t` their words in `s`. -/
def Below (fr : Frame) (b : Nat) (s t : State) : Prop :=
  ∀ h < b, SlotSame s t (fr.opAt h)

theorem Below.refl (fr : Frame) (b : Nat) (s : State) : Below fr b s s :=
  fun _ _ => SlotSame.refl _ _

theorem Below.trans {fr : Frame} {b : Nat} {s t u : State} (h1 : Below fr b s t)
    (h2 : Below fr b t u) (hsp : t.sp = s.sp) : Below fr b s u :=
  fun h hh => (h1 h hh).trans (h2 h hh) hsp

theorem Below.mono {fr : Frame} {b c : Nat} {s t : State} (h : Below fr b s t) (hc : c ≤ b) :
    Below fr c s t :=
  fun h' hh => h h' (by omega)

end LeanExe.M7
