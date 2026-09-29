import Project.TalosPrelude
import Project.TalosCompat
import Project.Attr
import Std.Tactic.BVDecide

/-!
# Shared lemmas for artifact proofs

Arithmetic and list facts that every artifact proof needs when it reasons
about generated `UInt64` code and byte or cell reads from linear memory.
The `u64_omega` tactic closes `UInt64` equalities and inequalities by
rewriting to `toNat` normal forms and calling `omega`, `getElem_of_some`
converts an optional local fact to its proof-carrying form, and
`wp_run_with` is the one instruction-stepping simplification macro.
-/

namespace Project.Common

@[u64_toNat] theorem size_eq : UInt64.size = 18446744073709551616 := rfl

attribute [u64_toNat] UInt64.toNat_add UInt64.toNat_sub UInt64.toNat_mul
  UInt64.toNat_ofNat UInt32.toNat_ofNat UInt64.toNat_ofNat'
  UInt32.toNat_ofNat'

theorem u64_eq_iff {a b : UInt64} : a = b ↔ a.toNat = b.toNat :=
  ⟨congrArg UInt64.toNat, UInt64.toNat.inj⟩

theorem u32_eq_iff {a b : UInt32} : a = b ↔ a.toNat = b.toNat :=
  ⟨congrArg UInt32.toNat, UInt32.toNat.inj⟩

/-- Adding two modulo-`UInt64` increments and subtracting the original value
leaves two, including across wraparound. -/
theorem u64_add_two_sub_self (x : UInt64) :
    x + 1 + 1 - x = 2 := by
  bv_decide

/-- Adding three modulo-`UInt64` increments and subtracting the original value
leaves three, including across wraparound. -/
theorem u64_add_three_sub_self (x : UInt64) :
    x + 1 + 1 + 1 - x = 3 := by
  bv_decide

/-- Close a `UInt64` equality or inequality goal, including negated
forms, by moving to `toNat` form and calling `omega`.  Bounds needed to
remove the residual moduli must already be in context as `Nat` facts. -/
macro "u64_omega" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic|
    (simp only [ge_iff_le, gt_iff_lt, ne_eq, u64_eq_iff, u32_eq_iff,
      UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, u64_toNat]
      $[$loc]?) <;>
    omega)

theorem toNat_ofNat_lt {n : Nat} (h : n < UInt64.size) :
    (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' h

theorem ofNat_inj {a b : Nat} (ha : a < UInt64.size) (hb : b < UInt64.size)
    (h : UInt64.ofNat a = UInt64.ofNat b) : a = b := by
  have := congrArg UInt64.toNat h
  rwa [toNat_ofNat_lt ha, toNat_ofNat_lt hb] at this

theorem toNat_add_one {x : UInt64} (h : x.toNat + 1 < UInt64.size) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [size_eq] at h
  rw [UInt64.toNat_add]
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [h1]
  omega

theorem getBang_eq {α : Type _} [Inhabited α] {l : List α} {i : Nat}
    (hi : i < l.length) : l[i]! = l[i] := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- Convert an optional element fact to its proof-carrying form.  The
bound is an autoparam, so a context that knows the list length closes it
without an explicit argument. -/
theorem getElem_of_some {α : Type _} {l : List α} {i : Nat} {v : α}
    (h : l[i]? = some v) (hi : i < l.length := by omega) : l[i] = v := by
  rw [List.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

/-- Prepend a six-part conjunction pack onto a tail in one step.  The
instruction proofs use this where the goal carries a `wp` term behind
side conditions: splitting such a goal with more than two live
components stalls the elaborator, while one application of this lemma
with a prepacked left side stays cheap. -/
theorem and6_and {A₁ A₂ A₃ A₄ A₅ A₆ B : Prop}
    (h : A₁ ∧ A₂ ∧ A₃ ∧ A₄ ∧ A₅ ∧ A₆) (hb : B) :
    A₁ ∧ A₂ ∧ A₃ ∧ A₄ ∧ A₅ ∧ A₆ ∧ B :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, hb⟩

theorem toUInt32_toNat (x : UInt64) : x.toUInt32.toNat = x.toNat % 4294967296 := by
  simp

theorem toUInt32_ofNat_mod_toNat (n : Nat) :
    (UInt32.ofNat (n % 4294967296)).toNat = n % 4294967296 :=
  UInt32.toNat_ofNat_of_lt' (Nat.mod_lt _ (by norm_num))

theorem toUInt32_eq_ofNat (x : UInt64) :
    x.toUInt32 = UInt32.ofNat (x.toNat % 4294967296) := by
  apply UInt32.toNat.inj
  rw [toUInt32_ofNat_mod_toNat]
  exact toUInt32_toNat x

/-- The input bytes as a module reads them: each index has its byte at the
wrapped 32-bit address, and that address is in bounds. -/
def BytesAt (st : Wasm.Store Unit) (ptr : UInt64) (bytes : List UInt8) : Prop :=
  ∀ i : Nat, i < bytes.length →
    st.mem.read8 ((ptr + UInt64.ofNat i).toUInt32) = bytes[i]! ∧
    ((ptr + UInt64.ofNat i).toUInt32).toNat + 1 ≤ st.mem.pages * 65536

/-- A byte write leaves every other address unchanged. -/
theorem write8_bytes_ne (mm : Wasm.Mem) (ad : UInt32) (v : UInt8) {x : Nat}
    (hx : x ≠ ad.toNat) : (mm.write8 ad v).bytes x = mm.bytes x := by
  unfold Wasm.Mem.write8
  dsimp only
  rw [if_neg hx]

/-- A byte write is visible at its own address.  The address is an equation
hypothesis so the rewrite never touches the address expression itself. -/
theorem write8_bytes_hit (mm : Wasm.Mem) (ad : UInt32) (v : UInt8) {x : Nat}
    (hx : x = ad.toNat) : (mm.write8 ad v).bytes x = v := by
  subst hx
  unfold Wasm.Mem.write8
  dsimp only
  rw [if_pos rfl]

/-- A word write leaves every address below it unchanged. -/
theorem write64_bytes_lo (mm : Wasm.Mem) (ad : UInt32) (v : UInt64) {x : Nat}
    (hx : x < ad.toNat) : (mm.write64 ad v).bytes x = mm.bytes x := by
  unfold Wasm.Mem.write64
  dsimp only
  split_ifs <;> first | rfl | omega

/-- A word write leaves every address outside its window unchanged. -/
theorem write64_bytes_ne (mm : Wasm.Mem) (ad : UInt32) (v : UInt64) {x : Nat}
    (hx : x < ad.toNat ∨ ad.toNat + 8 ≤ x) :
    (mm.write64 ad v).bytes x = mm.bytes x := by
  unfold Wasm.Mem.write64
  dsimp only
  split_ifs <;> first | rfl | omega

theorem write8_pages (mm : Wasm.Mem) (ad : UInt32) (v : UInt8) :
    (mm.write8 ad v).pages = mm.pages := rfl

/-- A byte write is read back at its own address. -/
theorem write8_bytes_same (mm : Wasm.Mem) (ad : UInt32) (v : UInt8) :
    (mm.write8 ad v).bytes ad.toNat = v := by
  unfold Wasm.Mem.write8
  simp

/-- The hypothesis-form variant for indexes stated away from `toNat`. -/
theorem write8_bytes_same' (mm : Wasm.Mem) (ad : UInt32) (v : UInt8)
    {x : Nat} (hx : x = ad.toNat) :
    (mm.write8 ad v).bytes x = v := by
  rw [hx]
  exact write8_bytes_same ..

/-- Two memories that agree on a word's window read the same word. -/
theorem read64_congr {m1 m2 : Wasm.Mem} (b : UInt32)
    (h : ∀ i : Nat, i < 8 → m1.bytes (b.toNat + i) = m2.bytes (b.toNat + i)) :
    m1.read64 b = m2.read64 b := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  have h4 := h 4 (by omega)
  have h5 := h 5 (by omega)
  have h6 := h 6 (by omega)
  have h7 := h 7 (by omega)
  rw [Nat.add_zero] at h0
  simp only [Wasm.Mem.read64]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

/-- A word write leaves a disjoint word read unchanged. -/
theorem read64_write64_ne (mm : Wasm.Mem) (ad : UInt32) (v : UInt64)
    (b : UInt32) (h : b.toNat + 8 ≤ ad.toNat ∨ ad.toNat + 8 ≤ b.toNat) :
    (mm.write64 ad v).read64 b = mm.read64 b :=
  read64_congr b fun i hi => write64_bytes_ne mm ad v (by omega)

/-- A byte write outside a word's window leaves the word read unchanged. -/
theorem read64_write8_ne (mm : Wasm.Mem) (ad : UInt32) (v : UInt8)
    (b : UInt32) (h : ad.toNat < b.toNat ∨ b.toNat + 8 ≤ ad.toNat) :
    (mm.write8 ad v).read64 b = mm.read64 b :=
  read64_congr b fun i hi => write8_bytes_ne mm ad v (by omega)

/-- Resolve a word read over a chain of word writes: peel disjoint writes
outermost-in, discharging separation by `omega` after normalizing the
`UInt32.ofNat (_ % 2^32)` address forms, and stop at the syntactic hit.
Address forms must already match at the hit; normalize first if not. -/
macro "read_frames" : tactic =>
  `(tactic|
    repeat first
      | rw [Wasm.Mem.read64_write64_same]
      | rw [read64_write64_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega)])

/-- Subtraction stays within `Nat` when the subtrahend fits. -/
theorem toNat_sub_le (p q : UInt64) (h : q.toNat ≤ p.toNat) :
    (p - q).toNat = p.toNat - q.toNat := by
  rw [UInt64.toNat_sub]
  have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
  have hp : p.toNat < UInt64.size := p.toNat_lt_size
  have hq : q.toNat < UInt64.size := q.toNat_lt_size
  omega

/-- Step generated instructions over the current frame.  The bracket list
supplies the frame facts and definitions the reduction needs; every module
uses this one macro instead of a local variant. -/
macro "wp_run_with" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 10000000 }) [wp_simp,
      Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
      Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.Function.numLocals,
      List.take, List.drop, List.replicate, List.length, List.map,
      List.length_set, List.getElem?_set,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
      Wasm.ValueType.zero, List.headD, $ts,*])

/-- Enter a generated conditional and select its positive branch. -/
macro "wp_guard_pos" h:term : tactic =>
  `(tactic| (refine Wasm.wp_iff_cons rfl ?_; rw [if_pos $h]))

/-- Enter a generated conditional and select its negative branch. -/
macro "wp_guard_neg" h:term : tactic =>
  `(tactic| (refine Wasm.wp_iff_cons rfl ?_; rw [if_neg $h]))

end Project.Common
