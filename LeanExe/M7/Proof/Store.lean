import LeanExe.M7.Proof.Relation
import LeanExe.Proof.Area

/-!
The relation between Talos's store and the area of `LeanExe/Area.lean` in the Cortex-M7 model's
memory.  `StoreRel P area lim cap gts st s` places the store's memory size less 8 in the word at
`area`, global `i` in the slot of two words at `area + 8 (i + 1)` by `SlotRel`, and byte `j` of the
memory at `area + 4096 + j`, with the area's bytes `Ram` and its end at or below the stack's limit
`lim`.  The code reads only the low word of the size, whose high word the area's bytes make 0.
`storeRel_init` derives the relation for the store in which a module starts, `initStore m cap`,
from a memory that holds `areaByte` of the module's initial store at each of the area's bytes, as
the setup of `LeanExe/M7/Setup.lean` leaves it.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit

/-- The machine holds Talos's store `st` in the area at `area`, below the stack's limit `lim`: the
memory's size less 8 in the word at `area`, global `i`, of the type `gts[i]`, in the slot at
`area + 8 (i + 1)`, and byte `j` of the memory at `area + 4096 + j` for every `j` below `cap` pages.
The memory's cap is `cap` pages, below 4096, and it holds at least 1 page, and the globals are at
most 511. -/
structure StoreRel (P : Platform) (area lim : UInt32) (cap : Nat) (gts : List ValueType)
    {α : Type} (st : Store α) (s : State) : Prop where
  caps : st.memoryCaps = [cap]
  cap_lt : cap < 4096
  glen : gts.length ≤ 511
  pages : 1 ≤ st.mem.pages ∧ st.mem.pages ≤ cap
  size : load32 s.mem area = UInt32.ofNat (st.mem.pages * 65536 - 8)
  types : Typed gts st.globals.globals
  globals : ∀ i (hi : i < st.globals.globals.length),
    SlotRel st.globals.globals[i] (load32 s.mem (area + UInt32.ofNat (8 * (i + 1))))
      (load32 s.mem (area + UInt32.ofNat (8 * (i + 1) + 4)))
  bytes : ∀ j < cap * 65536, s.mem (area + UInt32.ofNat (4096 + j)) = st.mem.bytes j
  ram : ∀ j < areaSize cap, Ram P (area + UInt32.ofNat j)
  below : area.toNat + areaSize cap ≤ lim.toNat

/-! ## Words from bytes -/

/-- The number of the word of four bytes, the lowest first. -/
theorem toNat_bytes32 (b0 b1 b2 b3 : UInt8) :
    (b0.toUInt32 ||| b1.toUInt32 <<< 8 ||| b2.toUInt32 <<< 16 ||| b3.toUInt32 <<< 24).toNat =
      b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat := by
  have h0 := b0.toNat_lt
  have h1 := b1.toNat_lt
  have h2 := b2.toNat_lt
  have h3 := b3.toNat_lt
  simp only [Nat.reducePow] at h0 h1 h2 h3
  rw [UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_or,
    toNat_shiftLeft32 _ 8 8 rfl (by decide) (by rw [UInt8.toNat_toUInt32]; omega),
    toNat_shiftLeft32 _ 16 16 rfl (by decide) (by rw [UInt8.toNat_toUInt32]; omega),
    toNat_shiftLeft32 _ 24 24 rfl (by decide) (by rw [UInt8.toNat_toUInt32]; omega),
    UInt8.toNat_toUInt32, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32,
    or_add_shift (x := b0.toNat) (y := b1.toNat) (k := 8) (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8) (y := b2.toNat) (k := 16) (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16) (y := b3.toNat) (k := 24)
      (by omega)]
  omega

/-- The number of the word that `load32` reads from four bytes that `f` gives. -/
theorem toNat_load32_of {m : UInt32 → UInt8} {a : UInt32} {f : Nat → UInt8}
    (h : ∀ k < 4, m (a + UInt32.ofNat k) = f k) :
    (load32 m a).toNat =
      (f 0).toNat + 256 * (f 1).toNat + 65536 * (f 2).toNat + 16777216 * (f 3).toNat := by
  have e0 : m a = f 0 := by
    have := h 0 (by decide)
    rwa [show UInt32.ofNat 0 = 0 from rfl, UInt32.add_zero] at this
  have e1 : m (a + 1) = f 1 := h 1 (by decide)
  have e2 : m (a + 2) = f 2 := h 2 (by decide)
  have e3 : m (a + 3) = f 3 := h 3 (by decide)
  unfold load32
  rw [e0, e1, e2, e3]
  exact toNat_bytes32 _ _ _ _

/-- Byte `k` of a 64-bit word, as a number. -/
theorem toNat_byteOf (x : UInt64) {k : Nat} (hk : k < 8) :
    (A64.byteOf x k).toNat = x.toNat / 2 ^ (8 * k) % 256 := by
  unfold A64.byteOf
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
    Nat.shiftRight_eq_div_pow, show 8 * k % 2 ^ 64 % 64 = 8 * k by omega]

/-- The low word of a 64-bit word whose bytes, the lowest first, lie from `a`. -/
theorem toNat_load32_lo {m : UInt32 → UInt8} {a : UInt32} {x : UInt64}
    (h : ∀ k < 4, m (a + UInt32.ofNat k) = A64.byteOf x k) :
    (load32 m a).toNat = x.toNat % 4294967296 := by
  rw [toNat_load32_of h, toNat_byteOf x (by decide), toNat_byteOf x (by decide),
    toNat_byteOf x (by decide), toNat_byteOf x (by decide)]
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one, Nat.reduceMul, Nat.reducePow]
  omega

/-- The high word of a 64-bit word whose bytes 4 to 7 lie from `a`. -/
theorem toNat_load32_hi {m : UInt32 → UInt8} {a : UInt32} {x : UInt64}
    (h : ∀ k < 4, m (a + UInt32.ofNat k) = A64.byteOf x (4 + k)) :
    (load32 m a).toNat = x.toNat / 4294967296 % 4294967296 := by
  rw [toNat_load32_of h, toNat_byteOf x (by decide), toNat_byteOf x (by decide),
    toNat_byteOf x (by decide), toNat_byteOf x (by decide)]
  simp only [Nat.add_zero, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  omega

/-- The two words of the slot at `a` whose bytes are those of `x` are `x`'s low and high words. -/
theorem load32_slot {m : UInt32 → UInt8} {a : UInt32} {x : UInt64}
    (h : ∀ k < 8, m (a + UInt32.ofNat k) = A64.byteOf x k) :
    load32 m a = x.toUInt32 ∧ load32 m (a + UInt32.ofNat 4) = (x >>> 32).toUInt32 := by
  apply eq_of_pairNat
  unfold pairNat
  rw [toNat_load32_lo fun k hk => h k (by omega),
    toNat_load32_hi fun k hk => by rw [add_ofNat_add]; exact h (4 + k) (by omega)]
  have : x.toNat < 18446744073709551616 := x.toNat_lt_size
  omega

/-- A slot whose words are those of `wordOf v` holds `v`, for an `i32` or an `i64`. -/
theorem slotRel_wordOf {t : ValueType} {v : Value} (ht : intType t = true) (hv : HasType t v) :
    SlotRel v (wordOf v).toUInt32 (wordOf v >>> 32).toUInt32 := by
  cases t <;> simp only [intType, Bool.false_eq_true] at ht <;> cases v <;>
    simp only [HasType] at hv
  · rename_i x
    refine ⟨UInt32.toUInt32_toUInt64 x, ?_⟩
    apply UInt32.toNat_inj.mp
    rw [wordOf, toNat_hi64, UInt32.toNat_toUInt64]
    have := toNat_lt32 x
    simp only [show (0 : UInt32).toNat = 0 from rfl]
    omega
  · exact ⟨rfl, rfl⟩

/-! ## The store in which a module starts -/

/-- A machine whose memory holds at `area` the bytes of the area of the module's initial store
holds that store with a memory of `cap` pages, when the area lies below 2^32 and its end at or below
the stack's limit `lim`. -/
theorem storeRel_init {P : Platform} {m : Module} {cap : Nat} {gts : List ValueType} {s : State}
    {area lim : UInt32} (hok : areaOk m cap = true) (hgt : globalTypesOf m = some gts)
    (hgl : gts.length ≤ 511) (hint : gts.all intType = true)
    (harea : ∀ j < areaSize cap, s.mem (area + UInt32.ofNat j) = areaByte m.initialStore j)
    (hram : ∀ j < areaSize cap, Ram P (area + UInt32.ofNat j))
    (hbelow : area.toNat + areaSize cap ≤ lim.toNat) :
    StoreRel P area lim cap gts (initStore m cap) s := by
  unfold areaOk at hok
  cases hd : m.memory with
  | none => rw [hd] at hok; cases hok
  | some d =>
      rw [hd] at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨-, h1⟩, h2⟩, h3⟩ := hok
      have hpg : (initStore m cap).mem.pages = d.pagesMin.toNat := initialStore_pages hd
      have hty : Typed gts (initStore m cap).globals.globals := typed_of_valueTypes _ _ hgt
      have hgl' := hty.length
      refine ⟨rfl, h3, hgl, by rw [hpg]; omega, ?_, hty, fun i hi => ?_, fun j hj => ?_, hram,
        hbelow⟩
      · apply UInt32.toNat_inj.mp
        rw [toNat_load32_lo (x := UInt64.ofNat ((initStore m cap).mem.pages * 65536 - 8))
            fun k hk => by
              rw [harea k (by unfold areaSize; omega)]
              simp only [areaByte, if_pos (show k < 8 by omega)]
              rfl,
          UInt32.toNat_ofNat', UInt64.toNat_ofNat', hpg]
        simp only [Nat.reducePow]
        omega
      · have hi' : i < gts.length := by omega
        have hti := hty.getElem hi'
        have hint' : intType gts[i] = true := List.all_eq_true.mp hint _ (List.getElem_mem hi')
        obtain ⟨e0, e1⟩ := load32_slot (m := s.mem) (a := area + UInt32.ofNat (8 * (i + 1)))
          (x := wordOf (initStore m cap).globals.globals[i]) fun k hk => by
            rw [add_ofNat_add, harea _ (by unfold areaSize; omega)]
            have e1 : (8 * (i + 1) + k) / 8 - 1 = i := by omega
            have e2 : (8 * (i + 1) + k) % 8 = k := by omega
            simp only [areaByte, e1, e2]
            rw [if_neg (by omega), if_pos (by omega)]
            have hi'' : i < (m.initialStore : Store Unit).globals.globals.length := hi
            rw [List.getElem?_eq_getElem hi'']
            rfl
        rw [add_ofNat_add] at e1
        rw [e0, e1]
        exact slotRel_wordOf hint' hti
      · rw [harea _ (by unfold areaSize; omega)]
        simp only [areaByte]
        rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]
        rfl

end LeanExe.M7
