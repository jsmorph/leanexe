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
the setup of `LeanExe/M7/Setup.lean` leaves it.  `StoreRel.congr` keeps the relation under code
that keeps every byte below the stack's limit, `StoreRel.load` gives the two words of the memory's
8 bytes from an address as those of Talos's `read64`, and `StoreRel.write` and
`StoreRel.setGlobal` give the relation after the word stores of a `store64` and a `globalSet`.
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

/-! ## Talos's memory words -/

theorem toNat_shiftLeft64 (x j : UInt64) (n : Nat) (hj : j.toNat = n) (hn : n < 64)
    (hx : x.toNat * 2 ^ n < 18446744073709551616) : (x <<< j).toNat = x.toNat * 2 ^ n := by
  rw [UInt64.toNat_shiftLeft, hj, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hn]
  exact Nat.mod_eq_of_lt hx

/-- The number of the 8 bytes from `b` that `read64` reads, the lowest first. -/
theorem toNat_read64 (m : Mem) (b : UInt32) :
    (m.read64 b).toNat = (m.bytes b.toNat).toNat + 256 * (m.bytes (b.toNat + 1)).toNat +
      65536 * (m.bytes (b.toNat + 2)).toNat + 16777216 * (m.bytes (b.toNat + 3)).toNat +
      4294967296 * (m.bytes (b.toNat + 4)).toNat +
      1099511627776 * (m.bytes (b.toNat + 5)).toNat +
      281474976710656 * (m.bytes (b.toNat + 6)).toNat +
      72057594037927936 * (m.bytes (b.toNat + 7)).toNat := by
  simp only [Mem.read64]
  generalize m.bytes b.toNat = b0
  generalize m.bytes (b.toNat + 1) = b1
  generalize m.bytes (b.toNat + 2) = b2
  generalize m.bytes (b.toNat + 3) = b3
  generalize m.bytes (b.toNat + 4) = b4
  generalize m.bytes (b.toNat + 5) = b5
  generalize m.bytes (b.toNat + 6) = b6
  generalize m.bytes (b.toNat + 7) = b7
  have h0 := b0.toNat_lt
  have h1 := b1.toNat_lt
  have h2 := b2.toNat_lt
  have h3 := b3.toNat_lt
  have h4 := b4.toNat_lt
  have h5 := b5.toNat_lt
  have h6 := b6.toNat_lt
  have h7 := b7.toNat_lt
  simp only [Nat.reducePow] at h0 h1 h2 h3 h4 h5 h6 h7
  rw [UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or,
    UInt64.toNat_or, UInt64.toNat_or,
    toNat_shiftLeft64 _ 8 8 rfl (by decide) (by rw [UInt8.toNat_toUInt64]; omega),
    toNat_shiftLeft64 _ 16 16 rfl (by decide) (by rw [UInt8.toNat_toUInt64]; omega),
    toNat_shiftLeft64 _ 24 24 rfl (by decide) (by rw [UInt8.toNat_toUInt64]; omega),
    toNat_shiftLeft64 _ 32 32 rfl (by decide) (by rw [UInt8.toNat_toUInt64]; omega),
    toNat_shiftLeft64 _ 40 40 rfl (by decide) (by rw [UInt8.toNat_toUInt64]; omega),
    toNat_shiftLeft64 _ 48 48 rfl (by decide) (by rw [UInt8.toNat_toUInt64]; omega),
    toNat_shiftLeft64 _ 56 56 rfl (by decide) (by rw [UInt8.toNat_toUInt64]; omega),
    UInt8.toNat_toUInt64, UInt8.toNat_toUInt64, UInt8.toNat_toUInt64, UInt8.toNat_toUInt64,
    UInt8.toNat_toUInt64, UInt8.toNat_toUInt64, UInt8.toNat_toUInt64, UInt8.toNat_toUInt64,
    or_add_shift (x := b0.toNat) (y := b1.toNat) (k := 8) (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8) (y := b2.toNat) (k := 16) (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16) (y := b3.toNat) (k := 24)
      (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24)
      (y := b4.toNat) (k := 32) (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 +
      b4.toNat * 2 ^ 32) (y := b5.toNat) (k := 40) (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 +
      b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40) (y := b6.toNat) (k := 48) (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 +
      b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48) (y := b7.toNat) (k := 56)
      (by omega)]
  omega

/-- Byte `k` of the word that `read64` reads from `b` is the memory's byte `b + k`. -/
theorem byteOf_read64 (m : Mem) (b : UInt32) {k : Nat} (hk : k < 8) :
    A64.byteOf (m.read64 b) k = m.bytes (b.toNat + k) := by
  apply UInt8.toNat_inj.mp
  rw [toNat_byteOf _ hk, toNat_read64]
  have h0 := (m.bytes b.toNat).toNat_lt
  have h1 := (m.bytes (b.toNat + 1)).toNat_lt
  have h2 := (m.bytes (b.toNat + 2)).toNat_lt
  have h3 := (m.bytes (b.toNat + 3)).toNat_lt
  have h4 := (m.bytes (b.toNat + 4)).toNat_lt
  have h5 := (m.bytes (b.toNat + 5)).toNat_lt
  have h6 := (m.bytes (b.toNat + 6)).toNat_lt
  have h7 := (m.bytes (b.toNat + 7)).toNat_lt
  simp only [Nat.reducePow] at h0 h1 h2 h3 h4 h5 h6 h7
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.add_zero, Nat.mul_zero, Nat.reduceMul, Nat.reducePow] <;> omega

/-- Byte `k` of the 8 bytes that `write64` writes from `y`, as a number. -/
theorem toNat_write64_at (m : Mem) (y : UInt32) (v : UInt64) {k : Nat} (hk : k < 8) :
    ((m.write64 y v).bytes (y.toNat + k)).toNat = v.toNat / 2 ^ (8 * k) % 256 := by
  have and255 : ∀ x : Nat, x &&& 255 = x % 256 := fun x => Nat.and_two_pow_sub_one_eq_mod x 8
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [Mem.write64, UInt64.toNat_and, and255, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow] <;> omega

theorem write64_outside (m : Mem) (y : UInt32) (v : UInt64) {j : Nat}
    (h : j < y.toNat ∨ y.toNat + 8 ≤ j) : (m.write64 y v).bytes j = m.bytes j := by
  have h0 : j ≠ y.toNat := by omega
  have h1 : j ≠ y.toNat + 1 := by omega
  have h2 : j ≠ y.toNat + 2 := by omega
  have h3 : j ≠ y.toNat + 3 := by omega
  have h4 : j ≠ y.toNat + 4 := by omega
  have h5 : j ≠ y.toNat + 5 := by omega
  have h6 : j ≠ y.toNat + 6 := by omega
  have h7 : j ≠ y.toNat + 7 := by omega
  simp only [Mem.write64, h0, h1, h2, h3, h4, h5, h6, h7, ite_false]

/-! ## Stores at offsets from a base -/

/-- A word store at the offset `x` from `c` leaves the byte at the offset `o` outside its four
bytes. -/
theorem store32_off_far {m : UInt32 → UInt8} {c v : UInt32} {x o : Nat}
    (hx : x + 4 ≤ 4294967296) (ho : o < 4294967296) (hd : o < x ∨ x + 4 ≤ o) :
    store32 m (c + UInt32.ofNat x) v (c + UInt32.ofNat o) = m (c + UInt32.ofNat o) := by
  apply store32_far
  rw [UInt32.lt_iff_toNat_lt, toNat_sub_offsets c (by omega) ho,
    show (4 : UInt32).toNat = 4 from rfl]
  omega

/-- The byte at the offset `o` within the four bytes of a word store at the offset `x` from `c`, as
a number. -/
theorem toNat_store32_off_at {m : UInt32 → UInt8} {c v : UInt32} {x o : Nat}
    (hx : x + 4 ≤ 4294967296) (h1 : x ≤ o) (h2 : o < x + 4) :
    (store32 m (c + UInt32.ofNat x) v (c + UInt32.ofNat o)).toNat =
      v.toNat / 2 ^ (8 * (o - x)) % 256 := by
  have hd : c + UInt32.ofNat o - (c + UInt32.ofNat x) = UInt32.ofNat (o - x) := by
    apply UInt32.toNat_inj.mp
    rw [toNat_sub_offsets c (by omega) (by omega), UInt32.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  have hlt : c + UInt32.ofNat o - (c + UInt32.ofNat x) < 4 := by
    rw [hd, UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat', show (4 : UInt32).toNat = 4 from rfl]
    simp only [Nat.reducePow]
    omega
  have e := toNat_byte v (UInt32.ofNat (o - x)) (o - x)
    (by rw [UInt32.toNat_ofNat']; simp only [Nat.reducePow]; omega) (by omega)
  rw [UInt8.toNat_toUInt32] at e
  simp only [store32, hlt, ↓reduceIte]
  rw [hd]
  exact e

/-! ## What keeps the relation -/

/-- The relation holds of a state whose bytes below the stack's limit are those of `s`. -/
theorem StoreRel.congr {P : Platform} {area lim : UInt32} {cap : Nat} {gts : List ValueType}
    {α : Type} {st : Store α} {s t : State} (h : StoreRel P area lim cap gts st s)
    (hmem : ∀ a : UInt32, a.toNat < lim.toNat → t.mem a = s.mem a) :
    StoreRel P area lim cap gts st t := by
  have hb := h.below
  have hl := toNat_lt32 lim
  have hk : ∀ j < areaSize cap, t.mem (area + UInt32.ofNat j) = s.mem (area + UInt32.ofNat j) :=
    fun j hj => hmem _ (by rw [toNat_add_ofNat (by omega)]; omega)
  have hgl := h.types.length
  have hg := h.glen
  refine ⟨h.caps, h.cap_lt, h.glen, h.pages, ?_, h.types, fun i hi => ?_, fun j hj => ?_, h.ram,
    h.below⟩
  · rw [load32_congr (m := s.mem) (m' := t.mem) fun k hk' => hk k (by unfold areaSize; omega)]
    exact h.size
  · rw [load32_congr (m := s.mem) (m' := t.mem) fun k hk' => by
        rw [add_ofNat_add]; exact hk _ (by unfold areaSize; omega),
      load32_congr (m := s.mem) (m' := t.mem) fun k hk' => by
        rw [add_ofNat_add]; exact hk _ (by unfold areaSize; omega)]
    exact h.globals i hi
  · rw [hk _ (by unfold areaSize; omega)]
    exact h.bytes j hj

/-- The two words of the memory's 8 bytes from `y`, within its size, are those of Talos's
`read64`. -/
theorem StoreRel.load {P : Platform} {area lim : UInt32} {cap : Nat} {gts : List ValueType}
    {α : Type} {st : Store α} {s : State} (h : StoreRel P area lim cap gts st s) {y : Nat}
    (hy : y + 8 ≤ st.mem.pages * 65536) :
    load32 s.mem (area + UInt32.ofNat (4096 + y)) = (st.mem.read64 (UInt32.ofNat y)).toUInt32 ∧
      load32 s.mem (area + UInt32.ofNat (4096 + y + 4)) =
        (st.mem.read64 (UInt32.ofNat y) >>> 32).toUInt32 := by
  have hcap : st.mem.pages * 65536 ≤ cap * 65536 := Nat.mul_le_mul_right _ h.pages.2
  have hc := h.cap_lt
  have hyn : (UInt32.ofNat y).toNat = y := by
    rw [UInt32.toNat_ofNat']; simp only [Nat.reducePow]; omega
  have e := load32_slot (m := s.mem) (a := area + UInt32.ofNat (4096 + y))
    (x := st.mem.read64 (UInt32.ofNat y)) fun k hk => by
      rw [add_ofNat_add, show 4096 + y + k = 4096 + (y + k) by omega, h.bytes _ (by omega),
        byteOf_read64 _ _ hk, hyn]
  rwa [add_ofNat_add] at e

/-- The relation after the stores of the two words of `v` at byte `y` of the memory, within its
size, which Talos's `write64` writes. -/
theorem StoreRel.write {P : Platform} {area lim : UInt32} {cap : Nat} {gts : List ValueType}
    {α : Type} {st : Store α} {s t : State} (h : StoreRel P area lim cap gts st s) {y : Nat}
    (hy : y + 8 ≤ st.mem.pages * 65536) {v : UInt64}
    (hmem : t.mem = store32 (store32 s.mem (area + UInt32.ofNat (4096 + y)) v.toUInt32)
      (area + UInt32.ofNat (4096 + y + 4)) (v >>> 32).toUInt32) :
    StoreRel P area lim cap gts { st with mem := st.mem.write64 (UInt32.ofNat y) v } t := by
  have hcap : st.mem.pages * 65536 ≤ cap * 65536 := Nat.mul_le_mul_right _ h.pages.2
  have hc := h.cap_lt
  have hgl := h.glen
  have hlen := h.types.length
  have hyn : (UInt32.ofNat y).toNat = y := by
    rw [UInt32.toNat_ofNat']; simp only [Nat.reducePow]; omega
  have hfar : ∀ o, o < 4096 + y ∨ 4096 + y + 8 ≤ o → o < 4294967296 →
      t.mem (area + UInt32.ofNat o) = s.mem (area + UInt32.ofNat o) := fun o ho ho' => by
    rw [hmem, store32_off_far (by omega) ho' (by omega), store32_off_far (by omega) ho' (by omega)]
  refine ⟨h.caps, h.cap_lt, h.glen, h.pages, ?_, h.types, fun i hi => ?_, fun j hj => ?_, h.ram,
    h.below⟩
  · rw [load32_congr (m := s.mem) (m' := t.mem) fun k hk => hfar k (by omega) (by omega)]
    exact h.size
  · change i < st.globals.globals.length at hi
    have hi' : i < gts.length := by omega
    rw [load32_congr (m := s.mem) (m' := t.mem) fun k hk => by
        rw [add_ofNat_add]; exact hfar _ (by omega) (by omega),
      load32_congr (m := s.mem) (m' := t.mem) fun k hk => by
        rw [add_ofNat_add]; exact hfar _ (by omega) (by omega)]
    exact h.globals i hi
  · show t.mem (area + UInt32.ofNat (4096 + j)) = (st.mem.write64 (UInt32.ofNat y) v).bytes j
    by_cases hin : y ≤ j ∧ j < y + 8
    · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 8 ∧ j = y + k := ⟨j - y, by omega, by omega⟩
      have hv := UInt64.toNat_lt v
      simp only [Nat.reducePow] at hv
      have hT : ((st.mem.write64 (UInt32.ofNat y) v).bytes (y + k)).toNat =
          v.toNat / 2 ^ (8 * k) % 256 := by
        have := toNat_write64_at st.mem (UInt32.ofNat y) v hk
        rwa [hyn] at this
      apply UInt8.toNat_inj.mp
      rw [hT, hmem]
      by_cases hk4 : k < 4
      · rw [store32_off_far (by omega) (by omega) (by omega),
          toNat_store32_off_at (by omega) (by omega) (by omega), UInt64.toNat_toUInt32,
          show 4096 + (y + k) - (4096 + y) = k by omega]
        rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
          simp only [Nat.mul_zero, Nat.reduceMul, Nat.reducePow] <;> omega
      · rw [toNat_store32_off_at (by omega) (by omega) (by omega), toNat_hi64,
          show 4096 + (y + k) - (4096 + y + 4) = k - 4 by omega]
        rcases (show k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with rfl | rfl | rfl | rfl <;>
          simp only [Nat.mul_zero, Nat.reduceMul, Nat.reducePow, Nat.reduceSub] <;> omega
    · rw [hfar _ (by omega) (by omega), write64_outside _ _ _ (by rw [hyn]; omega)]
      exact h.bytes j hj

/-- The relation after the stores of the words `w0` and `w1` of `v`, of the type `gts[i]`, into the
slot of global `i`. -/
theorem StoreRel.setGlobal {P : Platform} {area lim : UInt32} {cap : Nat} {gts : List ValueType}
    {α : Type} {st : Store α} {s t : State} (h : StoreRel P area lim cap gts st s) {i : Nat}
    (hi : i < gts.length) {v : Value} {w0 w1 : UInt32} (hv : SlotRel v w0 w1)
    (ht : HasType gts[i] v)
    (hmem : t.mem = store32 (store32 s.mem (area + UInt32.ofNat (8 * (i + 1))) w0)
      (area + UInt32.ofNat (8 * (i + 1) + 4)) w1) :
    StoreRel P area lim cap gts { st with globals := { globals := st.globals.globals.set i v } }
      t := by
  have hgl := h.glen
  have hlen := h.types.length
  have hfar : ∀ o, o + 4 ≤ 8 * (i + 1) ∨ 8 * (i + 1) + 8 ≤ o → o + 4 ≤ 4294967296 →
      load32 t.mem (area + UInt32.ofNat o) = load32 s.mem (area + UInt32.ofNat o) :=
    fun o ho ho' => by
      rw [hmem, load32_store32_off (by omega) ho' (by omega),
        load32_store32_off (by omega) ho' (by omega)]
  refine ⟨h.caps, h.cap_lt, h.glen, h.pages, ?_, h.types.set hi ht, fun j hj => ?_,
    fun j hj => ?_, h.ram, h.below⟩
  · have e := hfar 0 (by omega) (by omega)
    rw [show area + UInt32.ofNat 0 = area by simp] at e
    rw [e]
    exact h.size
  · simp only [List.length_set] at hj
    show SlotRel _ (load32 t.mem (area + UInt32.ofNat (8 * (j + 1))))
      (load32 t.mem (area + UInt32.ofNat (8 * (j + 1) + 4)))
    by_cases hji : j = i
    · subst hji
      rw [List.getElem_set_self, hmem, load32_store32,
        load32_store32_off (by omega) (by omega) (by omega), load32_store32]
      exact hv
    · rw [List.getElem_set_ne (Ne.symm hji), hfar _ (by omega) (by omega),
        hfar _ (by omega) (by omega)]
      exact h.globals j hj
  · show t.mem (area + UInt32.ofNat (4096 + j)) = st.mem.bytes j
    have hcap : cap < 4096 := h.cap_lt
    rw [hmem, store32_off_far (by omega) (by omega) (by omega),
      store32_off_far (by omega) (by omega) (by omega)]
    exact h.bytes j hj

end LeanExe.M7
