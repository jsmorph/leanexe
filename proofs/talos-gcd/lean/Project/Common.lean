import CodeLib

/-!
# Shared lemmas for artifact proofs

Arithmetic and list facts that every artifact proof needs when it reasons
about generated `UInt64` code and byte or cell reads from linear memory.
-/

namespace Project.Common

theorem size_eq : UInt64.size = 18446744073709551616 := rfl

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

end Project.Common
