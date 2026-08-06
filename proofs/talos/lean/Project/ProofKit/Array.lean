import Project.ProofKit.Memory

namespace Project.ProofKit.UInt64Array

open Wasm
open Project.ProofKit.Memory

def wordAddress (ptr : UInt64) (word : Nat) : UInt32 :=
  (ptr + UInt64.ofNat (8 * word)).toUInt32

def At (store : Store Unit) (ptr : UInt64) (values : Array UInt64) : Prop :=
  ptr.toNat + 8 * (values.size + 1) ≤ 4294967296 ∧
  ptr.toNat + 8 * (values.size + 1) ≤ store.mem.pages * 65536 ∧
  store.mem.read64 ptr.toUInt32 = UInt64.ofNat values.size ∧
  ∀ (i : Nat), (h : i < values.size) →
    store.mem.read64 (ptr + UInt64.ofNat (8 * (i + 1))).toUInt32 = values[i]

theorem wordAddress_toNat {ptr : UInt64} {words word : Nat}
    (hFit32 : ptr.toNat + 8 * words ≤ 4294967296)
    (hword : word < words) :
    (wordAddress ptr word).toNat = ptr.toNat + 8 * word := by
  have hOffset : 8 * word < UInt64.size := by
    have hSize : UInt64.size = 18446744073709551616 := rfl
    omega
  have hAddress32 : ptr.toNat + 8 * word < 4294967296 := by
    omega
  have hAddress64 : ptr.toNat + 8 * word < 2 ^ 64 := by
    norm_num
    omega
  unfold wordAddress
  rw [toUInt32_toNat, UInt64.toNat_add, toNat_ofNat_lt hOffset]
  rw [Nat.mod_eq_of_lt hAddress64, Nat.mod_eq_of_lt hAddress32]

theorem At.pointerAddress_toNat {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (h : At store ptr values) :
    ptr.toUInt32.toNat = ptr.toNat := by
  have hFit32 := h.1
  rw [toUInt32_toNat, Nat.mod_eq_of_lt]
  omega

theorem At.pointerAddress_eq {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (_h : At store ptr values) :
    UInt32.ofNat (ptr.toNat % 4294967296) = ptr.toUInt32 :=
  (toUInt32_eq_ofNat ptr).symm

theorem At.elementAddress_toNat {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (h : At store ptr values) (i : Nat)
    (hi : i < values.size) :
    ((ptr + UInt64.ofNat (8 * (i + 1))).toUInt32).toNat =
      ptr.toNat + 8 * (i + 1) := by
  exact wordAddress_toNat h.1 (by omega)

theorem At.elementAddress_eq {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (h : At store ptr values) (i : Nat)
    (hi : i < values.size) :
    UInt32.ofNat ((ptr.toNat + 8 * (i + 1)) % 4294967296) =
      (ptr + UInt64.ofNat (8 * (i + 1))).toUInt32 := by
  have hAddress32 : ptr.toNat + 8 * (i + 1) < 4294967296 := by
    have hFit32 := h.1
    omega
  apply UInt32.toNat.inj
  rw [h.elementAddress_toNat i hi]
  simp [Nat.mod_eq_of_lt hAddress32]

theorem At.lengthRead {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (h : At store ptr values) :
    store.mem.read64 ptr.toUInt32 = UInt64.ofNat values.size :=
  h.2.2.1

theorem At.elementRead {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (h : At store ptr values) (i : Nat)
    (hi : i < values.size) :
    store.mem.read64 (ptr + UInt64.ofNat (8 * (i + 1))).toUInt32 = values[i] :=
  h.2.2.2 i hi

theorem At.lengthBound {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (h : At store ptr values) :
    ptr.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
  have hFitMemory := h.2.1
  rw [h.pointerAddress_toNat]
  omega

theorem At.elementBound {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (h : At store ptr values) (i : Nat)
    (hi : i < values.size) :
    ((ptr + UInt64.ofNat (8 * (i + 1))).toUInt32).toNat + 8 ≤
      store.mem.pages * 65536 := by
  have hFitMemory := h.2.1
  rw [h.elementAddress_toNat i hi]
  omega

theorem At.generatedLengthBound {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (h : At store ptr values) :
    ptr.toNat % 4294967296 + 8 ≤ store.mem.pages * 65536 := by
  simpa [toUInt32_toNat] using h.lengthBound

theorem At.generatedElement {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (h : At store ptr values) (i : Nat)
    (hi : i < values.size) :
    (ptr.toNat + (i + 1) * 8) % 4294967296 + 8 ≤
        store.mem.pages * 65536 ∧
      store.mem.read64
        (UInt32.ofNat ((ptr.toNat + 8 * (i + 1)) % 4294967296)) =
        values[i] := by
  have hAddress := h.elementAddress_eq i hi
  constructor
  · have hBound :
        (UInt32.ofNat ((ptr.toNat + 8 * (i + 1)) %
          4294967296)).toNat + 8 ≤ store.mem.pages * 65536 := by
      rw [hAddress]
      exact h.elementBound i hi
    simpa [Nat.mul_comm] using hBound
  · rw [hAddress]
    exact h.elementRead i hi

theorem At.firstElementRead_add {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (h : At store ptr values)
    (hNonempty : 0 < values.size) :
    store.mem.read64 (ptr.toUInt32 + 8) = values[0] := by
  have hAddress := h.elementAddress_eq 0 hNonempty
  have hGeneratedAddress :
      UInt32.ofNat ((ptr.toNat + 8) % 4294967296) = ptr.toUInt32 + 8 := by
    apply UInt32.toNat.inj
    simp
  rw [← hGeneratedAddress, hAddress]
  exact h.elementRead 0 hNonempty

theorem At.size_lt {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (h : At store ptr values) :
    values.size < UInt64.size := by
  have hFit32 := h.1
  have hSize : UInt64.size = 18446744073709551616 := rfl
  omega

theorem At.encodedSize_eq {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (h : At store ptr values) {size : Nat}
    (hSize : size < UInt64.size) :
    UInt64.ofNat values.size = UInt64.ofNat size ↔ values.size = size := by
  constructor
  · intro heq
    have hNat := congrArg UInt64.toNat heq
    rw [UInt64.toNat_ofNat_of_lt' h.size_lt,
      UInt64.toNat_ofNat_of_lt' hSize] at hNat
    exact hNat
  · intro heq
    exact congrArg UInt64.ofNat heq

theorem At.encodedSize_eq_one {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (h : At store ptr values) :
    UInt64.ofNat values.size = 1 ↔ values.size = 1 := by
  simpa using h.encodedSize_eq (size := 1) (by norm_num [UInt64.size])

theorem At.frameBefore {initial final : Store Unit} {ptr : UInt64}
    {values : Array UInt64} {cutoff : Nat}
    (hEnd : ptr.toNat + 8 * (values.size + 1) ≤ cutoff)
    (hPages : final.mem.pages = initial.mem.pages)
    (hBytes : ∀ address : Nat, address < cutoff →
      final.mem.bytes address = initial.mem.bytes address)
    (h : At initial ptr values) :
    At final ptr values := by
  refine ⟨h.1, ?_, ?_, ?_⟩
  · rw [hPages]
    exact h.2.1
  · apply (read64_congr ptr.toUInt32 ?_).trans h.lengthRead
    intro i hi
    apply hBytes
    rw [h.pointerAddress_toNat]
    omega
  · intro i hi
    apply (read64_congr
      (ptr + UInt64.ofNat (8 * (i + 1))).toUInt32 ?_).trans
      (h.elementRead i hi)
    intro j hj
    apply hBytes
    rw [h.elementAddress_toNat i hi]
    omega

theorem At.write64After {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} {address : UInt32} {value : UInt64}
    (hAfter : ptr.toNat + 8 * (values.size + 1) ≤ address.toNat)
    (h : At store ptr values) :
    At { store with mem := store.mem.write64 address value } ptr values := by
  apply h.frameBefore hAfter
  · exact Mem.write64_pages ..
  · intro index hIndex
    exact write64_bytes_before store.mem address value hIndex

theorem singleton {store : Store Unit} {ptr value : UInt64}
    (hFit32 : ptr.toNat + 16 ≤ 4294967296)
    (hFitMemory : ptr.toNat + 16 ≤ store.mem.pages * 65536)
    (hLength : store.mem.read64 ptr.toUInt32 = 1)
    (hValue : store.mem.read64 (ptr + 8).toUInt32 = value) :
    At store ptr #[value] := by
  refine ⟨by simpa using hFit32, by simpa using hFitMemory, by simpa using hLength, ?_⟩
  intro i hi
  have hi0 : i = 0 := by simpa using hi
  subst i
  simpa using hValue

theorem pair {store : Store Unit} {ptr first second : UInt64}
    (hFit32 : ptr.toNat + 24 ≤ 4294967296)
    (hFitMemory : ptr.toNat + 24 ≤ store.mem.pages * 65536)
    (hLength : store.mem.read64 ptr.toUInt32 = 2)
    (hFirst : store.mem.read64 (ptr + 8).toUInt32 = first)
    (hSecond : store.mem.read64 (ptr + 16).toUInt32 = second) :
    At store ptr #[first, second] := by
  refine ⟨by simpa using hFit32, by simpa using hFitMemory, by simpa using hLength, ?_⟩
  intro i hi
  simp at hi
  interval_cases i
  · simpa using hFirst
  · simpa using hSecond

macro "uint64_array_singleton" : tactic =>
  `(tactic| apply Project.ProofKit.UInt64Array.singleton)

macro "uint64_array_pair" : tactic =>
  `(tactic| apply Project.ProofKit.UInt64Array.pair)

end Project.ProofKit.UInt64Array
