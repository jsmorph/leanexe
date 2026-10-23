import Verified.Bytes.Memory

namespace Verified.Bytes

open Wasm

abbrev Literal := List UInt8

def Literal.value (bytes : Literal) : LeanExe.Bytes := ⟨⟨bytes.toArray⟩⟩

def literalOffset : List Literal → Literal → Option Nat
  | [], _ => none
  | head :: tail, bytes =>
    if head = bytes then some 0 else (literalOffset tail bytes).map (head.length + ·)

theorem literalOffset_exists {pool : List Literal} {bytes : Literal} (h : bytes ∈ pool) :
    ∃ offset, literalOffset pool bytes = some offset := by
  induction pool with
  | nil => cases h
  | cons head tail ih =>
    by_cases hHead : head = bytes
    · exact ⟨0, by simp [literalOffset, hHead]⟩
    · obtain ⟨offset, hOffset⟩ :=
        ih ((List.mem_cons.mp h).resolve_left fun hEq => hHead hEq.symm)
      exact ⟨head.length + offset, by simp [literalOffset, hHead, hOffset]⟩

theorem literalOffset_split {pool : List Literal} {bytes : Literal} {offset : Nat}
    (h : literalOffset pool bytes = some offset) :
    ∃ before after, pool = before ++ bytes :: after ∧ offset = before.flatten.length := by
  induction pool generalizing offset with
  | nil => simp [literalOffset] at h
  | cons head tail ih =>
    by_cases hHead : head = bytes
    · subst head
      simp [literalOffset] at h
      subst offset
      exact ⟨[], tail, rfl, rfl⟩
    · simp only [literalOffset, ite_eq_right hHead, Option.map_eq_some_iff] at h
      obtain ⟨offset', hOffset, rfl⟩ := h
      obtain ⟨before, after, rfl, rfl⟩ := ih hOffset
      exact ⟨head :: before, after, rfl, by simp⟩

theorem literalOffset_bound {pool : List Literal} {bytes : Literal} {offset : Nat}
    (h : literalOffset pool bytes = some offset) :
    offset + bytes.length ≤ pool.flatten.length := by
  obtain ⟨before, after, rfl, rfl⟩ := literalOffset_split h
  simp only [List.flatten_append, List.flatten_cons, List.length_append]
  omega

theorem literalOffset_byte {pool : List Literal} {bytes : Literal} {offset index : Nat}
    (h : literalOffset pool bytes = some offset) (hi : index < bytes.length) :
    pool.flatten[offset + index]? = some bytes[index] := by
  obtain ⟨before, after, rfl, rfl⟩ := literalOffset_split h
  simp only [List.flatten_append, List.flatten_cons]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hi, List.getElem?_eq_getElem hi]

structure LiteralPool where
  base : Nat
  values : List Literal

namespace LiteralPool

def payload (pool : LiteralPool) : Literal := pool.values.flatten

def endAddress (pool : LiteralPool) : Nat := pool.base + pool.payload.length

def top (pool : LiteralPool) : Nat := 8 * ((pool.endAddress + 7) / 8)

def segments (pool : LiteralPool) : List DataSegment :=
  if pool.payload = [] then [] else
    [{ offset := some (UInt32.ofNat pool.base), bytes := pool.payload }]

def Valid (pool : LiteralPool) (mem : Mem) : Prop :=
  pool.endAddress ≤ 2 ^ 32 ∧ pool.endAddress ≤ mem.pages * 65536 ∧
    ∀ index byte, pool.payload[index]? = some byte → mem.bytes (pool.base + index) = byte

theorem top_ge (pool : LiteralPool) : pool.endAddress ≤ pool.top := by
  unfold top
  omega

theorem top_lt (pool : LiteralPool) : pool.top < pool.endAddress + 8 := by
  unfold top
  omega

theorem top_aligned (pool : LiteralPool) : pool.top % 8 = 0 := by
  simp [top]

theorem top_empty (base : Nat) (h : base % 8 = 0) : (LiteralPool.mk base []).top = base := by
  simp only [top, endAddress, payload, List.flatten_nil, List.length_nil, Nat.add_zero]
  omega

theorem segments_empty (base : Nat) : (LiteralPool.mk base []).segments = [] := rfl

theorem Valid.frame {pool : LiteralPool} {mem mem' : Mem} (h : pool.Valid mem)
    (hMemory : pool.endAddress ≤ mem'.pages * 65536)
    (hBytes : ∀ address, pool.base ≤ address → address < pool.endAddress →
      mem'.bytes address = mem.bytes address) : pool.Valid mem' := by
  refine ⟨h.1, hMemory, ?_⟩
  intro index byte hLookup
  have hi := (List.getElem?_eq_some_iff.mp hLookup).1
  exact (hBytes _ (by omega) (by dsimp only [endAddress]; omega)).trans (h.2.2 _ _ hLookup)

theorem Valid.literal_bounds {pool : LiteralPool} {mem : Mem} (h : pool.Valid mem)
    {bytes : Literal} {offset : Nat} (hOffset : literalOffset pool.values bytes = some offset) :
    pool.base ≤ (UInt64.ofNat (pool.base + offset)).toNat ∧
      (UInt64.ofNat (pool.base + offset)).toNat + bytes.value.data.size ≤ pool.endAddress := by
  have hBound := literalOffset_bound hOffset
  have hEnd : pool.base + pool.values.flatten.length ≤ 2 ^ 32 := h.1
  rw [UInt64.toNat_ofNat_of_lt' (by change pool.base + offset < 2 ^ 64; omega)]
  simp only [Literal.value, ByteArray.size, List.size_toArray]
  dsimp only [endAddress, payload]
  omega

theorem Valid.literal {pool : LiteralPool} {mem : Mem} (h : pool.Valid mem)
    {bytes : Literal} {offset : Nat} (hOffset : literalOffset pool.values bytes = some offset) :
    At mem (UInt64.ofNat (pool.base + offset)) bytes.value := by
  have hBound := literalOffset_bound hOffset
  have hEnd : pool.base + pool.values.flatten.length ≤ 2 ^ 32 := h.1
  have hMemory : pool.base + pool.values.flatten.length ≤ mem.pages * 65536 := h.2.1
  have hRoot : pool.base + offset < 2 ^ 64 := by
    omega
  have hRootNat : (UInt64.ofNat (pool.base + offset)).toNat = pool.base + offset :=
    UInt64.toNat_ofNat_of_lt' hRoot
  have hSize : bytes.value.data.size = bytes.length := by simp [Literal.value, ByteArray.size]
  refine ⟨?_, ?_, ?_⟩
  · rw [hRootNat, hSize]
    omega
  · rw [hRootNat, hSize]
    omega
  · intro index hi
    have hi' : index < bytes.length := by rwa [hSize] at hi
    have hByte : pool.payload[offset + index]? = some bytes[index] :=
      literalOffset_byte hOffset hi'
    rw [hRootNat, Nat.add_assoc, h.2.2 (offset + index) _ hByte]
    simp [Literal.value, ByteArray.getElem_eq_getElem_data]

end LiteralPool
end Verified.Bytes
