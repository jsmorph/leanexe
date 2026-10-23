import Verified.Wasi.HostSpec
import Verified.Wasi.WrapperCode
import LeanExe.ProofKit.MemoryFrame
import Verified.LocalFrame

namespace Verified.Wasi

open Wasm LeanExe.ProofKit LeanExe.ProofKit.Memory

theorem write32_bytes_outside (mem : Mem) (address value : UInt32) {index : Nat}
    (h : index < address.toNat ∨ address.toNat + 4 ≤ index) :
    (mem.write32 address value).bytes index = mem.bytes index := by
  unfold Mem.write32
  dsimp only
  split_ifs <;> first | rfl | omega

theorem read32_congr {first second : Mem} (address : UInt32)
    (h : ∀ index : Nat, index < 4 →
      first.bytes (address.toNat + index) = second.bytes (address.toNat + index)) :
    first.read32 address = second.read32 address := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  rw [Nat.add_zero] at h0
  simp only [Mem.read32]
  rw [h0, h1, h2, h3]

theorem read32_write32_disjoint (mem : Mem) (address value readAddress : UInt32)
    (h : readAddress.toNat + 4 ≤ address.toNat ∨ address.toNat + 4 ≤ readAddress.toNat) :
    (mem.write32 address value).read32 readAddress = mem.read32 readAddress :=
  read32_congr readAddress fun index hi => write32_bytes_outside mem address value (by omega)

theorem read32_write32 (mem : Mem) (address value : UInt32) :
    (mem.write32 address value).read32 address = value := by
  simp only [Mem.read32, Mem.write32]
  simp only [Nat.add_eq_left, OfNat.ofNat_ne_zero, Nat.succ_ne_self, reduceIte,
    Nat.reduceEqDiff]
  apply UInt32.toBitVec_inj.mp
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight,
    UInt32.toBitVec_and, UInt8.toBitVec_toUInt32, UInt32.toBitVec_toUInt8]
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  interval_cases bit <;> simp [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']

theorem write32_range (store : Store World) (address value : UInt32)
    (start stop : Nat) (hStart : start ≤ address.toNat) (hStop : address.toNat + 4 ≤ stop) :
    WritesRange store { store with mem := store.mem.write32 address value } start stop :=
  ⟨rfl, rfl, fun _ hOutside => write32_bytes_outside _ _ _ (by omega)⟩

def initializeScratch (store : Store World) (pointer length : UInt32) : Store World :=
  { store with mem := ((store.mem.write32 0 pointer).write32 4 length).write32 8 0 }

theorem initializeScratch_range (store : Store World) (pointer length : UInt32) :
    WritesRange store (initializeScratch store pointer length) 0 16 :=
  ((write32_range store 0 pointer 0 16 (by decide) (by decide)).trans
    (write32_range _ 4 length 0 16 (by decide) (by decide))).trans
      (write32_range _ 8 0 0 16 (by decide) (by decide))

theorem initializeScratch_reads (store : Store World) (pointer length : UInt32) :
    (initializeScratch store pointer length).mem.read32 0 = pointer ∧
      (initializeScratch store pointer length).mem.read32 4 = length ∧
      (initializeScratch store pointer length).mem.read32 8 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (read32_write32_disjoint _ 8 0 0 (by decide)).trans
      ((read32_write32_disjoint _ 4 length 0 (by decide)).trans (read32_write32 _ 0 pointer))
  · exact (read32_write32_disjoint _ 8 0 4 (by decide)).trans (read32_write32 _ 4 length)
  · exact read32_write32 _ 8 0

theorem wp_metadata {m : Module} {host : HostEnv World} {store : Store World} {s : Locals}
    {pointer length : UInt64} {pointerSlot lengthSlot : Nat} {rest : Program}
    {Q : Assertion World}
    (hPointer : s.get pointerSlot = some (.i64 pointer))
    (hLength : s.get lengthSlot = some (.i64 length))
    (hMemory : 16 ≤ store.mem.pages * 65536)
    (hNext : wp m rest Q (initializeScratch store pointer.toUInt32 length.toUInt32) s host) :
    wp m (metadataCode pointerSlot lengthSlot ++ rest) Q store s host := by
  simp only [metadataCode, List.cons_append, List.nil_append, wp_const_cons,
    wp_localGet_cons, Locals.get_values, hPointer, hLength, wp_wrapI64_cons, wrap_toUInt32,
    wp_store32_cons, UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero]
  rw [ite_eq_right (by omega)]
  simp only [Mem.write32, UInt32.reduceToNat]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  exact hNext

end Verified.Wasi
