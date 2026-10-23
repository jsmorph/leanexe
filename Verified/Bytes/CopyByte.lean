import Verified.Bytes.Write

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.ProofKit

def copyByteCode (source destination index : Nat) : Program :=
  [.localGet destination, .localGet index, .addI64, .wrapI64,
   .localGet source, .localGet index, .addI64, .wrapI64, .load8U 0, .store8 0]

theorem wp_copyByte {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {source destination index : UInt64} {input output : LeanExe.Bytes}
    {sourceSlot destinationSlot indexSlot : Nat} {rest : Program} {Q : Assertion Unit}
    (hHeap : heap.At store) (hSource : At store.mem source input)
    (hDestination : Allocated heap store destination output)
    (hIndex : index.toNat < input.data.size) (hOutput : index.toNat < output.data.size)
    (hSourceLocal : s.get sourceSlot = some (.i64 source))
    (hDestinationLocal : s.get destinationSlot = some (.i64 destination))
    (hIndexLocal : s.get indexSlot = some (.i64 index))
    (hNext : wp m rest Q (writeByte store destination index input.data[index.toNat]) s host) :
    wp m (copyByteCode sourceSlot destinationSlot indexSlot ++ rest) Q store s host := by
  have hAddress := hSource.index_address index hIndex
  have hInputMemory := hSource.memory
  have hMemory : ¬ store.mem.pages * 65536 < (source + index).toUInt32.toNat + 1 := by
    rw [hAddress]
    omega
  simp only [copyByteCode, List.cons_append, List.nil_append, wp_localGet_cons,
    Locals.get_values, hSourceLocal, hDestinationLocal, hIndexLocal,
    wp_addI64_cons, wp_wrapI64_cons, wrap_toUInt32, wp_load8U_cons,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right hMemory, hSource.read8 index hIndex]
  have hCast (value : UInt8) : value.toUInt32.toUInt8 = value := by
    apply UInt8.toNat_inj.mp
    simp only [UInt32.toNat_toUInt8, UInt8.toNat_toUInt32]
    exact Nat.mod_eq_of_lt value.toNat_lt
  refine wp_store hHeap hDestination hOutput ?_
  simpa only [hCast] using hNext

end Verified.Bytes
