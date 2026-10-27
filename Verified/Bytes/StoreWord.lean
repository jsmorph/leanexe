import Verified.Bytes.Write

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.ProofKit

theorem wp_storeWord {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {root index value : UInt64} {bytes : LeanExe.Bytes}
    {vs : List Value} {rest : Program} {Q : Assertion Unit}
    (hHeap : heap.At store) (h : Heap.Buffer heap store root bytes)
    (hi : index.toNat < bytes.data.size)
    (hNext : wp m rest Q (writeByte store root index value.toUInt8)
      { s with values := vs } host) :
    wp m (.wrapI64 :: .store8 0 :: rest) Q store
      { s with values := .i64 value :: .i32 (root + index).toUInt32 :: vs } host := by
  simp only [wp_wrapI64_cons, wrap_toUInt32]
  exact wp_store hHeap h hi (by simpa only [UInt64.toUInt8_toUInt32] using hNext)

end Verified.Bytes
