import Verified.Bytes.Step

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.Pipeline.Bytes

theorem represented_length {heap : Heap} {store : Store Unit} {values : List Value}
    {bytes : LeanExe.Bytes} (h : represented heap store values bytes) : values.length = 2 := by
  obtain ⟨root, length, rfl, _⟩ := h
  rfl

theorem roots_regions (store : Store Unit) (root length : UInt64) :
    (roots [.i64 root, .i64 length]).map (block store) = regions store root := by
  by_cases h : root = 0 <;> simp [roots, regions, h]

end Verified.Bytes
