import Verified.Bytes.Step

namespace Verified.Bytes

open Wasm LeanExe.Pipeline

def roots : List Value → List UInt64
  | [.i64 root, .i64 _] => if root = 0 then [] else [root]
  | _ => []

def represented (heap : Heap) (store : Store Unit) (values : List Value)
    (bytes : LeanExe.Bytes) : Prop :=
  ∃ root length, values = [.i64 root, .i64 length] ∧ Rep heap store root length bytes

instance : Represent LeanExe.Bytes where
  width _ := 2
  borrowed := represented
  owned := represented
  blocks store values _ := (roots values).map (block store)
  reads store values _ := (roots values).map (block store)
  moves _ _ _ := []

instance : Represent (Moved LeanExe.Bytes) where
  width _ := 2
  borrowed heap store values bytes := represented heap store values bytes.val
  owned heap store values bytes := represented heap store values bytes.val
  blocks store values _ := (roots values).map (block store)
  reads _ _ _ := []
  moves _ values _ := roots values

theorem represented_length {heap : Heap} {store : Store Unit} {values : List Value}
    {bytes : LeanExe.Bytes} (h : represented heap store values bytes) : values.length = 2 := by
  obtain ⟨root, length, rfl, _⟩ := h
  rfl

theorem roots_regions (store : Store Unit) (root length : UInt64) :
    (roots [.i64 root, .i64 length]).map (block store) = regions store root := by
  by_cases h : root = 0 <;> simp [roots, regions, h]

end Verified.Bytes
