import Project.ProofKit.WordArrayPushProgram
import Project.ProofKit.FixedFrame

namespace Project.ProofKit.WordArrayPush
open Wasm

structure Scratch where
  source : UInt64
  length : UInt64
  count : UInt64
  nextLength : UInt64
  target : UInt64
  counter : UInt64
  value : UInt64
  spare0 : UInt64
  spare1 : UInt64
  need : UInt64
  previous : UInt64
  current : UInt64
  capacity : UInt64
  next : UInt64
  root : UInt64

def Scratch.words (s : Scratch) : List Wasm.Value :=
  [.i64 s.source, .i64 s.length, .i64 s.count, .i64 s.nextLength, .i64 s.target, .i64 s.counter, .i64 s.value, .i64 s.spare0, .i64 s.spare1, .i64 s.need, .i64 s.previous, .i64 s.current, .i64 s.capacity, .i64 s.next, .i64 s.root]

def Scratch.write (s : Scratch) (field : Nat) (value : UInt64) : Scratch :=
  match field with
  | 0 => { s with source := value }
  | 1 => { s with length := value }
  | 2 => { s with count := value }
  | 3 => { s with nextLength := value }
  | 4 => { s with target := value }
  | 5 => { s with counter := value }
  | 6 => { s with value := value }
  | 7 => { s with spare0 := value }
  | 8 => { s with spare1 := value }
  | 9 => { s with need := value }
  | 10 => { s with previous := value }
  | 11 => { s with current := value }
  | 12 => { s with capacity := value }
  | 13 => { s with next := value }
  | 14 => { s with root := value }
  | _ => s

def frame (params saved tail : List Wasm.Value) (s : Scratch) : Locals :=
  { params := params, locals := saved ++ (s.words ++ tail), values := [] }

theorem frame_get (params saved tail : List Wasm.Value) (s : Scratch)
    (field : Nat) (hf : field < 15) :
    (frame params saved tail s).get (params.length + saved.length + field) = s.words[field]? := by
  interval_cases field <;> simp [frame, Scratch.words, Locals.get, Nat.add_assoc]

theorem frame_set (params saved tail : List Wasm.Value) (s : Scratch)
    (field : Nat) (hf : field < 15) (value : UInt64) :
    (frame params saved tail s).set? (params.length + saved.length + field) (.i64 value) =
      some (frame params saved tail (s.write field value)) := by
  interval_cases field <;> simp [frame, Scratch.words, Scratch.write, Locals.set?, Nat.add_assoc]

private theorem set_withValues (f : Locals) (stack : List Wasm.Value) (index : Nat)
    (value : Wasm.Value) :
    ({ f with values := stack } : Locals).set? index value =
      (f.set? index value).map (fun next => { next with values := stack }) := by
  by_cases hp : index < f.params.length <;>
    by_cases hl : index < f.params.length + f.locals.length <;>
    simp [Locals.set?, hp, hl]

theorem frame_set_values (params saved tail : List Wasm.Value) (s : Scratch)
    (field : Nat) (hf : field < 15) (value : UInt64) (stack : List Wasm.Value) :
    ({ frame params saved tail s with values := stack } : Locals).set?
      (params.length + saved.length + field) (.i64 value) =
      some { frame params saved tail (s.write field value) with values := stack } := by
  rw [set_withValues, frame_set params saved tail s field hf value]
  rfl

theorem frame_values (params saved tail : List Wasm.Value) (s : Scratch) :
    (frame params saved tail s).values = [] := rfl

theorem frame_with_empty (params saved tail : List Wasm.Value) (s : Scratch) :
    ({ frame params saved tail s with values := [] } : Locals) = frame params saved tail s := rfl

def allocationSaved (saved : List Wasm.Value) (s : Scratch) : List Wasm.Value :=
  saved ++ [.i64 s.source, .i64 s.length, .i64 s.count, .i64 s.nextLength, .i64 s.target, .i64 s.counter, .i64 s.value, .i64 s.spare0, .i64 s.spare1]

theorem allocationSaved_length (saved : List Wasm.Value) (s : Scratch) :
    (allocationSaved saved s).length = saved.length + 9 := by simp [allocationSaved]

theorem frame_as_search (params saved tail : List Wasm.Value) (s : Scratch) :
    frame params saved tail s =
      FixedArraySearch.frame params (allocationSaved saved s) tail
        s.need s.previous s.current s.capacity s.next s.root := by
  simp [frame, Scratch.words, allocationSaved, FixedArraySearch.frame, List.append_assoc]

#print axioms frame_get
#print axioms frame_set
#print axioms frame_as_search
end Project.ProofKit.WordArrayPush
