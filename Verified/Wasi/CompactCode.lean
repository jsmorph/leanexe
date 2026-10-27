import Verified.Bound

/-! The compaction of a process state.  After `begin` and after each step, the process entry
copies the state's arrays and byte strings to fresh blocks above the heap top, moves those blocks
down to the heap base that `_start` saved, subtracts the distance of the move from each root, and
sets the heap top just past the moved blocks with an empty free list.  The heap then holds the
literal pool and the current state and nothing else, so its use stays within the state's copy
cost whatever the steps allocated.  Stage 1 compacts states without trees. -/

namespace Verified.Wasi

open Wasm

/-- Whether the process entry compacts a state of type `t`: the state holds no tree. -/
def _root_.Verified.Ty.compactable : Ty → Bool
  | .elem _ | .array _ | .bytes => true
  | .pair a b => a.compactable && b.compactable
  | _ => false

theorem _root_.Verified.Ty.compactable_pair {a b : Ty}
    (h : (Ty.pair a b).compactable = true) : a.compactable = true ∧ b.compactable = true := by
  simpa [Ty.compactable] using h

/-- The words of a value of type `t` after the move of its blocks down by `delta` bytes: each array
root and each nonzero byte root less `delta`.  An empty byte string's root 0 stays 0. -/
def relocateWords (delta : UInt64) : Ty → List Value → List Value
  | .pair a b, ws => relocateWords delta a (ws.take a.width) ++ relocateWords delta b (ws.drop a.width)
  | .array _, ws => match ws with
    | [.i64 ptr] => [.i64 (ptr - delta)]
    | _ => ws
  | .bytes, ws => match ws with
    | [.i64 root, .i64 length] => [.i64 (if root = 0 then 0 else root - delta), .i64 length]
    | _ => ws
  | _, ws => ws

/-- The instructions that subtract the word in local `delta` from each array root and each
nonzero byte root of the value of type `t` whose words positions `loc` on hold.  A root is an
i64, so it lies in local `loc` itself. -/
def relocateCode (delta : Nat) : Ty → Nat → Program
  | .pair a b, loc => relocateCode delta a loc ++ relocateCode delta b (loc + a.width)
  | .array _, loc => [.localGet loc, .localGet delta, .subI64, .localSet loc]
  | .bytes, loc => [.localGet loc, .constI64 0, .neI64,
      .iff 0 0 [.localGet loc, .localGet delta, .subI64, .localSet loc] [] [] []]
  | _, _ => []

/-- The loop that moves the bytes from the address in local `src`, as many as local `count`
holds rounded up to a word, down to the address in local `dst`, a word at a time from the lowest
address up.  Local `index` holds the byte offset.  When `dst` is at most `src`, the loop reads
each word before any write reaches it. -/
def moveCode (dst src count index : Nat) : Program :=
  [.constI64 0, .localSet index,
    .block 0 0 [.loop 0 0 [.localGet index, .localGet count, .geUI64, .br_if 1,
      .localGet dst, .localGet index, .addI64, .wrapI64,
      .localGet src, .localGet index, .addI64, .wrapI64, .load64 0, .store64 0,
      .localGet index, .constI64 8, .addI64, .localSet index, .br 0]]]

/-- The compaction of the value of type `t` whose words positions `loc` on hold, in a function
with `h` positions.  Local `aux` holds the heap base; `aux + 1` holds the heap top rounded up to a
word, where the copy starts; `aux + 2` the copy's bytes; `aux + 3` the move's offset; and `aux + 4`
the distance of the move.  The copy's scratch positions start at `aux + 5`.  The code empties the
free list, so that the copy's blocks lie above the start, and empties it again at the end. -/
def compactCode (h : Nat) (t : Ty) (loc aux : Nat) : Program :=
  [.constI64 0, .globalSet 1,
    .globalGet 0, .constI64 7, .addI64, .constI64 8, .divUI64, .constI64 8, .mulI64,
    .localSet (aux + 1), .localGet (aux + 1), .globalSet 0] ++
  copyCode h t loc (aux + 5) ++ storeCode h loc t.types ++
  [.globalGet 0, .localGet (aux + 1), .subI64, .localSet (aux + 2)] ++
  moveCode aux (aux + 1) (aux + 2) (aux + 3) ++
  [.localGet (aux + 1), .localGet aux, .subI64, .localSet (aux + 4)] ++
  relocateCode (aux + 4) t loc ++
  [.localGet aux, .localGet (aux + 2), .addI64, .globalSet 0, .constI64 0, .globalSet 1]

/-- `n` rounded up to a multiple of 8. -/
def roundWord (n : Nat) : Nat := 8 * ((n + 7) / 8)

theorem roundWord_le (n : Nat) : n ≤ roundWord n := by
  unfold roundWord; omega

theorem roundWord_lt (n : Nat) : roundWord n < n + 8 := by
  unfold roundWord; omega

theorem roundWord_mod (n : Nat) : roundWord n % 8 = 0 := by
  unfold roundWord; omega

/-- A multiple of 8 at least `n` is at least `n` rounded up to a word. -/
theorem roundWord_le_of_mod {n m : Nat} (h : n ≤ m) (hm : m % 8 = 0) : roundWord n ≤ m := by
  unfold roundWord; omega

/-- Room for `c` bytes after `n`, both below a multiple of 8, when `c` is a multiple of 8, is room
for `c` bytes after `n` rounded up. -/
theorem roundWord_add_le {n c m : Nat} (h : n + c ≤ m) (hc : c % 8 = 0) (hm : m % 8 = 0) :
    roundWord n + c ≤ m := by
  unfold roundWord; omega

theorem _root_.Verified.Bytes.allocationCost_mod (count : Nat) :
    Bytes.allocationCost count % 8 = 0 := by
  unfold Bytes.allocationCost
  split <;> omega

/-- The copy cost of a compactable value is a multiple of 8: each block costs a 48-byte header and
a payload of whole words. -/
theorem _root_.Verified.Ty.copyCost_mod (t : Ty) (ht : t.compactable = true) (v : t.denote) :
    t.copyCost v % 8 = 0 := by
  induction t with
  | elem => simp [Ty.copyCost]
  | array e =>
    simp only [Ty.copyCost, allocCost]
    generalize v.size * e.width = k
    omega
  | bytes => simpa only [Ty.copyCost] using Bytes.allocationCost_mod v.data.size
  | pair a b iha ihb =>
    obtain ⟨ha, hb⟩ := Ty.compactable_pair ht
    have := iha ha v.1
    have := ihb hb v.2
    simp only [Ty.copyCost]
    omega
  | _ => simp [Ty.compactable] at ht

theorem relocateWords_length (delta : UInt64) (t : Ty) :
    ∀ ws : List Value, ws.length = t.width → (relocateWords delta t ws).length = t.width := by
  induction t with
  | pair a b iha ihb =>
    intro ws h
    simp only [relocateWords, List.length_append]
    rw [iha _ (by simp [List.length_take, h, Ty.width]),
      ihb _ (by simp [List.length_drop, h, Ty.width])]
    rfl
  | array =>
    intro ws h
    simp only [relocateWords]
    split <;> simp_all
  | bytes =>
    intro ws h
    simp only [relocateWords]
    split <;> simp_all
  | _ => intro ws h; simpa [relocateWords] using h

end Verified.Wasi
