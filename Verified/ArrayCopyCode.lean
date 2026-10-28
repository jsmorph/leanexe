import LeanExe.Runtime.Defs

/-! The code that allocates and copies arrays, which the copy of values and the copy of trees
both use. -/

namespace Verified

open Wasm

/-- The instructions that allocate a block of the byte count on top of the stack, put its address
in local `ptr`, and write the word in local `len` as its length word. -/
def allocBlockCode (len ptr : Nat) : Program :=
  [.call 0, .localSet ptr, .localGet ptr, .wrapI64, .localGet len, .store64 0]

/-- The instructions that allocate an array of as many words as local `count` holds, put its
address in local `ptr`, and write its length word. -/
def allocArrayCode (count ptr : Nat) : Program :=
  [.localGet count, .constI64 1, .addI64, .constI64 8, .mulI64] ++ allocBlockCode count ptr

/-- The loop that copies the elements of the array at the address in local `src`, as many as
local `count` holds, to the words from the address in local `dst` on, element `i` to the word at
`dst + (i + 1) * 8`.  Local `index` holds the index. -/
def copyIntoCode (src dst count index : Nat) : Program :=
  [.constI64 0, .localSet index,
    .block 0 0 [.loop 0 0 [.localGet index, .localGet count, .geUI64, .br_if 1,
      .localGet dst, .localGet index, .constI64 1, .addI64, .constI64 8, .mulI64, .addI64,
      .wrapI64,
      .localGet src, .localGet index, .constI64 1, .addI64, .constI64 8, .mulI64, .addI64,
      .wrapI64, .load64 0, .store64 0,
      .localGet index, .constI64 1, .addI64, .localSet index, .br 0]]]

/-- The instructions that copy the array whose address local `src` holds into a new array and
push the new array's address.  Local `base` holds the length, `base + 1` the new address, and
`base + 2` the index of the element being copied. -/
def copyArrayCode (src base : Nat) : Program :=
  [.localGet src, .wrapI64, .load64 0, .localSet base] ++ allocArrayCode base (base + 1) ++
    copyIntoCode src (base + 1) base (base + 2) ++ [.localGet (base + 1)]

end Verified
