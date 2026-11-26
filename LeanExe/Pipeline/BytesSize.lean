module

public import LeanExe.Pipeline.Bytes

@[expose] public section

/-! The size of a buffer that a store holds, which the call theorems of functions on buffers use
to meet the size premises of their programs' equations. -/

namespace LeanExe.Pipeline.Bytes

/-- A buffer that a store holds has fewer than `2 ^ 32` bytes. -/
theorem size_lt_of_borrowed {heap : Heap} {store : Wasm.Store Unit} {params : List Wasm.Value}
    {b : LeanExe.Bytes} (h : Represent.borrowed heap store params b) : b.data.size < 2 ^ 32 := by
  obtain ⟨root, length, -, hrep⟩ := h
  rcases hrep.buffer with ⟨-, h0⟩ | hbuf
  · omega
  · have h1 := hbuf.object.address
    have h2 := hbuf.capacity
    omega

end LeanExe.Pipeline.Bytes
