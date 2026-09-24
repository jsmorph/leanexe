import Project.LebU32.Main

/-!
# Specification for the self-compiled LEB128 encoder

The current generated encoder reuses two 56-byte objects.  `u32lebU64_correct`
proves termination, exact bytes, the returned pointer and length, ownership,
the final allocator globals, an unchanged page count, and preservation of
bytes below the starting heap top.  Its entry conditions describe the six
allocator globals, an empty free list, 112 bytes of available memory, and
a memory limit consistent with the store.  `u32leb_initial_correct` discharges
these conditions for the generated module's initial store and covers every
input below `2 ^ 32`.

`lebList` is the pure recursion that `LeanExe/Wasm/LebTheorems.lean` proves
equal to the shipped source encoder (`u32lebU64_eq_lebList`).  Composing the
two gives the end-to-end statement: the WASM the compiler emits for its own
encoder computes the encoder.

The historical exact-byte package uses `FrozenSpec` and its original
allocation schedule.  `test/self_emit.js` exercises the current compiled
encoder against a reference.
-/

namespace Project.LebU32.Spec

end Project.LebU32.Spec
