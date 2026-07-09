import Project.LebU32.Main

/-!
# Specification for the self-compiled LEB128 encoder

The artifact is the compiler's own unsigned LEB128 encoder, compiled by the
compiler.  `Main.lean` proves `u32lebU64_correct`: for every `n` below
`2 ^ 32` the export returns a pointer to a buffer holding exactly the bytes
of `lebList 10 n`, together with its length, leaving every byte below the
old heap top unchanged.

`lebList` is the pure recursion that `LeanExe/Wasm/LebTheorems.lean` proves
equal to the shipped source encoder (`u32lebU64_eq_lebList`).  Composing the
two gives the end-to-end statement: the WASM the compiler emits for its own
encoder computes the encoder.

The byte-identity check pins the decoded model to the artifact the compiler
ships, and `test/self_emit.js` independently exercises the compiled encoder
against a reference.
-/

namespace Project.LebU32.Spec

end Project.LebU32.Spec
