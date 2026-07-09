import Project.LebU32.Program
import Project.Common
import Project.LebU32.Exit

/-!
# Specification for the self-compiled LEB128 encoder — assembly in progress

The artifact is the compiler's own unsigned LEB128 encoder, compiled by the
compiler.  This file gates the decoded model's presence; the byte-identity
check confirms the shipped artifact matches the checked-in proof input.

The correctness proof is partway.  `LeanExe/Wasm/LebTheorems.lean` proves
`u32lebU64_eq_lebList`, identifying the shipped encoder with a pure
recursion.  The sorry-free artifact step lemmas live in the sibling files
`Defs.lean`, `Copy.lean` (`copyStepPos`), `Exit.lean` (`tailStepPos`), and
and the final-byte iteration.  What remains is the continuation-byte
branch and the export wrapper, composed into
`func0_encodes`: the export returns a pointer to exactly `lebList 10 n`.

The encoder's self-compilation is verified independently by
`test/self_emit.js`, which pins the compiled artifact's output against a
reference over the encoding domain's boundary values.
-/

namespace Project.LebU32.Spec

end Project.LebU32.Spec
