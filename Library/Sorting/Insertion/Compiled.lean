import Library.Sorting.Insertion.Proof
import Verified.Reflect.Command
import Verified.Call

/-! The verified compiler's module of `sortInsert`.  The function borrows its input and builds the
sorted array as the state of its loop, which grows in its own block.  `sortInsert_callSpec` composes
the generated `compiled.sortInsert.trapFree` with `sortInsert_eq`. -/

namespace Library.Sorting.Insertion

open Wasm LeanExe.Pipeline

set_option verified_compile.alignedNative true in
verified_compile compiled := [sortInsert]

theorem sortInsert_export :
    ({ name := "sortInsert", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- From a ready store with room for `compiled.sortInsert.bound xs` bytes, function 2, the export
`sortInsert`, returns without a trap the owned array `expected xs`, the elements of `xs` in
nondecreasing order, and leaves a ready store. -/
theorem sortInsert_callSpec :
    Verified.CallSpec compiled.module compiled.tables 2 expected compiled.sortInsert.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.sortInsert.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, hxs⟩ => sortInsert_eq x (show _ < 2 ^ 64 from hxs.values.size_lt)

#print axioms sortInsert_callSpec

end Library.Sorting.Insertion
