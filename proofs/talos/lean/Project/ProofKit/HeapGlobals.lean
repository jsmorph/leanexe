import Project.EulerRiemann.HeapState

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime

/-- Read the live runtime slots while preserving every unaccessed global. -/
def Heap.fromGlobals (store : Store Unit) (top allocations releases frees : UInt64) : Heap :=
  { top, nodes := [], allocations, retains := 0, releases, frees
    retainsOverride := store.globals.globals[3]?
    extraGlobals := store.globals.globals.drop 6 }

theorem Heap.fromGlobals_at (store : Store Unit) (top allocations releases frees : UInt64)
    (h0 : store.globals.globals[0]? = some (.i64 top))
    (h1 : store.globals.globals[1]? = some (.i64 0))
    (h2 : store.globals.globals[2]? = some (.i64 allocations))
    (h4 : store.globals.globals[4]? = some (.i64 releases))
    (h5 : store.globals.globals[5]? = some (.i64 frees)) :
    (Heap.fromGlobals store top allocations releases frees).At store := by
  refine ⟨?_, FreeListAt.nil, by simp [Heap.fromGlobals]⟩
  have hLength := (List.getElem?_eq_some_iff.mp h5).choose
  have h3 := List.getElem?_eq_getElem (show 3 < store.globals.globals.length by omega)
  apply List.ext_getElem?
  intro index
  by_cases hi : index < 6
  · interval_cases index <;>
      simp only [Heap.fromGlobals, Heap.globals, freeHead, List.cons_append, List.nil_append,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, h0, h1, h2, h3, h4, h5]
  · simp only [Heap.fromGlobals, Heap.globals, List.getElem?_append, List.length_cons,
      List.length_nil, Nat.reduceAdd, hi, ite_false, List.getElem?_drop]
    congr 1
    omega

#print axioms Heap.fromGlobals_at
end Project.EulerRiemann.Execution
