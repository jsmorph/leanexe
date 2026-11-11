import Library.Graphs.TopologicalSort.Compiled
import Verified.Master

namespace Library.Graphs.TopologicalSort

/-- The export `topoSort`, called on a well-formed array of a vertex count and pairs of vertices,
returns a topological order of the vertices, or the empty array when no topological order
exists. -/
theorem topoSort_master :
    Verified.Master compiled.module compiled.tables "topoSort" compiled.topoSort.bound
      (fun xs : Array UInt64 => Valid xs)
      (fun xs (y : Array UInt64) => IsTopologicalOrder xs y ∨
        (y = #[] ∧ ∀ order, ¬ IsTopologicalOrder xs order)) :=
  .of_trapFree (.ofA compiled.topoSort.trapFree) nofun topoSort_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs ⟨_, _, hxs⟩ hv => topoSort_spec xs hv hxs.values.size_lt

#print axioms topoSort_master

end Library.Graphs.TopologicalSort
