import Library.Graphs.Dijkstra.Compiled
import Verified.Master

namespace Library.Graphs.Dijkstra

/-- The export `dijkstra`, called on a vertex count `n`, a source `s`, and a graph in forward-star
form `first`, `heads`, `lens` that `WellFormed` accepts, returns an array of `n` words whose word
`v` is the least length of a walk from `s` to `v` when that length is below `2 ^ 64 - 1`, and
`2 ^ 64 - 1` otherwise. -/
theorem dijkstra_master :
    Verified.Master compiled.module compiled.tables "dijkstra" compiled.dijkstra.bound
      (fun x : UInt64 × UInt64 × Array UInt64 × Array UInt64 × Array UInt64 =>
        WellFormed x.1.toNat x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (fun x (y : Array UInt64) =>
        Distances x.1.toNat x.2.1.toNat x.2.2.1 x.2.2.2.1 x.2.2.2.2 y) :=
  .of_trapFree (.ofA compiled.dijkstra.trapFree) nofun dijkstra_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ hwf => dijkstra_spec x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 hwf

#print axioms dijkstra_master

end Library.Graphs.Dijkstra
