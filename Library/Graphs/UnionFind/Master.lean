import Library.Graphs.UnionFind.Compiled
import Verified.Master

namespace Library.Graphs.UnionFind

/-- The export `classes`, called on a count `n` and arrays `js` and `ks` of pairs, returns an array
of `n` words whose word `i` is the least element of the class of `i` in the least equivalence
relation that relates `js[t]` and `ks[t]` for every pair `t` with both elements below `n`. -/
theorem classes_master :
    Verified.Master compiled.module compiled.tables "classes" compiled.classes.bound
      (fun _ => True)
      (fun (x : UInt64 × Array UInt64 × Array UInt64) (y : Array UInt64) =>
        y.size = x.1.toNat ∧
          ∀ i < x.1.toNat, IsLeast {j | Equivalent x.1.toNat x.2.1 x.2.2 i j} y[i]!.toNat) :=
  .of_trapFree (.ofA compiled.classes.trapFree) nofun classes_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, _, _, _, _, ⟨_, _, hjs⟩, ⟨_, _, hks⟩⟩ _ =>
      classes_spec x.1 x.2.1 x.2.2 hjs.values.size_lt hks.values.size_lt

#print axioms classes_master

end Library.Graphs.UnionFind
