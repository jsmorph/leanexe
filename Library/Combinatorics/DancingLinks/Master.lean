import Library.Combinatorics.DancingLinks.Compiled
import Verified.Master

namespace Library.Combinatorics.DancingLinks

/-- The export `count`, called on a valid exact-cover input `x`, returns the number of its exact
covers modulo `2 ^ 64`.  The bound counts 1,000 frames, and `Valid x`, which limits the items to
998, gives the frames condition by `count_fits`. -/
theorem count_master :
    Verified.Master compiled.module compiled.tables "count" (compiled.count.bound 1000)
      (fun x : Array UInt64 => Valid x)
      (fun x (y : UInt64) => y = UInt64.ofNat (coverCount x)) :=
  .of_trapFree (.ofA compiled.count.trapFree) nofun count_export
    (fun x _ _ hv h => ⟨count_fits x hv, h⟩) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, hxs⟩ hv =>
      count_eq x hv (by have := hxs.values.size_lt_memory32; omega)

#print axioms count_master

/-- The export `valid`, called on an array `x`, returns 1 when `x` is a valid exact-cover input and
0 otherwise. -/
theorem valid_master :
    Verified.Master compiled.module compiled.tables "valid" compiled.valid.bound (fun _ => True)
      (fun (x : Array UInt64) (y : UInt64) => y = if Valid x then 1 else 0) :=
  .of_trapFree (.ofA compiled.valid.trapFree) nofun valid_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, hxs⟩ _ =>
      valid_eq x (by have := hxs.values.size_lt_memory32; omega)

#print axioms valid_master

end Library.Combinatorics.DancingLinks
