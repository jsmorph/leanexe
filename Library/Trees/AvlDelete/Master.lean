import Library.Trees.AvlDelete.Compiled
import Verified.Master

namespace Library.Trees.AvlDelete

open LeanExe.Pipeline
open Library.Trees.Avl (AvlTree)

/-- The export `delete`, called on a word `x` and a balanced tree of words that the caller moves,
returns the tree after the deletion of `x` by `deleteA`. -/
theorem delete_master :
    Verified.Master compiled.module compiled.tables "delete" compiled.delete.bound (fun _ => True)
      (fun (x : UInt64 × Moved AvlTree) y => y = (deleteA x.1 x.2.val).2) :=
  .of_trapFree (.ofA compiled.delete.trapFree) nofun delete_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => delete_eq x.1 x.2.val

#print axioms delete_master

end Library.Trees.AvlDelete
