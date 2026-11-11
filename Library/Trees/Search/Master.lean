import Library.Trees.Search.Compiled
import Verified.Master

namespace Library.Trees.Search

open LeanExe.Pipeline Library.Trees.WordTree

/-- The export `search`, called on a word `x` and a tree of words, returns whether the search of
Algorithm T for `x` succeeds. -/
theorem search_master :
    Verified.Master compiled.module compiled.tables "search" compiled.search.bound (fun _ => True)
      (fun (x : UInt64 × KeyTree) y => y = (algorithmT x.1 x.2).1) :=
  .of_trapFree (.ofA compiled.search.trapFree) nofun search_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => search_eq x.1 x.2

#print axioms search_master

/-- The export `insert`, called on a word `x` and a tree of words that the caller moves, returns
the tree after the insertion of Algorithm T. -/
theorem insert_master :
    Verified.Master compiled.module compiled.tables "insert" compiled.insert.bound (fun _ => True)
      (fun (x : UInt64 × Moved KeyTree) y => y = (algorithmT x.1 x.2.val).2) :=
  .of_trapFree (.ofA compiled.insert.trapFree) nofun insert_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => insert_eq x.1 x.2.val

#print axioms insert_master

end Library.Trees.Search
