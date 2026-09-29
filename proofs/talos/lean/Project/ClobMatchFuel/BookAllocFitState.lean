import Project.Runtime.FreeList
import Project.ProofKit.FixedArrayHeader

namespace Project.ClobMatchFuel.BookAllocFit
open Wasm Project.Common Project.Runtime Project.Clob

abbrev bookAllocFitMem (mem : Mem) (choice : FreeChoice) : Mem :=
  fixedArrayAllocFitMem mem choice 5

abbrev bookAllocFitStore (st : Store Unit) (choice : FreeChoice) :
    Store Unit :=
  fixedArrayAllocFitStore st choice 5

theorem freeListAt_bookAllocFitMem {mem : Mem} {nodes : List FreeNode}
    {need : UInt64} {choice : FreeChoice}
    (hList : FreeListAt mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice) :
    FreeListAt (bookAllocFitMem mem choice) choice.remaining := by
  exact freeListAt_fixedArrayAllocFitMem 5 hList hTake

#print axioms freeListAt_bookAllocFitMem

end Project.ClobMatchFuel.BookAllocFit
