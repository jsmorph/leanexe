import Verified.TreeMemory
import Verified.TreeInitialize

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_treeCopyBegin {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {store : Store Unit} {s : Locals} {ptr input : Nat}
    {parent : Option Nat} {p source parentValue : UInt64}
    {rest : Program} {Q : Assertion Unit} (hRaw : RecordStorage shape heap store p)
    (hHeap : heap.At store) (hPtr : s.get ptr = some (.i64 p))
    (hInput : s.get input = some (.i64 source))
    (hParent : parent.elim (parentValue = 0) (fun pos => s.get pos = some (.i64 parentValue)))
    (hNext : wp m rest Q (beginRecordStore store p source parentValue) s host) :
    wp m (treeCopyBegin ptr [.localGet input]
      (parent.elim [.constI64 0] (fun pos => [.localGet pos])) ++ rest)
      Q store s host := by
  have hBase := hRaw.base
  have hAddress := hRaw.address
  have hBelow := hRaw.below
  have hTop := hHeap.top
  have hRoom (back : UInt64) (h8 : 8 ≤ back.toNat) (h40 : back.toNat ≤ 40) :
      (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [headerAddress_toNat (by omega) (by omega)]
    omega
  simp only [treeCopyBegin, List.append_assoc]
  have hTail : wp m (headerStore ptr 24 [.localGet input] ++
      headerStore ptr 8 [.constI64 0] ++ rest) Q
      (recordHeaderWrite store p 40 parentValue) s host := by
    refine wp_headerStoreLocal hPtr hInput ?_ ?_
    · simpa only [recordHeaderWrite, Mem.write64_pages] using hRoom 24 (by decide) (by decide)
    refine wp_headerStoreWord hPtr ?_ hNext
    simpa only [recordHeaderWrite, Mem.write64_pages] using hRoom 8 (by decide) (by decide)
  cases parent with
  | none =>
    subst parentValue
    exact wp_headerStoreWord hPtr (hRoom 40 (by decide) (by decide)) hTail
  | some pos =>
    exact wp_headerStoreLocal hPtr hParent (hRoom 40 (by decide) (by decide)) hTail

#print axioms wp_treeCopyBegin

end Verified
