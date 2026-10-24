import Verified.TreeMemory
import Verified.TreeInitialize
import Verified.TreeSelect

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_treeCopyBegin {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} (r : Fin shape.records) {width size : Nat} {store : Store Unit}
    {s : Locals} {ptr input : Nat} {parent : Option Nat} {p source parentValue : UInt64}
    {rest : Program} {Q : Assertion Unit} (hRaw : RecordStorage width heap store p)
    (hHeap : heap.At store) (hPtr : s.get ptr = some (.i64 p))
    (hInput : s.get input = some (.i64 source))
    (hSourceRoom : source.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hTagged : shape.tagged = true →
      store.mem.read64 source.toUInt32 = UInt64.ofNat (shape.ctorIndex r))
    (hSize : shape.width r = size)
    (hParent : parent.elim (parentValue = 0) (fun pos => s.get pos = some (.i64 parentValue)))
    (hNext : wp m rest Q (beginRecordStore shape.tagged store p source parentValue size) s host) :
    wp m (treeCopyBegin shape input ptr [.localGet input]
      (parent.elim [.constI64 0] (fun pos => [.localGet pos])) ++ rest)
      Q store s host := by
  subst hSize
  have hBase := hRaw.base
  have hAddress := hRaw.address
  have hBelow := hRaw.below
  have hTop := hHeap.top
  have hRoom (back : UInt64) (h8 : 8 ≤ back.toNat) (h40 : back.toNat ≤ 40) :
      (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [headerAddress_toNat (by omega) (by omega)]
    omega
  have hLink (store0 : Store Unit) (hPages : store0.mem.pages = store.mem.pages)
      (hNext0 : wp m rest Q (linkRecordStore store0 p source parentValue) s host) :
      wp m (headerStore ptr 40 (parent.elim [.constI64 0] (fun pos => [.localGet pos])) ++
        (headerStore ptr 24 [.localGet input] ++ (headerStore ptr 8 [.constI64 0] ++ rest)))
        Q store0 s host := by
    have hTail : wp m (headerStore ptr 24 [.localGet input] ++
        (headerStore ptr 8 [.constI64 0] ++ rest)) Q
        (recordHeaderWrite store0 p 40 parentValue) s host := by
      refine wp_headerStoreLocal hPtr hInput ?_ ?_
      · simpa only [recordHeaderWrite, Mem.write64_pages, hPages] using
          hRoom 24 (by decide) (by decide)
      refine wp_headerStoreWord hPtr ?_ hNext0
      simpa only [recordHeaderWrite, Mem.write64_pages, hPages] using
        hRoom 8 (by decide) (by decide)
    have hRoom40 : (p - 40).toUInt32.toNat + 8 ≤ store0.mem.pages * 65536 := by
      rw [hPages]
      exact hRoom 40 (by decide) (by decide)
    cases parent with
    | none =>
      subst parentValue
      exact wp_headerStoreWord hPtr hRoom40 hTail
    | some pos =>
      exact wp_headerStoreLocal hPtr hParent hRoom40 hTail
  simp only [treeCopyBegin, List.append_assoc]
  cases hT : shape.tagged with
  | false =>
    rw [hT] at hNext
    simpa only [Bool.false_eq_true, ite_false, List.nil_append] using hLink store rfl hNext
  | true =>
    rw [hT] at hNext
    simp only [ite_true, List.append_assoc]
    refine wp_headerStorePushes hPtr (hRoom 16 (by decide) (by decide))
      (PushesWord.selectCode r (fun r => UInt64.ofNat (shape.width r))
        (PushesWord.tag hInput hSourceRoom) (fun h => hTagged h)) ?_
    exact hLink _ (Mem.write64_pages ..) hNext

#print axioms wp_treeCopyBegin

end Verified
