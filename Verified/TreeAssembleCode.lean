import Verified.TreeAssemble
import Verified.TreeFieldsStore
import Verified.TreeMemory

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def sealRecordCode (width ptr : Nat) (mask : UInt64) : Program :=
  headerStore ptr 24 [.constI64 1] ++
    headerStore ptr 16 [.constI64 (UInt64.ofNat width)] ++
    headerStore ptr 8 [.constI64 mask]

theorem wp_sealRecord {m : Module} {host : HostEnv Unit} {heap : Heap}
    {width : Nat} {store : Store Unit} {s : Locals} {ptr : Nat} {p mask : UInt64}
    {rest : Program} {Q : Assertion Unit} (hRaw : RecordStorage width heap store p)
    (hAt : heap.At store) (hPtr : s.get ptr = some (.i64 p))
    (hNext : wp m rest Q (recordSeal width store p mask) s host) :
    wp m (sealRecordCode width ptr mask ++ rest) Q store s host := by
  have hBase := hRaw.base
  have hAddress := hRaw.address
  have hBelow := hRaw.below
  have hTop := hAt.top
  have hRoom (back : UInt64) (h8 : 8 ≤ back.toNat) (h24 : back.toNat ≤ 24) :
      (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [headerAddress_toNat (by omega) (by omega)]
    omega
  simp only [sealRecordCode, List.append_assoc]
  refine wp_headerStoreWord hPtr (hRoom 24 (by decide) (by decide)) ?_
  refine wp_headerStoreWord hPtr ?_ ?_
  · simpa only [Mem.write64_pages] using hRoom 16 (by decide) (by decide)
  refine wp_headerStoreWord hPtr ?_ ?_
  · simpa only [Mem.write64_pages] using hRoom 8 (by decide) (by decide)
  exact hNext

theorem recordWriteValues_append (ptr : UInt64) :
    ∀ (i : Nat) (pre words : List UInt64) (store : Store Unit),
      recordWriteValues ptr i (pre ++ words) store =
        recordWriteValues ptr (i + pre.length) words (recordWriteValues ptr i pre store)
  | i, [], words, store => by simp [recordWriteValues]
  | i, word :: pre, words, store => by
    simp only [List.cons_append, recordWriteValues, List.length_cons]
    rw [recordWriteValues_append ptr (i + 1) pre words]
    congr 1
    omega

/-- The store of the tag of record constructor `r` into slot 0 of a record of positive width. -/
theorem wp_tagStore {m : Module} {host : HostEnv Unit} {heap : Heap} {width : Nat}
    {shape : TreeShape} (r : Fin shape.records) {store : Store Unit} {s : Locals} {ptr : Nat}
    {p : UInt64} {rest : Program} {Q : Assertion Unit} (hRaw : RecordStorage width heap store p)
    (hAt : heap.At store) (hPos : 0 < width) (hPtr : s.get ptr = some (.i64 p))
    (hNext : wp m rest Q (recordWriteValues p 0 (shape.tagWords r) store) s host) :
    wp m (shape.tagStoreCode r ptr ++ rest) Q store s host := by
  have hBase := hRaw.base
  have hAddress := hRaw.address
  have hBelow := hRaw.below
  have hCapacity := hRaw.capacity
  have hTop := hAt.top
  unfold TreeShape.tagStoreCode
  unfold TreeShape.tagWords at hNext
  by_cases ht : shape.tagged = true
  · rw [ite_eq_left ht] at hNext ⊢
    have hRoom : p.toNat % 4294967296 + 8 ≤ store.mem.pages * 65536 := by omega
    simp only [Locals.get] at hPtr
    simpa [recordWriteValues, slotAddress, wp_simp, hPtr, wrap_toUInt32_num,
      Nat.not_lt.mpr hRoom] using hNext
  · rw [ite_eq_right ht] at hNext ⊢
    simpa only [List.nil_append, recordWriteValues] using hNext

/-- The stores of the words `words` after the words `pre` already in the record, and the seal of
its header. -/
theorem wp_assembleRecord {m : Module} {host : HostEnv Unit} {heap : Heap}
    {width : Nat} {store : Store Unit} {s : Locals} {ptr : Nat} {p : UInt64}
    {pre words : List UInt64} {slots : List LeanExe.Pipeline.Slot} {srcs : List Nat}
    {tys : List ValueType}
    {rest : Program} {Q : Assertion Unit}
    (hRaw : RecordStorage width heap store p) (hAt : heap.At store)
    (hPtr : s.get ptr = some (.i64 p)) (hLength : (pre ++ words).length = width)
    (hShort : width ≤ 64) (hCount : store.mem.read64 (p - 40).toUInt32 = 1)
    (hValues : List.Forall₂ (fun word slot => slot.ValueOwned heap store word) (pre ++ words)
      slots)
    (hLocals : SourcesHold s s.positions srcs tys words)
    (hApart : (block store p :: fieldBlocks store (pre ++ words) slots).Pairwise regionsDisjoint)
    (hNext : ∀ store', heap.At store' → NodeOwned heap store' p (.record slots) →
      Node.blocks store' p (.record slots) =
        block store p :: fieldBlocks store (pre ++ words) slots →
      Step heap store (fun r => regionsDisjoint r (block store p)) heap store' [] →
      wp m rest Q store' s host) :
    wp m (recordStoreCode s.positions ptr pre.length srcs tys ++
      sealRecordCode width ptr (maskOf slots) ++ rest)
      Q (recordWriteValues p 0 pre store) s host := by
  have hAddress := hRaw.address
  have hRoom := hRaw.capacity
  have hBelow := hRaw.below
  have hTop := hAt.top
  have hLength' := hLength
  simp only [List.length_append] at hLength'
  have hPreWrites := recordWriteValues_range p 0 pre store (by omega)
  obtain ⟨hAt1, hRaw1, _, _⟩ := hRaw.writeValues hAt 0 (pre ++ words) (by omega)
  obtain ⟨hAt2, hNode2, hBlocks2, hStep2⟩ :=
    hRaw.assemble hAt hLength hShort hCount hValues hApart
  have hAppend := recordWriteValues_append p 0 pre words store
  rw [Nat.zero_add] at hAppend
  rw [List.append_assoc]
  refine wp_recordStoreCode hPtr pre.length srcs tys words (recordWriteValues p 0 pre store)
    hLocals (by omega) (by rw [hPreWrites.2.1]; omega) ?_
  rw [← hAppend]
  exact wp_sealRecord hRaw1 hAt1 hPtr (hNext _ hAt2 hNode2 hBlocks2 hStep2)

end Verified
