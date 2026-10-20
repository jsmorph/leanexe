import Verified.TreeAssemble
import Verified.TreeFieldsStore
import Verified.TreeMemory

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def sealRecordCode (shape : TreeShape) (ptr : Nat) (mask : UInt64) : Program :=
  headerStore ptr 24 [.constI64 1] ++
    headerStore ptr 16 [.constI64 (UInt64.ofNat shape.fields.length)] ++
    headerStore ptr 8 [.constI64 mask]

theorem wp_sealRecord {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {store : Store Unit} {s : Locals} {ptr : Nat} {p mask : UInt64}
    {rest : Program} {Q : Assertion Unit} (hRaw : RecordStorage shape heap store p)
    (hAt : heap.At store) (hPtr : s.get ptr = some (.i64 p))
    (hNext : wp m rest Q (recordSeal shape store p mask) s host) :
    wp m (sealRecordCode shape ptr mask ++ rest) Q store s host := by
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

theorem wp_assembleRecord {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {store : Store Unit} {s : Locals} {ptr : Nat} {p : UInt64}
    {words : List UInt64} {slots : List LeanExe.Pipeline.Slot} {srcs : List Nat}
    {rest : Program} {Q : Assertion Unit}
    (hRaw : RecordStorage shape heap store p) (hAt : heap.At store)
    (hPtr : s.get ptr = some (.i64 p)) (hLength : words.length = shape.fields.length)
    (hCount : store.mem.read64 (p - 40).toUInt32 = 1)
    (hValues : List.Forall₂ (fun word slot => slot.ValueOwned heap store word) words slots)
    (hLocals : List.Forall₂ (fun src word => s.get src = some (.i64 word)) srcs words)
    (hApart : (block store p :: fieldBlocks store words slots).Pairwise regionsDisjoint)
    (hNext : ∀ store', heap.At store' → NodeOwned heap store' p (.record slots) →
      Node.blocks store' p (.record slots) = block store p :: fieldBlocks store words slots →
      Step heap store (fun r => regionsDisjoint r (block store p)) heap store' [] →
      wp m rest Q store' s host) :
    wp m (recordStoreCode ptr 0 srcs ++ sealRecordCode shape ptr (maskOf slots) ++ rest)
      Q store s host := by
  have hAddress := hRaw.address
  have hRoom := hRaw.capacity
  have hBelow := hRaw.below
  have hTop := hAt.top
  obtain ⟨hAt1, hRaw1, _, _⟩ := hRaw.writeValues hAt 0 words (by omega)
  obtain ⟨hAt2, hNode2, hBlocks2, hStep2⟩ := hRaw.assemble hAt hLength hCount hValues hApart
  rw [List.append_assoc]
  exact wp_recordStoreCode hPtr 0 srcs words store hLocals (by omega) (by omega)
    (wp_sealRecord hRaw1 hAt1 hPtr (hNext _ hAt2 hNode2 hBlocks2 hStep2))

end Verified
