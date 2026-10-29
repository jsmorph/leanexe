import Verified.AlignedCall
import Verified.AlignedTreeFields
import Verified.TreeSlotCode
import Verified.TreeAllocate

/-!
The accesses to a record's header and slots under the flag, which the construction, the match,
and the copy of trees share.  A record's pointer is a multiple of 8, and so are the offsets of its
header words (8 to 48 bytes before the pointer) and of its slots (`slotAddress_mod8`), so each
lemma is its original in `TreeMemory.lean`, `TreeSlotCode.lean`, `TreeSelect.lean`, or
`TreeAllocate.lean` with `wpX strict` for `wp`, a premise that the pointer (and the header
offset) is a multiple of 8, and the alignment conjunct of the access.  `PushesWordX` is
`PushesWord` under the flag.  A new record's pointer and capacity are multiples of 8 and the heap
after its allocation is aligned (`wpX_recordAllocateWith`).
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

section

variable {strict : Bool} {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}

/-- `PushesWord` under the flag. -/
def PushesWordX (strict : Bool) (m : Module) (host : HostEnv Unit) (code : Program)
    (store : Store Unit) (s : Locals) (v : UInt64) : Prop :=
  ∀ (vs : List Value) (rest : Program) (Q : Assertion Unit),
    wpX strict m rest Q store { s with values := .i64 v :: vs } host →
      wpX strict m (code ++ rest) Q store { s with values := vs } host

theorem PushesWordX.const {v : UInt64} : PushesWordX strict m host [.constI64 v] store s v := by
  intro vs rest Q h
  simpa only [List.singleton_append, wpX_constI64_cons] using h

theorem PushesWordX.local {src : Nat} {v : UInt64} (hValue : s.get src = some (.i64 v)) :
    PushesWordX strict m host [.localGet src] store s v := by
  intro vs rest Q h
  simpa only [List.singleton_append, wpX_localGet_cons, Locals.get_values, hValue] using h

theorem PushesWordX.tag {ptr : Nat} {p : UInt64} (hPtr : s.get ptr = some (.i64 p))
    (hRoom : p.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hAl : strict = true → p.toNat % 8 = 0) :
    PushesWordX strict m host (treeTagCode ptr) store s (store.mem.read64 p.toUInt32) := by
  intro vs rest Q h
  simp only [treeTagCode, List.cons_append, List.nil_append, wpX_localGet_cons,
    Locals.get_values, hPtr, wpX_wrapI64_cons, wrap_toUInt32, wpX_load64_cons, UInt32.toNat_zero,
    Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega)]
  exact ⟨fun hs => UInt64.toUInt32_mod8 (hAl hs), h⟩

theorem PushesWord.tag {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {ptr : Nat} {p : UInt64} (hPtr : s.get ptr = some (.i64 p))
    (hRoom : p.toUInt32.toNat + 8 ≤ store.mem.pages * 65536) :
    PushesWord m host (treeTagCode ptr) store s (store.mem.read64 p.toUInt32) :=
  PushesWordX.tag (strict := false) hPtr hRoom nofun
#print axioms PushesWord.tag

theorem PushesWordX.selectChain {tag : Program} {t : UInt64}
    (hTag : PushesWordX strict m host tag store s t) :
    ∀ pairs : List (UInt64 × UInt64),
      PushesWordX strict m host (Verified.selectChain tag pairs) store s (chainPick t 0 pairs)
  | [] => PushesWordX.const
  | [(_, _)] => PushesWordX.const
  | (i, v) :: p :: rest => by
    intro vs code Q h
    have hRest := PushesWordX.selectChain hTag (p :: rest)
    rw [Verified.selectChain, List.append_assoc]
    apply hTag
    simp only [List.cons_append, List.nil_append, wpX_constI64_cons, wpX_eqI64_cons]
    apply wpX_iff_cons rfl
    rw [chainPick] at h
    by_cases hi : t = i
    · rw [ite_eq_left hi] at h
      rw [ite_eq_left hi, ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
      simpa [wpX_constI64_cons] using h
    · rw [ite_eq_right hi] at h
      rw [ite_eq_right hi, ite_eq_right (by decide : ¬(0 : UInt32) ≠ 0),
        ← List.append_nil (Verified.selectChain tag (p :: rest))]
      apply hRest vs []
      simpa using h

/-- `PushesWord.selectCode` under the flag. -/
theorem PushesWordX.selectCode {shape : TreeShape} (r : Fin shape.records) {tag : Program}
    {t : UInt64} (value : Fin shape.records → UInt64)
    (hTag : PushesWordX strict m host tag store s t)
    (ht : shape.tagged = true → t = UInt64.ofNat (shape.ctorIndex r)) :
    PushesWordX strict m host (shape.selectCode tag value) store s (value r) := by
  have h := PushesWordX.selectChain hTag (shape.tagPairs value)
  rwa [shape.chainPick_tag r value 0 t ht] at h

/-- `wp_headerStorePushes` under the flag. -/
theorem wpX_headerStorePushes {ptr : Nat} {p back value : UInt64} {code rest : Program}
    {Q : Assertion Unit} (hPtr : s.get ptr = some (.i64 p))
    (hRoom : (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hAl : strict = true → p.toNat % 8 = 0 ∧ back.toNat % 8 = 0)
    (hCode : PushesWordX strict m host code store s value)
    (hNext : wpX strict m rest Q
      { store with mem := store.mem.write64 (p - back).toUInt32 value } s host) :
    wpX strict m (headerStore ptr back code ++ rest) Q store s host := by
  simp only [headerStore, List.append_assoc, List.cons_append, List.nil_append]
  simp only [wpX_localGet_cons, hPtr, wpX_constI64_cons, wpX_subI64_cons, wpX_wrapI64_cons,
    wrap_toUInt32]
  apply hCode
  simp only [wpX_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega)]
  exact ⟨fun hs => UInt64.toUInt32_mod8 (UInt64.sub_mod8 (hAl hs).1 (hAl hs).2), by
    simpa using hNext⟩

theorem wp_headerStorePushes {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {ptr : Nat} {p back value : UInt64} {code rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p))
    (hRoom : (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hCode : PushesWord m host code store s value)
    (hNext : wp m rest Q
      { store with mem := store.mem.write64 (p - back).toUInt32 value } s host) :
    wp m (headerStore ptr back code ++ rest) Q store s host :=
  wpX_headerStorePushes (strict := false) hPtr hRoom nofun hCode hNext
#print axioms wp_headerStorePushes

/-- `wp_headerLoad` under the flag. -/
theorem wpX_headerLoad {ptr : Nat} {p back : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p))
    (hRoom : (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hAl : strict = true → p.toNat % 8 = 0 ∧ back.toNat % 8 = 0)
    (hNext : wpX strict m rest Q store
      { s with values := .i64 (store.mem.read64 (p - back).toUInt32) :: s.values } host) :
    wpX strict m (headerLoad ptr back ++ rest) Q store s host := by
  simp only [headerLoad, List.cons_append, List.nil_append, wpX_localGet_cons, hPtr,
    wpX_constI64_cons, wpX_subI64_cons, wpX_wrapI64_cons, wrap_toUInt32, wpX_load64_cons,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega)]
  exact ⟨fun hs => UInt64.toUInt32_mod8 (UInt64.sub_mod8 (hAl hs).1 (hAl hs).2), hNext⟩

theorem wp_headerLoad {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {ptr : Nat} {p back : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p))
    (hRoom : (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hNext : wp m rest Q store
      { s with values := .i64 (store.mem.read64 (p - back).toUInt32) :: s.values } host) :
    wp m (headerLoad ptr back ++ rest) Q store s host :=
  wpX_headerLoad (strict := false) hPtr hRoom nofun hNext
#print axioms wp_headerLoad

/-- `wp_headerStoreWord` under the flag. -/
theorem wpX_headerStoreWord {ptr : Nat} {p back value : UInt64} {rest : Program}
    {Q : Assertion Unit} (hPtr : s.get ptr = some (.i64 p))
    (hRoom : (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hAl : strict = true → p.toNat % 8 = 0 ∧ back.toNat % 8 = 0)
    (hNext : wpX strict m rest Q
      { store with mem := store.mem.write64 (p - back).toUInt32 value } s host) :
    wpX strict m (headerStore ptr back [.constI64 value] ++ rest) Q store s host :=
  wpX_headerStorePushes hPtr hRoom hAl PushesWordX.const hNext

theorem wp_headerStoreWord {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {ptr : Nat} {p back value : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p))
    (hRoom : (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hNext : wp m rest Q
      { store with mem := store.mem.write64 (p - back).toUInt32 value } s host) :
    wp m (headerStore ptr back [.constI64 value] ++ rest) Q store s host :=
  wpX_headerStoreWord (strict := false) hPtr hRoom nofun hNext
#print axioms wp_headerStoreWord

/-- `wp_headerStoreLocal` under the flag. -/
theorem wpX_headerStoreLocal {ptr src : Nat} {p back value : UInt64} {rest : Program}
    {Q : Assertion Unit} (hPtr : s.get ptr = some (.i64 p))
    (hValue : s.get src = some (.i64 value))
    (hRoom : (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hAl : strict = true → p.toNat % 8 = 0 ∧ back.toNat % 8 = 0)
    (hNext : wpX strict m rest Q
      { store with mem := store.mem.write64 (p - back).toUInt32 value } s host) :
    wpX strict m (headerStore ptr back [.localGet src] ++ rest) Q store s host :=
  wpX_headerStorePushes hPtr hRoom hAl (PushesWordX.local hValue) hNext

theorem wp_headerStoreLocal {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {ptr src : Nat} {p back value : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p)) (hValue : s.get src = some (.i64 value))
    (hRoom : (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hNext : wp m rest Q
      { store with mem := store.mem.write64 (p - back).toUInt32 value } s host) :
    wp m (headerStore ptr back [.localGet src] ++ rest) Q store s host :=
  wpX_headerStoreLocal (strict := false) hPtr hValue hRoom nofun hNext
#print axioms wp_headerStoreLocal

theorem wpX_treeSlotAddress {ptr index i : Nat} {p : UInt64} {rest : Program}
    {Q : Assertion Unit} (hPtr : s.get ptr = some (.i64 p))
    (hIndex : s.get index = some (.i64 (UInt64.ofNat i)))
    (hNext : wpX strict m rest Q store { s with values := .i32 (slotAddress p i) :: s.values }
      host) :
    wpX strict m (treeSlotAddress ptr index ++ rest) Q store s host := by
  simpa only [treeSlotAddress, List.cons_append, List.nil_append, wpX_localGet_cons,
    Locals.get_values, hPtr, hIndex, wpX_constI64_cons, wpX_mulI64_cons, wpX_addI64_cons,
    wpX_wrapI64_cons, wrap_toUInt32, treeSlotAddress_eq] using hNext

theorem wp_treeSlotAddress {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {ptr index i : Nat} {p : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p)) (hIndex : s.get index = some (.i64 (UInt64.ofNat i)))
    (hNext : wp m rest Q store { s with values := .i32 (slotAddress p i) :: s.values } host) :
    wp m (treeSlotAddress ptr index ++ rest) Q store s host :=
  wpX_treeSlotAddress (strict := false) hPtr hIndex hNext

/-- `wp_treeSlotLoad` under the flag. -/
theorem wpX_treeSlotLoad {ptr index i : Nat} {p : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p)) (hIndex : s.get index = some (.i64 (UInt64.ofNat i)))
    (hRoom : (slotAddress p i).toNat + 8 ≤ store.mem.pages * 65536)
    (hAl : strict = true → p.toNat % 8 = 0)
    (hNext : wpX strict m rest Q store
      { s with values := .i64 (store.mem.read64 (slotAddress p i)) :: s.values } host) :
    wpX strict m (treeSlotAddress ptr index ++ .load64 0 :: rest) Q store s host := by
  apply wpX_treeSlotAddress hPtr hIndex
  simp only [wpX_load64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (Nat.not_lt.mpr hRoom)]
  exact ⟨fun hs => slotAddress_mod8 (hAl hs) i, hNext⟩

theorem wp_treeSlotLoad {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {ptr index i : Nat} {p : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p)) (hIndex : s.get index = some (.i64 (UInt64.ofNat i)))
    (hRoom : (slotAddress p i).toNat + 8 ≤ store.mem.pages * 65536)
    (hNext : wp m rest Q store
      { s with values := .i64 (store.mem.read64 (slotAddress p i)) :: s.values } host) :
    wp m (treeSlotAddress ptr index ++ .load64 0 :: rest) Q store s host :=
  wpX_treeSlotLoad (strict := false) hPtr hIndex hRoom nofun hNext

/-- `wp_treeSlotStore` under the flag. -/
theorem wpX_treeSlotStore {ptr index value i : Nat} {p word : UInt64} {rest : Program}
    {Q : Assertion Unit} (hPtr : s.get ptr = some (.i64 p))
    (hIndex : s.get index = some (.i64 (UInt64.ofNat i)))
    (hValue : s.get value = some (.i64 word))
    (hRoom : (slotAddress p i).toNat + 8 ≤ store.mem.pages * 65536)
    (hAl : strict = true → p.toNat % 8 = 0)
    (hNext : wpX strict m rest Q { store with mem := store.mem.write64 (slotAddress p i) word } s
      host) :
    wpX strict m (treeSlotAddress ptr index ++ [.localGet value, .store64 0] ++ rest) Q store s
      host := by
  apply wpX_treeSlotAddress hPtr hIndex
  simp only [List.append_eq, List.cons_append, List.nil_append, wpX_localGet_cons,
    Locals.get_values, hValue, wpX_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (Nat.not_lt.mpr hRoom)]
  exact ⟨fun hs => slotAddress_mod8 (hAl hs) i, by simpa using hNext⟩

theorem wp_treeSlotStore {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {ptr index value i : Nat} {p word : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p)) (hIndex : s.get index = some (.i64 (UInt64.ofNat i)))
    (hValue : s.get value = some (.i64 word))
    (hRoom : (slotAddress p i).toNat + 8 ≤ store.mem.pages * 65536)
    (hNext : wp m rest Q { store with mem := store.mem.write64 (slotAddress p i) word } s host) :
    wp m (treeSlotAddress ptr index ++ [.localGet value, .store64 0] ++ rest) Q store s host :=
  wpX_treeSlotStore (strict := false) hPtr hIndex hValue hRoom nofun hNext
#print axioms wp_treeSlotStore

/-- `wp_treeCopyAdvance` under the flag. -/
theorem wpX_treeCopyAdvance {ptr index i : Nat} {p : UInt64} {rest : Program}
    {Q : Assertion Unit} (hPtr : s.get ptr = some (.i64 p))
    (hIndex : s.get index = some (.i64 (UInt64.ofNat i)))
    (hRoom : (p - 8).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hAl : strict = true → p.toNat % 8 = 0)
    (hNext : wpX strict m rest Q (recordHeaderWrite store p 8 (UInt64.ofNat (i + 1))) s host) :
    wpX strict m (treeCopyAdvance ptr index ++ rest) Q store s host := by
  rw [treeCopyAdvance]
  refine wpX_headerStorePushes hPtr hRoom (fun hs => ⟨hAl hs, rfl⟩) ?_ hNext
  intro vs rest' Q' h
  have hEq : UInt64.ofNat (i + 1) = UInt64.ofNat i + 1 := by rw [UInt64.ofNat_add]; rfl
  rw [hEq] at h
  simpa only [List.cons_append, List.nil_append, wpX_localGet_cons, Locals.get_values, hIndex,
    wpX_constI64_cons, wpX_addI64_cons] using h

theorem wp_treeCopyAdvance {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {ptr index i : Nat} {p : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p)) (hIndex : s.get index = some (.i64 (UInt64.ofNat i)))
    (hRoom : (p - 8).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hNext : wp m rest Q (recordHeaderWrite store p 8 (UInt64.ofNat (i + 1))) s host) :
    wp m (treeCopyAdvance ptr index ++ rest) Q store s host :=
  wpX_treeCopyAdvance (strict := false) hPtr hIndex hRoom nofun hNext
#print axioms wp_treeCopyAdvance

end

/-- `wp_recordAllocateWith` under the flag: the new record's pointer and capacity are multiples
of 8, and the heap after the allocation is aligned. -/
theorem wpX_recordAllocateWith {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit}
    {shape : TreeShape} (r : Fin shape.records) {heap : Heap} {store : Store Unit} {s : Locals}
    {dst : Nat} {code rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hHeapAl : strict = true → heap.Aligned) (hCap : store.memoryCap m 0 ≤ 65535)
    (hCode : PushesWordX strict m host code store s (8 * UInt64.ofNat (shape.width r)))
    (hTrap : TrapOK (!decide (heap.Within store m (allocCost (8 * shape.width r)))) Q)
    (hLow : s.params.length ≤ dst) (hHigh : dst < s.params.length + s.locals.length)
    (hNext : ∀ heap' store' ptr,
      Step heap store (fun _ => True) heap' store' [block store' ptr] →
      RecordStorage (shape.width r) heap' store' ptr →
      store'.mem.read64 (ptr - 40).toUInt32 = 1 →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * shape.width r) →
      (strict = true → ptr.toNat % 8 = 0 ∧ capacityAt store' ptr % 8 = 0 ∧ heap'.Aligned) →
      wpX strict m rest Q store' (setLocal s dst (.i64 ptr)) host) :
    wpX strict m (code ++ ([.call 0, .localSet dst] ++ rest)) Q store s host := by
  obtain ⟨hBytes, hAligned⟩ := treeRecordBytes shape r
  have hShort := shape.width_le r
  refine hCode s.values _ _ ?_
  simp only [List.cons_append, List.nil_append]
  refine wpX_alloc hm hRt hAt hHeapAl (by rw [hBytes]; omega) hCap
    (by rw [hAligned, hBytes]) hTrap ?_
  intro hFits hTop
  have hNeed8 := allocSize_mod8 (8 * UInt64.ofNat (shape.width r))
  rw [hAligned] at hFits hTop hNeed8 ⊢
  let heap' := heap.allocate (8 * UInt64.ofNat (shape.width r))
  let store' := heap.allocateStore store (8 * UInt64.ofNat (shape.width r)) 1
  let ptr := FixedArrayAllocate.root heap.top (8 * UInt64.ofNat (shape.width r)) heap.free
  have hBlock := hAt.allocate_block 1 hFits
  have hRoom := allocated_capacity (8 * UInt64.ofNat (shape.width r)) heap.free
  have hStorage : RecordStorage (shape.width r) heap' store' ptr :=
    RecordStorage.ofBlock hBlock (by rw [hBytes] at hRoom; exact hRoom)
  have hStep : Step heap store (fun _ => True) heap' store' [block store' ptr] :=
    Step.allocate 1 hAt hFits
  exact wpX_localSet_local hLow hHigh (hNext heap' store' ptr hStep hStorage hBlock.fresh.2.1 hTop
    fun hs => ⟨(hHeapAl hs).root hNeed8, by
      rw [hBlock.capacity_eq]; exact (hHeapAl hs).capacity_alloc hNeed8,
      (hHeapAl hs).allocate hNeed8⟩)

/-- The allocation of a record of record constructor `r`, after code that pushes its size. -/
theorem wp_recordAllocateWith {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {shape : TreeShape} (r : Fin shape.records) {heap : Heap} {store : Store Unit} {s : Locals}
    {dst : Nat} {code rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hCode : PushesWord m host code store s (8 * UInt64.ofNat (shape.width r)))
    (hTrap : TrapOK (!decide (heap.Within store m (allocCost (8 * shape.width r)))) Q)
    (hLow : s.params.length ≤ dst) (hHigh : dst < s.params.length + s.locals.length)
    (hNext : ∀ heap' store' ptr,
      Step heap store (fun _ => True) heap' store' [block store' ptr] →
      RecordStorage (shape.width r) heap' store' ptr →
      store'.mem.read64 (ptr - 40).toUInt32 = 1 →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * shape.width r) →
      wp m rest Q store' (setLocal s dst (.i64 ptr)) host) :
    wp m (code ++ ([.call 0, .localSet dst] ++ rest)) Q store s host :=
  wpX_recordAllocateWith (strict := false) hm nofun r hAt nofun hCap hCode hTrap hLow hHigh
    (fun heap' store' ptr a1 a2 a3 a4 _ => hNext heap' store' ptr a1 a2 a3 a4)

/-- `wp_recordAllocate` under the flag. -/
theorem wpX_recordAllocate {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit}
    {shape : TreeShape} (r : Fin shape.records) {heap : Heap} {store : Store Unit} {s : Locals}
    {dst : Nat} {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hHeapAl : strict = true → heap.Aligned) (hCap : store.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (heap.Within store m (allocCost (8 * shape.width r)))) Q)
    (hLow : s.params.length ≤ dst) (hHigh : dst < s.params.length + s.locals.length)
    (hNext : ∀ heap' store' ptr,
      Step heap store (fun _ => True) heap' store' [block store' ptr] →
      RecordStorage (shape.width r) heap' store' ptr →
      store'.mem.read64 (ptr - 40).toUInt32 = 1 →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * shape.width r) →
      (strict = true → ptr.toNat % 8 = 0 ∧ capacityAt store' ptr % 8 = 0 ∧ heap'.Aligned) →
      wpX strict m rest Q store' (setLocal s dst (.i64 ptr)) host) :
    wpX strict m (recordAllocate (shape.width r) dst ++ rest) Q store s host :=
  wpX_recordAllocateWith hm hRt r (code := [.constI64 _]) hAt hHeapAl hCap PushesWordX.const hTrap
    hLow hHigh hNext

/-- The allocation of a record of record constructor `r`. -/
theorem wp_recordAllocate {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {shape : TreeShape} (r : Fin shape.records) {heap : Heap} {store : Store Unit} {s : Locals}
    {dst : Nat} {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (heap.Within store m (allocCost (8 * shape.width r)))) Q)
    (hLow : s.params.length ≤ dst) (hHigh : dst < s.params.length + s.locals.length)
    (hNext : ∀ heap' store' ptr,
      Step heap store (fun _ => True) heap' store' [block store' ptr] →
      RecordStorage (shape.width r) heap' store' ptr →
      store'.mem.read64 (ptr - 40).toUInt32 = 1 →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * shape.width r) →
      wp m rest Q store' (setLocal s dst (.i64 ptr)) host) :
    wp m (recordAllocate (shape.width r) dst ++ rest) Q store s host :=
  wpX_recordAllocate (strict := false) hm nofun r hAt nofun hCap hTrap hLow hHigh
    (fun heap' store' ptr a1 a2 a3 a4 _ => hNext heap' store' ptr a1 a2 a3 a4)
#print axioms wp_recordAllocate

/-- `wp_treeCopyAllocate` under the flag. -/
theorem wpX_treeCopyAllocate {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit}
    {shape : TreeShape} (r : Fin shape.records) {heap : Heap} {store : Store Unit} {s : Locals}
    {src dst : Nat} {t : UInt64} {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hHeapAl : strict = true → heap.Aligned) (hCap : store.memoryCap m 0 ≤ 65535)
    (hTag : PushesWordX strict m host (treeTagCode src) store s t)
    (hTagged : shape.tagged = true → t = UInt64.ofNat (shape.ctorIndex r))
    (hTrap : TrapOK (!decide (heap.Within store m (allocCost (8 * shape.width r)))) Q)
    (hLow : s.params.length ≤ dst) (hHigh : dst < s.params.length + s.locals.length)
    (hNext : ∀ heap' store' ptr,
      Step heap store (fun _ => True) heap' store' [block store' ptr] →
      RecordStorage (shape.width r) heap' store' ptr →
      store'.mem.read64 (ptr - 40).toUInt32 = 1 →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * shape.width r) →
      (strict = true → ptr.toNat % 8 = 0 ∧ capacityAt store' ptr % 8 = 0 ∧ heap'.Aligned) →
      wpX strict m rest Q store' (setLocal s dst (.i64 ptr)) host) :
    wpX strict m (treeCopyAllocate shape src dst ++ rest) Q store s host := by
  rw [treeCopyAllocate, List.append_assoc]
  exact wpX_recordAllocateWith hm hRt r hAt hHeapAl hCap
    (PushesWordX.selectCode r (fun r => 8 * UInt64.ofNat (shape.width r)) hTag hTagged)
    hTrap hLow hHigh hNext

/-- The allocation of a record of record constructor `r`, whose width the code selects by the
tag `t` that the code at local `src` pushes. -/
theorem wp_treeCopyAllocate {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {shape : TreeShape} (r : Fin shape.records) {heap : Heap} {store : Store Unit} {s : Locals}
    {src dst : Nat} {t : UInt64} {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hTag : PushesWord m host (treeTagCode src) store s t)
    (hTagged : shape.tagged = true → t = UInt64.ofNat (shape.ctorIndex r))
    (hTrap : TrapOK (!decide (heap.Within store m (allocCost (8 * shape.width r)))) Q)
    (hLow : s.params.length ≤ dst) (hHigh : dst < s.params.length + s.locals.length)
    (hNext : ∀ heap' store' ptr,
      Step heap store (fun _ => True) heap' store' [block store' ptr] →
      RecordStorage (shape.width r) heap' store' ptr →
      store'.mem.read64 (ptr - 40).toUInt32 = 1 →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * shape.width r) →
      wp m rest Q store' (setLocal s dst (.i64 ptr)) host) :
    wp m (treeCopyAllocate shape src dst ++ rest) Q store s host :=
  wpX_treeCopyAllocate (strict := false) hm nofun r hAt nofun hCap hTag hTagged hTrap hLow hHigh
    (fun heap' store' ptr a1 a2 a3 a4 _ => hNext heap' store' ptr a1 a2 a3 a4)
#print axioms wp_treeCopyAllocate

/-- The tag tests of a shape, as a branch nested in `d` blocks, run the branch of record
constructor `r`, which they nest in `chainDepth` further blocks. -/
theorem RunsTailBranch.dispatchCode {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {shape : TreeShape} (r : Fin shape.records) {ptr : Nat} {p : UInt64}
    {d : Nat} {Q : Assertion Unit} (branch : Fin shape.records → Program)
    (hPtr : s.get ptr = some (.i64 p))
    (hRoom : p.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hTag : shape.tagged = true →
      store.mem.read64 p.toUInt32 = UInt64.ofNat (shape.ctorIndex r))
    (hBranch : RunsTailBranch m host (branch r)
      (d + if r.val + 1 < shape.records then r.val + 1 else r.val) Q store s) :
    RunsTailBranch m host (shape.dispatchCode ptr branch) d Q store s := by
  apply RunsTailBranch.dispatchChain (PushesWord.tag hPtr hRoom)
  rw [shape.chainPick_tag r branch [] _ hTag, shape.chainDepth_tag r branch _ hTag]
  exact hBranch
#print axioms RunsTailBranch.dispatchCode

end Verified
