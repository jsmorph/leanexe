import Verified.Compile
import LeanExe.Pipeline.Allocation

/-! The instantiation theorem: the store in which the module of a program with tables starts, as
Talos's `Module.initialStore` builds it, meets the allocator invariant and holds each table as a
borrowed array at its address.  The data segments write each table's length word and words with
the bytes that `Mem.write64` stores, so `read64_write64` reads them back, and the segments' ranges
follow one another from 4096, so each table keeps the bytes that its segment writes. -/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- Eight bytes that hold a word's bytes read as the word. -/
theorem read64_of_bytes (mem : Mem) (a : UInt32) (w : UInt64)
    (h : ∀ j < 8, mem.bytes (a.toNat + j) = (wordBytes w)[j]!) : mem.read64 a = w := by
  rw [Memory.read64_congr a (m2 := mem.write64 a w) fun j hj => ?_, Memory.read64_write64]
  rw [h j hj]
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> simp [wordBytes, Mem.write64] <;> omega

theorem wordBytes_length (w : UInt64) : (wordBytes w).length = 8 := rfl

theorem flatMap_wordBytes_length : (l : List UInt64) → (l.flatMap wordBytes).length = 8 * l.length
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, List.length_append, wordBytes_length, flatMap_wordBytes_length l,
      List.length_cons]
    omega

/-- Byte `j` of word `i` of a list of words, as bytes. -/
theorem flatMap_wordBytes_getElem? : (l : List UInt64) → {i j : Nat} → i < l.length → j < 8 →
    (l.flatMap wordBytes)[8 * i + j]? = (wordBytes l[i]!)[j]?
  | [], _, _, h, _ => absurd h (by simp)
  | x :: l, i, j, hi, hj => by
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add, List.getElem?_append_left (by rw [wordBytes_length]; omega)]
      rfl
    | succ i =>
      rw [List.getElem?_append_right (by rw [wordBytes_length]; omega), wordBytes_length,
        show 8 * (i + 1) + j - 8 = 8 * i + j by omega,
        flatMap_wordBytes_getElem? l (by simp at hi; omega) hj]
      rfl

/-- The step of `Module.initialStore` that writes a data segment of memory 0. -/
def segStep (acc : Mem) (seg : DataSegment) : Mem :=
  match seg.offset with
  | some off =>
    if seg.memIdx = 0 && seg.offsetExpr.isEmpty then
      if off.toNat + seg.bytes.length ≤ acc.pages * 65536 then acc.writeBytes off.toNat seg.bytes
      else acc
    else acc
  | none => acc

/-- The start of table `k`, as a number. -/
def tableStart (tables : List (Array UInt64)) (k : Nat) : Nat :=
  4096 + 8 * ((tables.take k).map fun t => t.size + 1).sum

/-- The bytes of table `t`: its length word and its words. -/
def tableBytes (t : Array UInt64) : List UInt8 :=
  (UInt64.ofNat t.size :: t.toList).flatMap wordBytes

theorem tableBytes_length (t : Array UInt64) : (tableBytes t).length = 8 * (t.size + 1) := by
  rw [tableBytes, flatMap_wordBytes_length, List.length_cons, Array.length_toList]

theorem tableStart_succ (tables : List (Array UInt64)) {k : Nat} (hk : k < tables.length) :
    tableStart tables (k + 1) = tableStart tables k + 8 * (tables[k]!.size + 1) := by
  simp only [tableStart, List.take_add_one, List.map_append, List.sum_append,
    List.getElem?_eq_getElem hk, Option.toList_some, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, getElem!_pos tables k hk]
  omega

theorem tableStart_mono (tables : List (Array UInt64)) {k n : Nat} (hkn : k ≤ n)
    (hn : n ≤ tables.length) : tableStart tables k ≤ tableStart tables n := by
  induction n with
  | zero => obtain rfl : k = 0 := by omega
            exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le hkn with h | h
    · rw [tableStart_succ tables (by omega)]
      have := ih (by omega) (by omega)
      omega
    · rw [h]

theorem tableStart_length (tables : List (Array UInt64)) :
    tableStart tables tables.length = tablesEnd tables := by
  simp [tableStart, tablesEnd]

theorem tableAddr_toUInt32 (tables : List (Array UInt64)) {k : Nat} (hk : k ≤ tables.length)
    (h32 : tablesEnd tables < 4294967296) :
    (tableAddr tables k).toUInt32.toNat = tableStart tables k := by
  have hle := tableStart_mono tables hk (Nat.le_refl _)
  rw [tableStart_length] at hle
  rw [Memory.toUInt32_toNat]
  show (UInt64.ofNat (tableStart tables k)).toNat % 4294967296 = _
  rw [UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega),
    Nat.mod_eq_of_lt (by omega)]

theorem tableSegments_length (tables : List (Array UInt64)) :
    (tableSegments tables).length = tables.length := by
  simp [tableSegments]

/-- The data segment of table `t`, the `k`-th of `tables`. -/
def tableSegment (tables : List (Array UInt64)) (k : Nat) (t : Array UInt64) : DataSegment :=
  { offset := some (tableAddr tables k).toUInt32, bytes := tableBytes t }

theorem tableSegments_getElem? (tables : List (Array UInt64)) {n : Nat} (hn : n < tables.length) :
    (tableSegments tables)[n]? = some (tableSegment tables n tables[n]!) := by
  simp only [tableSegments, List.getElem?_mapIdx, List.getElem?_eq_getElem hn, Option.map_some,
    getElem!_pos tables n hn]
  rfl

/-- The data segments of the tables, written from an empty memory of `P` pages that holds them:
after the first `n` segments, the memory keeps its pages and holds the bytes of each of the first
`n` tables from its start. -/
theorem tables_written (tables : List (Array UInt64)) (P : Nat)
    (hEnd : tablesEnd tables ≤ P * 65536) (h32 : tablesEnd tables < 4294967296) :
    ∀ n, n ≤ tables.length →
      (((tableSegments tables).take n).foldl segStep (Mem.empty P)).pages = P ∧
      ∀ k < n, ∀ i < 8 * (tables[k]!.size + 1),
        (((tableSegments tables).take n).foldl segStep (Mem.empty P)).bytes
          (tableStart tables k + i) = (tableBytes tables[k]!)[i]! := by
  intro n
  induction n with
  | zero => intro _; exact ⟨rfl, fun k hk => absurd hk (by omega)⟩
  | succ n ih =>
    intro hn
    obtain ⟨hPages, hBytes⟩ := ih (by omega)
    have hlt : n < tables.length := by omega
    rw [List.take_add_one, tableSegments_getElem? tables hlt, Option.toList_some,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize ((tableSegments tables).take n).foldl segStep (Mem.empty P) = mem at hPages hBytes
    have hStart := tableStart_succ tables hlt
    have hEndN := tableStart_mono tables (k := n + 1) (by omega) (Nat.le_refl _)
    rw [tableStart_length] at hEndN
    have hAddr := tableAddr_toUInt32 tables (Nat.le_of_lt hlt) h32
    have hFits : (tableAddr tables n).toUInt32.toNat + (tableBytes tables[n]!).length ≤
        mem.pages * 65536 := by
      rw [hAddr, tableBytes_length, hPages]
      omega
    have hStep : segStep mem (tableSegment tables n tables[n]!) =
        mem.writeBytes (tableStart tables n) (tableBytes tables[n]!) := by
      simp only [segStep, tableSegment, decide_true, List.isEmpty_nil, Bool.and_self, ↓reduceIte]
      rw [hAddr] at hFits ⊢
      exact if_pos hFits
    rw [hStep]
    refine ⟨hPages, fun k hk i hi => ?_⟩
    simp only [Mem.writeBytes]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk' | rfl
    · have hkn := tableStart_mono tables (Nat.succ_le_of_lt hk') (Nat.le_of_lt hlt)
      rw [tableStart_succ tables (by omega)] at hkn
      rw [dite_eq_right (by omega)]
      exact hBytes k hk' i hi
    · rw [dite_eq_left ⟨by omega, by rw [tableBytes_length]; omega⟩]
      rw [getElem!_pos _ i (by rw [tableBytes_length]; omega)]
      simp

theorem tableBytes_word (t : Array UInt64) {i j : Nat} (hi : i ≤ t.size) (hj : j < 8) :
    (tableBytes t)[8 * i + j]! = (wordBytes ((UInt64.ofNat t.size :: t.toList)[i]!))[j]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, tableBytes,
    flatMap_wordBytes_getElem? _ (by simp; omega) hj]

/-- The pages of a module with tables `tables`: 16, or enough for the tables. -/
def tablePages (tables : List (Array UInt64)) : Nat := max 16 ((tablesEnd tables + 65535) / 65536)

theorem initialStore_mem {S : List Sig} (prog : Prog S) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) (hFit : tablesEnd tables ≤ 65535 * 65536) :
    ((compileWith prog tables wrappers).initialStore : Store Unit).mem =
      (tableSegments tables).foldl segStep (Mem.empty (tablePages tables)) := by
  have hP : (UInt32.ofNat (tablePages tables)).toNat = tablePages tables :=
    UInt32.toNat_ofNat_of_lt' (by simp only [tablePages, UInt32.size]; omega)
  show (tableSegments tables).foldl segStep
    (Mem.empty (UInt32.ofNat (tablePages tables)).toNat) = _
  rw [hP]

theorem tablePages_end (tables : List (Array UInt64)) :
    tablesEnd tables ≤ tablePages tables * 65536 := by
  have hDiv := Nat.div_add_mod (tablesEnd tables + 65535) 65536
  have hMod := Nat.mod_lt (tablesEnd tables + 65535) (show 0 < 65536 by omega)
  have hMax := Nat.mul_le_mul_right 65536 (Nat.le_max_right 16 ((tablesEnd tables + 65535) / 65536))
  simp only [tablePages]
  generalize (tablesEnd tables + 65535) % 65536 = r at *
  generalize (tablesEnd tables + 65535) / 65536 = q at *
  generalize max 16 q = P at *
  generalize tablesEnd tables = e at *
  omega

theorem tablePages_cap (tables : List (Array UInt64)) (hFit : tablesEnd tables ≤ 65535 * 65536) :
    tablePages tables ≤ 65535 := by
  simp only [tablePages]
  refine Nat.max_le.mpr ⟨by omega, ?_⟩
  have hDiv := Nat.div_add_mod (tablesEnd tables + 65535) 65536
  generalize (tablesEnd tables + 65535) % 65536 = r at *
  generalize (tablesEnd tables + 65535) / 65536 = q at *
  generalize tablesEnd tables = e at *
  omega

/-- The heap of a module with tables `tables` when it is instantiated: the bump pointer after
the tables, no free block, and no allocation. -/
def initialHeap (tables : List (Array UInt64)) : Heap :=
  { top := UInt64.ofNat (tablesEnd tables), free := [], allocs := 0, releases := 0, frees := 0 }

/-- The instantiation theorem.  The store in which the module of a program with tables starts, as
Talos's `Module.initialStore` builds it, meets the allocator invariant for `initialHeap`, caps its
memory at 65,535 pages, and holds each table as a borrowed array at its address.  The functions'
and wrappers' theorems therefore apply to the first call, whose owned arguments the host
allocates after the tables. -/
theorem compileWith_initialStore {S : List Sig} (prog : Prog S) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) (hFit : tablesEnd tables ≤ 65535 * 65536) :
    let store : Store Unit := (compileWith prog tables wrappers).initialStore
    (initialHeap tables).At store ∧ store.memoryCap (compileWith prog tables wrappers) 0 ≤ 65535 ∧
      ∀ k (hk : k < tables.length),
        (initialHeap tables).Borrowed store (tableAddr tables k) tables[k] := by
  intro store
  have h32 : tablesEnd tables < 4294967296 := by omega
  have hMem : store.mem = (tableSegments tables).foldl segStep (Mem.empty (tablePages tables)) :=
    initialStore_mem prog tables wrappers hFit
  have hEndP := tablePages_end tables
  have hPagesCap := tablePages_cap tables hFit
  obtain ⟨hPages, hBytes⟩ := tables_written tables (tablePages tables) hEndP h32 tables.length
    (Nat.le_refl _)
  rw [List.take_of_length_le (by rw [tableSegments_length]), ← hMem] at hPages hBytes
  have hTop : (UInt64.ofNat (tablesEnd tables)).toNat = tablesEnd tables :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hBase : 4096 ≤ tablesEnd tables := by
    rw [← tableStart_length]; simp [tableStart]
  have hAt : (initialHeap tables).At store := by
    refine ⟨rfl, .nil, ?_, ?_, ?_, nofun, nofun⟩
    · simp only [initialHeap, hTop]; exact hBase
    · simp only [initialHeap, hTop, hPages]; exact hEndP
    · rw [hPages]; exact hPagesCap
  have hCap : store.memoryCap (compileWith prog tables wrappers) 0 ≤ 65535 := by
    show (([Nat.min 65535 Module.memoryHardCap][0]?).getD _) ≤ 65535
    simp [Module.memoryHardCap]
  refine ⟨hAt, hCap, fun k hk => ?_⟩
  have hkEnd := tableStart_mono tables (k := k + 1) (by omega) (Nat.le_refl _)
  rw [tableStart_length, tableStart_succ tables hk, getElem!_pos tables k hk] at hkEnd
  have hAddr : (tableAddr tables k).toNat = tableStart tables k :=
    UInt64.toNat_ofNat_of_lt' (by
      show tableStart tables k < UInt64.size
      rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hAddr32 := tableAddr_toUInt32 tables (Nat.le_of_lt hk) h32
  have hRead : ∀ i, i ≤ tables[k].size → ∀ (a : UInt32), a.toNat = tableStart tables k + 8 * i →
      store.mem.read64 a = (UInt64.ofNat tables[k].size :: tables[k].toList)[i]! := by
    intro i hi a ha
    refine read64_of_bytes _ a _ fun j hj => ?_
    rw [ha, Nat.add_assoc, hBytes k hk (8 * i + j) (by rw [getElem!_pos tables k hk]; omega),
      getElem!_pos tables k hk, tableBytes_word _ hi hj]
  refine ⟨⟨by rw [hAddr]; omega, by rw [hAddr, hPages]; omega, ?_, fun i hi => ?_⟩,
    by simp only [initialHeap, hTop, hAddr]; omega, nofun⟩
  · rw [hRead 0 (Nat.zero_le _) _ (by rw [hAddr32]; omega)]
    rfl
  · rw [hRead (i + 1) (by omega) _ (by
      rw [Memory.toUInt32_toNat, UInt64.toNat_add, hAddr,
        UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
      omega)]
    simp [hi]

end Verified
