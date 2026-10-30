import Library.Hashing.Crc.Compiled
import Library.Hashing.Crc.Proof
import Verified.Call

/-! The bytes of the module `crc` compute CRC-32 and CRC-32C.  An entry, called from a ready store
with a borrowed array `msg` and a byte count `n`, returns without a trap the word whose value is
the CRC of the transcription `Library.Hashing.Crc.Spec` for the first `n` bytes of `msg`.  An
update entry, called also with the CRC of some bytes `A`, returns the CRC of `A` followed by those
bytes.  A store is ready, as `Verified.Ready` states, when the allocator invariant holds, the two
tables are borrowed arrays at their addresses, and the memory cap is at most 65,535 pages.  The
array stays borrowed, the store stays ready, and every region of the heap before the call keeps its
bytes.  The store in which the module starts is ready. -/

namespace Library.Hashing.Crc

open Wasm LeanExe.Pipeline Library.Bytes Library.Hashing.Crc.Proof
open Verified (Ready)

set_option maxRecDepth 10000 in
/-- The table of CRC-32C, at address 6152, is the program's second table.  The address depends on
the size of the first table, whose unfolding needs a raised `maxRecDepth`. -/
theorem crc32c_table :
    ∀ t ∈ [((6152 : UInt64), crc32cTable)], ∃ i, ∃ hi : i < compiled.tables.length,
      t = (Verified.tableAddr compiled.tables i, compiled.tables[i]) :=
  fun _ ht => ⟨1, by decide, List.mem_singleton.mp ht⟩

theorem crc32_export :
    ({ name := "crc32", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem crc32c_export :
    ({ name := "crc32c", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem crc32Update_export :
    ({ name := "crc32Update", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem crc32cUpdate_export :
    ({ name := "crc32cUpdate", funcIdx := 7 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 4, the export `crc32`, returns CRC-32 of the first `n` bytes of `msg`. -/
theorem crc32_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (msg : Array UInt64) (n ptr : UInt64) (h : Ready compiled.module compiled.tables heap store)
    (hb : heap.Borrowed store ptr msg) :
    Runs false env compiled.module 4 store [.i64 n, .i64 ptr] fun final values =>
      ∃ c : UInt64, values.reverse = [.i64 c] ∧
        c.toNat = Spec.crc32 (messageBytes msg n.toNat) ∧
        ∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (Verified.ImplementsTables.call compiled.crc32.implements compiled.tables
    (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩) env heap store [.i64 ptr, .i64 n]
    (msg, n) h ⟨[.i64 ptr], [.i64 n], rfl, ⟨ptr, rfl, hb⟩, rfl⟩ rfl trivial).mono
    fun _ _ ⟨heap', hv, hR, hkept, hkeep, _⟩ =>
      ⟨crc32 msg n, hv, crc32_spec msg n, heap', hR, hkept _ _ hb, hkeep⟩

/-- Function 5, the export `crc32c`, returns CRC-32C of the first `n` bytes of `msg`. -/
theorem crc32c_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (msg : Array UInt64) (n ptr : UInt64) (h : Ready compiled.module compiled.tables heap store)
    (hb : heap.Borrowed store ptr msg) :
    Runs false env compiled.module 5 store [.i64 n, .i64 ptr] fun final values =>
      ∃ c : UInt64, values.reverse = [.i64 c] ∧
        c.toNat = Spec.crc32c (messageBytes msg n.toNat) ∧
        ∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (Verified.ImplementsTables.call compiled.crc32c.implements compiled.tables crc32c_table env heap
    store [.i64 ptr, .i64 n] (msg, n) h ⟨[.i64 ptr], [.i64 n], rfl, ⟨ptr, rfl, hb⟩, rfl⟩ rfl
    trivial).mono
    fun _ _ ⟨heap', hv, hR, hkept, hkeep, _⟩ =>
      ⟨crc32c msg n, hv, crc32c_spec msg n, heap', hR, hkept _ _ hb, hkeep⟩

/-- Function 6, the export `crc32Update`, returns CRC-32 of the bytes `A` followed by the first
`n` bytes of `msg`, from CRC-32 `crc` of `A`. -/
theorem crc32Update_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (A : List UInt8) (crc : UInt64) (hcrc : crc.toNat = Spec.crc32 A) (msg : Array UInt64)
    (n ptr : UInt64) (h : Ready compiled.module compiled.tables heap store)
    (hb : heap.Borrowed store ptr msg) :
    Runs false env compiled.module 6 store [.i64 n, .i64 ptr, .i64 crc] fun final values =>
      ∃ c : UInt64, values.reverse = [.i64 c] ∧
        c.toNat = Spec.crc32 (A ++ messageBytes msg n.toNat) ∧
        ∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (Verified.ImplementsTables.call compiled.crc32Update.implements compiled.tables
    (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩) env heap store
    [.i64 crc, .i64 ptr, .i64 n] (crc, msg, n) h
    ⟨[.i64 crc], [.i64 ptr, .i64 n], rfl, rfl, [.i64 ptr], [.i64 n], rfl, ⟨ptr, rfl, hb⟩, rfl⟩
    rfl trivial).mono fun _ _ ⟨heap', hv, hR, hkept, hkeep, _⟩ =>
      ⟨crc32Update crc msg n, hv, crc32Update_spec A crc hcrc msg n, heap', hR, hkept _ _ hb,
        hkeep⟩

/-- Function 7, the export `crc32cUpdate`, returns CRC-32C of the bytes `A` followed by the first
`n` bytes of `msg`, from CRC-32C `crc` of `A`. -/
theorem crc32cUpdate_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (A : List UInt8) (crc : UInt64) (hcrc : crc.toNat = Spec.crc32c A) (msg : Array UInt64)
    (n ptr : UInt64) (h : Ready compiled.module compiled.tables heap store)
    (hb : heap.Borrowed store ptr msg) :
    Runs false env compiled.module 7 store [.i64 n, .i64 ptr, .i64 crc] fun final values =>
      ∃ c : UInt64, values.reverse = [.i64 c] ∧
        c.toNat = Spec.crc32c (A ++ messageBytes msg n.toNat) ∧
        ∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (Verified.ImplementsTables.call compiled.crc32cUpdate.implements compiled.tables crc32c_table
    env heap store [.i64 crc, .i64 ptr, .i64 n] (crc, msg, n) h
    ⟨[.i64 crc], [.i64 ptr, .i64 n], rfl, rfl, [.i64 ptr], [.i64 n], rfl, ⟨ptr, rfl, hb⟩, rfl⟩
    rfl trivial).mono fun _ _ ⟨heap', hv, hR, hkept, hkeep, _⟩ =>
      ⟨crc32cUpdate crc msg n, hv, crc32cUpdate_spec A crc hcrc msg n, heap', hR, hkept _ _ hb,
        hkeep⟩

#print axioms crc32_call
#print axioms crc32c_call
#print axioms crc32Update_call
#print axioms crc32cUpdate_call

end Library.Hashing.Crc
