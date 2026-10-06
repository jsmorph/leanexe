import Examples.Drone.Verify

/-! Complete execution and a memory bound.  From an allocator state with no free block whose
`top` leaves room for 66 blocks of `tableBytes` bytes within `pages` pages, `compute` returns its
words without a trap and ends with at most `pages` pages.  With the terrain below address 8192,
70 pages (4.375 MiB) suffice for every terrain. -/

namespace Examples.Drone

open Wasm LeanExe.Pipeline LeanExe.IR LeanExe.Runtime Examples.Drone

/-- An allocator with no free block and room above `top` for 66 blocks of `tableBytes` bytes,
with their headers, within `pages` pages. -/
theorem room_bounded {heap : Heap} {store : Store Unit} {m : Wasm.Module} (pages : Nat)
    (hFree : heap.free = []) (hTop : heap.top.toNat + 66 * (tableBytes.toNat + 48) ≤ pages * 65536)
    (hPages : store.mem.pages ≤ pages) (hCap : pages ≤ store.memoryCap m 0) :
    heap.Bounded store m tableBytes (0 + 66) pages := by
  refine ⟨?_, hPages, hCap⟩
  unfold Heap.Budget
  rw [hFree]
  simp only [units, List.map_nil, List.sum_nil, Nat.sub_zero]
  omega

/-- From such an allocator state, with a memory cap that allows `pages` pages, `compute`
returns its words without a trap, and memory ends with at most `pages` pages. -/
theorem compute_runs (terrain : Array UInt64) (pages : Nat) (env : HostEnv Unit)
    (store : Store Unit) (heap : Heap) (params : List Value) (hHeap : heap.At store)
    (hArgs : Represent.borrowed heap store params terrain) (hFree : heap.free = [])
    (hTop : heap.top.toNat + 66 * (tableBytes.toNat + 48) ≤ pages * 65536)
    (hPages : store.mem.pages ≤ pages) (hCap : pages ≤ store.memoryCap drone.module 0)
    (hMax : store.memoryCap drone.module 0 ≤ 65535) :
    Runs false env drone.module 16 store params.reverse fun final values =>
      ∃ heap' : Heap, heap'.At final ∧ Represent.owned heap' final values.reverse (compute terrain) ∧
        final.mem.pages ≤ pages :=
  (compute_implementsA (a := false) 0 pages env store heap params terrain hHeap
    (fun _ => room_bounded pages hFree hTop hPages hCap) hArgs Separate.nil hMax).mono
    fun _ _ ⟨heap', hAt, hOwned, _, _, hPost⟩ => ⟨heap', hAt, hOwned, (hPost rfl).within⟩

/-- The bytes of `drone.module` decode to a module whose entry 16, called with a terrain that an
allocator with no free block has placed below address 8192, and with a memory cap of at least 70
pages, returns the words of `compute` without a trap and ends with at most 70 pages. -/
theorem drone_compute_total : ∃ bytes, Wasm.Encoding.encode drone.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧
      ∀ (terrain : Array UInt64) (ptr : UInt64) (env : HostEnv Unit) (store : Store Unit)
        (heap : Heap), heap.At store → heap.Borrowed store ptr terrain → heap.free = [] →
        heap.top.toNat ≤ 8192 → store.mem.pages ≤ 70 → 70 ≤ store.memoryCap m 0 →
        store.memoryCap m 0 ≤ 65535 →
        Runs false env m 16 store [.i64 ptr] fun final values =>
          ∃ heap' : Heap, heap'.At final ∧
            Represent.owned heap' final values.reverse (compute terrain) ∧
            final.mem.pages ≤ 70 := by
  obtain ⟨bytes, success, decoded⟩ := drone_round_trip
  refine ⟨bytes, success, drone.module, decoded, ?_⟩
  intro terrain ptr env store heap hHeap hT hFree hTop hPages hCap hMax
  exact compute_runs terrain 70 env store heap [.i64 ptr] hHeap ⟨ptr, rfl, hT⟩ hFree
    (by unfold tableBytes; simp; omega) hPages hCap hMax

end Examples.Drone
