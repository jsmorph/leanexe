import Examples.Euler.Verify

/-! Complete execution and a memory bound.  From the allocator state of a fresh instance, both
solve exports return their words without a trap, and memory ends within a page count that `n`
fixes: at most 1,407 pages (88 MiB), for every `n`. -/

namespace Examples.Euler

open Wasm LeanExe.Pipeline LeanExe.IR LeanExe.Runtime Examples.Euler

/-- The cells of a grid of a run: `n * n` for `n` in range, and 1 otherwise. -/
def runCells (n : UInt64) : Nat := if (2 ≤ n && n ≤ 800) = true then (n * n).toNat else 1

/-- The bytes of a grid of `runCells n` cells. -/
def runBytes (n : UInt64) : UInt64 := UInt64.ofNat (8 * (runCells n * 6 + 1))

/-- The pages of a run: the 16 pages of a fresh instance, or the heap base and three grids with
their headers, rounded up to pages. -/
def runPages (n : UInt64) : Nat :=
  max 16 ((4096 + 3 * ((runBytes n).toNat + 48) + 65535) / 65536)

theorem runCells_le (n : UInt64) : 1 ≤ runCells n ∧ runCells n ≤ 640000 := by
  unfold runCells
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le,
      UInt64.reduceToNat] at h
    have hLo := Nat.mul_le_mul h.1 h.1
    have hHi : n.toNat * n.toNat ≤ 640000 := Nat.mul_le_mul h.2 h.2
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (lt_of_le_of_lt hHi (by decide))]
    exact ⟨le_trans (by decide) hLo, hHi⟩
  · omega

theorem runCells_eq {n : UInt64} (h : (2 ≤ n && n ≤ 800) = true) :
    (n * n).toNat = runCells n := by
  rw [runCells, if_pos h]

theorem runBytes_grid (n : UInt64) : GridBytes (runCells n) (runBytes n) := by
  have := runCells_le n
  refine ⟨?_, by omega⟩
  rw [runBytes, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]

theorem runPages_le (n : UInt64) : runPages n ≤ 1407 := by
  have := runCells_le n
  have hBytes := (runBytes_grid n).bytes
  unfold runPages
  omega

/-- A fresh allocator state, with room for three grids within `runPages n` pages. -/
theorem fresh_bounded {heap : Heap} {store : Store Unit} {m : Wasm.Module} (n : UInt64)
    (hFree : heap.free = []) (hTop : heap.top.toNat = 4096)
    (hPages : store.mem.pages ≤ runPages n) (hCap : runPages n ≤ store.memoryCap m 0) :
    heap.Bounded store m (runBytes n) (0 + 3) (runPages n) := by
  refine ⟨?_, hPages, hCap⟩
  unfold Heap.Budget
  rw [hFree, hTop]
  simp only [units, List.map_nil, List.sum_nil, Nat.sub_zero]
  unfold runPages
  omega

/-- From a store whose allocator holds no free block and whose `top` is the heap base, with at
most `runPages n` pages and a cap that allows them, `solve n` returns its words without a trap,
and memory ends with at most `runPages n` pages. -/
theorem solve_runs (n : UInt64) (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (hHeap : heap.At store) (hFree : heap.free = []) (hTop : heap.top.toNat = 4096)
    (hPages : store.mem.pages ≤ runPages n) (hCap : runPages n ≤ store.memoryCap euler.module 0)
    (hMax : store.memoryCap euler.module 0 ≤ 65535) :
    Runs false env euler.module 23 store [.i64 n] fun final values =>
      ∃ heap' : Heap, heap'.At final ∧ Represent.owned heap' final values.reverse (solve n) ∧
        final.mem.pages ≤ runPages n :=
  (solve_implementsA (a := false) (runBytes_grid n) 0 (runPages n) env store heap [.i64 n] n
    hHeap (fun _ => ⟨runCells_eq, (runCells_le n).1, fresh_bounded n hFree hTop hPages hCap⟩)
    rfl Separate.nil hMax).mono
    fun _ _ ⟨heap', hAt, hOwned, _, _, hPost⟩ => ⟨heap', hAt, hOwned, (hPost rfl).within⟩

/-- `solve_runs` for the reconstructed solver. -/
theorem reconstructedSolve_runs (n trials : UInt64) (env : HostEnv Unit) (store : Store Unit)
    (heap : Heap) (hHeap : heap.At store) (hFree : heap.free = [])
    (hTop : heap.top.toNat = 4096) (hPages : store.mem.pages ≤ runPages n)
    (hCap : runPages n ≤ store.memoryCap euler.module 0)
    (hMax : store.memoryCap euler.module 0 ≤ 65535) :
    Runs false env euler.module 56 store [.i64 trials, .i64 n] fun final values =>
      ∃ heap' : Heap, heap'.At final ∧
        Represent.owned heap' final values.reverse (reconstructedSolve n trials) ∧
        final.mem.pages ≤ runPages n :=
  (reconstructedSolve_implementsA (aborts := false) (runBytes_grid n) 0 (runPages n) env store
    heap [.i64 n, .i64 trials] (n, trials) hHeap
    (fun _ => ⟨runCells_eq, (runCells_le n).1, fresh_bounded n hFree hTop hPages hCap⟩)
    rfl Separate.nil hMax).mono
    fun _ _ ⟨heap', hAt, hOwned, _, _, hPost⟩ => ⟨heap', hAt, hOwned, (hPost rfl).within⟩

/-- The bytes of `euler.module` decode to a module whose two solve exports, called on the state of
a fresh instance (allocator `top` at the heap base 4096, no free block, 16 pages) with a memory cap
of at least 1,407 pages, return the words of `solve n` and of `reconstructedSolve n trials`
without a trap, and end with at most 1,407 pages. -/
theorem euler_solve_total : ∃ bytes, Wasm.Encoding.encode euler.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧
      (∀ (n : UInt64) (env : HostEnv Unit) (store : Store Unit) (heap : Heap),
        heap.At store → heap.free = [] → heap.top.toNat = 4096 → store.mem.pages = 16 →
        1407 ≤ store.memoryCap m 0 → store.memoryCap m 0 ≤ 65535 →
        Runs false env m 23 store [.i64 n] fun final values =>
          ∃ heap' : Heap, heap'.At final ∧ Represent.owned heap' final values.reverse (solve n) ∧
            final.mem.pages ≤ 1407) ∧
      (∀ (n trials : UInt64) (env : HostEnv Unit) (store : Store Unit) (heap : Heap),
        heap.At store → heap.free = [] → heap.top.toNat = 4096 → store.mem.pages = 16 →
        1407 ≤ store.memoryCap m 0 → store.memoryCap m 0 ≤ 65535 →
        Runs false env m 56 store [.i64 trials, .i64 n] fun final values =>
          ∃ heap' : Heap, heap'.At final ∧
            Represent.owned heap' final values.reverse (reconstructedSolve n trials) ∧
            final.mem.pages ≤ 1407) := by
  obtain ⟨bytes, success, decoded⟩ := euler_round_trip
  refine ⟨bytes, success, euler.module, decoded, ?_, ?_⟩
  · intro n env store heap hHeap hFree hTop hPages hCap hMax
    have hLe := runPages_le n
    exact (solve_runs n env store heap hHeap hFree hTop
      (by rw [hPages]; unfold runPages; omega) (by omega) hMax).mono
      fun _ _ ⟨heap', hAt, hOwned, hFinal⟩ => ⟨heap', hAt, hOwned, hFinal.trans hLe⟩
  · intro n trials env store heap hHeap hFree hTop hPages hCap hMax
    have hLe := runPages_le n
    exact (reconstructedSolve_runs n trials env store heap hHeap hFree hTop
      (by rw [hPages]; unfold runPages; omega) (by omega) hMax).mono
      fun _ _ ⟨heap', hAt, hOwned, hFinal⟩ => ⟨heap', hAt, hOwned, hFinal.trans hLe⟩

#print axioms euler_solve_total

end Examples.Euler
