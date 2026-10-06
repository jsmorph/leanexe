import Examples.Increment.Module
import Examples.Increment.Spec
import LeanExe.IR.Build
import LeanExe.IR.Correct
import LeanExe.IR.Combinators
import LeanExe.Pipeline.Budget
import LeanExe.Encoding.RoundTrip

/-! The bytes of `increment.module` compute the specification `expected`, and from an allocator
whose `top` leaves room for one block of 72 bytes, the call returns without a trap and leaves the
16 pages a module starts with. -/

namespace Examples.Increment

open Wasm LeanExe.Pipeline LeanExe.IR LeanExe.Runtime Examples.Increment

/-- The program computes the specification on every input that memory can hold. -/
theorem compute_eq (xs : Array UInt64) (h : xs.size < 2 ^ 64) : compute xs = expected xs := by
  have hn : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  unfold compute expected
  by_cases hs : xs.size ≤ 8
  · have hle : xs.size.toUInt64 ≤ 8 := by rw [UInt64.le_iff_toNat_le, hn]; simpa using hs
    simp only [hle, ite_true, hs]
    apply Array.ext
    · rw [build_size, hn, Array.size_map]
    · intro i hi _
      rw [build_size, hn] at hi
      rw [Array.getElem_map, ← getElem!_pos (LeanExe.build _ _) i (by rw [build_size, hn]; exact hi),
        build_get (by rw [hn]; exact hi), UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hi h),
        getElem!_pos xs i hi]
  · have hle : ¬ xs.size.toUInt64 ≤ 8 := by rw [UInt64.le_iff_toNat_le, hn]; simpa using hs
    simp only [hle, ite_false, hs]
    rfl

/-- Under `a = false`, the heap has room for one block of 72 bytes, enough for nine words. -/
theorem compute_implementsA {a : Bool} (pages : Nat) :
    ImplementsA a increment.module 2 compute
      (fun _ heap store => a = false → heap.Bounded store increment.module 72 1 pages)
      (fun _ _ _ heap' final => a = false → heap'.Bounded final increment.module 72 0 pages) := by
  refine Func.implements_heapA [(increment.ir, "compute")] 0 increment.ir "compute" rfl compute
    _ _ (by rintro _ _ _ _ ⟨ptr, rfl, -⟩; rfl) ?_
  rintro xs heap initial _ hHeap hPre ⟨ptr, rfl, hXs⟩ hCap
  have hW := hXs.values
  have hLength0 := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength0
  have hSize := hW.size_lt
  set start := increment.ir.state [.i64 ptr] with hStartDef
  have hStart : start.params.length + start.locals.length = 8 := rfl
  have hGet0 : start.get 0 = some (.i64 ptr) := rfl
  let n := xs.size.toUInt64
  let count : UInt64 := if n ≤ 8 then n else 0
  have hCount8 : count.toNat ≤ 8 := by
    simp only [count]; split
    · rename_i h; exact UInt64.le_iff_toNat_le.mp h
    · simp
  let s1 := start.update 1 (.i64 (UInt64.ofNat xs.size))
  let s2 := s1.update 2 (.i64 (UInt64.ofNat xs.size))
  let s3 := s2.update 3 (.i64 count)
  show TripleA _ _ (.seq (.load .u64 1 (.get 0)) (.seq (.assign 2 (.get 1))
    (.seq (.assign 3 (.ite (.leU (.get 2) (.const 8)) (.get 2) (.const 0)))
      (Stmt.build 4 5 6 (.get 3) (.bin .add (.read 0 (.get 6)) (.const 1)))))) 7 _ _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s3) ?_) ?_
  · simp [Stmt.run, Expr.eval, hLength0, hW.lengthRead, State.set?_eq_update, hStart, s1, hGet0]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, s3, count, n]
  have hS3 : s3.params.length + s3.locals.length = 8 := by simp [s3, s2, s1, hStart]
  have hNeed : UInt64.ofNat (8 * (count.toNat + 1)) ≤ 72 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
    simp; omega
  refine (Stmt.build_specA (n := count) (fun i => xs[i.toNat]! + 1) rfl rfl rfl (by decide)
    (by decide) (by omega) hHeap hCap (fun _ => by omega)
    (fun ha => (hPre ha).room hHeap (by omega) hNeed (by decide) hCap)
    ⟨s3, by simp [Expr.eval, s3, s2, s1, hStart]⟩ ?_).mono (fun _ _ h => h) ?_
  · intro k store state hk hAt hFrame hIndex
    have hState : state.params.length + state.locals.length = 8 := by
      rw [hFrame.params, hFrame.locals]; exact hS3
    have g0 : state.get 0 = some (.i64 ptr) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s3, s2, s1, hGet0])
    have g0' : (state.update 7 (.i64 (UInt64.ofNat k))).get 0 = some (.i64 ptr) := by
      rw [State.get_update_ne (by decide)]; exact g0
    exact ⟨state.update 7 (.i64 (UInt64.ofNat k)), by
      simp [Expr.eval, hIndex, State.set?_eq_update, hState,
        Expr.readValue_at (hAt ptr _ hXs) g0', U64Op.apply]⟩
  rintro store state ⟨p, -, hPtr, hNew, hPages⟩
  exact ⟨_, hNew.at_, hNew.caps, [.i64 p], state,
    by simp [increment.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨p, rfl, hNew.owned⟩,
    hNew.keeps, fun ha => (hPre ha).allocate (spare := 0) hHeap hNeed (by decide) hCap hPages
      hNew.caps⟩

theorem compute_implements : Implements increment.module 2 compute :=
  (compute_implementsA (a := true) 0).implements_of fun _ _ _ h => nomatch h

/-- `encode` succeeds on `increment.module`, and its bytes decode to a module that computes the
specification `expected`. -/
theorem increment_bytes : ∃ bytes, Wasm.Encoding.encode increment.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 expected := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip increment.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, increment.module, decoded, compute_implements.congr
    fun _ _ _ xs ⟨_, _, hXs⟩ => compute_eq xs hXs.values.size_lt⟩

/-- The bytes of `increment.module` decode to a module whose export, called with an array in
memory under an allocator whose `top` leaves 120 bytes within the first 16 pages, with 16 pages
and a cap that allows them, returns the words of `expected` without a trap and leaves memory at
16 pages. -/
theorem increment_total : ∃ bytes, Wasm.Encoding.encode increment.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧
      ∀ (xs : Array UInt64) (ptr : UInt64) (env : HostEnv Unit) (store : Store Unit) (heap : Heap),
        heap.At store → heap.Borrowed store ptr xs → heap.top.toNat + 120 ≤ 16 * 65536 →
        store.mem.pages ≤ 16 → 16 ≤ store.memoryCap m 0 → store.memoryCap m 0 ≤ 65535 →
        Runs false env m 2 store [.i64 ptr] fun final values =>
          ∃ heap' : Heap, heap'.At final ∧
            Represent.owned heap' final values.reverse (expected xs) ∧ final.mem.pages ≤ 16 := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip increment.module (by decide) (by decide +kernel)
  refine ⟨bytes, success, increment.module, decoded, ?_⟩
  intro xs ptr env store heap hHeap hXs hTop hPages hCap hMax
  have hBounded : heap.Bounded store increment.module 72 1 16 := by
    refine ⟨?_, hPages, hCap⟩
    unfold Heap.Budget
    have : (72 : UInt64).toNat = 72 := rfl
    rw [this]
    have : 1 - units 72 heap.free ≤ 1 := Nat.sub_le _ _
    have : (1 - units 72 heap.free) * (72 + 48) ≤ 120 := by
      calc (1 - units 72 heap.free) * (72 + 48) ≤ 1 * (72 + 48) := Nat.mul_le_mul_right _ this
        _ = 120 := rfl
    omega
  rw [← compute_eq xs hXs.values.size_lt]
  exact ((compute_implementsA (a := false) 16) env store heap [.i64 ptr] xs hHeap
    (fun _ => hBounded) ⟨ptr, rfl, hXs⟩ Separate.nil hMax).mono
    fun _ _ ⟨heap', hAt, hOwned, _, _, hPost⟩ => ⟨heap', hAt, hOwned, (hPost rfl).within⟩

#print axioms increment_total

end Examples.Increment
