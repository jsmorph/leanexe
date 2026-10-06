import Examples.Updates.Module
import LeanExe.IR.Correct
import LeanExe.IR.Build
import LeanExe.IR.Fold
import LeanExe.Encoding.RoundTrip

/-! The `updates` function `pushCopy` computes its Lean definition exactly: its `push` onto an
array that is used again copies the array. -/

namespace Examples.Updates

open Wasm LeanExe.Pipeline LeanExe.IR LeanExe.Runtime LeanExe.ProofKit

/-- A new array and a handed-over array returned together: an owned pair in disjoint blocks,
and every region apart from the handed-over block keeps its bytes and lies apart from both. -/
theorem newArray_with_moved {heap heap' : Heap} {initial store : Store Unit}
    {p q : UInt64} {ys xs : Array UInt64}
    (hNew : heap.NewArray initial heap' store p ys) (hOwned : heap.Owned initial q xs) :
    Represent.owned heap' store [.i64 p, .i64 q] (ys, xs) ∧
      heap.Keeps initial ([q].map (block initial)) heap' store
        (Represent.blocks store [.i64 p, .i64 q] (ys, xs)) := by
  obtain ⟨hOwned', hCap⟩ := hNew.ownedKeep q xs hOwned
  have hBlock : block store q = block initial q := block_eq hCap
  have hApart := hNew.ownedApart q xs hOwned
  refine ⟨Represent.owned_pair.mpr ⟨hNew.owned, hOwned', ?_⟩, fun r hr hpos hA => ?_⟩
  · rw [hBlock]
    exact regionsDisjoint_symm hApart
  obtain ⟨hBytes, hRegion, hFresh⟩ := hNew.keeps r hr hpos fun _ hb => nomatch hb
  refine ⟨hBytes, hRegion, fun b hb => ?_⟩
  change b ∈ [block store p, block store q] at hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hFresh _ (List.mem_singleton_self _)
  · rw [List.mem_singleton.mp hb, hBlock]
    exact hA _ (List.mem_singleton_self _)

/-- `pushCopy` with its two arguments as one pair, the array handed over. -/
def pushCopyTuple (x : Moved (Array UInt64) × UInt64) : Array UInt64 × Array UInt64 :=
  Examples.Updates.pushCopy x.1.val x.2

/-- `pushCopy` copies its array with the value pushed, since the result uses the array again, and
returns the copy with the array. -/
theorem pushCopy_implements : Implements updates.module 5 pushCopyTuple := by
  refine Func.implements_moves updates.funcs 3 updates.pushCopy.ir "pushCopy" rfl pushCopyTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨⟨xs⟩, v⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨q, rfl, hOwned⟩, rfl⟩ - hCap
  change heap.Owned initial q xs at hOwned
  rw [show Represent.moves initial ([.i64 q] ++ Scalar.values v) (Moved.mk xs, v) = [q] from rfl]
  have hMemory32 : (compile updates.funcs).memIs64 = false := rfl
  have hImports : (compile updates.funcs).imports = [] := rfl
  have hAlloc : (compile updates.funcs).funcs[0]? = some (allocFunction 0) := rfl
  let z : Value := .i64 0
  let start : State := { params := [.i64 q, .i64 v], locals := [z, z, z, z, z, z] }
  let s1 : State := { params := [.i64 q, .i64 v], locals := [.i64 v, z, z, z, z, z] }
  let s2 : State :=
    { params := [.i64 q, .i64 v], locals := [.i64 v, .i64 (UInt64.ofNat xs.size), z, z, z, z] }
  show Triple _ (.seq (.assign 2 (.get 1)) (.seq (.arraySize 3 0)
      (.build 4 5 6 (.bin .add (.get 3) (.const 1))
        (.ite (.ltU (.get 6) (.get 3)) (.read 0 (.get 6)) (.get 2))))) 7
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1)
    (Stmt.assign_spec.mono (fun s st ⟨hs, hst⟩ => ⟨v, start, s1, by rw [hst]; rfl, rfl, hs, rfl⟩)
      fun _ _ h => h) ?_
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2)
    ((Stmt.arraySize_spec hOwned.values (before := s1) rfl (by simp [s1])).mono (fun _ _ h => h)
      fun _ _ ⟨hs, hSet⟩ => ⟨hs, (Option.some.inj (hSet.symm.trans rfl))⟩) ?_
  refine (Stmt.pushBuild_spec (src := 0) (size := 3) (v := 2) hMemory32 hImports hAlloc
    (by decide) (by decide) (by decide) (by simp [s2]) hHeap hCap rfl rfl rfl
    hOwned.borrowed).mono (fun _ _ h => h) ?_
  rintro store state ⟨p, hFrame, hDst, hNew⟩
  obtain ⟨hPair, hKeeps⟩ := newArray_with_moved hNew hOwned
  have hSrc : state.get 0 = some (.i64 q) := hFrame.get 0 (by decide) (by decide)
  exact ⟨_, hNew.at_, hNew.caps, [.i64 p, .i64 q], state,
    by simp [Expr.evalResults, Expr.eval, updates.pushCopy.ir, Func.scratch, hDst, hSrc],
    hPair, hKeeps⟩

/-- `encode` succeeds on `updates.module`, and its bytes decode to a module whose export
`pushCopy` computes `Examples.Updates.pushCopy` exactly.  The other exports, `pushTwo`,
`setTwice`, and `insertErase`, have no theorem: their in-place rules are proved through `clob`
and `trees`. -/
theorem updates_bytes : ∃ bytes, Wasm.Encoding.encode updates.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 5 pushCopyTuple := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip updates.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, updates.module, decoded, pushCopy_implements⟩

#print axioms updates_bytes

end Examples.Updates
