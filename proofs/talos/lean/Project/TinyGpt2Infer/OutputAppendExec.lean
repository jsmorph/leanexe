import Project.TinyGpt2Infer.OutputPrepareFrame
import Project.TinyGpt2Infer.OutputCopy
import Project.TinyGpt2Infer.OutputReleaseExec
import Project.TinyGpt2Infer.OutputAppend

namespace Project.TinyGpt2Infer.Spec
open Wasm Project.TinyGpt2 Project.Runtime Project.ProofKit ArrayPushLayout FixedArrayFold

theorem output_append_shape : (outputBody.drop 69).take 78 =
    (outputBody.drop 69).take 21 ++ (outputBody.drop 90).take 15 ++
      (outputBody.drop 105).take 42 := rfl

theorem output_append_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (pointer empty value : UInt64) (x : Row) (start count : Nat) (input : Array UInt64)
    (hSaved : OutputSaved pointer empty x frame)
    (hState : OutputMemory.State start count initial)
    (hInput : UInt64Array.At initial (node start count).root input) (hSize : input.size = count)
    (hSource : frame.get 53 = some (.i64 (node start count).root))
    (hCount : frame.get 55 = some (.i64 (UInt64.ofNat count)))
    (hLength : frame.get 54 = some (.i64 (UInt64.ofNat count)))
    (hValue : frame.get 59 = some (.i64 value))
    (hNextLength : frame.get 56 = some (.i64 (UInt64.ofNat (count + 1))))
    (hNeed : frame.get 62 = some (.i64 (UInt64.ofNat (capacity (count + 1)))))
    (hCurrent : frame.get 23 = some (.i64 (node start count).root))
    (hOwned : frame.get 71 = some (.i64 empty))
    (hEmpty : empty = (node start 0).root)
    (hFit : top start (count + 1) < 4294967296)
    (hMemory : top start (count + 1) ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap module 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (finalFrame : Locals),
      OutputMemory.State start (count + 1) final →
      UInt64Array.At final (node start (count + 1)).root (input.push value) →
      OutputSaved pointer empty x finalFrame →
      finalFrame.get 23 = some (.i64 (node start (count + 1)).root) →
      finalFrame.get 24 = some (.i64 (node start (count + 1)).root) →
      finalFrame.get 50 = frame.get 50 → finalFrame.get 71 = some (.i64 empty) →
      final.mem.pages = initial.mem.pages →
      (∀ address : Nat, address < start → final.mem.bytes address = initial.mem.bytes address) →
      final = { initial with mem := final.mem, globals := final.globals } →
      wp module rest Q final finalFrame env) :
    wp module ((outputBody.drop 69).take 78 ++ rest) Q initial frame env := by
  obtain ⟨allocations, retains, releases, frees, hGlobals⟩ := hState.globals
  have hOldFit := (top_mono start (show count ≤ count + 1 by omega)).trans_lt hFit
  have hOld := node_toNat start count hOldFit
  have hNew := node_toNat start (count + 1) hFit
  have hOldRoot := root_ge start count
  have hRoot := root_ge start (count + 1)
  have hEnd : (node start (count + 1)).root.toNat + 8 * (input.size + 2) =
      top start (count + 1) := by
    rw [hNew.1, hSize]
    rfl
  rw [output_append_shape]
  simp only [List.append_assoc]
  apply output_prepare_frame_spec env initial frame pointer empty x start count
    allocations retains releases frees hSaved hGlobals hState.freeList
    hFit hMemory hPages hCap hNextLength hNeed
  intro prepared hPrepared hTarget hPreserved
  let preparedStore := OutputMemory.prepare initial start (count + 1) allocations
  have hPreparedPages : preparedStore.mem.pages = initial.mem.pages :=
    OutputMemory.prepare_pages initial start (count + 1) allocations hFit hMemory
  have hPreparedArray := OutputMemory.prepare_array allocations hInput hSize hFit hMemory
  have hCounter : prepared.validIndex 58 := hPrepared.valid 58 (by decide)
  apply output_copy_spec env preparedStore prepared (node start count).root
    (node start (count + 1)).root input value hCounter hPrepared.values
    ((hPreserved 53 (by decide) (by decide)).trans hSource) hTarget
    (by rw [hSize]; exact (hPreserved 55 (by decide) (by decide)).trans hCount)
    (by rw [hSize]; exact (hPreserved 54 (by decide) (by decide)).trans hLength)
    ((hPreserved 59 (by decide) (by decide)).trans hValue)
    hPreparedArray (by rw [hEnd]; exact hFit.le)
    (by rw [hEnd, hPreparedPages]; exact hMemory)
    (by rw [hSize]; exact OutputMemory.prepare_length ..)
    (Or.inl (by
      rw [hOld.1, hNew.1, hSize]
      exact (separated start (show count < count + 1 by omega)).trans (by unfold root; omega)))
  intro middle hWrites hOldArray hNewArray
  rw [hEnd] at hWrites
  have hMiddleBuffers : OutputMemory.Buffers start count middle := by
    apply (OutputMemory.prepare_buffers allocations hState.toBuffers hFit hMemory).frame
      hOldFit hWrites.2.1.ge
    intro address hAddress
    apply hWrites.2.2 address (Or.inl ?_)
    rw [hNew.1]
    rw [top_eq_next_base] at hAddress
    unfold root
    omega
  have hMiddleGlobals : middle.globals.globals =
      [.i64 (UInt64.ofNat (top start (count + 1))), .i64 (freeHead (freed start count)),
        .i64 (allocations + 1), .i64 retains, .i64 releases, .i64 frees] := by
    rw [hWrites.1]
    exact OutputMemory.allocate_globals initial start (count + 1) allocations
      (freeHead (freed start count)) retains releases frees
      (by simpa only [OutputMemory.globals, top_eq_next_base] using hGlobals)
  let copied := FixedArrayCopy.counterFrame prepared 58 input.size hCounter
  have hCopied : OutputSaved pointer empty x copied := hPrepared.counter input.size hCounter
  have hCopiedGet (index : Nat) (hIndex : index ≠ 58) : copied.get index = prepared.get index :=
    FixedArrayCopy.counterFrame_get_ne prepared 58 input.size index hCounter hIndex
  apply output_release_region_spec env middle copied (node start count).root empty
    (node start count).capacity (freeHead (freed start count)) releases frees
    (node start (count + 1)).root input count hCopied.params hCopied.locals hCopied.values
    (by rw [hCopiedGet 23 (by decide), hPreserved 23 (by decide) (by decide)]; exact hCurrent)
    ((hCopiedGet 57 (by decide)).trans hTarget)
    (by rw [hCopiedGet 71 (by decide), hPreserved 71 (by decide) (by decide)]; exact hOwned)
    (by
      rw [hEmpty]
      constructor
      · intro hEq
        by_contra hCount
        have hSep := separated start (show 0 < count by omega)
        have hZero := node_toNat start 0 ((top_mono start (show 0 ≤ count + 1 by omega)).trans_lt hFit)
        have hNat := congrArg UInt64.toNat hEq
        rw [hOld.1, hZero.1] at hNat
        simp only [top, root, capacity] at hSep hNat
        omega
      · rintro rfl
        rfl)
    (by
      intro hEq
      have hNat := congrArg UInt64.toNat hEq
      rw [hOld.1, hNew.1] at hNat
      have hSep := separated start (show count < count + 1 by omega)
      simp only [top, root, capacity] at hSep hNat
      omega)
    (by
      intro hEq
      have hNat := congrArg UInt64.toNat hEq
      rw [hNew.1] at hNat
      change root start (count + 1) = 0 at hNat
      omega)
    (by rw [hOld.1]; omega) hMiddleBuffers.currentHeader hOldArray
    (by simp [hMiddleGlobals]) (by simp [hMiddleGlobals]) (by simp [hMiddleGlobals])
  have hResult := OutputMemory.append_result initial middle start count allocations retains releases frees
    (input.push value) hState.toBuffers hGlobals hFit hMemory hWrites hNewArray
  have hGets := outputReleaseFrame_get copied (node start (count + 1)).root hCopied.params hCopied.locals
  apply hNext _ _ hResult.1 hResult.2.1
    (outputReleaseFrame_saved hCopied _) hGets.1 hGets.2.1
    (hGets.2.2.1.trans ((hCopiedGet 50 (by decide)).trans (hPreserved 50 (by decide) (by decide))))
    (hGets.2.2.2.trans ((hCopiedGet 71 (by decide)).trans
      ((hPreserved 71 (by decide) (by decide)).trans hOwned))) hResult.2.2.1 hResult.2.2.2.1 hResult.2.2.2.2

#print axioms output_append_spec
end Project.TinyGpt2Infer.Spec
