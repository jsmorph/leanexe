import Project.EulerRiemann.RetryIteration

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity

theorem retryInvariant.values {initial : Store Unit} {initialHeap : Heap} {n : Nat}
    {time source need : UInt64} {grid : Array Traversal.Cell} {expected : Control.Attempt}
    {spare limit : Nat} {store : Store Unit} {frame : Locals}
    (h : retryInvariant initial initialHeap n time source need grid expected spare limit store frame) :
    frame.values = [] := by
  obtain ⟨heap, _, hActive | hDone⟩ := h
  · obtain ⟨fuel, dt, hFrame, _⟩ := hActive
    exact hFrame.values
  · obtain ⟨fuel, dt, result, hFrame, _⟩ := hDone
    exact hFrame.values

theorem retry_loop_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n : Nat) (time : UInt64)
    (expected : Control.Attempt) (spare limit : Nat) (store : Store Unit) (frame : Locals)
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hOwner : initialHeap.Owns initial source grid) (hSuccess : expected.status = 0)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerRiemann.«module» 0 * 65536)
    (hInv : retryInvariant initial initialHeap n time source.root
      (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit store frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final heap resultFrame,
      RetryStoreAt initial initialHeap final heap →
      RetryDone initial initialHeap n time source.root
        (normalizedCapacity (UInt64.ofNat grid.size) 7) expected spare limit final heap resultFrame →
      wp Project.EulerRiemann.«module» rest Q final resultFrame env) :
    wp Project.EulerRiemann.«module» ([.block 0 0 [.loop 0 0 retryLoop]] ++ rest)
      Q store frame env := by
  have hEntryValues := hInv.values
  simp only [List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := retryInvariant initial initialHeap n time source.root
    (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit)
    (μ := fun _ current => retryMeasure current)
  · exact hInv
  · intro current currentFrame hCurrent
    have hValues := hCurrent.values
    refine wp.conseq ?_ (retry_iteration_spec env initial initialHeap source grid n time expected
      spare limit current currentFrame hn hIndexed hOwner hSuccess hLimit hCap hCurrent)
    intro cont hPost
    cases cont with
    | Break depth final resultFrame =>
      cases depth with
      | zero =>
        obtain ⟨hResult, hDecrease⟩ := hPost
        have hResultValues := hResult.values
        have hTrim : { resultFrame with values := [] } = resultFrame := by rw [← hResultValues]
        simpa only [List.take_zero, List.drop_zero, List.nil_append, hValues, hTrim]
          using And.intro hResult hDecrease
      | succ depth =>
        cases depth with
        | zero =>
          obtain ⟨heap, hStore, hDone⟩ := hPost
          have hResultValues := (show retryInvariant initial initialHeap n time source.root
            (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit final resultFrame
            from ⟨heap, hStore, Or.inr hDone⟩).values
          have hTrim : { resultFrame with values := [] } = resultFrame := by rw [← hResultValues]
          simpa only [List.take_zero, List.drop_zero, List.nil_append, hEntryValues, hTrim]
            using hNext final heap resultFrame hStore hDone
        | succ depth => exact False.elim hPost
    | _ => exact False.elim hPost

#print axioms retry_loop_spec

end Project.EulerRiemann.Execution
