import Project.EulerReconstructed.RetryTotalValid
import Project.EulerReconstructed.RetryTotalInvalid

namespace Project.EulerReconstructed.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayCapacity
open Project.EulerRiemann
open Project.EulerRiemann.Execution
open Project.EulerRiemann.Control (Attempt)

theorem retry_total_iteration_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (source : FreeNode) (grid : Array Project.EulerRiemann.Traversal.Cell) (n : Nat) (trials time alpha : UInt64)
    (expected : Attempt) (spare limit pageLimit : Nat) (store : Store Unit) (frame : Locals)
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Project.EulerRiemann.Traversal.Indexed n grid)
    (hOwner : initialHeap.Owns initial source grid) (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hPageLimit : pageLimit ≤ 65536) (hLimitPages : limit ≤ pageLimit * 65536)
    (hInv : retryTotalInvariant initial initialHeap n trials time alpha source.root
      (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit pageLimit store frame) :
    wp module retryLoop
      (retryTotalIterationPost initial initialHeap n trials time alpha source.root
        (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit pageLimit (retryMeasure frame))
      store frame env := by
  obtain ⟨heap, hStore, hPages, hState⟩ := hInv
  rcases hState with ⟨hActive, hScratch⟩ | hDone
  · obtain ⟨fuel, dt, hFrame, hSame, hReserved⟩ := hActive
    by_cases hFuel : fuel = 0
    · subst fuel
      rw [← List.take_append_drop 7 retryLoop]
      have hShape := AnnotationMatches.function_125_while_loop_0_guard_eq
      change some (retryLoop.take 7) = some (FuelGuard.program 0 13) at hShape
      rw [Option.some.inj hShape]
      apply FuelGuard.program_spec 0 13 module env store frame 0 0 hFrame.values
        (by simp [Locals.get, hFrame.params])
        (by simpa [Locals.get, hFrame.params, hFrame.locals, boolWord] using hFrame.done)
      exact ⟨heap, hStore, hPages, Or.inr ⟨dt, hFrame, hSame, hReserved, hScratch⟩⟩
    · have hParams := hFrame.params
      have hLocals := hFrame.locals
      have hValues := hFrame.values
      rcases frame with ⟨params, locals, values⟩
      dsimp only at hParams hLocals hValues ⊢
      subst params
      subst values
      let frame : Locals := ⟨[.i64 fuel, .i64 (UInt64.ofNat n), .i64 trials, .i64 time,
        .i64 dt, .i64 alpha, .i64 source.root, .i64 source.root], locals, []⟩
      rw [retry_loop_parts, List.append_assoc]
      apply retry_active_guard_spec env store frame fuel n trials time dt alpha source.root 0 0 hFrame hFuel
      apply retry_validity_spec env store frame fuel n trials time dt alpha source.root 0 0 false hFrame
      cases hValid : Time.validAdvance time dt with
      | true =>
        dsimp only [frame]
        reconstructed_retry_total_peel
        refine retry_total_valid_spec env initial initialHeap source grid n fuel trials time dt alpha expected
          spare limit pageLimit store heap frame hn hIndexed hOwner hLimit hCap hStore hPages hPageLimit
          hLimitPages hFrame hScratch hSame
          hReserved hFuel hValid _ [] ?_
        intro final resultFrame hFinal hDecrease
        have hEmpty : ({ resultFrame with values := [] } : Locals) = resultFrame :=
          Frame.ext _ _ rfl rfl hFinal.values.symm
        simpa [wp_simp, retryTotalIterationPost, BlockLoop.stepPost, hEmpty, frame] using
          And.intro hFinal hDecrease
      | false =>
        dsimp only [frame]
        reconstructed_retry_total_peel
        refine retry_total_invalid_spec env initial initialHeap n fuel trials time dt alpha source.root grid expected
          spare limit pageLimit store heap frame hLimit hCap hStore hPages hLimitPages hFrame hScratch hSame hReserved hFuel hValid _ [] ?_
        intro final resultFrame hFinal hDecrease
        have hEmpty : ({ resultFrame with values := [] } : Locals) = resultFrame :=
          Frame.ext _ _ rfl rfl hFinal.values.symm
        simpa [wp_simp, retryTotalIterationPost, BlockLoop.stepPost, hEmpty, frame] using
          And.intro hFinal hDecrease
  · obtain ⟨result, hFrame, hResult, hReserved, hCapacity, hSeparated⟩ := hDone
    rw [← List.take_append_drop 7 retryLoop]
    apply retry_returned_guard_spec env store frame expected.status expected.dt result.root hFrame
    exact ⟨heap, hStore, hPages, Or.inl ⟨result, hFrame, hResult, hReserved, hCapacity, hSeparated⟩⟩

#print axioms retry_total_iteration_spec

end Project.EulerReconstructed.Execution
