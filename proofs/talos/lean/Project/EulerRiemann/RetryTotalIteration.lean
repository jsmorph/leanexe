import Project.EulerRiemann.RetryTotalValid
import Project.EulerRiemann.RetryTotalInvalid

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayCapacity

theorem retry_total_iteration_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n : Nat) (time : UInt64)
    (expected : Control.Attempt) (spare limit pageLimit : Nat) (store : Store Unit) (frame : Locals)
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hOwner : initialHeap.Owns initial source grid) (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hPageLimit : pageLimit ≤ 65536) (hLimitPages : limit ≤ pageLimit * 65536)
    (hInv : retryTotalInvariant initial initialHeap n time source.root
      (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit pageLimit store frame) :
    wp module retryLoop
      (retryTotalIterationPost initial initialHeap n time source.root
        (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit pageLimit (retryMeasure frame))
      store frame env := by
  obtain ⟨heap, hStore, hPages, hState⟩ := hInv
  rcases hState with ⟨hActive, hScratch⟩ | hDone
  · obtain ⟨fuel, dt, hFrame, hSame, hReserved⟩ := hActive
    by_cases hFuel : fuel = 0
    · subst fuel
      rw [← List.take_append_drop 7 retryLoop]
      have hShape := AnnotationMatches.function_81_while_loop_0_guard_eq
      change some (retryLoop.take 7) = some (FuelGuard.program 0 11) at hShape
      rw [Option.some.inj hShape]
      apply FuelGuard.program_spec 0 11 module env store frame 0 0 hFrame.values
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
      let frame : Locals := ⟨[.i64 fuel, .i64 (UInt64.ofNat n), .i64 time,
        .i64 dt, .i64 source.root, .i64 source.root], locals, []⟩
      rw [retry_loop_parts, List.append_assoc]
      simp only [retry_invalid_shape]
      apply retry_active_guard_spec env store frame fuel n time dt source.root 0 0 hFrame hFuel
      apply retry_validity_spec env store frame fuel n time dt source.root 0 0 false hFrame
      cases hValid : Time.validAdvance time dt with
      | true =>
        dsimp only [frame]
        retry_total_peel
        refine retry_total_valid_spec env initial initialHeap source grid n fuel time dt expected
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
        retry_total_peel
        refine retry_total_invalid_spec env initial initialHeap n fuel time dt source.root grid expected
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

end Project.EulerRiemann.Execution
