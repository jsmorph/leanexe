import Project.LebU32.RecyclingInvariant

namespace Project.LebU32.Recycling
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution Spec

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem loop_spec (env : HostEnv Unit) (initial store : Store Unit) (base : UInt64)
    (target : List UInt8) (frame : Locals) (hTarget : target.length ≤ 5)
    (hInv : loopInvariant initial base target store frame)
    (hFit32 : base.toNat + 560 < 4294967296)
    (hFit : base.toNat + 560 ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result heap node bytes fuel,
      Arena initial base bytes.size heap final → Buffer base heap final node bytes →
      target = bytes.data.toList → Finished result fuel node.root bytes.size →
      wp «module» rest Q final result env) :
    wp «module» ([.block 0 0 [.loop 0 0 loopBody]] ++ rest) Q store frame env := by
  have hFrameValues : frame.values = [] := by
    rcases hInv with ⟨_, _, _, _, _, hState⟩
    rcases hState with ⟨_, _, _, _, _, hRunning⟩ | ⟨_, _, hFinished⟩
    · exact hRunning.values
    · exact hFinished.values
  simp only [List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := loopInvariant initial base target) (μ := measure)
  · exact hInv
  · rintro current currentFrame ⟨heap, node, bytes, hArena, hBuffer, hState⟩
    rcases hState with ⟨fuel, v, hFuel, hSum, hSplit, hRunning⟩ | ⟨fuel, hSplit, hFinished⟩
    · have hSize := running_size_bound hTarget hFuel hSplit
      have hFuel64 : fuel < UInt64.size := by change fuel < 18446744073709551616; omega
      have hFuelNat := UInt64.toNat_ofNat_of_lt' hFuel64
      have hFuelNe : UInt64.ofNat fuel ≠ 0 := by
        intro hZero
        have := congrArg UInt64.toNat hZero
        simp only [hFuelNat, UInt64.toNat_zero] at this
        omega
      have hCurrentValues := hRunning.values
      have hCurrentMeasure := measure_running current hRunning
      rw [active_head_shape]
      apply active_head_spec env current currentFrame (UInt64.ofNat fuel) v node.root bytes.size hRunning hFuelNe
      intro prepared hPrepared hLow hRest
      apply dispatch_spec env current prepared v hPrepared.values hRest
      · intro hZero
        have hFinalSplit := split_final target bytes fuel v hFuel hSplit hZero
        apply positive_spec env initial current base heap node bytes prepared (UInt64.ofNat fuel) v
          hArena hBuffer hPrepared hLow hSize hFit32 hFit hPages (rest := [])
        intro final result hFinished hArena' hBuffer'
        have hResultFrame : ({ result with values := [] } : Locals) = result :=
          Frame.ext _ _ rfl rfl hFinished.values.symm
        simp only [wp_nil, branchPost, List.take_zero, List.drop_zero, hCurrentValues, List.nil_append, hResultFrame]
        refine ⟨?_, ?_⟩
        · refine ⟨heap.allocate 8, allocatedNode heap.top 8 heap.nodes, bytes.push (v % 128).toUInt8, ?_, hBuffer', Or.inr ?_⟩
          · simpa only [ByteArray.size_push] using hArena'
          · exact ⟨UInt64.ofNat fuel, hFinalSplit, by simpa only [ByteArray.size_push] using hFinished⟩
        · rw [measure_finished final hFinished, hCurrentMeasure]
          omega
      · intro hNonzero
        have hNextSplit := split_cont target bytes fuel v hFuel hSplit hNonzero
        have hSub : UInt64.ofNat fuel - 1 = UInt64.ofNat (fuel - 1) := by
          simpa using (UInt64.ofNat_sub (show 1 ≤ fuel by omega)).symm
        apply negative_spec env initial current base heap node bytes prepared (UInt64.ofNat fuel) v
          hArena hBuffer hPrepared hLow hRest hSize hFit32 hFit hPages (rest := [])
        intro final result nextHeap hContinued hArena' hBuffer'
        rw [hSub] at hContinued
        have hResultFrame : ({ result with values := [] } : Locals) = result :=
          Frame.ext _ _ rfl rfl hContinued.values.symm
        simp only [wp_nil, branchPost, List.take_zero, List.drop_zero, hCurrentValues, List.nil_append, hResultFrame]
        refine ⟨?_, ?_⟩
        · refine ⟨nextHeap, allocatedNode heap.top 8 heap.nodes, bytes.push (v % 128 + 128).toUInt8,
            ?_, hBuffer', Or.inl ?_⟩
          · simpa only [ByteArray.size_push] using hArena'
          · refine ⟨fuel - 1, v / 128, by omega, ?_, hNextSplit, ?_⟩
            · rw [ByteArray.size_push]; omega
            · simpa only [ByteArray.size_push] using hContinued
        · rw [measure_running final hContinued, hCurrentMeasure, hFuelNat,
            UInt64.toNat_ofNat_of_lt' (show fuel - 1 < UInt64.size by omega)]
          omega
    · apply finished_body_spec env current currentFrame fuel node.root bytes.size hFinished
      simpa only [wp_nil, List.take_zero, List.drop_zero, List.nil_append,
        hFrameValues, hFinished.values, show ({ currentFrame with values := [] } : Locals) = currentFrame from
          Frame.ext _ _ rfl rfl hFinished.values.symm] using
        hNext current currentFrame heap node bytes fuel hArena hBuffer hSplit hFinished

#print axioms loop_spec
end Project.LebU32.Recycling
