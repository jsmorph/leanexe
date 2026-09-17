import Project.TinyGpt2Checked.ClipPrepareCode

namespace Project.TinyGpt2Checked.Spec
open Wasm Project.ProofKit Project.Runtime UInt64Array Memory Project.F64Clip Project.F64Clip.Spec

theorem accept_program_spec (env : HostEnv Unit) (initial : Store Unit)
    (count bound owner ptr base : UInt64) (w : Array UInt64)
    (allocations retains releases frees : UInt64)
    (hGlobals : initial.globals.globals =
      [.i64 base, .i64 0, .i64 allocations, .i64 retains, .i64 releases, .i64 frees])
    (hInput : At initial ptr w)
    (hBefore : ptr.toNat+8*(w.size+1) ≤ base.toNat)
    (hFit : base.toNat+48+8*(w.size+1) ≤ 4294967296)
    (hMemory : base.toNat+48+8*(w.size+1) ≤ initial.mem.pages*65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap Project.TinyGpt2Checked.module 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final frame, prepareResult initial ptr base allocations w (w.map (clip bound)) final frame →
      wp Project.TinyGpt2Checked.module rest Q final frame env) :
    wp Project.TinyGpt2Checked.module (acceptProgram ++ rest) Q initial (prepareFrame count bound owner ptr 1) env := by
  have hWords := clip_allocation_words base w.size hFit
  have hAllocatedPages := clip_allocate_pages initial base w.size allocations hFit hMemory
  have hInitializedPages := clip_initialize_pages initial base w.size allocations hFit hMemory
  have hInitializedInput := clip_initialize_input initial base ptr w.size w allocations
    hInput hBefore hFit hMemory
  have hOutputBefore : ptr.toNat+8*(w.size+1) ≤ (base+48).toNat := by rw [hWords.2]; omega
  have hPrefix : PrefixAt (clipInitialize initial base w.size allocations) (base+48) (w.map (clip bound)) 0 := by
    simpa using clip_initialize_prefix initial base (w.map (clip bound)) allocations
      (by simpa using hFit) (by simpa using hMemory)
  have hNeeded : FixedArrayBump.requiredPages base (clipCapacity w.size) ≤ initial.mem.pages := by
    unfold FixedArrayBump.requiredPages
    rw [hWords.1]
    omega
  unfold acceptProgram
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  wp_fixed_frame [prepareFrame]
  simp [hInput.pointerAddress_eq, hInput.lengthRead]
  rw [ite_eq_right (Nat.not_lt.mpr hInput.generatedLengthBound)]
  apply FixedArrayCapacity.localProgram_spec 18 (UInt64.ofNat w.size) 1 23
    Project.TinyGpt2Checked.module env initial _ rfl rfl (by change 4 ≤ 23; decide)
    (by change 23 < 29; decide)
  rw [clip_capacity_normalized base w.size hFit]
  change wp Project.TinyGpt2Checked.module _ Q initial
    (acceptAllocationFrame count bound owner ptr w.size (clipCapacity w.size) 0 0 0 0 0) env
  apply FixedArrayAllocateNone.program_spec Project.TinyGpt2Checked.module env initial
    [.i64 count, .i64 bound, .i64 owner, .i64 ptr] (mapFrame count bound owner ptr 0 w.size 0 0 0 0 []).locals
    [] 23 rfl (FixedArrayReuse.program 23 1) base (clipCapacity w.size) 1 0 0 0 0 0 allocations []
  · simp [hGlobals]
  · simp [hGlobals, freeHead]
  · simp [hGlobals]
  · exact .nil
  · rfl
  · rw [hWords.1]
    exact hFit
  · exact hPages
  · rfl
  · exact hNeeded.trans hCap
  · intro previous
    wp_fixed_frame [FixedArraySearch.frame, mapFrame]
    apply FixedArrayResult.lengthStoreLocal_spec Project.TinyGpt2Checked.module env
      (clipAllocate initial base w.size allocations) _ (base+48) (UInt64.ofNat w.size) 19 18 rfl rfl
    · rw [Memory.toUInt32_toNat, hWords.2, Nat.mod_eq_of_lt (by omega), hAllocatedPages]
      omega
    · wp_fixed_frame
      change wp Project.TinyGpt2Checked.module ([.block 0 0 [.loop 0 0 mapBody]] ++ _) Q
        (clipInitialize initial base w.size allocations)
        (mapFrame count bound owner ptr (base+48) w.size 0 0 0 0
          [.i64 (clipCapacity w.size), .i64 previous, .i64 0, .i64 (base+48+clipCapacity w.size),
           .i64 ((base+48+clipCapacity w.size-1)/65536+1), .i64 (base+48)]) env
      apply map_program_spec env _ count bound owner ptr (base+48) w _ hInitializedInput hOutputBefore hPrefix
      intro final last argument result hOutput hWrites
      wp_fixed_frame [mapFrame, finishOwnedProgram, List.append]
      apply hNext
      exact ⟨rfl, rfl, rfl, hOutput, hInitializedInput.writesRange hWrites (Or.inl hOutputBefore),
        hWrites.2.1.trans hInitializedPages, by simpa using hWrites⟩

#print axioms accept_program_spec
end Project.TinyGpt2Checked.Spec
