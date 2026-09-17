import Project.F64Clip.PrepareCode

namespace Project.F64Clip.Spec
open Wasm Project.ProofKit Project.Runtime UInt64Array Memory

theorem reject_program_spec (env : HostEnv Unit) (initial : Store Unit)
    (count bound ptr base : UInt64) (w : Array UInt64)
    (allocations retains releases frees : UInt64)
    (hGlobals : initial.globals.globals =
      [.i64 base, .i64 0, .i64 allocations, .i64 retains, .i64 releases, .i64 frees])
    (hInput : At initial ptr w)
    (hBefore : ptr.toNat+8*(w.size+1) ≤ base.toNat)
    (hFit : base.toNat+56 ≤ 4294967296)
    (hMemory : base.toNat+56 ≤ initial.mem.pages*65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap Project.F64Clip.module 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final frame, prepareResult initial ptr base allocations w #[] final frame →
      wp Project.F64Clip.module rest Q final frame env) :
    wp Project.F64Clip.module (rejectProgram ++ rest) Q initial (prepareFrame count bound ptr 0) env := by
  have hFit' : base.toNat+48+8*(0+1) ≤ 4294967296 := by omega
  have hMemory' : base.toNat+48+8*(0+1) ≤ initial.mem.pages*65536 := by omega
  have hWords := clip_allocation_words base 0 hFit'
  have hAllocatedPages := clip_allocate_pages initial base 0 allocations hFit' hMemory'
  have hInitializedPages := clip_initialize_pages initial base 0 allocations hFit' hMemory'
  have hInitializedInput := clip_initialize_input initial base ptr 0 w allocations
    hInput hBefore hFit' hMemory'
  have hOutput := PrefixAt.complete
    (clip_initialize_prefix initial base #[] allocations hFit' hMemory')
  have hNeeded : FixedArrayBump.requiredPages base 8 ≤ initial.mem.pages := by
    unfold FixedArrayBump.requiredPages
    change (base.toNat+48+8-1)/65536+1 ≤ initial.mem.pages
    omega
  unfold rejectProgram
  simp only [List.append_assoc]
  apply FixedArrayCapacity.constantProgram_spec 0 1 19 Project.F64Clip.module env initial _
    rfl (by change 3 ≤ 19; decide) (by change 19 < 27; decide)
  change wp Project.F64Clip.module _ Q initial
    (rejectAllocationFrame count bound ptr 8 0 0 0 0 0) env
  apply FixedArrayAllocateNone.program_spec Project.F64Clip.module env initial
    [.i64 count, .i64 bound, .i64 ptr]
    (rejectSaved count bound ptr)
    [.i64 0, .i64 0] 19 rfl (FixedArrayReuse.program 19 1) base 8 1 0 0 0 0 0 allocations []
  · simp [hGlobals]
  · simp [hGlobals, freeHead]
  · simp [hGlobals]
  · exact .nil
  · rfl
  · change base.toNat+48+8 ≤ 4294967296
    omega
  · exact hPages
  · rfl
  · exact hNeeded.trans hCap
  · intro previous
    wp_fixed_frame [FixedArraySearch.frame, rejectSaved, List.cons_append, List.nil_append]
    apply FixedArrayResult.lengthStore_spec Project.F64Clip.module env
      (clipAllocate initial base 0 allocations) _ (base+48) 0 15 rfl rfl
    · rw [Memory.toUInt32_toNat, hWords.2, Nat.mod_eq_of_lt (by omega), hAllocatedPages]
      omega
    · wp_fixed_frame [FixedArrayResult.finishProgram, List.cons_append, List.nil_append]
      apply hNext
      exact ⟨rfl, rfl, hOutput, hInitializedInput, hInitializedPages, WritesRange.refl ..⟩

#print axioms reject_program_spec
end Project.F64Clip.Spec
