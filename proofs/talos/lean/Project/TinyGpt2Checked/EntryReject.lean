import Project.TinyGpt2Checked.EntryCode

namespace Project.TinyGpt2Checked.Spec
open Wasm Project.ProofKit Project.Runtime UInt64Array Memory Project.F64Clip.Spec

def checkedResult (initial : Store Unit) (pointer base : UInt64)
    (input output : Array UInt64) : AssertionF Unit := fun final frame =>
  ∃ root : UInt64, frame.get 26 = some (.i64 root) ∧ frame.values = [] ∧
    UInt64Array.At final root output ∧ UInt64Array.At final pointer input ∧
    final.mem.pages = initial.mem.pages ∧
    (∀ address : Nat, address < base.toNat → final.mem.bytes address = initial.mem.bytes address) ∧
    final = { initial with mem := final.mem, globals := final.globals }

theorem token_reject_spec (env : HostEnv Unit) (initial : Store Unit)
    (pointer bound t0 t1 t2 t3 base : UInt64) (weights : Array UInt64)
    (allocations retains releases frees : UInt64)
    (hGlobals : initial.globals.globals =
      [.i64 base, .i64 0, .i64 allocations, .i64 retains, .i64 releases, .i64 frees])
    (hInput : At initial pointer weights)
    (hBefore : pointer.toNat+8*(weights.size+1) ≤ base.toNat)
    (hFit : base.toNat+56 ≤ 4294967296)
    (hMemory : base.toNat+56 ≤ initial.mem.pages*65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap module 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final frame, checkedResult initial pointer base weights #[] final frame →
      wp module rest Q final frame env) :
    wp module (tokenReject ++ rest) Q initial (checkedFrame pointer bound t0 t1 t2 t3) env := by
  have hFit' : base.toNat+48+8*(0+1) ≤ 4294967296 := by omega
  have hMemory' : base.toNat+48+8*(0+1) ≤ initial.mem.pages*65536 := by omega
  have hWords := clip_allocation_words base 0 hFit'
  have hAllocatedPages := clip_allocate_pages initial base 0 allocations hFit' hMemory'
  have hInitializedPages := clip_initialize_pages initial base 0 allocations hFit' hMemory'
  have hInitializedInput := clip_initialize_input initial base pointer 0 weights allocations
    hInput hBefore hFit' hMemory'
  have hOutput := PrefixAt.complete
    (clip_initialize_prefix initial base #[] allocations hFit' hMemory')
  have hNeeded : FixedArrayBump.requiredPages base 8 ≤ initial.mem.pages := by
    unfold FixedArrayBump.requiredPages
    change (base.toNat+48+8-1)/65536+1 ≤ initial.mem.pages
    omega
  rw [token_reject_shape]
  simp only [List.append_assoc]
  apply FixedArrayCapacity.constantProgram_spec 0 1 31 module env initial _
    rfl (by change 6 ≤ 31; decide) (by change 31 < 37; decide)
  change wp module _ Q initial
    (FixedArraySearch.frame (checkedParams pointer bound t0 t1 t2 t3)
      (List.replicate 25 (.i64 0)) [] 8 0 0 0 0 0) env
  apply FixedArrayAllocateNone.program_spec module env initial
    (checkedParams pointer bound t0 t1 t2 t3) (List.replicate 25 (.i64 0))
    [] 31 rfl (FixedArrayReuse.program 31 1) base 8 1 0 0 0 0 0 allocations []
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
    wp_fixed_frame [FixedArraySearch.frame, checkedParams, List.replicate,
      List.cons_append, List.nil_append]
    apply FixedArrayResult.lengthStore_spec module env
      (clipAllocate initial base 0 allocations) _ (base+48) 0 27 rfl rfl
    · rw [Memory.toUInt32_toNat, hWords.2, Nat.mod_eq_of_lt (by omega), hAllocatedPages]
      omega
    · wp_fixed_frame [List.cons_append, List.nil_append]
      apply hNext
      exact ⟨base+48, rfl, rfl, hOutput, hInitializedInput, hInitializedPages,
        clip_initialize_below initial base 0 allocations hFit',
        clip_initialize_store initial base 0 allocations hFit' hMemory'⟩

#print axioms token_reject_spec
end Project.TinyGpt2Checked.Spec
