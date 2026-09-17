import Project.TinyGpt2Checked.EntryReject

namespace Project.TinyGpt2Checked.Spec
open Wasm Project.ProofKit Project.Runtime Project.TinyGpt2 Project.F64Clip.Spec
open ArrayPushLayout

set_option maxRecDepth 8192

theorem layout_size_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env module 7 initial []
      (fun final values => final = initial ∧ values = [.i64 2488]) := by
  refine TerminatesWith.of_wp_entry_for (f := func7Def) rfl ?_ (by decide)
  change wp module func7 _ initial (func7Def.toLocals []) env
  unfold func7
  wp_fixed_frame [func7Def]
  exact ⟨trivial, rfl⟩

def checkedPreparedOutput (weights : Array UInt64) (bound t0 t1 t2 t3 : UInt64) : Array UInt64 :=
  let clipped := Project.F64Clip.prepare 2488 bound weights
  if clipped.size = 2488 then infer clipped t0 t1 t2 t3 else clipped

theorem token_accept_spec (env : HostEnv Unit) (initial : Store Unit)
    (pointer bound t0 t1 t2 t3 base : UInt64) (weights : Array UInt64)
    (allocations retains releases frees : UInt64)
    (hGlobals : initial.globals.globals =
      [.i64 base, .i64 0, .i64 allocations, .i64 retains, .i64 releases, .i64 frees])
    (hInput : UInt64Array.At initial pointer weights)
    (hBefore : pointer.toNat+8*(weights.size+1) ≤ base.toNat)
    (hFit : base.toNat+48+8*(weights.size+1)+277560 < 4294967296)
    (hMemory : base.toNat+48+8*(weights.size+1)+277560 ≤ initial.mem.pages*65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap module 0)
    (ht0 : t0.toNat < 256) (ht1 : t1.toNat < 256)
    (ht2 : t2.toNat < 256) (ht3 : t3.toNat < 256)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final frame,
      checkedResult initial pointer base weights (checkedPreparedOutput weights bound t0 t1 t2 t3)
        final frame → wp module rest Q final frame env) :
    wp module (tokenAccept ++ rest) Q initial (checkedFrame pointer bound t0 t1 t2 t3) env := by
  let clipped := Project.F64Clip.prepare 2488 bound weights
  have hSizeLe : clipped.size ≤ weights.size := by
    simp [clipped, Project.F64Clip.prepare]; split <;> simp
  have hClipFit : base.toNat+48+8*(weights.size+1) ≤ 4294967296 := by omega
  have hClipMemory : base.toNat+48+8*(weights.size+1) ≤ initial.mem.pages*65536 := by omega
  have hClippedFit : base.toNat+48+8*(clipped.size+1) ≤ 4294967296 := by omega
  have hWords := clip_allocation_words base clipped.size hClippedFit
  let start := base.toNat+48+8*(clipped.size+1)
  have hStartFit : top start 256 < 4294967296 := by
    rw [inference_output_reservation]; dsimp only [start]; omega
  have hStartMemory : top start 256 ≤ initial.mem.pages*65536 := by
    rw [inference_output_reservation]; dsimp only [start]; omega
  have hTopWord : base+48+clipCapacity clipped.size = UInt64.ofNat start := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, hWords.2, hWords.1]
    rw [UInt64.toNat_ofNat_of_lt' (by change start < 18446744073709551616; dsimp [start]; omega)]
    exact Nat.mod_eq_of_lt (by change start < 18446744073709551616; dsimp [start]; omega)
  change wp module (tokenAccept ++ rest) Q initial (checkedFrame pointer bound t0 t1 t2 t3) env
  unfold tokenAccept
  simp only [List.cons_append, List.nil_append]
  refine wp_call_tw (layout_size_exact env initial) ?_
  rintro checked values ⟨hChecked, rfl⟩
  subst checked
  wp_fixed_frame [checkedFrame, checkedParams, func85Def]
  refine wp_call_tw (prepare_state env initial 2488 bound 0 pointer base weights
    allocations retains releases frees hGlobals hInput hBefore hClipFit hClipMemory hPages hCap) ?_
  rintro prepared values ⟨rfl, hClipped, hInput', hPages', hGlobals', hHeader, hBytes', hStore'⟩
  change UInt64Array.At prepared (base+48) clipped at hClipped
  change prepared.globals.globals =
    [.i64 (base+48+clipCapacity clipped.size), .i64 0, .i64 (allocations+1),
      .i64 retains, .i64 releases, .i64 frees] at hGlobals'
  wp_fixed_frame
  refine wp_call_tw (layout_size_exact env prepared) ?_
  rintro checked values ⟨hChecked, rfl⟩
  subst checked
  wp_fixed_frame
  simp only [show (2 : Nat)^32 = 4294967296 from rfl, UInt32.toNat_zero,
    Nat.add_zero, UInt32.add_zero, hClipped.pointerAddress_eq, hClipped.lengthRead,
    ite_eq_right (Nat.not_lt.mpr hClipped.lengthBound)]
  have hSizeWord : UInt64.ofNat clipped.size = 2488 ↔ clipped.size = 2488 :=
    hClipped.encodedSize_eq (by decide)
  by_cases hs : clipped.size = 2488
  · have hWord : UInt64.ofNat clipped.size = 2488 := hSizeWord.mpr hs
    repeat first
      | wp_fixed_frame [hWord]
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp)
    refine wp_call_tw (infer_exact env prepared (base+48) (base+48) clipped t0 t1 t2 t3 start
      (allocations+1) retains releases frees hClipped (by omega) ht0 ht1 ht2 ht3
      (by rw [hTopWord] at hGlobals'; exact hGlobals')
      (by rw [hWords.2])
      hStartFit (by rw [hPages']; exact hStartMemory)
      (by rw [hPages']; exact hPages)
      (by rw [hPages', hStore']; exact hCap)) ?_
    rintro final values ⟨rfl, hOutput, _, hFinalPages, hFinalBytes, hFinalStore⟩
    wp_fixed_frame
    apply hNext
    refine ⟨(node start 256).root, rfl, rfl, ?_, ?_, hFinalPages.trans hPages', ?_, ?_⟩
    · change UInt64Array.At final (node start 256).root
        (if clipped.size = 2488 then infer clipped t0 t1 t2 t3 else clipped)
      simpa only [hs, ite_true] using hOutput
    · apply hInput'.frame hFinalPages.ge
      intro address _ hAddress
      exact hFinalBytes address (by dsimp [start]; omega)
    · intro address hAddress
      exact (hFinalBytes address (by dsimp [start]; omega)).trans (hBytes' address hAddress)
    · rw [hFinalStore, hStore']
  · have hWord : UInt64.ofNat clipped.size ≠ 2488 := fun h => hs (hSizeWord.mp h)
    repeat first
      | wp_fixed_frame [hWord]
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp)
    apply hNext
    refine ⟨base+48, rfl, rfl, ?_, hInput', hPages', hBytes', hStore'⟩
    change UInt64Array.At prepared (base+48)
      (if clipped.size = 2488 then infer clipped t0 t1 t2 t3 else clipped)
    simpa only [hs, ite_false] using hClipped

#print axioms token_accept_spec
end Project.TinyGpt2Checked.Spec
