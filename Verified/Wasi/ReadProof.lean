import Verified.Wasi.ReadOverflow
import Verified.Wasi.ReadCodeFacts
import Verified.Wasi.ReadInvoke
import Verified.Wasi.ReadCost

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem wp_read {World : Type} {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {capacity : UInt64}
    {values : List Value} {rest : Program} {Q : Assertion (Observed World)} {aborts : Bool}
    (hHost : env.Satisfies target (hostSpec host))
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hRoom : capacity.toNat < 4294967296 → capacity ≠ 0 → aborts = false →
      heap.Room (PureTransport.erase initial) source (allocSize capacity))
    (hResource : aborts = true → ∀ final : Store (Observed World),
      final.host = initial.host → Q (.Trap final "unreachable"))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (root length : UInt64)
      (result : LeanExe.Wasi.ReadResult) (trace : List Event),
      Exec (observedHost host) (readSome capacity) initial.host trace (.returned result) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap' (PureTransport.erase final) root length result.bytes →
      heap'.top.toNat ≤ heap.top.toNat + readCost capacity →
      wp target rest Q final
        (readLocals capacity root result.errno length
          (.i64 length :: .i64 root :: .i64 result.errno :: values)) env)
    (hTrap : ∀ (final : Store (Observed World)) (heap' : Heap) (root : UInt64)
      (message : String) (trace : List Event),
      Exec (observedHost host) (readSome capacity) initial.host trace (.trapped message) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      heap'.top.toNat ≤ heap.top.toNat + readCost capacity → Q (.Trap final message)) :
    wp target (readCode 0 1 2 3 ++ rest) Q initial (readLocals capacity 0 0 0 values) env := by
  by_cases hOverflow : 4294967296 ≤ capacity.toNat
  · refine wp_read_overflow hOverflow ?_
    refine hNext heap initial 0 0 ⟨61, LeanExe.Bytes.empty⟩ []
      (.read_reject hOverflow (.pure initial.host _)) ?_ (Bytes.Rep.empty _ _) ?_
    · simpa only [Bytes.regions, ite_true] using
        Step.refl hHeap (fun region => regionsDisjoint region ABI.scratch)
    · rw [readCost_overflow hOverflow]
      omega
  · have hSmall : capacity.toNat < 4294967296 := by omega
    have hNotLarge : ¬((4294967296 : UInt64) ≤ capacity) := by
      rw [UInt64.le_iff_toNat_le]
      change ¬4294967296 ≤ capacity.toNat
      omega
    rw [readCode_parts]
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, readLocals_capacity,
      readLocals_stack, wp_constI64_cons, wp_geUI64_cons, ge_iff_le,
      ite_eq_right hNotLarge, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide : ¬((0 : UInt32) ≠ 0))]
    simp only [readValidCode, List.append_assoc]
    refine wp_read_allocate runtime layout profile hImports sourceHost hHeap
      (Nat.le_of_lt hSmall) hCap (fun hNonzero hFalse => hRoom hSmall hNonzero hFalse)
      ?_ ?_ ?_
    · intro hAbort final hWorld
      exact hResource hAbort final hWorld
    · intro hZero
      have hReady : ReadReady heap (PureTransport.erase initial) 0 capacity :=
        Or.inl ⟨rfl, hZero⟩
      have hBefore : Step heap (PureTransport.erase initial)
          (fun region => regionsDisjoint region ABI.scratch)
          heap (PureTransport.erase initial) (Bytes.regions (PureTransport.erase initial) 0) := by
        simpa only [Bytes.regions, ite_true] using
          Step.refl hHeap (fun region => regionsDisjoint region ABI.scratch)
      change wp target (readCallCode 1 0 ++ readResultCode ++ []) _ initial
        (readLocals capacity 0 0 0 values) env
      refine wp_read_invoke (budget := readCost capacity)
        runtime layout profile hImports sourceHost hHost hSmall hReady
        hBefore rfl (by omega) ?_ ?_
      · intro heap' final root length result trace hExec hStep hRep hTop
        simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero,
          readLocals_values, readLocals_stack]
        exact wp_read_return (hNext heap' final root length result trace hExec hStep hRep hTop)
      · intro final heap' message trace hExec hStep hTop
        exact hTrap final heap' 0 message trace hExec hStep hTop
    · intro hNonzero before hFits hStore hWorld
      obtain ⟨hAllocate, hBuffer, hCapacity, hTop⟩ :=
        read_allocation_buffer hHeap (Nat.le_of_lt hSmall) hFits hStore
      let root := FixedArrayAllocate.root heap.top (allocSize capacity) heap.free
      have hReady : ReadReady (heap.allocate (allocSize capacity))
          (PureTransport.erase before) root capacity := Or.inr ⟨_, hBuffer, hCapacity⟩
      have hBefore : Step heap (PureTransport.erase initial)
          (fun region => regionsDisjoint region ABI.scratch)
          (heap.allocate (allocSize capacity)) (PureTransport.erase before)
          (Bytes.regions (PureTransport.erase before) root) := by
        have hRoot : root ≠ 0 := hBuffer.nonzero
        rw [Bytes.regions, ite_eq_right hRoot]
        exact hAllocate.mono
          (keep' := fun region => regionsDisjoint region ABI.scratch)
          (fresh' := [block (PureTransport.erase before) root])
          (fun _ _ => True.intro) (fun _ h => h)
      have hBudget : (heap.allocate (allocSize capacity)).top.toNat ≤
          heap.top.toNat + readCost capacity := by
        rw [readCost_positive hSmall hNonzero]
        exact hTop
      change wp target (readCallCode 1 0 ++ readResultCode ++ []) _ before
        (readLocals capacity root 0 0 values) env
      refine wp_read_invoke (budget := readCost capacity)
        runtime layout profile hImports sourceHost hHost hSmall hReady
        hBefore hWorld hBudget ?_ ?_
      · intro heap' final root' length result trace hExec hStep hRep hTop
        simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero,
          readLocals_values, readLocals_stack]
        exact wp_read_return (hNext heap' final root' length result trace hExec hStep hRep hTop)
      · intro final heap' message trace hExec hStep hTop
        exact hTrap final heap' root message trace hExec hStep hTop

end Verified.Wasi
