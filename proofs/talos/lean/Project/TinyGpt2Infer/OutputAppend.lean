import Project.TinyGpt2Infer.OutputPrepare

namespace Project.TinyGpt2Infer.OutputMemory
open Wasm Project.Runtime Project.Clob Project.ProofKit ArrayPushLayout

theorem append_result (initial middle : Store Unit) (start count : Nat)
    (allocations retains releases frees : UInt64) (output : Array UInt64)
    (hBuffers : Buffers start count initial)
    (hGlobals : initial.globals.globals = globals start count allocations retains releases frees)
    (hFit : top start (count + 1) < 4294967296)
    (hMemory : top start (count + 1) ≤ initial.mem.pages * 65536)
    (hWrites : Memory.WritesRange (prepare initial start (count + 1) allocations) middle
      (node start (count + 1)).root.toNat (top start (count + 1)))
    (hOutput : UInt64Array.At middle (node start (count + 1)).root output) :
    let final := finish middle start count releases frees
    State start (count + 1) final ∧
    UInt64Array.At final (node start (count + 1)).root output ∧
    final.mem.pages = initial.mem.pages ∧
    (∀ address : Nat, address < start → final.mem.bytes address = initial.mem.bytes address) ∧
    final = { initial with mem := final.mem, globals := final.globals } := by
  have hOldTop := top_mono start (show count ≤ count + 1 by omega)
  have hNew := node_toNat start (count + 1) hFit
  have hNewRoot := root_ge start (count + 1)
  have hNextBase := top_eq_next_base start count
  have hMiddleBuffers : Buffers start count middle := by
    apply (prepare_buffers allocations hBuffers hFit hMemory).frame (hOldTop.trans_lt hFit)
      hWrites.2.1.ge
    intro address hAddress
    apply hWrites.2.2 address (Or.inl ?_)
    rw [hNew.1]
    simp only [root, ← hNextBase]
    omega
  have hMiddleHeader : FreshFixedArrayAt middle (node start (count + 1)).root
      (node start (count + 1)).capacity 1 := by
    apply FreshFixedArrayAt.frame (base := (node start (count + 1)).root)
      (by rw [hNew.1]; exact (Nat.le_add_right _ _).trans_lt hFit)
      (by rw [hNew.1]; omega) (Nat.le_refl _)
      (fun address hAddress => hWrites.2.2 address (Or.inl hAddress))
      (prepare_header initial start (count + 1) allocations hFit)
  have hMiddlePages : middle.mem.pages = initial.mem.pages :=
    hWrites.2.1.trans (prepare_pages initial start (count + 1) allocations hFit hMemory)
  have hMiddleGlobals : middle.globals.globals =
      [.i64 (UInt64.ofNat (top start (count + 1))), .i64 (freeHead (freed start count)),
        .i64 (allocations + 1), .i64 retains, .i64 releases, .i64 frees] := by
    rw [hWrites.1]
    exact allocate_globals initial start (count + 1) allocations (freeHead (freed start count))
      retains releases frees (by simpa only [globals, hNextBase] using hGlobals)
  refine ⟨finish_state hMiddleBuffers hFit (by simpa only [hMiddlePages] using hMemory)
    hMiddleHeader (allocations + 1) retains releases frees hMiddleGlobals,
    finish_array hFit hOutput releases frees, ?_, ?_, ?_⟩
  · exact (finish_pages middle start count releases frees).trans hMiddlePages
  · intro address hAddress
    rw [finish_below middle start count releases frees (hOldTop.trans_lt hFit) address hAddress,
      hWrites.2.2 address (Or.inl (by rw [hNew.1]; omega))]
    apply prepare_below initial start (count + 1) allocations hFit address
    unfold base
    omega
  · let final := finish middle start count releases frees
    change final = { initial with mem := final.mem, globals := final.globals }
    calc
      final = { middle with mem := final.mem, globals := final.globals } := finish_store ..
      _ = { (prepare initial start (count + 1) allocations) with
          mem := final.mem, globals := final.globals } := by rw [hWrites.1]
      _ = { initial with mem := final.mem, globals := final.globals } := by rw [prepare_store]

#print axioms append_result
end Project.TinyGpt2Infer.OutputMemory
