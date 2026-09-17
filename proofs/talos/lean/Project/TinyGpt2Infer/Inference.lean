import Project.TinyGpt2Infer.InitialSetup
import Project.TinyGpt2Infer.OutputExit

namespace Project.TinyGpt2Infer.Spec
open Wasm Project.TinyGpt2 Project.Runtime Project.ProofKit ArrayPushLayout

theorem infer_export : module.findExport "infer" = some 75 := rfl

theorem inference_output_reservation (start : Nat) : top start 256 = start + 277560 := by
  unfold top root base capacity
  ring

theorem inference_initial_memory : top 24056 256 = 301616 ∧ top 24056 256 ≤ 16 * 65536 := by decide

theorem inference_stages : func75 = func75.take 52 ++ (func75.drop 52).take 15 ++
    (func75.drop 67).take 22 ++ [.block 0 0 [.loop 0 0 outputBody]] ++ func75.drop 90 := by
  have hPrefix : func75.take 89 =
      func75.take 52 ++ (func75.drop 52).take 15 ++ (func75.drop 67).take 22 := by
    rw [show 89 = 67 + 22 from rfl, List.take_add,
      show 67 = 52 + 15 from rfl, List.take_add]
  calc
    func75 = func75.take 89 ++ [.block 0 0 [.loop 0 0 outputBody]] ++ func75.drop 90 :=
      inference_loop_shape
    _ = _ := by rw [hPrefix]

theorem infer_exact (env : HostEnv Unit) (initial : Store Unit)
    (pointer : UInt64) (weights : Array UInt64) (t0 t1 t2 t3 : UInt64) (start : Nat)
    (allocations retains releases frees : UInt64)
    (hWeights : UInt64Array.At initial pointer weights) (hSize : 2488 ≤ weights.size)
    (ht0 : t0.toNat < 256) (ht1 : t1.toNat < 256)
    (ht2 : t2.toNat < 256) (ht3 : t3.toNat < 256)
    (hGlobals : initial.globals.globals =
      [.i64 (UInt64.ofNat start), .i64 0, .i64 allocations, .i64 retains, .i64 releases, .i64 frees])
    (hWeightsBefore : pointer.toNat + 8 * (weights.size + 1) ≤ start)
    (hFit : top start 256 < 4294967296)
    (hMemory : top start 256 ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap module 0) :
    TerminatesWith env module 75 initial [.i64 t3, .i64 t2, .i64 t1, .i64 t0, .i64 pointer]
      (fun final values => values = [.i64 (node start 256).root] ∧
        UInt64Array.At final (node start 256).root (infer weights t0 t1 t2 t3) ∧
        UInt64Array.At final pointer weights ∧
        final.mem.pages = initial.mem.pages ∧
        (∀ address : Nat, address < start → final.mem.bytes address = initial.mem.bytes address) ∧
        final = { initial with mem := final.mem, globals := final.globals }) := by
  have hZeroTop := top_mono start (show 0 ≤ 256 by decide)
  have hZeroFit := hZeroTop.trans_lt hFit
  have hZeroMemory := hZeroTop.trans hMemory
  let prepared := OutputMemory.prepare initial start 0 allocations
  have hPreparedPages : prepared.mem.pages = initial.mem.pages :=
    OutputMemory.prepare_pages initial start 0 allocations hZeroFit hZeroMemory
  have hPreparedBytes (address : Nat) (hAddress : address < start) :
      prepared.mem.bytes address = initial.mem.bytes address := by
    apply OutputMemory.prepare_below initial start 0 allocations hZeroFit address
    simpa only [base, Nat.mul_zero, Nat.add_zero] using hAddress
  have hPreparedState := OutputMemory.prepare_initial_state initial start allocations retains releases frees
    hGlobals hZeroFit hZeroMemory
  have hPreparedWeights : UInt64Array.At prepared pointer weights := by
    apply hWeights.frame hPreparedPages.ge
    intro address _ hAddress
    exact hPreparedBytes address (hAddress.trans_le hWeightsBefore)
  have hPreparedCap : prepared.memoryCap module 0 = initial.memoryCap module 0 := by
    dsimp only [prepared]
    rw [OutputMemory.prepare_store]
    rfl
  refine TerminatesWith.of_wp_entry_for (f := func75Def) rfl ?_ (by decide)
  change wp module func75 _ initial (func75Def.toLocals (inferenceParams pointer t0 t1 t2 t3)) env
  rw [inference_stages]
  simp only [List.append_assoc]
  apply inference_prefix_spec env initial pointer weights t0 t1 t2 t3 hWeights hSize ht0 ht1 ht2 ht3
  apply initial_allocation_spec env initial pointer t0 t1 t2 t3 (hidden weights t0 t1 t2 t3 3) start
    allocations retains releases frees hGlobals hZeroFit hZeroMemory hPages hCap
  intro previous
  apply initial_setup_spec env initial pointer t0 t1 t2 t3 (hidden weights t0 t1 t2 t3 3) start
    allocations previous hZeroFit hZeroMemory
  apply output_loop_spec env prepared _ pointer (node start 0).root weights
    (hidden weights t0 t1 t2 t3 3) start 0
    (initialReadyFrame_locals pointer t0 t1 t2 t3 (hidden weights t0 t1 t2 t3 3) start previous)
    hPreparedState hPreparedState.emptyArray hPreparedWeights hSize hWeightsBefore (by decide) hFit
    (by rw [hPreparedPages]; exact hMemory)
    (by rw [hPreparedPages]; exact hPages)
    (by rw [hPreparedPages, hPreparedCap]; exact hCap)
  intro current currentFrame hProgress
  obtain ⟨allocations', retains', releases', frees', hCurrentGlobals⟩ := hProgress.heap.globals
  have hEmpty := node_toNat start 0 hZeroFit
  have hRoot := root_ge start 0
  apply output_exit_spec env current currentFrame (node start 0).root (node start 0).capacity
    (freeHead (freed start 256)) releases' frees' (node start 256).root
    hProgress.locals.params hProgress.locals.locals hProgress.locals.values
    hProgress.locals.current hProgress.locals.output hProgress.locals.empty
    (by rw [hEmpty.1]; omega) hProgress.heap.emptyHeader hProgress.heap.emptyArray
    (by simp [hCurrentGlobals, OutputMemory.globals])
    (by simp [hCurrentGlobals, OutputMemory.globals])
    (by simp [hCurrentGlobals, OutputMemory.globals])
  let final := FixedArrayRelease.store current (node start 0).root
    (freeHead (freed start 256)) releases' frees'
  have hExit := output_exit_memory current start releases' frees'
    (logitPrefix weights (hidden weights t0 t1 t2 t3 3) 256) hFit hProgress.output
  have hFinalPages : final.mem.pages = initial.mem.pages :=
    hExit.2.1.trans (hProgress.pages.trans hPreparedPages)
  have hFinalBytes (address : Nat) (hAddress : address < start) :
      final.mem.bytes address = initial.mem.bytes address :=
    (hExit.2.2.1 address hAddress).trans
      ((hProgress.bytes address hAddress).trans (hPreparedBytes address hAddress))
  change [Value.i64 (node start 256).root] = [Value.i64 (node start 256).root] ∧
    UInt64Array.At final (node start 256).root (infer weights t0 t1 t2 t3) ∧
    UInt64Array.At final pointer weights ∧ final.mem.pages = initial.mem.pages ∧
    (∀ address : Nat, address < start → final.mem.bytes address = initial.mem.bytes address) ∧
    final = { initial with mem := final.mem, globals := final.globals }
  refine ⟨rfl, ?_, ?_, hFinalPages, hFinalBytes, ?_⟩
  · simpa only [infer_eq_logitPrefix] using hExit.1
  · apply hWeights.frame hFinalPages.ge
    intro address _ hAddress
    exact hFinalBytes address (hAddress.trans_le hWeightsBefore)
  · calc
      final = { current with mem := final.mem, globals := final.globals } := hExit.2.2.2
      _ = { prepared with mem := final.mem, globals := final.globals } := by rw [hProgress.store]
      _ = { initial with mem := final.mem, globals := final.globals } := by
        dsimp only [prepared]
        rw [OutputMemory.prepare_store]

#print axioms infer_exact
end Project.TinyGpt2Infer.Spec
