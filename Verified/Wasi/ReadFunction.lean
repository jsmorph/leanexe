import Verified.Wasi.ReadProof

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

inductive ReadRun {World : Type} (host : Host World) (heap : Heap)
    (initial : Store (Observed World)) (capacity : UInt64) (aborts : Bool) :
    Result (Observed World) → Prop where
  | returned (heap' : Heap) (final : Store (Observed World)) (root length : UInt64)
      (result : LeanExe.Wasi.ReadResult) (trace : List Event)
      (execution : Exec (observedHost host) (readSome capacity)
        initial.host trace (.returned result) final.host)
      (step : Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root))
      (bytes : Bytes.Rep heap' (PureTransport.erase final) root length result.bytes)
      (top : heap'.top.toNat ≤ heap.top.toNat + readCost capacity) :
      ReadRun host heap initial capacity aborts
        (.Success [.i64 length, .i64 root, .i64 result.errno] final)
  | hostTrap (heap' : Heap) (final : Store (Observed World)) (root : UInt64)
      (message : String) (trace : List Event)
      (execution : Exec (observedHost host) (readSome capacity)
        initial.host trace (.trapped message) final.host)
      (step : Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root))
      (top : heap'.top.toNat ≤ heap.top.toNat + readCost capacity) :
      ReadRun host heap initial capacity aborts (.Trap final message)
  | resource {final : Store (Observed World)} (allowed : aborts = true)
      (world : final.host = initial.host) :
      ReadRun host heap initial capacity aborts (.Trap final "unreachable")

theorem readFunction_run {World : Type} {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {capacity : UInt64}
    {index typeIdx : Nat} {aborts : Bool}
    (hFunction : target.funcs[index]? = some (readFunction typeIdx))
    (hHost : env.Satisfies target (hostSpec host))
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hRoom : capacity.toNat < 4294967296 → capacity ≠ 0 → aborts = false →
      heap.Room (PureTransport.erase initial) source (allocSize capacity)) :
    ∃ bound, ∀ fuel ≥ bound,
      ReadRun host heap initial capacity aborts
        (run fuel target (3 + index) initial [.i64 capacity] env) := by
  let Q : Assertion (Observed World) := fun continuation =>
    match continuation with
    | .Fallthrough final locals =>
        ReadRun host heap initial capacity aborts (.Success (locals.values.take 3) final)
    | .Trap final message => ReadRun host heap initial capacity aborts (.Trap final message)
    | _ => False
  have hBody : wp target (readCode 0 1 2 3 ++ []) Q initial
      (readLocals capacity 0 0 0 []) env := by
    refine wp_read runtime layout profile hImports sourceHost hHost hHeap hCap hRoom ?_ ?_ ?_
    · intro hAllowed final hWorld
      exact ReadRun.resource hAllowed hWorld
    · intro heap' final root length result trace hExec hStep hRep hTop
      simpa only [wp_nil, Q, readLocals_stack, List.take_succ_cons, List.take_zero] using
        ReadRun.returned heap' final root length result trace hExec hStep hRep hTop
    · intro final heap' root message trace hExec hStep hTop
      exact ReadRun.hostTrap heap' final root message trace hExec hStep hTop
  simp only [List.append_nil] at hBody
  unfold wp at hBody
  obtain ⟨bound, hBound⟩ := hBody
  have hImport : target.imports[3 + index]? = none :=
    List.getElem?_eq_none (by rw [hImports, ABI.imports_length]; omega)
  refine ⟨bound, fun fuel hFuel => ?_⟩
  have hContinuation := hBound fuel hFuel
  rw [run_eq hImport]
  simp only [hImports, ABI.imports_length,
    show 3 + index - 3 = index by omega, hFunction]
  have hArgs : ([Value.i64 capacity].take (readFunction typeIdx).numParams).reverse =
      [Value.i64 capacity] := rfl
  have hDrop : [Value.i64 capacity].drop (readFunction typeIdx).numParams = [] := rfl
  have hResults : (readFunction typeIdx).results.length = 3 := rfl
  have hCode : (readFunction typeIdx).body = readCode 0 1 2 3 := rfl
  simp only [hArgs, hDrop, hResults, hCode, readFunction_locals, List.append_nil]
  cases hExec : exec fuel target initial (readLocals capacity 0 0 0 [])
      (readCode 0 1 2 3) env with
  | Fallthrough final locals =>
      simpa only [Q, hExec] using hContinuation
  | Trap final message =>
      simpa only [Q, hExec] using hContinuation
  | Break label final locals =>
      exact False.elim (by simpa only [Q, hExec] using hContinuation)
  | Return final values =>
      exact False.elim (by simpa only [Q, hExec] using hContinuation)
  | Invalid message =>
      exact False.elim (by simpa only [Q, hExec] using hContinuation)
  | OutOfFuel =>
      exact False.elim (by simpa only [Q, hExec] using hContinuation)
  | ReturnCall entry final values =>
      exact False.elim (by simpa only [Q, hExec] using hContinuation)
  | Throwing tag values final locals =>
      exact False.elim (by simpa only [Q, hExec] using hContinuation)

theorem readFunction_run_with_budget {World : Type} {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {capacity : UInt64} {index typeIdx : Nat}
    (hFunction : target.funcs[index]? = some (readFunction typeIdx))
    (hHost : env.Satisfies target (hostSpec host))
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hBudget : heap.Within (PureTransport.erase initial) source (readCost capacity)) :
    ∃ bound, ∀ fuel ≥ bound,
      ReadRun host heap initial capacity false
        (run fuel target (3 + index) initial [.i64 capacity] env) :=
  readFunction_run runtime layout profile hImports sourceHost hFunction hHost hHeap hCap
    (fun hSize hNonzero _ => read_room_of_budget hSize hNonzero hCap hBudget)

end Verified.Wasi
