import Verified.Wasi.ProcessEntryProofs

namespace Verified.Wasi

open Wasm LeanExe.Wasi

def ProcessEntryRunResult {World σ : Type} (host : Host World)
    (begin : Action (ProcessStep σ)) (process : Process σ) (world : World) : Result World → Prop
  | .Trap final message => ProcessEntryResult host begin process world (.Trap final message)
  | _ => False

theorem process_entry_run {World σ : Type} {target : Wasm.Module} {host : Host World}
    {begin : Action (ProcessStep σ)} {process : Process σ} {world : World}
    {function : Wasm.Function} {index fuel : Nat}
    {initial : Store World} {targetHost : HostEnv World}
    (imports : target.imports = ABI.imports)
    (lookup : target.funcs[index]? = some function)
    (body : pwp target function.body (ProcessEntryResult host begin process world)
      initial (function.toLocals []) targetHost)
    (completed : run fuel target (3 + index) initial [] targetHost ≠ .OutOfFuel) :
    ProcessEntryRunResult host begin process world
      (run fuel target (3 + index) initial [] targetHost) := by
  have noImport : target.imports[3 + index]? = none :=
    List.getElem?_eq_none (by rw [imports, ABI.imports_length]; omega)
  rw [run_eq noImport] at completed ⊢
  simp only [imports, ABI.imports_length, show 3 + index - 3 = index by omega,
    lookup, List.take_nil, List.drop_nil, List.reverse_nil] at completed ⊢
  cases executed : exec fuel target initial (function.toLocals []) function.body targetHost with
  | OutOfFuel => exact False.elim (completed (by simp only [executed]))
  | Trap final message =>
      have classification := body fuel (by simp [executed])
      simpa only [executed, ProcessEntryRunResult] using classification
  | _ =>
      have classification := body fuel (by simp [executed])
      rw [executed] at classification
      cases classification

end Verified.Wasi
