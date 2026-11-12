import Verified.Wasi.ReadFunction
import Verified.Wasi.Wrappers

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem wp_call_returned_at {World : Type} {m : Module} {env : HostEnv World}
    {initial final : Store World} {s : Locals} {index fuel : Nat} {values : List Value}
    {rest : Program} {Q : Assertion World}
    (hRun : run fuel m index initial s.values env = .Success values final)
    (hNext : wp m rest Q final { s with values } env) :
    wp m (.call index :: rest) Q initial s env := by
  refine wp_call_at (Post := fun current out => current = final ∧ out = values) ?_ ?_
  · refine ⟨fuel, fun next hFuel => ⟨values, final, ?_, rfl, rfl⟩⟩
    rw [run_fuel_mono hFuel (by rw [hRun]; intro h; cases h)]
    exact hRun
  · rintro current out ⟨rfl, rfl⟩
    exact hNext

theorem wp_call_trapped_at {World : Type} {m : Module} {env : HostEnv World}
    {initial final : Store World} {s : Locals} {index fuel : Nat} {message : String}
    {rest : Program} {Q : Assertion World}
    (hRun : run fuel m index initial s.values env = .Trap final message)
    (hTrap : Q (.Trap final message)) :
    wp m (.call index :: rest) Q initial s env := by
  unfold wp
  refine ⟨fuel + 1, fun next hFuel => ?_⟩
  obtain ⟨next, rfl⟩ : ∃ previous, next = previous + 1 := ⟨next - 1, by omega⟩
  rw [exec_call_cons,
    run_fuel_mono (by omega : fuel ≤ next) (by rw [hRun]; intro h; cases h), hRun]
  exact hTrap

theorem wp_read_helper_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {capacity : UInt64}
    {typeIdx : Nat} {aborts : Bool} {s : Locals} {values : List Value}
    {rest : Program} {Q : Assertion (Observed World)}
    (hFunction : target.funcs[source.funcs.length]? = some (readFunctionWith calls typeIdx))
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hRoom : capacity.toNat < 4294967296 → capacity ≠ 0 → aborts = false →
      heap.Room (PureTransport.erase initial) source (allocSize capacity))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (root length : UInt64)
      (result : LeanExe.Wasi.ReadResult) (trace : List Event),
      Exec (observedHost host) (readSome capacity)
        initial.host trace (.returned result) final.host →
      Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap' (PureTransport.erase final) root length result.bytes →
      heap'.top.toNat ≤ heap.top.toNat + readCost capacity →
      wp target rest Q final
        { s with values := .i64 length :: .i64 root :: .i64 result.errno :: values } env)
    (hHostTrap : ∀ (heap' : Heap) (final : Store (Observed World)) (root : UInt64)
      (message : String) (trace : List Event),
      Exec (observedHost host) (readSome capacity)
        initial.host trace (.trapped message) final.host →
      Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      heap'.top.toNat ≤ heap.top.toNat + readCost capacity → Q (.Trap final message))
    (hResource : aborts = true → ∀ final : Store (Observed World),
      final.host = initial.host → Q (.Trap final "unreachable")) :
    wp target (.call (Wrappers.readIndexWith calls source) :: rest) Q initial
      { s with values := .i64 capacity :: values } env := by
  obtain ⟨bound, hBound⟩ := readFunction_run_with (calls := calls) runtime layout profile hImports sourceHost
    hFunction hHost hHeap hCap hRoom
  have hImport : target.imports[Wrappers.readIndexWith calls source]? = none :=
    List.getElem?_eq_none (by
      rw [hImports, ABI.importsWith_length]
      simp only [Wrappers.readIndexWith, Module.extraIndexWith]
      omega)
  have hLookup : target.funcs[Wrappers.readIndexWith calls source - target.imports.length]? =
      some (readFunctionWith calls typeIdx) := by
    simpa only [Wrappers.readIndexWith, Module.extraIndexWith, hImports, ABI.importsWith_length,
      Nat.add_zero, Nat.add_sub_cancel_left] using hFunction
  have hAt : ReadRun host heap initial capacity aborts
      (run bound target (Wrappers.readIndexWith calls source) initial [.i64 capacity] env) := by
    simpa only [Wrappers.readIndexWith, Module.extraIndexWith, Nat.add_zero] using hBound bound le_rfl
  generalize hRun : run bound target (Wrappers.readIndexWith calls source) initial
    [.i64 capacity] env = outcome at hAt
  cases hAt with
  | returned heap' final root length result trace hExec hStep hRep hTop =>
      have hCall := run_append_of_success hImport hLookup (by rfl) hRun values
      exact wp_call_returned_at hCall
        (hNext heap' final root length result trace hExec hStep hRep hTop)
  | hostTrap heap' final root message trace hExec hStep hTop =>
      have hCall := run_append_of_trap hImport hLookup (by rfl) hRun values
      exact wp_call_trapped_at hCall
        (hHostTrap heap' final root message trace hExec hStep hTop)
  | resource hAllowed hWorld =>
      have hCall := run_append_of_trap hImport hLookup (by rfl) hRun values
      exact wp_call_trapped_at hCall (hResource hAllowed _ hWorld)

theorem wp_read_helper {World : Type} {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {capacity : UInt64}
    {typeIdx : Nat} {aborts : Bool} {s : Locals} {values : List Value}
    {rest : Program} {Q : Assertion (Observed World)}
    (hFunction : target.funcs[source.funcs.length]? = some (readFunction typeIdx))
    (hHost : env.Satisfies target (hostSpec host))
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hRoom : capacity.toNat < 4294967296 → capacity ≠ 0 → aborts = false →
      heap.Room (PureTransport.erase initial) source (allocSize capacity))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (root length : UInt64)
      (result : LeanExe.Wasi.ReadResult) (trace : List Event),
      Exec (observedHost host) (readSome capacity)
        initial.host trace (.returned result) final.host →
      Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap' (PureTransport.erase final) root length result.bytes →
      heap'.top.toNat ≤ heap.top.toNat + readCost capacity →
      wp target rest Q final
        { s with values := .i64 length :: .i64 root :: .i64 result.errno :: values } env)
    (hHostTrap : ∀ (heap' : Heap) (final : Store (Observed World)) (root : UInt64)
      (message : String) (trace : List Event),
      Exec (observedHost host) (readSome capacity)
        initial.host trace (.trapped message) final.host →
      Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      heap'.top.toNat ≤ heap.top.toNat + readCost capacity → Q (.Trap final message))
    (hResource : aborts = true → ∀ final : Store (Observed World),
      final.host = initial.host → Q (.Trap final "unreachable")) :
    wp target (.call (Wrappers.readIndex source) :: rest) Q initial
      { s with values := .i64 capacity :: values } env := by
  layout_instance wp_read_helper_with

theorem wp_read_helper_with_budget_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {capacity : UInt64}
    {typeIdx : Nat} {s : Locals} {values : List Value}
    {rest : Program} {Q : Assertion (Observed World)}
    (hFunction : target.funcs[source.funcs.length]? = some (readFunctionWith calls typeIdx))
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hBudget : heap.Within (PureTransport.erase initial) source (readCost capacity))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (root length : UInt64)
      (result : LeanExe.Wasi.ReadResult) (trace : List Event),
      Exec (observedHost host) (readSome capacity)
        initial.host trace (.returned result) final.host →
      Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap' (PureTransport.erase final) root length result.bytes →
      heap'.top.toNat ≤ heap.top.toNat + readCost capacity →
      wp target rest Q final
        { s with values := .i64 length :: .i64 root :: .i64 result.errno :: values } env)
    (hHostTrap : ∀ (heap' : Heap) (final : Store (Observed World)) (root : UInt64)
      (message : String) (trace : List Event),
      Exec (observedHost host) (readSome capacity)
        initial.host trace (.trapped message) final.host →
      Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      heap'.top.toNat ≤ heap.top.toNat + readCost capacity → Q (.Trap final message)) :
    wp target (.call (Wrappers.readIndexWith calls source) :: rest) Q initial
      { s with values := .i64 capacity :: values } env :=
  wp_read_helper_with (calls := calls) (aborts := false) runtime layout profile hImports sourceHost hFunction hHost hHeap hCap
    (fun hSize hNonzero _ => read_room_of_budget hSize hNonzero hCap hBudget)
    hNext hHostTrap (fun h => Bool.noConfusion h)

theorem wp_read_helper_with_budget {World : Type} {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {capacity : UInt64}
    {typeIdx : Nat} {s : Locals} {values : List Value}
    {rest : Program} {Q : Assertion (Observed World)}
    (hFunction : target.funcs[source.funcs.length]? = some (readFunction typeIdx))
    (hHost : env.Satisfies target (hostSpec host))
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hBudget : heap.Within (PureTransport.erase initial) source (readCost capacity))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (root length : UInt64)
      (result : LeanExe.Wasi.ReadResult) (trace : List Event),
      Exec (observedHost host) (readSome capacity)
        initial.host trace (.returned result) final.host →
      Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap' (PureTransport.erase final) root length result.bytes →
      heap'.top.toNat ≤ heap.top.toNat + readCost capacity →
      wp target rest Q final
        { s with values := .i64 length :: .i64 root :: .i64 result.errno :: values } env)
    (hHostTrap : ∀ (heap' : Heap) (final : Store (Observed World)) (root : UInt64)
      (message : String) (trace : List Event),
      Exec (observedHost host) (readSome capacity)
        initial.host trace (.trapped message) final.host →
      Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      heap'.top.toNat ≤ heap.top.toNat + readCost capacity → Q (.Trap final message)) :
    wp target (.call (Wrappers.readIndex source) :: rest) Q initial
      { s with values := .i64 capacity :: values } env := by
  layout_instance wp_read_helper_with_budget_with

end Verified.Wasi
