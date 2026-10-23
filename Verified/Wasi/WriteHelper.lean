import Verified.Wasi.CallWrappers

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

def writeLocals (root length : UInt64) : Locals :=
  { params := [.i64 root, .i64 length], locals := [.i32 0], values := [] }

inductive WriteRun {World : Type} (host : Host World)
    (initial : Store (Observed World)) (output : Output) (bytes : LeanExe.Bytes) :
    Result (Observed World) → Prop where
  | returned (final : Store (Observed World)) (result : LeanExe.Wasi.WriteResult)
      (trace : List Event)
      (execution : Exec (observedHost host) (.write output bytes .pure)
        initial.host trace (.returned result) final.host)
      (frame : GuestFrame initial final [ABI.scratch]) :
      WriteRun host initial output bytes (.Success [.i64 result.count, .i64 result.errno] final)
  | hostTrap (final : Store (Observed World)) (message : String) (trace : List Event)
      (execution : Exec (observedHost host) (.write output bytes .pure)
        initial.host trace (.trapped message) final.host)
      (frame : GuestFrame initial final [ABI.scratch]) :
      WriteRun host initial output bytes (.Trap final message)

theorem writeFunction_run {World : Type} {m : Module} {host : Host World}
    {env : HostEnv (Observed World)} {initial : Store (Observed World)}
    {output : Output} {root length : UInt64} {bytes : LeanExe.Bytes} {index typeIdx : Nat}
    (hImports : m.imports = ABI.imports)
    (hFunction : m.funcs[index]? = some (writeFunction output typeIdx))
    (hHost : env.Satisfies m (hostSpec host))
    (hBytes : Bytes.At initial.mem root bytes) (hRoot : root.toNat < 4294967296)
    (hLength : length.toNat = bytes.data.size) (hSize : bytes.data.size < 4294967296)
    (hApart : root.toNat + bytes.data.size ≤ 0 ∨ 16 ≤ root.toNat)
    (hMemory : 16 ≤ initial.mem.pages * 65536) :
    ∃ bound, ∀ fuel ≥ bound,
      WriteRun host initial output bytes
        (run fuel m (3 + index) initial [.i64 length, .i64 root] env) := by
  let Q : Assertion (Observed World) := fun continuation =>
    match continuation with
    | .Fallthrough final locals =>
        WriteRun host initial output bytes (.Success (locals.values.take 2) final)
    | .Trap final message => WriteRun host initial output bytes (.Trap final message)
    | _ => False
  have hBody : wp m (writeCode output 0 1 2 ++ []) Q initial (writeLocals root length) env := by
    refine wp_write output hImports hHost hBytes hRoot hLength hSize hApart hMemory
      (by rfl) (by rfl) (by change 2 ≤ 2; omega) (by change 2 < 3; omega) ?_ ?_
    · intro final errno committed hWrite hFrame
      simp only [wp_nil, Q]
      change WriteRun host initial output bytes
        (.Success [.i64 (if errno = 0 then committed else 0), .i64 errno] final)
      exact .returned final (writeResult errno committed)
        [.write output bytes (.returned errno committed)]
        (.write_return hWrite (.pure final.host _)) hFrame
    · intro final message committed hWrite hFrame
      exact .hostTrap final message [.write output bytes (.trapped message committed)]
        (.write_trap hWrite) hFrame
  simp only [List.append_nil] at hBody
  unfold wp at hBody
  obtain ⟨bound, hBound⟩ := hBody
  have hImport : m.imports[3 + index]? = none :=
    List.getElem?_eq_none (by rw [hImports, ABI.imports_length]; omega)
  refine ⟨bound, fun fuel hFuel => ?_⟩
  have hContinuation := hBound fuel hFuel
  rw [run_eq hImport]
  simp only [hImports, ABI.imports_length,
    show 3 + index - 3 = index by omega, hFunction]
  have hArgs : ([Value.i64 length, Value.i64 root].take
      (writeFunction output typeIdx).numParams).reverse =
      [Value.i64 root, Value.i64 length] := rfl
  have hDrop : [Value.i64 length, Value.i64 root].drop
      (writeFunction output typeIdx).numParams = [] := rfl
  have hResults : (writeFunction output typeIdx).results.length = 2 := rfl
  have hCode : (writeFunction output typeIdx).body = writeCode output 0 1 2 := rfl
  have hLocals : (writeFunction output typeIdx).toLocals
      [Value.i64 root, Value.i64 length] = writeLocals root length := rfl
  simp only [hArgs, hDrop, hResults, hCode, hLocals, List.append_nil]
  cases hExec : exec fuel m initial (writeLocals root length)
      (writeCode output 0 1 2) env with
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

theorem write_buffer_abi {World : Type} {initial : Store World} {heap : Heap}
    {root length : UInt64} {bytes : LeanExe.Bytes}
    (hHeap : heap.At (PureTransport.erase initial))
    (hRep : Bytes.Rep heap (PureTransport.erase initial) root length bytes) :
    Bytes.At initial.mem root bytes ∧ root.toNat < 4294967296 ∧
      (root.toNat + bytes.data.size ≤ 0 ∨ 16 ≤ root.toNat) ∧
      16 ≤ initial.mem.pages * 65536 := by
  refine ⟨hRep.toAt hHeap, ?_, ?_, ?_⟩
  · rcases hRep.buffer with ⟨rfl, _⟩ | hBuffer
    · decide
    · have := hBuffer.object.address
      omega
  · rcases hRep.buffer with ⟨rfl, hEmpty⟩ | hBuffer
    · exact Or.inl (by simp [hEmpty])
    · have := hBuffer.object.base
      exact Or.inr (by omega)
  · have := hHeap.base
    have := hHeap.top
    change 16 ≤ (PureTransport.erase initial).mem.pages * 65536
    omega

theorem wp_write_helper {World : Type} {source target : Module} {host : Host World}
    {env : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {root length : UInt64} {bytes : LeanExe.Bytes} {output : Output} {typeIdx : Nat}
    {s : Locals} {values : List Value} {rest : Program} {Q : Assertion (Observed World)}
    (hImports : target.imports = ABI.imports)
    (hFunction : target.funcs[match output with
      | .stdout => source.funcs.length + 1
      | .stderr => source.funcs.length + 2]? = some (writeFunction output typeIdx))
    (hHost : env.Satisfies target (hostSpec host))
    (hHeap : heap.At (PureTransport.erase initial))
    (hRep : Bytes.Rep heap (PureTransport.erase initial) root length bytes)
    (hNext : ∀ (final : Store (Observed World)) (result : LeanExe.Wasi.WriteResult)
      (trace : List Event),
      Exec (observedHost host) (.write output bytes .pure)
        initial.host trace (.returned result) final.host →
      GuestFrame initial final [ABI.scratch] →
      Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.scratch)
        heap (PureTransport.erase final) [] →
      Bytes.Rep heap (PureTransport.erase final) root length bytes →
      wp target rest Q final { s with values := .i64 result.count :: .i64 result.errno :: values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host) (.write output bytes .pure)
        initial.host trace (.trapped message) final.host →
      GuestFrame initial final [ABI.scratch] →
      Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.scratch)
        heap (PureTransport.erase final) [] →
      Bytes.Rep heap (PureTransport.erase final) root length bytes → Q (.Trap final message)) :
    wp target (.call (match output with
      | .stdout => Wrappers.stdoutIndex source
      | .stderr => Wrappers.stderrIndex source) :: rest) Q initial
      { s with values := .i64 length :: .i64 root :: values } env := by
  let index := match output with
    | .stdout => source.funcs.length + 1
    | .stderr => source.funcs.length + 2
  have hIndex : 3 + index = (match output with
      | .stdout => Wrappers.stdoutIndex source
      | .stderr => Wrappers.stderrIndex source) := by
    cases output <;>
      simp only [index, Wrappers.stdoutIndex, Wrappers.stderrIndex, Module.extraIndex] <;>
      omega
  rw [← hIndex]
  obtain ⟨hBytes, hRoot, hApart, hMemory⟩ := write_buffer_abi hHeap hRep
  obtain ⟨bound, hBound⟩ := writeFunction_run (index := index) hImports hFunction hHost hBytes hRoot
    hRep.length_eq hRep.size_lt hApart hMemory
  have hImport : target.imports[3 + index]? = none :=
    List.getElem?_eq_none (by rw [hImports, ABI.imports_length]; omega)
  have hLookup : target.funcs[3 + index - target.imports.length]? =
      some (writeFunction output typeIdx) := by
    simpa only [hImports, ABI.imports_length, Nat.add_sub_cancel_left] using hFunction
  have hAt := hBound bound le_rfl
  generalize hRun : run bound target (3 + index) initial
    [.i64 length, .i64 root] env = outcome at hAt
  cases hAt with
  | returned final result trace hExec hFrame =>
      have hCall := run_append_of_success hImport hLookup (by rfl) hRun values
      exact wp_call_returned_at hCall
        (hNext final result trace hExec hFrame (hFrame.scratchStep hHeap)
          (hFrame.scratchRep hHeap hRep))
  | hostTrap final message trace hExec hFrame =>
      have hCall := run_append_of_trap hImport hLookup (by rfl) hRun values
      exact wp_call_trapped_at hCall
        (hTrap final message trace hExec hFrame (hFrame.scratchStep hHeap)
          (hFrame.scratchRep hHeap hRep))

end Verified.Wasi
