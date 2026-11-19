import Verified.Wasi.CallWrappers
import Verified.Wasi.SysWindow

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

def writeLocals (root size start count : UInt64) : Locals :=
  { params := [.i64 root, .i64 size, .i64 start, .i64 count], locals := [.i64 0, .i64 0, .i32 0],
    values := [] }

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

/-- The window of a represented buffer meets the premises of the write wrapper: its bytes lie in
memory at its address, below `2^32`, as many as its length, and at or above the scratch bytes
unless it is empty at address 0. -/
theorem write_window_abi {World : Type} {initial : Store World} {heap : Heap}
    {root size : UInt64} {buffer : LeanExe.Bytes} {start count address length : UInt64}
    (hHeap : heap.At (PureTransport.erase initial))
    (hRep : Bytes.Rep heap (PureTransport.erase initial) root size buffer)
    (hWindow : WindowAt heap (PureTransport.erase initial) root size buffer start count
      address length) :
    Bytes.At initial.mem address (buffer.range start count) ∧ address.toNat < 4294967296 ∧
      length.toNat = (buffer.range start count).data.size ∧
      (buffer.range start count).data.size < 4294967296 ∧
      (address.toNat + (buffer.range start count).data.size ≤ 0 ∨ 16 ≤ address.toNat) ∧
      16 ≤ initial.mem.pages * 65536 := by
  have hSize : (buffer.range start count).data.size = length.toNat := by
    rw [LeanExe.Bytes.range_size, hWindow.length_toNat]
  have hFits := hWindow.fits
  refine ⟨bytes_at_window (hRep.toAt hHeap) hWindow.address_toNat, by omega, hSize.symm,
    by omega, ?_, ?_⟩
  · rcases hWindow.separate with high | ⟨zero, address⟩
    · exact Or.inr high
    · left
      rw [hSize, zero, address]
      rfl
  · have := hHeap.base
    have := hHeap.top
    change 16 ≤ (PureTransport.erase initial).mem.pages * 65536
    omega

/-- A call of the write wrapper with the root and size of a represented buffer and the start and
count of a window writes the window's bytes. -/
theorem writeFunction_run_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {m : Module} {host : Host World}
    {env : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {output : Output} {root size start count : UInt64} {buffer : LeanExe.Bytes}
    {index typeIdx : Nat}
    (hImports : m.imports = ABI.importsWith calls)
    (hFunction : m.funcs[index]? = some (writeFunction output typeIdx))
    (hHost : env.Satisfies m (hostSpecWith host calls))
    (hHeap : heap.At (PureTransport.erase initial))
    (hRep : Bytes.Rep heap (PureTransport.erase initial) root size buffer) :
    ∃ bound, ∀ fuel ≥ bound,
      WriteRun host initial output (buffer.range start count)
        (run fuel m (3 + calls.length + index) initial
          [.i64 count, .i64 start, .i64 size, .i64 root] env) := by
  obtain ⟨hBytes, hAddress, hLength, hSize, hApart, hMemory⟩ :=
    write_window_abi hHeap hRep (window_at hRep hHeap start count)
  let bytes := buffer.range start count
  let Q : Assertion (Observed World) := fun continuation =>
    match continuation with
    | .Fallthrough final locals =>
        WriteRun host initial output bytes (.Success (locals.values.take 2) final)
    | .Trap final message => WriteRun host initial output bytes (.Trap final message)
    | _ => False
  have hBody : wp m (windowCode 0 2 3 4 ++ (writeCode output 4 5 6 ++ [])) Q initial
      (writeLocals root size start count) env := by
    refine wp_window_code (rootWord := root) (size := size) (startWord := start)
      (countWord := count) (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega)
      (by simp [writeLocals]) (by simp [writeLocals]) ?_
    intro s outside _ getAddress getLength
    refine wp_write_with output hImports hHost hBytes hAddress hLength hSize hApart hMemory
      getAddress getLength (by rw [outside.params]; simp [writeLocals])
      (by rw [outside.params, outside.length]; simp [writeLocals]) ?_ ?_
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
  have hImport : m.imports[3 + calls.length + index]? = none :=
    List.getElem?_eq_none (by rw [hImports, ABI.importsWith_length]; omega)
  refine ⟨bound, fun fuel hFuel => ?_⟩
  have hContinuation := hBound fuel hFuel
  rw [run_eq hImport]
  simp only [hImports, ABI.importsWith_length,
    show 3 + calls.length + index - (3 + calls.length) = index by omega, hFunction]
  have hArgs : ([Value.i64 count, .i64 start, .i64 size, .i64 root].take
      (writeFunction output typeIdx).numParams).reverse =
      [Value.i64 root, .i64 size, .i64 start, .i64 count] := rfl
  have hDrop : [Value.i64 count, .i64 start, .i64 size, .i64 root].drop
      (writeFunction output typeIdx).numParams = [] := rfl
  have hResults : (writeFunction output typeIdx).results.length = 2 := rfl
  have hCode : (writeFunction output typeIdx).body =
      windowCode 0 2 3 4 ++ writeCode output 4 5 6 := rfl
  have hLocals : (writeFunction output typeIdx).toLocals
      [Value.i64 root, .i64 size, .i64 start, .i64 count] =
      writeLocals root size start count := rfl
  simp only [hArgs, hDrop, hResults, hCode, hLocals, List.append_nil]
  cases hExec : exec fuel m initial (writeLocals root size start count)
      (windowCode 0 2 3 4 ++ writeCode output 4 5 6) env with
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

theorem writeFunction_run {World : Type} {m : Module} {host : Host World}
    {env : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {output : Output} {root size start count : UInt64} {buffer : LeanExe.Bytes}
    {index typeIdx : Nat}
    (hImports : m.imports = ABI.imports)
    (hFunction : m.funcs[index]? = some (writeFunction output typeIdx))
    (hHost : env.Satisfies m (hostSpec host))
    (hHeap : heap.At (PureTransport.erase initial))
    (hRep : Bytes.Rep heap (PureTransport.erase initial) root size buffer) :
    ∃ bound, ∀ fuel ≥ bound,
      WriteRun host initial output (buffer.range start count)
        (run fuel m (3 + index) initial [.i64 count, .i64 start, .i64 size, .i64 root] env) := by
  layout_instance writeFunction_run_with

/-- A call of the write wrapper with the root and size of a represented buffer and the start and
count of a window writes the window's bytes and keeps the heap and the buffer. -/
theorem wp_write_helper_at_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {target : Module} {host : Host World}
    {env : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {root size : UInt64} {buffer : LeanExe.Bytes} {start count : UInt64}
    {output : Output} {index typeIdx : Nat}
    {s : Locals} {values : List Value} {rest : Program} {Q : Assertion (Observed World)}
    (hImports : target.imports = ABI.importsWith calls)
    (hFunction : target.funcs[index]? = some (writeFunction output typeIdx))
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hHeap : heap.At (PureTransport.erase initial))
    (hRep : Bytes.Rep heap (PureTransport.erase initial) root size buffer)
    (hNext : ∀ (final : Store (Observed World)) (result : LeanExe.Wasi.WriteResult)
      (trace : List Event),
      Exec (observedHost host) (.write output (buffer.range start count) .pure)
        initial.host trace (.returned result) final.host →
      GuestFrame initial final [ABI.scratch] →
      Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.low)
        heap (PureTransport.erase final) [] →
      Bytes.Rep heap (PureTransport.erase final) root size buffer →
      wp target rest Q final { s with values := .i64 result.count :: .i64 result.errno :: values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host) (.write output (buffer.range start count) .pure)
        initial.host trace (.trapped message) final.host →
      GuestFrame initial final [ABI.scratch] →
      Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.low)
        heap (PureTransport.erase final) [] →
      Bytes.Rep heap (PureTransport.erase final) root size buffer → Q (.Trap final message)) :
    wp target (.call (3 + calls.length + index) :: rest) Q initial
      { s with values := .i64 count :: .i64 start :: .i64 size :: .i64 root :: values } env := by
  obtain ⟨bound, hBound⟩ := writeFunction_run_with (calls := calls) (index := index)
    (start := start) (count := count) hImports hFunction hHost hHeap hRep
  have hImport : target.imports[3 + calls.length + index]? = none :=
    List.getElem?_eq_none (by rw [hImports, ABI.importsWith_length]; omega)
  have hLookup : target.funcs[3 + calls.length + index - target.imports.length]? =
      some (writeFunction output typeIdx) := by
    simpa only [hImports, ABI.importsWith_length, Nat.add_sub_cancel_left] using hFunction
  have hAt := hBound bound le_rfl
  generalize hRun : run bound target (3 + calls.length + index) initial
    [.i64 count, .i64 start, .i64 size, .i64 root] env = outcome at hAt
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

theorem wp_write_helper_at {World : Type} {target : Module} {host : Host World}
    {env : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {root size : UInt64} {buffer : LeanExe.Bytes} {start count : UInt64}
    {output : Output} {index typeIdx : Nat}
    {s : Locals} {values : List Value} {rest : Program} {Q : Assertion (Observed World)}
    (hImports : target.imports = ABI.imports)
    (hFunction : target.funcs[index]? = some (writeFunction output typeIdx))
    (hHost : env.Satisfies target (hostSpec host))
    (hHeap : heap.At (PureTransport.erase initial))
    (hRep : Bytes.Rep heap (PureTransport.erase initial) root size buffer)
    (hNext : ∀ (final : Store (Observed World)) (result : LeanExe.Wasi.WriteResult)
      (trace : List Event),
      Exec (observedHost host) (.write output (buffer.range start count) .pure)
        initial.host trace (.returned result) final.host →
      GuestFrame initial final [ABI.scratch] →
      Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.low)
        heap (PureTransport.erase final) [] →
      Bytes.Rep heap (PureTransport.erase final) root size buffer →
      wp target rest Q final { s with values := .i64 result.count :: .i64 result.errno :: values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host) (.write output (buffer.range start count) .pure)
        initial.host trace (.trapped message) final.host →
      GuestFrame initial final [ABI.scratch] →
      Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.low)
        heap (PureTransport.erase final) [] →
      Bytes.Rep heap (PureTransport.erase final) root size buffer → Q (.Trap final message)) :
    wp target (.call (3 + index) :: rest) Q initial
      { s with values := .i64 count :: .i64 start :: .i64 size :: .i64 root :: values } env := by
  layout_instance wp_write_helper_at_with

end Verified.Wasi
