module

public import Verified.Wasi.ReadProof

@[expose] public section

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

def readLocals (pointer capacity : UInt64) : Locals :=
  { params := [.i64 pointer, .i64 capacity], locals := [.i32 0], values := [] }

/-- The outcomes of a call of the read wrapper with `pointer` and `capacity`: the host's read with
the errno and the bytes read, which lie at `pointer` on errno 0, or the host's trap, each with
the frame of the scratch bytes and the region. -/
inductive ReadRun {World : Type} (host : Host World) (initial : Store (Observed World))
    (pointer capacity : UInt64) : Result (Observed World) → Prop where
  | returned (final : Store (Observed World)) (errno : UInt64) (committed : LeanExe.Bytes)
      (read : (observedHost host).read initial.host capacity (.returned errno committed)
        final.host)
      (frame : GuestFrame initial final [ABI.scratch, (pointer.toNat, capacity.toNat)])
      (data : errno = 0 → Bytes.At final.mem pointer committed) :
      ReadRun host initial pointer capacity
        (.Success [.i64 (if errno = 0 then committed.size else 0), .i64 errno] final)
  | hostTrap (final : Store (Observed World)) (message : String) (committed : LeanExe.Bytes)
      (read : (observedHost host).read initial.host capacity (.trapped message committed)
        final.host)
      (frame : GuestFrame initial final [ABI.scratch, (pointer.toNat, capacity.toNat)]) :
      ReadRun host initial pointer capacity (.Trap final message)

theorem readFunction_run_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {m : Module} {host : Host World}
    {env : HostEnv (Observed World)} {initial : Store (Observed World)}
    {pointer capacity : UInt64} {index typeIdx : Nat}
    (hImports : m.imports = ABI.importsWith calls)
    (hFunction : m.funcs[index]? = some (readFunction typeIdx))
    (hHost : env.Satisfies m (hostSpecWith host calls))
    (hMemory : 16 ≤ initial.mem.pages * 65536)
    (hBuffer : pointer.toNat + capacity.toNat ≤ initial.mem.pages * 65536)
    (hAddress : pointer.toNat + capacity.toNat < 4294967296)
    (hSeparate : capacity = 0 ∨ 16 ≤ pointer.toNat) :
    ∃ bound, ∀ fuel ≥ bound,
      ReadRun host initial pointer capacity
        (run fuel m (3 + calls.length + index) initial [.i64 capacity, .i64 pointer] env) := by
  have hPointer : pointer.toNat < 4294967296 := by omega
  have hCapacity : capacity.toNat < 4294967296 := by omega
  have hPointerNat : pointer.toUInt32.toNat = pointer.toNat := by
    rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt hPointer]
  have hCapacityNat : capacity.toUInt32.toNat = capacity.toNat := by
    rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt hCapacity]
  have hPointerCast := read_narrow64 pointer hPointer
  have hCapacityCast := read_narrow64 capacity hCapacity
  let Q : Assertion (Observed World) := fun continuation =>
    match continuation with
    | .Fallthrough final locals =>
        ReadRun host initial pointer capacity (.Success (locals.values.take 2) final)
    | .Trap final message => ReadRun host initial pointer capacity (.Trap final message)
    | _ => False
  have hBody : wp m (readCode 0 1 2 ++ []) Q initial (readLocals pointer capacity) env := by
    refine wp_read_wrapper_with (pointer := pointer.toUInt32) (capacity := capacity.toUInt32)
      hImports hHost hMemory
      (by rw [hPointerNat, hCapacityNat]; exact hBuffer)
      (by rw [hPointerNat, hCapacityNat]; omega)
      (by
        rcases hSeparate with zero | high
        · left
          rw [zero]
          rfl
        · right
          rw [hPointerNat]
          exact high)
      (by rw [hPointerCast]; rfl) (by rw [hCapacityCast]; rfl)
      (by change 2 ≤ 2; omega) (by change 2 < 3; omega) ?_ ?_
    · intro final errno committed hRead hFrame hData
      rw [hCapacityCast] at hRead
      rw [hPointerNat, hCapacityNat] at hFrame
      simp only [wp_nil, Q]
      change ReadRun host initial pointer capacity
        (.Success [.i64 (if errno = 0 then committed.size else 0), .i64 errno] final)
      exact .returned final errno committed hRead hFrame
        (fun zero => by simpa only [hPointerCast] using hData zero)
    · intro final message committed hRead hFrame
      rw [hCapacityCast] at hRead
      rw [hPointerNat, hCapacityNat] at hFrame
      exact .hostTrap final message committed hRead hFrame
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
  have hArgs : ([Value.i64 capacity, Value.i64 pointer].take
      (readFunction typeIdx).numParams).reverse = [Value.i64 pointer, Value.i64 capacity] := rfl
  have hDrop : [Value.i64 capacity, Value.i64 pointer].drop
      (readFunction typeIdx).numParams = [] := rfl
  have hResults : (readFunction typeIdx).results.length = 2 := rfl
  have hCode : (readFunction typeIdx).body = readCode 0 1 2 := rfl
  have hLocals : (readFunction typeIdx).toLocals
      [Value.i64 pointer, Value.i64 capacity] = readLocals pointer capacity := rfl
  simp only [hArgs, hDrop, hResults, hCode, hLocals, List.append_nil]
  cases hExec : exec fuel m initial (readLocals pointer capacity) (readCode 0 1 2) env with
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

end Verified.Wasi
