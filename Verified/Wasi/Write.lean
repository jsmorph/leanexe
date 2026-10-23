import Verified.Wasi.Scratch
import Verified.Wasi.GuestFrame
import Interpreter.Wasm.Wp.Call

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.ProofKit

theorem narrow_word (value : UInt64) (h : value.toNat < 4294967296) :
    UInt64.ofNat value.toUInt32.toNat = value := by
  rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt h, UInt64.ofNat_toNat]

theorem wp_write {World : Type} {m : Module} {host : Host World}
    {env : HostEnv (Observed World)} {store : Store (Observed World)} {s : Locals}
    {root length : UInt64} {bytes : LeanExe.Bytes} {pointerSlot lengthSlot errnoSlot : Nat}
    {rest : Program} {Q : Assertion (Observed World)}
    (output : Output) (hImports : m.imports = ABI.imports)
    (hHost : env.Satisfies m (hostSpec host))
    (hBytes : Bytes.At store.mem root bytes) (hRoot : root.toNat < 4294967296)
    (hLength : length.toNat = bytes.data.size) (hSize : bytes.data.size < 4294967296)
    (hApart : root.toNat + bytes.data.size ≤ 0 ∨ 16 ≤ root.toNat)
    (hMemory : 16 ≤ store.mem.pages * 65536)
    (hPointerLocal : s.get pointerSlot = some (.i64 root))
    (hLengthLocal : s.get lengthSlot = some (.i64 length))
    (hErrnoLow : s.params.length ≤ errnoSlot)
    (hErrnoHigh : errnoSlot < s.params.length + s.locals.length)
    (hNext : ∀ (final : Store (Observed World)) (errno committed : UInt64),
      (observedHost host).write store.host output bytes (.returned errno committed) final.host →
      GuestFrame store final [ABI.scratch] →
      wp m rest Q final
        { (setLocal s errnoSlot (.i32 errno.toUInt32)) with
          values := (Value.i64 (if errno = 0 then committed else 0) ::
            Value.i64 errno :: s.values) } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (committed : UInt64),
      (observedHost host).write store.host output bytes (.trapped message committed) final.host →
      GuestFrame store final [ABI.scratch] → Q (.Trap final message)) :
    wp m (writeCode output pointerSlot lengthSlot errnoSlot ++ rest) Q store s env := by
  have hRootCast : root.toUInt32.toUInt64 = root := by
    rw [UInt64.toUInt64_toUInt32]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mod, UInt64.reduceToNat, Nat.mod_eq_of_lt hRoot]
  have hLengthCast : length.toUInt32 = UInt32.ofNat bytes.data.size := by
    rw [Memory.toUInt32_eq_ofNat, Nat.mod_eq_of_lt (by omega), hLength]
  let initial := initializeScratch store root.toUInt32 length.toUInt32
  have hWrites := initializeScratch_range store root.toUInt32 length.toUInt32
  have hFrame : GuestFrame store initial [ABI.scratch] := GuestFrame.ofScratchWrites hWrites
  have hInput : Bytes.At initial.mem root.toUInt32.toUInt64 bytes := by
    rw [hRootCast]
    exact hBytes.writesRange hWrites hApart
  have hRequest : WriteRequest initial
      [.i32 output.fd.toUInt32, .i32 0, .i32 1, .i32 8] output root.toUInt32 bytes := by
    have hReads := initializeScratch_reads store root.toUInt32 length.toUInt32
    exact ⟨rfl, hMemory, hReads.1, hReads.2.1.trans hLengthCast, hSize, hInput⟩
  simp only [writeCode, List.append_assoc]
  refine wp_metadata hPointerLocal hLengthLocal hMemory ?_
  simp only [List.cons_append, List.nil_append, wp_const_cons]
  refine wp_call_host_contract (id := 1) (imp := ABI.imports[1]!) (c := writeContract host)
    (by simp [hImports, ABI.imports]) hHost
    (by simp [hImports, ABI.imports]) (hostSpec_write host) ?_ ?_ ?_
  · intro values final hContract
    have hResult := hContract output root.toUInt32 bytes (by
      simpa [ABI.imports, ABI.transferType] using hRequest)
    obtain ⟨errno, committed, rfl, hWrite, hGuest, hCount⟩ := hResult
    have hErrnoBound : errno.toNat ≤ 76 := (host.write_bound hWrite.1).2
    have hCommittedBound : committed.toNat < 4294967296 :=
      ((host.write_bound hWrite.1).1).trans_lt hSize
    have hErrno := narrow_word errno (by omega)
    have hCommitted := narrow_word committed hCommittedBound
    have hGuest' := hFrame.trans hGuest
    refine wp_localSet_local (s := s) (vs := s.values) hErrnoLow hErrnoHigh ?_
    let finalLocals := setLocal { s with values := s.values } errnoSlot (.i32 errno.toUInt32)
    have hErrnoLocal : finalLocals.get errnoSlot = some (.i32 errno.toUInt32) :=
      Locals.get_setLocal_same hErrnoLow hErrnoHigh
    change wp m _ Q final finalLocals env
    simp only [wp_localGet_cons, hErrnoLocal, wp_extendUI32_cons, Locals.get_values,
      hErrno, wp_eqz_cons, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    by_cases hZero : errno = 0
    · have hCount' := hCount hZero
      simp only [hZero, UInt64.toUInt32_ofNat, ↓reduceIte]
      rw [ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
      simp only [List.drop_zero, wp_const_cons, wp_load32_cons,
        UInt32.reduceToNat, Nat.add_zero, UInt32.add_zero]
      rw [ite_eq_right (by rw [hGuest.pages, hFrame.pages]; omega), hCount']
      simp only [wp_extendUI32_cons, hCommitted]
      simpa only [wp_nil, List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append,
        List.drop_zero, finalLocals, setLocal, hZero, ↓reduceIte] using
        hNext final errno committed hWrite hGuest'
    · have hNarrowNe : errno.toUInt32 ≠ 0 := by
        intro hNarrow
        apply hZero
        calc
          errno = UInt64.ofNat errno.toUInt32.toNat := hErrno.symm
          _ = 0 := by rw [hNarrow]; rfl
      simp only [hNarrowNe, ite_false]
      rw [ite_eq_right (by decide : ¬((0 : UInt32) ≠ 0))]
      simpa only [wp_simp, List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append,
        List.drop_zero, finalLocals, setLocal, hZero, ite_false] using
        hNext final errno committed hWrite hGuest'
  · intro final message hContract
    obtain ⟨committed, hWrite, hGuest⟩ :=
      hContract output root.toUInt32 bytes (by simpa [ABI.imports, ABI.transferType] using hRequest)
    exact hTrap final message committed hWrite (hFrame.trans hGuest)
  · intro final tag arguments hContract
    exact False.elim (hContract output root.toUInt32 bytes (by
      simpa [ABI.imports, ABI.transferType] using hRequest))

end Verified.Wasi
