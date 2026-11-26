module

public import Verified.Wasi.ReadCall
public import Verified.Wasi.Write

@[expose] public section

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.ProofKit

theorem read_narrow64 (word : UInt64) (h : word.toNat < 4294967296) :
    word.toUInt32.toUInt64 = word := by
  rw [UInt64.toUInt64_toUInt32]
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mod, UInt64.reduceToNat, Nat.mod_eq_of_lt h]

/-- The body of the read wrapper reads at most `capacity` bytes of stdin to `pointer` and leaves
the errno and, on errno 0, the number of bytes read. -/
theorem wp_read_wrapper_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {m : Module} {host : Host World}
    {env : HostEnv (Observed World)} {store : Store (Observed World)} {s : Locals}
    {pointer capacity : UInt32} {pointerSlot capacitySlot errnoSlot : Nat}
    {rest : Program} {Q : Assertion (Observed World)}
    (hImports : m.imports = ABI.importsWith calls)
    (hHost : env.Satisfies m (hostSpecWith host calls))
    (hMemory : 16 ≤ store.mem.pages * 65536)
    (hBuffer : pointer.toNat + capacity.toNat ≤ store.mem.pages * 65536)
    (hAddress : pointer.toNat + capacity.toNat ≤ 2 ^ 32)
    (hSeparate : capacity = 0 ∨ 16 ≤ pointer.toNat)
    (hPointerLocal : s.get pointerSlot = some (.i64 pointer.toUInt64))
    (hCapacityLocal : s.get capacitySlot = some (.i64 capacity.toUInt64))
    (hErrnoLow : s.params.length ≤ errnoSlot)
    (hErrnoHigh : errnoSlot < s.params.length + s.locals.length)
    (hNext : ∀ (final : Store (Observed World)) (errno : UInt64) (committed : LeanExe.Bytes),
      (observedHost host).read store.host capacity.toUInt64
        (.returned errno committed) final.host →
      GuestFrame store final [ABI.scratch, (pointer.toNat, capacity.toNat)] →
      (errno = 0 → Bytes.At final.mem pointer.toUInt64 committed) →
      wp m rest Q final
        { (setLocal s errnoSlot (.i32 errno.toUInt32)) with
          values := (Value.i64 (if errno = 0 then committed.size else 0) ::
            Value.i64 errno :: s.values) } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (committed : LeanExe.Bytes),
      (observedHost host).read store.host capacity.toUInt64
        (.trapped message committed) final.host →
      GuestFrame store final [ABI.scratch, (pointer.toNat, capacity.toNat)] →
      Q (.Trap final message)) :
    wp m (readCode pointerSlot capacitySlot errnoSlot ++ rest) Q store s env := by
  simp only [readCode, List.append_assoc]
  refine wp_read_call_with hImports hHost hMemory hBuffer hAddress hSeparate hPointerLocal
    hCapacityLocal ?_ hTrap
  intro final errno committed hRead hFrame hData
  have hErrnoBound : errno.toNat ≤ 76 := ((observedHost host).read_bound hRead).2
  have hSize : committed.data.size < 4294967296 := by
    have hBound := ((observedHost host).read_bound hRead).1
    simp only [Transfer.committed, UInt32.toNat_toUInt64] at hBound
    have := capacity.toNat_lt
    omega
  have hErrno := narrow_word errno (by omega)
  have hSizeCast : UInt64.ofNat (UInt32.ofNat committed.data.size).toNat = committed.size := by
    rw [UInt32.toNat_ofNat_of_lt' (by change committed.data.size < 4294967296; exact hSize)]
    rfl
  simp only [List.cons_append, List.nil_append]
  refine wp_localSet_local (s := s) (vs := s.values) hErrnoLow hErrnoHigh ?_
  let finalLocals := setLocal { s with values := s.values } errnoSlot (.i32 errno.toUInt32)
  have hErrnoLocal : finalLocals.get errnoSlot = some (.i32 errno.toUInt32) :=
    Locals.get_setLocal_same hErrnoLow hErrnoHigh
  change wp m _ Q final finalLocals env
  simp only [wp_localGet_cons, hErrnoLocal, wp_extendUI32_cons, Locals.get_values,
    hErrno, wp_eqz_cons, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  by_cases hZero : errno = 0
  · obtain ⟨hAt, hCount⟩ := hData hZero
    simp only [hZero, UInt64.toUInt32_ofNat, ↓reduceIte]
    rw [ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
    simp only [List.drop_zero, wp_const_cons, wp_load32_cons,
      UInt32.reduceToNat, Nat.add_zero, UInt32.add_zero]
    rw [ite_eq_right (by rw [hFrame.pages]; omega), hCount]
    simp only [wp_extendUI32_cons, hSizeCast]
    simpa only [wp_nil, List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append,
      List.drop_zero, finalLocals, setLocal, hZero, ↓reduceIte] using
      hNext final errno committed hRead hFrame (fun _ => hAt)
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
      hNext final errno committed hRead hFrame (fun zero => absurd zero hZero)

end Verified.Wasi
