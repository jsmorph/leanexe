import Project.Validate.Program
import Project.Common
import LeanExe.Examples.AsciiDigits
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block

/-!
# Input read for `validateGeneric`

`func1` reads one input byte from linear memory.  The `BytesAt` hypothesis
states what the host wrote.
-/

namespace Project.Validate.Spec

open Wasm
open Project.Common
open LeanExe.Examples.AsciiDigits

set_option maxHeartbeats 64000000

/-- `func1` reads one input byte from linear memory. -/
theorem func1_terminates (env : HostEnv Unit) (st : Store Unit)
    (owner ptr len index : UInt64) (bytes : List UInt8)
    (hLen : len = UInt64.ofNat bytes.length)
    (hSize : bytes.length < UInt64.size)
    (hBytes : BytesAt st ptr bytes)
    (hIndex : index.toNat < bytes.length) :
    TerminatesWith (m := «module») (id := 1) (initial := st) (env := env)
      [.i64 index, .i64 len, .i64 ptr, .i64 owner]
      (fun st' vs => st' = st ∧ vs = [.i64 (bytes[index.toNat]!.toUInt64)]) := by
  apply TerminatesWith.of_wp_entry_for (f := func1Def)
  · simp [«module»]
  · change wp «module» func1 _ st
      { params := [.i64 owner, .i64 ptr, .i64 len, .i64 index],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0], values := [] } env
    unfold func1
    obtain ⟨hRead, hBound⟩ := hBytes index.toNat hIndex
    rw [UInt64.ofNat_toNat] at hRead hBound
    have hLt : index < len := by
      rw [hLen, UInt64.lt_iff_toNat_lt, toNat_ofNat_lt hSize]
      exact hIndex
    have hNoTrap : ¬ ((ptr + index).toUInt32.toNat + 1 > st.mem.pages * 65536) := by
      omega
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp [hLt])]
    wp_run
    simp_all [func1Def]
    have haddr : UInt32.ofNat ((ptr.toNat + index.toNat) % 4294967296) =
        ptr.toUInt32 + index.toUInt32 := by
      apply UInt32.toNat.inj
      simp
    rw [haddr, hRead]

end Project.Validate.Spec
