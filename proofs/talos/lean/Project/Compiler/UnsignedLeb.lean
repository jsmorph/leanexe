import Project.Compiler.ByteLists
import LeanExe.Wasm.LebTheorems
import LeanExe.Wasm.Binary
import Project.Artifact.Binary.Proof.Leb

namespace Project.Compiler.UnsignedLeb

def bytes : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, n =>
      if n < 128 then [UInt8.ofNat n]
      else UInt8.ofNat (n % 128 + 128) :: bytes fuel (n / 128)

theorem native_bytes (fuel : Nat) (v : UInt64) :
    LeanExe.Wasm.Leb.lebList fuel v = bytes fuel v.toNat := by
  induction fuel generalizing v with
  | zero => rfl
  | succ fuel ih =>
    simp only [LeanExe.Wasm.Leb.lebList, bytes]
    have hzero : v / 128 = 0 ↔ v.toNat < 128 := by
      rw [← UInt64.toNat_inj]
      simp
    by_cases hv : v.toNat < 128
    · simp only [beq_iff_eq, hzero, hv, ite_true]
      congr 1
      apply UInt8.toNat.inj
      simp [UInt64.toNat_toUInt8, UInt64.toNat_mod, Nat.mod_eq_of_lt hv]
    · simp only [beq_iff_eq, hzero, hv, ite_false, ih]
      have low : v.toNat % 128 + 128 < 2 ^ 64 := by omega
      congr 1
      · apply UInt8.toNat.inj
        simp [UInt64.toNat_toUInt8, UInt64.toNat_add, UInt64.toNat_mod,
          Nat.mod_eq_of_lt low]

open Wasm.Binary.Leb.Proof

theorem trace (fuel extra width shift acc n : Nat)
    (shiftFits : shift < width) (room : width ≤ shift + 7 * fuel)
    (bound : n < 2 ^ (width - shift)) :
    UnsignedTrace width shift fuel acc (bytes (fuel + extra) n) (acc + n * 2 ^ shift) := by
  induction fuel generalizing shift acc n with
  | zero => omega
  | succ fuel ih =>
    rw [Nat.succ_add, bytes]
    by_cases small : n < 128
    · rw [if_pos small]
      have nb : (UInt8.ofNat n).toNat = n := by simp; omega
      simpa [nb, Nat.mod_eq_of_lt small] using
        (UnsignedTrace.terminal (width := width) (shift := shift) (value := acc)
          fuel (UInt8.ofNat n) (by simpa [nb] using small) shiftFits
          (by simpa [nb, Nat.mod_eq_of_lt small] using bound))
    · rw [if_neg small]
      have shiftNext : shift + 7 < width := by
        by_contra h
        have power : 2 ^ (width - shift) ≤ 2 ^ 7 :=
          Nat.pow_le_pow_right (by decide) (by omega)
        norm_num at power
        omega
      have fuelPositive : 0 < fuel := by omega
      have power : 2 ^ (width - shift) = 128 * 2 ^ (width - (shift + 7)) := by
        have diff : width - shift = 7 + (width - (shift + 7)) := by omega
        rw [diff, Nat.pow_add]
      have divided : n / 128 < 2 ^ (width - (shift + 7)) := by
        rw [power] at bound
        omega
      have nb : (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 := by
        simp
        omega
      have tail := ih (shift + 7) (acc + n % 128 * 2 ^ shift) (n / 128)
        shiftNext (by omega) divided
      have valueEq : acc + n % 128 * 2 ^ shift + n / 128 * 2 ^ (shift + 7) =
          acc + n * 2 ^ shift := by
        rw [Nat.pow_add]
        calc
          _ = acc + (n % 128 + 128 * (n / 128)) * 2 ^ shift := by ring
          _ = _ := by rw [Nat.mod_add_div]
      rw [valueEq] at tail
      apply UnsignedTrace.next fuel (UInt8.ofNat (n % 128 + 128)) _ _
        (by rw [nb]; omega) fuelPositive
      simpa [nb] using tail

theorem u32 (v : UInt64) (bound : v.toNat < 2 ^ 32) :
    Wasm.Binary.Grammar.U32 (LeanExe.Wasm.Leb.u32lebU64 v).toList v.toNat := by
  rw [show (LeanExe.Wasm.Leb.u32lebU64 v).toList = LeanExe.Wasm.Leb.lebList 10 v from
    by rw [byteArray_toList]; exact LeanExe.Wasm.Leb.u32lebU64_eq_lebList v, native_bytes]
  have h := trace 5 5 32 0 0 v.toNat (by decide) (by decide) bound
  refine ⟨h.length_le, h.continuationForm, terminalFitsFrom_zero h.terminalFitsFrom, ?_⟩
  simpa using h.value_eq.symm

theorem u64 (v : UInt64) :
    Wasm.Binary.Grammar.U64 (LeanExe.Wasm.Leb.u32lebU64 v).toList v.toNat := by
  rw [byteArray_toList, LeanExe.Wasm.Leb.u32lebU64_eq_lebList, native_bytes]
  have h := trace 10 0 64 0 0 v.toNat (by decide) (by decide) v.toNat_lt
  refine ⟨h.length_le, h.continuationForm, terminalFitsFrom_zero h.terminalFitsFrom, ?_⟩
  simpa using h.value_eq.symm

theorem production_u32 (n : Nat) (bound : n < 2 ^ 32) :
    Wasm.Binary.Grammar.U32 (LeanExe.Wasm.Binary.u32leb n) n := by
  have small : n < 2 ^ 64 := by omega
  have hn : (UInt64.ofNat n).toNat = n := UInt64.toNat_ofNat_of_lt' small
  simpa [LeanExe.Wasm.Binary.u32leb, hn] using u32 (UInt64.ofNat n) (by simpa [hn])

end Project.Compiler.UnsignedLeb
