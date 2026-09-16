import Project.ProofKit.ArrayPrefix
import Project.ProofKit.FixedArrayCopy
import Project.ProofKit.Frame

namespace Project.ProofKit.UInt64Array
open Wasm FixedArrayCopy

def pushStoreProgram (targetLocal lengthLocal valueLocal : Nat) : Wasm.Program :=
  [.localGet targetLocal, .localGet lengthLocal, .constI64 1, .mulI64,
    .constI64 1, .addI64, .constI64 8, .mulI64, .addI64, .wrapI64,
    .localGet valueLocal, .store64 0]

theorem pushStoreProgram_spec (targetLocal lengthLocal valueLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (target : UInt64) (input : Array UInt64) (value : UInt64)
    (hValues : frame.values = [])
    (hTarget : frame.get targetLocal = some (.i64 target))
    (hLength : frame.get lengthLocal = some (.i64 (UInt64.ofNat input.size)))
    (hValue : frame.get valueLocal = some (.i64 value))
    (hPrefix : PrefixAt store target (input.push value) input.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (writeElement store target input.size value) frame env) :
    wp module_ (pushStoreProgram targetLocal lengthLocal valueLocal ++ rest)
      Q store frame env := by
  have hBound := hPrefix.elementBound input.size (by simp)
  have hAddress : UInt32.ofNat
      ((target + (UInt64.ofNat input.size * 1 + 1) * 8).toNat % 2^32) =
      wordAddress target (input.size + 1) := by
    rw [UInt64.mul_one]
    change UInt32.ofNat
      ((target + (UInt64.ofNat input.size + UInt64.ofNat 1) * UInt64.ofNat 8).toNat % 4294967296) = _
    rw [← UInt64.ofNat_add, ← UInt64.ofNat_mul]
    simpa [wordAddress, Nat.mul_comm] using
      (Memory.toUInt32_eq_ofNat (target + UInt64.ofNat ((input.size + 1) * 8))).symm
  have hFrame : { frame with values := [] } = frame := Frame.ext _ _ rfl rfl hValues.symm
  simp only [pushStoreProgram, List.cons_append, List.nil_append, wp_localGet_cons,
    Frame.withValues_get, hTarget, hLength, hValue, hValues, wp_constI64_cons,
    wp_mulI64_cons, wp_addI64_cons, wp_wrapI64_cons, wp_store64_cons]
  rw [hAddress]
  simp only [UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]
  rw [if_neg (Nat.not_lt.mpr hBound)]
  simpa only [writeElement, hFrame] using hNext

theorem pushCopy_spec (sourceLocal targetLocal countLocal lengthLocal counterLocal valueLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (source target : UInt64) (input : Array UInt64) (value : UInt64)
    (hCounter : frame.validIndex counterLocal) (hValues : frame.values = [])
    (hSourceNe : sourceLocal ≠ counterLocal) (hTargetNe : targetLocal ≠ counterLocal)
    (hCountNe : countLocal ≠ counterLocal) (hLengthNe : lengthLocal ≠ counterLocal)
    (hValueNe : valueLocal ≠ counterLocal)
    (hSource : frame.get sourceLocal = some (.i64 source))
    (hTarget : frame.get targetLocal = some (.i64 target))
    (hCount : frame.get countLocal = some (.i64 (UInt64.ofNat input.size)))
    (hLength : frame.get lengthLocal = some (.i64 (UInt64.ofNat input.size)))
    (hValue : frame.get valueLocal = some (.i64 value))
    (hInput : At initial source input)
    (hFit : target.toNat + 8 * (input.size + 2) ≤ 4294967296)
    (hMemory : target.toNat + 8 * (input.size + 2) ≤ initial.mem.pages * 65536)
    (hHeader : initial.mem.read64 target.toUInt32 = UInt64.ofNat (input.size + 1))
    (hSeparate : source.toNat + 8 * (input.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (input.size + 2) ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Store Unit,
      Memory.WritesRange initial final target.toNat (target.toNat + 8 * (input.size + 2)) →
      At final source input → At final target (input.push value) →
      wp module_ rest Q final (counterFrame frame counterLocal input.size hCounter) env) :
    wp module_ (prefixProgram sourceLocal targetLocal countLocal counterLocal ++
      pushStoreProgram targetLocal lengthLocal valueLocal ++ rest) Q initial frame env := by
  rw [List.append_assoc]
  apply prefixProgram_framed_spec sourceLocal targetLocal countLocal counterLocal
    module_ env initial frame source target input.size (input.size + 1) input.size
    hCounter hSourceNe hTargetNe hCountNe hValues hSource hTarget hCount
    (Nat.le_refl _) (by omega) hInput.1 (by simpa [Nat.add_assoc] using hFit)
    hInput.2.1 (by simpa [Nat.add_assoc] using hMemory) (by simpa [Nat.add_assoc] using hSeparate)
  intro middle hPages hMiddleHeader _ hCopied hWrites
  have hPrefix : PrefixAt middle target (input.push value) input.size := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Nat.add_assoc] using hFit
    · simpa [Nat.add_assoc, hPages] using hMemory
    · simpa using hMiddleHeader.trans hHeader
    · intro i hi hOld
      rw [Array.getElem_push_lt hOld]
      exact (hCopied i hOld).trans (hInput.elementRead i hOld)
  apply pushStoreProgram_spec targetLocal lengthLocal valueLocal module_ env middle
    (counterFrame frame counterLocal input.size hCounter) target input value rfl
    ((counterFrame_get_ne _ _ _ _ hCounter hTargetNe).trans hTarget)
    ((counterFrame_get_ne _ _ _ _ hCounter hLengthNe).trans hLength)
    ((counterFrame_get_ne _ _ _ _ hCounter hValueNe).trans hValue) hPrefix
  have hFull : At (writeElement middle target input.size value) target (input.push value) := by
    have hDone := (hPrefix.write_next (by simp))
    have hComplete : PrefixAt (writeElement middle target input.size value) target
        (input.push value) (input.push value).size := by simpa using hDone
    exact hComplete.complete
  have hFirst := hWrites.mono (show target.toNat ≤ target.toNat + 8 by omega)
    (show target.toNat + 8 * (input.size + 1) ≤ target.toNat + 8 * (input.size + 2) by omega)
  have hLast := writeElement_frame middle target (input.size + 1) input.size value
    (by simpa [Nat.add_assoc] using hFit) (by omega)
  have hTotal : Memory.WritesRange initial (writeElement middle target input.size value)
      target.toNat (target.toNat + 8 * (input.size + 2)) := by
    simpa [Nat.add_assoc] using hFirst.trans hLast
  exact hNext _ hTotal (hInput.writesRange hTotal hSeparate) hFull

#print axioms pushStoreProgram_spec
#print axioms pushCopy_spec
end Project.ProofKit.UInt64Array
