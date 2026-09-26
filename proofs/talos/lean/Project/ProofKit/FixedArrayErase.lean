import Project.ProofKit.FixedArrayCopy

namespace Project.ProofKit.FixedArrayCopy

open Wasm

theorem eraseIdxProgram_framed_spec
    (sourceLocal targetLocal prefixLocal suffixLocal counterLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (sourcePtr targetPtr : UInt64)
    (input : Array UInt64) (erase : Nat)
    (hErase : erase < input.size)
    (hSource : UInt64Array.At initial sourcePtr input)
    (hCounter : frame.validIndex counterLocal)
    (hCounterSource : sourceLocal ≠ counterLocal)
    (hCounterTarget : targetLocal ≠ counterLocal)
    (hCounterPrefix : prefixLocal ≠ counterLocal)
    (hCounterSuffix : suffixLocal ≠ counterLocal)
    (hValues : frame.values = [])
    (hSourceLocal : frame.get sourceLocal = some (.i64 sourcePtr))
    (hTargetLocal : frame.get targetLocal = some (.i64 targetPtr))
    (hPrefixLocal : frame.get prefixLocal =
      some (.i64 (UInt64.ofNat erase)))
    (hSuffixLocal : frame.get suffixLocal =
      some (.i64 (UInt64.ofNat (input.size - 1 - erase))))
    (hTargetFit32 :
      targetPtr.toNat + 8 * ((input.size - 1) + 1) ≤ 4294967296)
    (hTargetFitMemory :
      targetPtr.toNat + 8 * ((input.size - 1) + 1) ≤
        initial.mem.pages * 65536)
    (hTargetLength : initial.mem.read64 targetPtr.toUInt32 =
      UInt64.ofNat (input.size - 1))
    (hDisjoint :
      sourcePtr.toNat + 8 * (input.size + 1) ≤ targetPtr.toNat ∨
      targetPtr.toNat + 8 * input.size ≤ sourcePtr.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final : Store Unit,
      UInt64Array.At final targetPtr (input.eraseIdx! erase) →
      Project.ProofKit.Memory.WritesRange initial final
        (targetPtr.toNat + 8) (targetPtr.toNat + 8 * input.size) →
      wp module_ rest Q final
        (counterFrame frame counterLocal (input.size - 1 - erase) hCounter)
        env) :
    wp module_
      (program 1 sourceLocal targetLocal prefixLocal suffixLocal counterLocal ++
        rest)
      Q initial frame env := by
  refine program_framed_spec
    (skipCells := 1) (sourceLocal := sourceLocal) (targetLocal := targetLocal)
    (prefixLocal := prefixLocal) (suffixLocal := suffixLocal)
    (counterLocal := counterLocal) (module_ := module_) (env := env)
    (initial := initial) (frame := frame) (sourcePtr := sourcePtr)
    (targetPtr := targetPtr) (sourceCells := input.size)
    (targetCells := input.size - 1) (prefixCells := erase)
    (suffixCells := input.size - 1 - erase) (hCounter := hCounter)
    (hCounterSource := hCounterSource) (hCounterTarget := hCounterTarget)
    (hCounterPrefix := hCounterPrefix) (hCounterSuffix := hCounterSuffix)
    (hValues := hValues) (hSourceLocal := hSourceLocal)
    (hTargetLocal := hTargetLocal) (hPrefixLocal := hPrefixLocal)
    (hSuffixLocal := hSuffixLocal) (hSourceRange := by omega)
    (hTargetRange := by omega) (hSourceFit32 := hSource.1)
    (hTargetFit32 := hTargetFit32) (hSourceFitMemory := hSource.2.1)
    (hTargetFitMemory := hTargetFitMemory) (hDisjoint := by simpa [Nat.sub_add_cancel (by omega : 1 ≤ input.size)] using hDisjoint)
    (Q := Q) (rest := rest) ?_
  intro final hPages hHeader _ hPrefix hSuffix hWrites
  apply hDone final
  · apply UInt64Array.At.eraseIdx!_of_reads hErase hSource hTargetFit32
      (by rw [hPages]; exact hTargetFitMemory)
      (hHeader.trans hTargetLength)
    · intro cell hCell
      simpa [cellRead, cellAddress, UInt64Array.wordAddress] using
        hPrefix cell hCell
    · intro cell hCellLower hCellUpper
      have hOffset : cell - erase < input.size - 1 - erase := by omega
      have hTargetIndex : erase + (cell - erase) = cell := by omega
      have hSourceIndex : erase + 1 + (cell - erase) = cell + 1 := by omega
      simpa [cellRead, cellAddress, UInt64Array.wordAddress, hTargetIndex,
        hSourceIndex, Nat.add_assoc] using hSuffix (cell - erase) hOffset
  · have sizeEq : erase + (input.size - 1 - erase) + 1 = input.size := by omega
    simpa only [sizeEq] using hWrites


#print axioms eraseIdxProgram_framed_spec

end Project.ProofKit.FixedArrayCopy
