import Project.ProofKit.WordArrayGenerateLoop
import Project.ProofKit.WordArrayReverseRead

namespace Project.ProofKit.WordArrayReverse
open Wasm UInt64Array FixedArrayCopy WordArrayGenerateLoop

def copyProgram (sourceLocal lengthLocal targetLocal counterLocal : Nat) : Wasm.Program :=
  [.constI64 0, .localSet counterLocal] ++
    WordArrayGenerateLoop.program counterLocal lengthLocal targetLocal (readProgram sourceLocal lengthLocal counterLocal)

theorem copy_spec (sourceLocal lengthLocal targetLocal counterLocal : Nat) (module_ : Wasm.Module)
    (env : HostEnv Unit) (initial : Store Unit) (frame : Locals) (source target : UInt64) (input : Array UInt64)
    (hCounter : frame.validIndex counterLocal) (hSourceNe : sourceLocal ≠ counterLocal)
    (hLengthNe : lengthLocal ≠ counterLocal) (hTargetNe : targetLocal ≠ counterLocal)
    (hValues : frame.values = []) (hSourceLocal : frame.get sourceLocal = some (.i64 source))
    (hLengthLocal : frame.get lengthLocal = some (.i64 (UInt64.ofNat input.size)))
    (hTargetLocal : frame.get targetLocal = some (.i64 target))
    (hSource : At initial source input) (hFit : target.toNat + 8 * (input.size + 1) ≤ 4294967296)
    (hMemory : target.toNat + 8 * (input.size + 1) ≤ initial.mem.pages * 65536)
    (hLength : initial.mem.read64 target.toUInt32 = UInt64.ofNat input.size)
    (hSeparate : source.toNat + 8 * (input.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (input.size + 1) ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Store Unit, At final source input → At final target input.reverse →
      Memory.WritesRange initial final target.toNat (target.toNat + 8 * (input.size + 1)) →
      wp module_ rest Q final (counterFrame frame counterLocal input.size hCounter) env) :
    wp module_ (copyProgram sourceLocal lengthLocal targetLocal counterLocal ++ rest) Q initial frame env := by
  simp only [copyProgram, List.cons_append, List.nil_append]
  apply initializeCounter_spec hCounter hValues
  let P : Locals → Prop := fun next => ∃ index, next = counterFrame frame counterLocal index hCounter
  apply WordArrayGenerateLoop.program_spec counterLocal lengthLocal targetLocal
    (readProgram sourceLocal lengthLocal counterLocal) module_ env initial _ target input.reverse P
    hLengthNe hTargetNe
  · refine ⟨rfl, counterFrame_get_counter .., ?_, ?_, (counterFrame_validIndex ..).2 hCounter⟩
    · simpa only [Array.size_reverse] using (counterFrame_get_ne _ _ _ _ _ hLengthNe).trans hLengthLocal
    · exact (counterFrame_get_ne _ _ _ _ _ hTargetNe).trans hTargetLocal
  · exact ⟨0, rfl⟩
  · apply PrefixAt.empty
    · simpa only [Array.size_reverse] using hFit
    · simpa only [Array.size_reverse] using hMemory
    · simpa only [Array.size_reverse] using hLength
  · rintro next index hNextCounter ⟨old, rfl⟩
    exact ⟨index, counterFrame_counterFrame ..⟩
  · rintro current next index hi hReady ⟨old, rfl⟩ hWrites nextQ nextRest hWordNext
    have hCurrentSource := hSource.writesRange hWrites
      (by simpa only [Array.size_reverse] using hSeparate)
    apply read_spec sourceLocal lengthLocal counterLocal module_ env current
      { counterFrame frame counterLocal old hCounter with values := [.i32 (wordAddress target (index + 1))] }
      source input index (wordAddress target (index + 1))
      (by simpa only [Array.size_reverse] using hi) hCurrentSource rfl
      ((counterFrame_get_ne _ _ _ _ _ hSourceNe).trans hSourceLocal)
      (by simpa only [Array.size_reverse, Frame.withValues_get] using hReady.2.2.1) hReady.2.1
    simpa only [Array.getElem_reverse] using hWordNext _ hReady ⟨old, rfl⟩
  · rintro final result hReady ⟨index, rfl⟩ hOutput hWrites
    have hEq := hReady.2.1
    rw [counterFrame_get_counter] at hEq
    have hWord : UInt64.ofNat index = UInt64.ofNat input.size := by
      simpa only [Array.size_reverse, Option.some.injEq, Value.i64.injEq] using hEq
    have hFrame : counterFrame frame counterLocal index hCounter =
        counterFrame frame counterLocal input.size hCounter := by
      simp only [counterFrame, hWord]
    rw [hFrame]
    exact hNext final (hSource.writesRange hWrites (by simpa only [Array.size_reverse] using hSeparate))
      hOutput (by simpa only [Array.size_reverse] using hWrites)

#print axioms copy_spec
end Project.ProofKit.WordArrayReverse
