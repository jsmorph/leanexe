import Project.ProofKit.WordArrayPushInstall

namespace Project.ProofKit.WordArrayPush
open Wasm

theorem copy_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (s : Scratch) (input : Array UInt64)
    (hLength : s.length = UInt64.ofNat input.size) (hCount : s.count = UInt64.ofNat input.size)
    (hInput : UInt64Array.At store s.source input)
    (hFit : s.target.toNat + 8 * (input.size + 2) ≤ 4294967296)
    (hMemory : s.target.toNat + 8 * (input.size + 2) ≤ store.mem.pages * 65536)
    (hHeader : store.mem.read64 s.target.toUInt32 = UInt64.ofNat (input.size + 1))
    (hSeparate : s.source.toNat + 8 * (input.size + 1) ≤ s.target.toNat ∨
      s.target.toNat + 8 * (input.size + 2) ≤ s.source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Store Unit,
      Memory.WritesRange store final s.target.toNat (s.target.toNat + 8 * (input.size + 2)) →
      UInt64Array.At final s.source input → UInt64Array.At final s.target (input.push s.value) →
      wp module_ rest Q final
        { frame params saved tail { s with counter := UInt64.ofNat input.size } with values := [.i64 s.target] } env) :
    wp module_ (FixedArrayCopy.prefixProgram (params.length + saved.length)
      (params.length + saved.length + 4) (params.length + saved.length + 2)
      (params.length + saved.length + 5) ++
      UInt64Array.pushStoreProgram (params.length + saved.length + 4)
        (params.length + saved.length + 1) (params.length + saved.length + 6) ++
      [.localGet (params.length + saved.length + 4)] ++ rest) Q store
      (frame params saved tail s) env := by
  simp only [List.append_assoc]
  refine UInt64Array.pushCopy_spec _ _ _ _ _ _ module_ env store
    (frame params saved tail s) s.source s.target input s.value
    (frame_valid params saved tail s 5 (by decide)) rfl
    (by omega) (by omega) (by omega) (by omega) (by omega)
    ?_ ?_ ?_ ?_ ?_ hInput hFit hMemory hHeader hSeparate Q _ ?_
  · simpa only [Nat.add_zero, Scratch.words, List.getElem?_cons_zero] using
      frame_get params saved tail s 0 (by decide)
  · simpa only [Scratch.words, List.getElem?_cons_zero, List.getElem?_cons_succ] using
      frame_get params saved tail s 4 (by decide)
  · simpa only [Scratch.words, List.getElem?_cons_zero, List.getElem?_cons_succ, hCount] using
      frame_get params saved tail s 2 (by decide)
  · simpa only [Scratch.words, List.getElem?_cons_zero, List.getElem?_cons_succ, hLength] using
      frame_get params saved tail s 1 (by decide)
  · simpa only [Scratch.words, List.getElem?_cons_zero, List.getElem?_cons_succ] using
      frame_get params saved tail s 6 (by decide)
  · intro final hWrites hOld hNew
    rw [counterFrame_eq]
    wp_push_frame [List.cons_append, List.nil_append]
    exact hNext final hWrites hOld hNew

#print axioms copy_spec
end Project.ProofKit.WordArrayPush
