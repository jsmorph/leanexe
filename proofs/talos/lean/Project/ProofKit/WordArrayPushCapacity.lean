import Project.ProofKit.WordArrayPushPrepare

namespace Project.ProofKit.WordArrayPush
open Wasm

theorem frame_valid (params saved tail : List Wasm.Value) (s : Scratch)
    (field : Nat) (hf : field < 15) :
    (frame params saved tail s).validIndex (params.length + saved.length + field) := by
  simp only [Locals.validIndex, frame, List.length_append, Scratch.words, List.length_cons,
    List.length_nil]
  omega

theorem capacityFrame_eq (params saved tail : List Wasm.Value) (s : Scratch)
    (need : UInt64) :
    FixedArrayCapacity.capacityFrame (frame params saved tail s)
      (params.length + saved.length + 9) need = frame params saved tail { s with need := need } := by
  simp [FixedArrayCapacity.capacityFrame, frame, Scratch.words, Nat.add_assoc]

theorem capacity_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (s : Scratch)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store
      (frame params saved tail { s with need := FixedArrayCapacity.normalizedCapacity s.nextLength 1 }) env) :
    wp module_ (FixedArrayCapacity.localProgram (params.length + saved.length + 3) 1
      (params.length + saved.length + 9) ++ rest) Q store (frame params saved tail s) env := by
  refine FixedArrayCapacity.localProgram_spec _ s.nextLength 1 _ module_ env store
    (frame params saved tail s) ?_ rfl (by simp [frame]; omega)
    (frame_valid params saved tail s 9 (by decide)) Q rest ?_
  · simpa only [Scratch.words, List.getElem?_cons_zero, List.getElem?_cons_succ] using
      frame_get params saved tail s 3 (by decide)
  · simpa only [capacityFrame_eq] using hNext

#print axioms capacity_spec
end Project.ProofKit.WordArrayPush
