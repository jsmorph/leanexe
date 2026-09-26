import Project.ProofKit.WordArrayPushCapacity
import Project.ProofKit.FixedArrayResult

namespace Project.ProofKit.WordArrayPush
open Wasm

theorem install_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (s : Scratch)
    (hBound : s.root.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (FixedArrayResult.writeLength store s.root s.nextLength)
      (frame params saved tail { s with target := s.root }) env) :
    wp module_ (installLength (params.length + saved.length) ++ rest) Q store
      (frame params saved tail s) env := by
  simp only [installLength, List.cons_append, List.nil_append]
  wp_push_frame [show 2^32 = 4294967296 by decide, ← Memory.toUInt32_eq_ofNat, UInt32.add_zero, UInt32.toNat_zero,
    Nat.not_lt.mpr hBound]
  exact hNext

theorem counterFrame_eq (params saved tail : List Wasm.Value) (s : Scratch) (count : Nat)
    (hCounter : (frame params saved tail s).validIndex (params.length + saved.length + 5)) :
    FixedArrayCopy.counterFrame (frame params saved tail s) (params.length + saved.length + 5)
      count hCounter = frame params saved tail { s with counter := UInt64.ofNat count } := by
  simp [FixedArrayCopy.counterFrame, Locals.set, frame, Scratch.words, Nat.add_assoc]

#print axioms install_spec
#print axioms counterFrame_eq
end Project.ProofKit.WordArrayPush
