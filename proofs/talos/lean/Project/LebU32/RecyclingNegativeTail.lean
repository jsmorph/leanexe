import Project.LebU32.RecyclingFrame

namespace Project.LebU32.Recycling
open Wasm Project.ProofKit PackedFloatFrame

set_option maxRecDepth 32768
set_option maxHeartbeats 600000

structure ContinueReady (frame : Locals) (fuel v old root : UInt64) (size : Nat) : Prop extends Shape frame where
  fuel : frame.get 0 = some (.i64 fuel)
  tracked : frame.get 5 = some (.i64 old)
  done : frame.get 9 = some (.i64 0)
  input : frame.get 16 = some (.i64 v)
  owner : frame.get 21 = some (.i64 root)
  pointer : frame.get 22 = some (.i64 root)
  size : frame.get 23 = some (.i64 (UInt64.ofNat size))

theorem negative_tail_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel v old root : UInt64) (size : Nat) (h : ContinueReady frame fuel v old root size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, Running result (fuel - 1) v root size → wp «module» rest Q store result env) :
    wp «module» (negativeTail ++ rest) Q store frame env := by
  have hp := h.params
  have hl := h.locals
  have hv := h.values
  have hf := h.fuel
  have hi := h.input
  have ho := h.owner
  have hptr := h.pointer
  have hs := h.size
  have hd := h.done
  simp only [Locals.get, hp, hl, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] at hf hi ho hptr hs hd
  simp only [negativeTail, List.cons_append, List.nil_append]
  wp_packed_frame [hp, hl, hv, hf, hi, ho, hptr, hs]
  apply hNext _
  refine ⟨⟨?_, ?_, rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.length_set] using hp
  · simpa only [List.length_set] using hl
  · repeat apply I64Values.set
    exact h.typed
  all_goals simp only [Locals.get, hp, hl, List.length_set, List.getElem?_set, hd,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte]

#print axioms negative_tail_spec
end Project.LebU32.Recycling
