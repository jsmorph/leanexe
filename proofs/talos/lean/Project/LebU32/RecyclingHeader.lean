import Project.LebU32.RecyclingFrame

namespace Project.LebU32.Recycling
open Wasm Project.ProofKit PackedFloatFrame

set_option maxRecDepth 32768
set_option maxHeartbeats 600000

theorem active_head_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel v root : UInt64) (size : Nat) (h : Running frame fuel v root size) (hFuel : fuel ≠ 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, Running result fuel v root size →
      result.get 10 = some (.i64 (v % 128)) → result.get 11 = some (.i64 (v / 128)) →
      wp «module» rest Q store result env) :
    wp «module» (activeHead ++ rest) Q store frame env := by
  have hp := h.params
  have hl := h.locals
  have hv := h.values
  have hf := h.fuel
  have hi := h.input
  have ho := h.owner
  have hptr := h.pointer
  have hs := h.size
  have ht := h.tracked
  have hd := h.done
  simp only [Locals.get, hp, hl, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] at hf hi ho hptr hs ht hd
  simp only [activeHead, List.cons_append, List.nil_append]
  wp_packed_frame [hp, hl, hv, hf, hd, hFuel]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by decide)]
  wp_packed_frame [hp, hl, hv, hd]
  wp_packed_frame [hp, hl, hi]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hp, hl, hi]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hp, hl]
  apply hNext _ ?_ ?_ ?_
  · refine ⟨⟨hp, ?_, rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [List.length_set] using hl
    · repeat apply I64Values.set
      exact h.typed
    all_goals simp only [Locals.get, hp, hl, List.length_set, List.getElem?_set,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte, hf, hi, ho, hptr, hs, ht, hd]
  all_goals simp only [Locals.get, hp, hl, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte]

#print axioms active_head_spec
end Project.LebU32.Recycling
