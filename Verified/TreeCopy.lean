import Verified.TreeCopyRecordCode

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_copyTree {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {shape : TreeShape} {src base : Nat} {source : UInt64}
    {value : Node} {rest : Program} {Q : Assertion Unit}
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hLayout : NodeLayout shape value) (hSource : NodeBorrowed heap store source value)
    (hTrap : TrapOK (!decide (heap.Within store m
      (allocCost (8 * shape.fields.length) * value.records))) Q)
    (hSrc : s.get src = some (.i64 source)) (hSrcBase : src < base)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ heap' store' s' ptr,
      Step heap store (fun _ => True) heap' store' (Node.blocks store' ptr value) →
      NodeOwned heap' store' ptr value → (Node.blocks store' ptr value).Pairwise regionsDisjoint →
      Frame base s s' →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * shape.fields.length) * value.records →
      wp m rest Q store' { s' with values := .i64 ptr :: s.values } host) :
    wp m (treeCopyCode shape src base ++ rest) Q store s host := by
  let post : Assertion Unit := fun cont => match cont with
    | .Fallthrough store' s' => wp m rest Q store' { s' with values := s'.values.take 1 ++ s.values } host
    | .Break 0 store' s' => wp m rest Q store' { s' with values := s'.values.take 1 ++ s.values } host
    | .Break (k + 1) store' s' => Q (.Break k store' s')
    | other => Q other
  cases value with
  | null =>
    have hZero : source = 0 := hSource
    subst source
    simp only [treeCopyCode, List.cons_append, List.nil_append, wp_localGet_cons, hSrc,
      wp_eqzI64_cons]
    rw [wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    simp (config := { decide := true }) only [ite_true, List.drop_zero]
    refine wp.conseq (Q := post) ?_ ?_
    · intro c hc
      cases c with
      | Break k _ _ => cases k <;> exact hc
      | _ => exact hc
    change wp m [.constI64 0] post store s host
    simpa only [wp_constI64_cons, wp_nil, post, List.take_succ_cons, List.take_zero,
      List.cons_append, List.nil_append] using hNext heap store s 0 (Step.refl hAt _) rfl (by simp [Node.blocks])
        (Frame.refl base s) (by simp [Node.records])
  | record slots =>
    have hNonzero := hSource.1.nonzero
    simp only [treeCopyCode, List.cons_append, List.nil_append, wp_localGet_cons, hSrc,
      wp_eqzI64_cons, hNonzero, ite_false]
    rw [wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    simp (config := { decide := true }) only [ite_false, List.drop_zero]
    refine wp.conseq (Q := post) ?_ ?_
    · intro c hc
      cases c with
      | Break k _ _ => cases k <;> exact hc
      | _ => exact hc
    have hRun := wp_treeCopyRecord hm (host := host) (rest := []) (Q := post) hAt hCap hLayout hSource
      (hTrap.imp (Q' := post) (fun _ h => h)) hSrc hSrcBase hLow hHigh
      (fun heap' store' s' ptr hStep hOwned hApart hFrame hBudget => by
        simpa only [wp_nil, post, List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append] using
          hNext heap' store' s' ptr hStep hOwned hApart hFrame hBudget)
    simpa only [List.append_nil] using hRun

#print axioms wp_copyTree

end Verified
