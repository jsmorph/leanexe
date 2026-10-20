import Verified.TreeCopyBodyCode

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_treeCopyLoop {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 s : Locals}
    {rest : Program} {Q : Assertion Unit}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q)
    (hNext : ∀ heap' store' s', NodeOwned heap' store' result (.record root) →
      (Node.blocks store' result (.record root)).Pairwise regionsDisjoint →
      Step heap0 initial (fun _ => True) heap' store' (Node.blocks store' result (.record root)) →
      heap'.top.toNat ≤ limit → Frame base s0 s' → s'.get base = some (.i64 result) →
      s'.values = s0.values → wp m rest Q store' s' host) :
    wp m (.block 0 0 [.loop 0 0 (treeCopyBody shape base)] :: rest) Q store s host := by
  let Inv : Nat → AssertionF Unit := fun n store' s' => ∃ heap' current' parents',
    CopyInv shape heap0 initial root result limit heap' store' current' parents' ∧
      CopyLocals base s0 result current'.pointer s' ∧ (current'.work parents').steps = n
  let done : Assertion Unit := fun cont => match cont with
    | .Fallthrough store' s' => wp m rest Q store' { s' with values := s.values } host
    | .Break 0 store' s' => wp m rest Q store' { s' with values := s.values } host
    | .Break (k + 1) store' s' => Q (.Break k store' s')
    | other => Q other
  refine wp_block_cons ?_
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  refine wp.conseq (Q := done) ?_ ?_
  · intro c hc
    cases c with
    | Break k _ _ => cases k <;> exact hc
    | _ => exact hc
  refine wp_loop_ghost Inv (current.work parents).steps ⟨heap, current, parents, h, hLocals, rfl⟩ ?_
  rintro n store' s' ⟨heap', current', parents', hInv, hVars, hMeasure⟩
  have hLow' : s'.params.length ≤ base := by
    rw [hVars.frame.params, ← hLocals.frame.params]
    exact hLow
  have hHigh' : base + 6 ≤ s'.positions := by
    rw [hVars.frame.positions, ← hLocals.frame.positions]
    exact hHigh
  refine wp_treeCopyBody hm hInv hVars hLow' hHigh' hCap ?_ ?_ ?_
  · exact hTrap.imp (fun _ h => h)
  · intro heap'' store'' s'' next parents'' hInv' hVars' hWork
    refine ⟨(next.work parents'').steps, ?_, ?_⟩
    · rw [← hMeasure]
      exact hWork.decreases
    · simp only [List.take_zero, List.drop_zero, List.nil_append]
      have hStack : s'.values = s''.values := hVars.values.trans hVars'.values.symm
      rw [hStack]
      exact ⟨heap'', next, parents'', hInv', hVars', rfl⟩
  · intro store'' s'' hOwned hApart hStep hBudget hVars'
    change wp m rest Q store'' { s'' with values := s.values } host
    have hStack : s.values = s''.values := hLocals.values.trans hVars'.values.symm
    rw [hStack]
    exact hNext heap' store'' s'' hOwned hApart hStep hBudget hVars'.frame hVars'.result hVars'.values

#print axioms wp_treeCopyLoop

end Verified
