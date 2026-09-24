import Project.ClobFindBest.SearchRead
import Project.ClobFindBest.SearchDecision
import Project.ClobFindBest.SearchAdvance

namespace Project.ClobFindBest.SearchStep
open Wasm Project.Common Project.Clob Project.ClobFindBest.Model Project.ClobFindBest.Helpers
  Project.ClobFindBest.SearchFrame Project.ClobFindBest.SearchProgram
  Project.ClobFindBest.SearchDecision Project.ClobFindBest.SearchAdvance
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem step_spec (m : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (eligibleId releaseId : Nat) (base : Locals) (fuel owner ptr : UInt64)
    (os : List OrderL) (taker : OrderL) (k : Nat) (best : Option Nat)
    (hParams : base.params = params fuel owner ptr taker k best)
    (hLocals : base.locals.length = 56) (hValues : base.values = [])
    (hOwner : base.locals[0]? = some (.i64 0))
    (hLength : os.length < 4294967296) (hk : k < os.length)
    (hBest : ∀ j, best = some j → j < k) (hInput : OrdersAt st ptr os)
    (hEligible : TerminatesWith env m eligibleId st
      [.i64 os[k]!.oqty, .i64 os[k]!.oprice, .i64 os[k]!.oside,
        .i64 os[k]!.otrader, .i64 os[k]!.oid, .i64 taker.oqty, .i64 taker.oprice,
        .i64 taker.oside, .i64 taker.otrader, .i64 taker.oid]
      (fun st1 vs => vs = [.i64 (boolWord (eligibleL taker os[k]!))] ∧ st1 = st))
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final, AdvanceFrame base final fuel owner ptr taker k (bestStepL os taker k best) →
      wp m rest Q st final env) :
    wp m ((readCandidate ++ decision true eligibleId ++ [.localSet 41] ++
      decision false eligibleId ++ [.localSet 42] ++ advance releaseId) ++ rest) Q st base env := by
  simp only [List.append_assoc]
  apply SearchRead.read_spec m env st base fuel owner ptr os taker k best
    hParams hLocals hValues hLength hk hInput
  intro loaded hRead
  have hP := hRead.params.trans hParams
  have hL := hRead.locals
  apply decision_spec m env st eligibleId true loaded fuel owner ptr os taker k best
    hP hL hRead.values hRead.candidate hLength hk hBest hInput hEligible
  intro tagged hTag
  have hTaggedP := hTag.params.trans hP
  have hTaggedL := hTag.locals
  simp only [List.cons_append, List.nil_append]
  wp_run_with [hTaggedP, params, hTaggedL, hTag.values, selectedWord]
  let tagBase : Locals :=
    { params := params fuel owner ptr taker k best
      locals := tagged.locals.set 30 (.i64 (optionTag (bestStepL os taker k best)))
      values := [] }
  have hTagCandidate := hRead.candidate.frame hTag
  have hTagBaseCandidate : Candidate tagBase os[k]! := by
    constructor <;> simp only [tagBase, List.getElem?_set, Nat.reduceEqDiff, if_false]
    · exact hTagCandidate.oid
    · exact hTagCandidate.trader
    · exact hTagCandidate.side
    · exact hTagCandidate.price
    · exact hTagCandidate.qty
  change wp m (decision false eligibleId ++ _) _ st tagBase env
  apply decision_spec m env st eligibleId false tagBase fuel owner ptr os taker k best
    rfl (by simp [tagBase, hTaggedL]) rfl hTagBaseCandidate hLength hk hBest hInput hEligible
  intro selected hPayload
  have hSelectedP : selected.params = params fuel owner ptr taker k best := hPayload.params
  have hSelectedL := hPayload.locals
  wp_run_with [hSelectedP, params, hSelectedL, hPayload.values, selectedWord]
  let ready : Locals :=
    { params := params fuel owner ptr taker k best
      locals := selected.locals.set 31 (.i64 (optionPayload (bestStepL os taker k best)))
      values := [] }
  have hKept (i : Nat) (hi : i < 4) : ready.locals[i]? = base.locals[i]? := by
    simp only [ready, List.getElem?_set, show ¬31=i by omega, if_false]
    rw [hPayload.kept i (by omega)]
    simp only [tagBase, List.getElem?_set, show ¬30=i by omega, if_false]
    rw [hTag.kept i (by omega), hRead.kept i hi]
  change wp m (advance releaseId ++ rest) Q st ready env
  apply advance_spec m env st releaseId ready fuel owner ptr taker k best (bestStepL os taker k best)
    rfl (by simp [ready, hSelectedL]) rfl (by rw [hKept 0 (by omega)]; exact hOwner)
    (by
      simp only [ready, List.getElem?_set, Nat.reduceEqDiff, if_false]
      rw [hPayload.kept 30 (by omega)]
      simp [tagBase, hTaggedL])
    (by simp [ready, hSelectedL]) (by omega)
  intro final hFinal
  apply hNext final
  refine ⟨hFinal.params, hFinal.locals, hFinal.values, hFinal.owner, ?_⟩
  intro i hLow hHigh
  exact (hFinal.kept i hLow hHigh).trans (hKept i (by omega))

#print axioms step_spec
end Project.ClobFindBest.SearchStep
