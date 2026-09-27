import Project.EulerConservative.StateGuard

namespace Project.EulerConservative.Execution
open Wasm
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

/-- Normalize concrete local frames while consuming determined instructions. -/
macro "side_word_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [boolWord, List.set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
        reduceIte, ite_true, ite_false, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
    | refine wp_iff_cons rfl ?_
      simp [boolWord, *])

theorem sideCheckedBits_rejected_input {m : Wasm.Module}
    (layout : HelperLayout m) (hside : m.funcs[5]? = some func5Def)
    (env : HostEnv Unit) (initial : Store Unit) (rho momentum energy : UInt64)
    (hguard : Model.stateGuard rho momentum energy = false) :
    TerminatesWith env m 5 initial [.i64 energy, .i64 momentum, .i64 rho]
      (fun final values => final = initial ∧
        values = [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func5Def)
    (by simpa [layout.noImports] using hside) ?_ (by simp [layout.noImports])
  change wp m func5 _ initial (func5Def.toLocals [.i64 rho, .i64 momentum, .i64 energy]) env
  unfold func5
  wp_run [func5Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  refine wp_call_tw (stateGuard_exact layout env initial rho momentum energy) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  side_word_peel
  refine wp_call_tw (rejectedSide_exact layout env initial) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  side_word_peel
  simp

#print axioms sideCheckedBits_rejected_input
end Project.EulerConservative.Execution
