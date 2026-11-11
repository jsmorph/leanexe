import Demos.Gate.AssignmentVerified
import Demos.Gate.AssignmentSoundness
import Verified.Call

/-! The call of the module's export `check` and its composition with `check_sound`.
`check_call` states that the export returns `check c perm u v` without a trap from every ready
store, from the generated `compiled.check.implements`.  `assignment_optimal` joins the module's
bytes, the export, the readiness of the start store, the call, and the optimality of an accepted
assignment. -/

namespace Demos.Gate.Assignment

theorem check_export :
    ({ name := "check", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The export `check` returns, without a trap and from every ready store, the result of the
check. -/
theorem check_call :
    _root_.Verified.Call compiled.module compiled.tables 6
      (fun x : Array Int64 × Array UInt64 × Array Int64 × Array Int64 =>
        check x.1 x.2.1 x.2.2.1 x.2.2.2) (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  _root_.Verified.ImplementsTables.call
    (_root_.Verified.ImplementsTables.ofA compiled.check.implements) compiled.tables
    (fun _ h => absurd h List.not_mem_nil)

/-- The module's bytes decode to the module, whose export `check` returns `check c perm u v`
without a trap from every ready store, starting with the store in which the module starts.  When
the check accepts, the proposed assignment is a permutation through allowed pairs whose cost,
`Σ u + Σ v`, is the least of every permutation through allowed pairs. -/
theorem assignment_optimal :
    (∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok compiled.module) ∧
      ({ name := "check", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports ∧
      _root_.Verified.Ready compiled.module compiled.tables
        (_root_.Verified.initialHeap compiled.tables) compiled.module.initialStore ∧
      _root_.Verified.Call compiled.module compiled.tables 6
        (fun x : Array Int64 × Array UInt64 × Array Int64 × Array Int64 =>
          check x.1 x.2.1 x.2.2.1 x.2.2.2) (fun _ _ _ => True) (fun _ _ _ _ _ => True) ∧
      ∀ (c : Array Int64) (perm : Array UInt64) (u v : Array Int64),
        perm.size < 2 ^ 64 ∧ c.size < 2 ^ 64 ∧ u.size < 2 ^ 64 ∧ v.size < 2 ^ 64 →
        (check c perm u v).status = 0 →
        IsPerm perm.size (fun i => (perm[i]!).toNat) ∧
          (∀ i < perm.size, Allowed c perm.size i (perm[i]!).toNat) ∧
          cost c perm.size (fun i => (perm[i]!).toNat) =
            ∑ i ∈ Finset.range perm.size, (u[i]!).toInt +
              ∑ j ∈ Finset.range perm.size, (v[j]!).toInt ∧
          ∀ f, IsPerm perm.size f → (∀ i < perm.size, Allowed c perm.size i (f i)) →
            cost c perm.size (fun i => (perm[i]!).toNat) ≤ cost c perm.size f := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  refine ⟨⟨bytes, henc, hdec⟩, check_export,
    _root_.Verified.Ready.initial rfl compiled.initial, check_call, fun c perm u v hs h => ?_⟩
  obtain ⟨-, -, -, -, -, hp, ha, hc, ho⟩ := check_sound hs h
  exact ⟨hp, ha, hc, ho⟩

#print axioms check_call
#print axioms assignment_optimal

end Demos.Gate.Assignment
