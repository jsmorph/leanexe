import Project.ProofKit.PackedReleaseGuard

namespace Project.ProofKit.PackedReleaseFilter
open Wasm PackedFloatFrame

def check (ownerLocal retainedLocal : Nat) : Instruction :=
  .iff 0 1 [.localGet ownerLocal, .localGet retainedLocal, .eqI64, .eqz] [.const 0] [] [.i32]

def tests (ownerLocal : Nat) (retained : List Nat) : Wasm.Program := retained.map (check ownerLocal)

theorem tests_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (frame : Locals) (ownerLocal : Nat) (owner : UInt64) (retained : List (Nat × UInt64)) (active : Bool)
    (hOwner : frame.get ownerLocal = some (.i64 owner))
    (hRetained : ∀ entry ∈ retained, frame.get entry.1 = some (.i64 entry.2))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store { frame with values :=
      [.i32 (if active && retained.all (fun entry => owner != entry.2) then 1 else 0)] } env) :
    wp module_ (tests ownerLocal (retained.map Prod.fst) ++ rest) Q store
      { frame with values := [.i32 (if active then 1 else 0)] } env := by
  induction retained generalizing active with
  | nil => simpa only [tests, List.map_nil, List.nil_append, List.all_nil, Bool.and_true] using hNext
  | cons entry retained ih =>
    have hHead := hRetained entry (by simp)
    have hTail : ∀ entry ∈ retained, frame.get entry.1 = some (.i64 entry.2) := by
      intro entry hMem
      exact hRetained entry (by simp [hMem])
    have hContinue : wp module_ (tests ownerLocal (retained.map Prod.fst) ++ rest) Q store
        { frame with values := [.i32 (if active && (owner != entry.2) then 1 else 0)] } env := by
      apply ih _ hTail
      simpa only [List.all_cons, ← Bool.and_assoc] using hNext
    simp only [tests, List.map_cons, List.cons_append, check, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    simp only [Locals.get] at hOwner hHead
    cases active <;> by_cases hEq : owner = entry.2 <;>
      simp [wp_simp, hOwner, hHead, hEq, tests] at hContinue ⊢ <;> exact hContinue

#print axioms tests_spec

def program (ownerLocal : Nat) (retained : List Nat) (action : Wasm.Program) : Wasm.Program :=
  [.localGet ownerLocal, .constI64 0, .eqI64, .eqz] ++ tests ownerLocal retained ++ [.iff 0 0 action []]

def afterAction (module_ : Wasm.Module) (env : HostEnv Unit) (rest : Wasm.Program) (Q : Assertion Unit) : Assertion Unit :=
  fun cont => match cont with
    | .Fallthrough store frame => wp module_ rest Q store { frame with values := [] } env
    | .Break 0 store frame => wp module_ rest Q store { frame with values := [] } env
    | .Break (level + 1) store frame => Q (.Break level store frame)
    | other => Q other

theorem program_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (frame : Locals) (ownerLocal : Nat) (owner : UInt64) (retained : List (Nat × UInt64))
    (action : Wasm.Program) (hValues : frame.values = [])
    (hOwner : frame.get ownerLocal = some (.i64 owner))
    (hRetained : ∀ entry ∈ retained, frame.get entry.1 = some (.i64 entry.2))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hTaken : owner ≠ 0 ∧ (∀ entry ∈ retained, owner ≠ entry.2) →
      wp module_ action (afterAction module_ env rest Q) store frame env)
    (hSkip : ¬(owner ≠ 0 ∧ (∀ entry ∈ retained, owner ≠ entry.2)) →
      wp module_ rest Q store frame env) :
    wp module_ (program ownerLocal (retained.map Prod.fst) action ++ rest) Q store frame env := by
  have hFrame : ({ frame with values := [] } : Locals) = frame := Frame.ext _ _ rfl rfl hValues.symm
  have hFlag : (if (if owner = 0 then (1 : UInt32) else 0) = 0 then (1 : UInt32) else 0) =
      (if owner != 0 then 1 else 0) := by by_cases h : owner = 0 <;> simp [h]
  have hOwnerRead := hOwner
  simp only [Locals.get] at hOwnerRead
  simp only [program, List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hValues, hOwnerRead, hFlag]
  apply tests_spec module_ env store frame ownerLocal owner retained (owner != 0) hOwner hRetained
  refine wp_iff_cons rfl ?_
  have hEnabled : ((owner != 0) && retained.all (fun entry => owner != entry.2)) = true ↔
      owner ≠ 0 ∧ (∀ entry ∈ retained, owner ≠ entry.2) := by simp
  by_cases h : ((owner != 0) && retained.all (fun entry => owner != entry.2)) = true
  · simp only [h, ite_true]
    rw [ite_eq_left (by decide)]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    rw [hFrame]
    apply wp.imp (hTaken (hEnabled.mp h))
    intro continuation hCont
    cases continuation with
    | Break level next result => cases level <;> exact hCont
    | _ => exact hCont
  · simpa [wp_simp, h, hFrame] using hSkip (fun enabled => h (hEnabled.mpr enabled))

#print axioms program_spec

end Project.ProofKit.PackedReleaseFilter
