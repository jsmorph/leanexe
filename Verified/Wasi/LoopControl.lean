import Verified.TailLoop
import Verified.LocalFrame
import LeanExe.ProofKit.Sequencing
import Verified.AlignedTailLoop

namespace Verified.Wasi

open Wasm

def loopControlCode (countSlot indexSlot : Nat) (test step : Program) : Program :=
  [.block 0 0 [.loop 0 0
    ([.localGet indexSlot, .localGet countSlot, .geUI64, .br_if 1] ++
      test ++ [.eqzI64, .br_if 1] ++ step ++
      [.localGet indexSlot, .constI64 1, .addI64, .localSet indexSlot, .br 0]) [] []] [] []]

def LoopTerminal (Q : Assertion World) : Assertion World
  | .Fallthrough _ _ | .Break _ _ _ | .OutOfFuel => False
  | other => Q other

def LoopTestPost (Q : Assertion World) (ready : UInt64 → Bool → AssertionF World)
    (values : List Value) (index : UInt64) : Assertion World
  | .Fallthrough store locals => ∃ decision : Bool,
      locals.values = .i64 (if decision then 1 else 0) :: values ∧
        ready index decision store { locals with values := values }
  | other => LoopTerminal Q other

def LoopStepPost (Q : Assertion World) (invariant : UInt64 → AssertionF World)
    (values : List Value) (indexSlot : Nat) (index : UInt64) : Assertion World
  | .Fallthrough store locals =>
      locals.values = values ∧ locals.get indexSlot = some (.i64 index) ∧
        locals.params.length ≤ indexSlot ∧ indexSlot < locals.params.length + locals.locals.length ∧
        invariant (index + 1) store (setLocal locals indexSlot (.i64 (index + 1)))
  | other => LoopTerminal Q other

theorem loop_increment_toNat {index count : UInt64} (bound : index < count) :
    (index + 1).toNat = index.toNat + 1 := by
  have less := UInt64.lt_iff_toNat_lt.mp bound
  have size := count.toNat_lt
  rw [UInt64.toNat_add]
  change (index.toNat + 1) % 2 ^ 64 = index.toNat + 1
  exact Nat.mod_eq_of_lt (by omega)

theorem loop_rank_decreases {index count : UInt64} (bound : index < count) :
    count.toNat - (index + 1).toNat < count.toNat - index.toNat := by
  rw [loop_increment_toNat bound]
  have less := UInt64.lt_iff_toNat_lt.mp bound
  omega

theorem wp_loopControl {World : Type} {m : Module} {host : HostEnv World}
    {store : Store World} {locals : Locals} {count : UInt64} {countSlot indexSlot : Nat}
    {test step rest : Program} {Q : Assertion World} {values : List Value}
    (invariant : UInt64 → AssertionF World) (ready : UInt64 → Bool → AssertionF World)
    (initial : invariant 0 store locals)
    (shape : ∀ index state frame, invariant index state frame →
      index ≤ count ∧ frame.get countSlot = some (.i64 count) ∧
        frame.get indexSlot = some (.i64 index) ∧ frame.values = values)
    (testRun : ∀ index state frame, invariant index state frame → index < count →
      wp m test (LoopTestPost Q ready values index) state frame host)
    (stepRun : ∀ index state frame, ready index true state frame → index < count →
      wp m step (LoopStepPost Q invariant values indexSlot index) state frame host)
    (done : ∀ state frame, invariant count state frame → wp m rest Q state frame host)
    (stopped : ∀ index state frame, ready index false state frame →
      wp m rest Q state frame host) :
    wp m (loopControlCode countSlot indexSlot test step ++ rest) Q store locals host := by
  have initialStack := (shape 0 store locals initial).2.2.2
  let outside : Assertion World := fun continuation => match continuation with
    | .Fallthrough state frame | .Break 0 state frame =>
        wp m rest Q state { frame with values := values } host
    | .Break (label + 1) state frame => Q (.Break label state frame)
    | other => Q other
  simp only [loopControlCode, List.append_assoc, List.cons_append, List.nil_append]
  apply wp_block_cons
  simp only [List.take_zero, List.drop_zero, List.nil_append, initialStack]
  change wp m [.loop 0 0 _ [] []] outside store locals host
  refine Tail.wp_loop_indexed (Inv := invariant)
    (rank := fun index => count.toNat - index.toNat) initial ?_
  intro index state frame inv
  obtain ⟨bound, countLocal, indexLocal, stack⟩ := shape index state frame inv
  let post : Assertion World := fun continuation => match continuation with
    | .Fallthrough final after => wp m [] outside final { after with values := values } host
    | .Break 0 final after =>
        ∃ next, invariant next final { after with values := values } ∧
          count.toNat - next.toNat < count.toNat - index.toNat
    | .Break (label + 1) final after => outside (.Break label final after)
    | other => outside other
  simp only [List.take_zero, List.drop_zero, List.nil_append, stack]
  change wp m _ post state frame host
  simp only [wp_localGet_cons, Locals.get_values, indexLocal, countLocal,
    wp_geUI64_cons, wp_br_if_cons]
  by_cases complete : count ≤ index
  · have same : index = count := UInt64.le_antisymm bound complete
    subst index
    simp (config := { decide := true }) only [ge_iff_le, complete, ↓reduceIte]
    change wp m rest Q state { frame with values := values } host
    rw [← stack]
    exact done state frame inv
  · have less : index < count := by
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [UInt64.le_iff_toNat_le] at complete
      omega
    simp (config := { decide := true }) only [ge_iff_le, complete, ↓reduceIte]
    change wp m (test ++ _ ) post state { frame with values := frame.values } host
    apply wp_append
    refine wp.conseq (fun continuation result => ?_) (testRun index state frame inv less)
    cases continuation with
    | Fallthrough final after =>
        obtain ⟨decision, testedStack, tested⟩ := result
        change wp m ([.eqzI64, .br_if 1] ++ step ++ _) post final after host
        cases decision with
        | false =>
            simp (config := { decide := true }) only [List.cons_append, List.nil_append,
              wp_eqzI64_cons, testedStack, wp_br_if_cons, ↓reduceIte]
            exact stopped index final _ tested
        | true =>
            simp (config := { decide := true }) only [List.cons_append, List.nil_append,
              wp_eqzI64_cons, testedStack, wp_br_if_cons, ↓reduceIte]
            apply wp_append
            refine wp.conseq (fun continuation result => ?_)
              (stepRun index final _ tested less)
            cases continuation with
            | Fallthrough final after =>
                obtain ⟨afterStack, afterIndex, low, high, next⟩ := result
                change wp m [.localGet indexSlot, .constI64 1, .addI64,
                  .localSet indexSlot, .br 0] post final after host
                simp only [wp_localGet_cons, afterIndex, wp_constI64_cons, wp_addI64_cons]
                refine wp_localSet_local (s := after) (vs := after.values) low high ?_
                rw [wp_br_cons]
                refine ⟨index + 1, ?_, loop_rank_decreases less⟩
                change invariant (index + 1) final
                  { setLocal after indexSlot (.i64 (index + 1)) with values := values }
                rw [← afterStack]
                exact next
            | Break => exact result.elim
            | OutOfFuel => exact result.elim
            | _ => exact result
    | Break => exact result.elim
    | OutOfFuel => exact result.elim
    | _ => exact result

end Verified.Wasi
