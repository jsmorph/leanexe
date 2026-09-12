import Project.EulerRiemann.ExecutionInitialStates

namespace Project.EulerRiemann.Execution
open Wasm

local macro "weighted_call" h:term : tactic => `(tactic|
  (wp_run [func86Def, stateValues, List.set, List.length_set, List.getElem?_set,
      reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
   refine wp_call_tw $h ?_
   rintro current values ⟨hStore, hValues⟩
   subst current
   subst values))

theorem weighted_tail_spec (env : HostEnv Unit) (initial : Store Unit) (x y : Fin 6)
    (frame : Locals) (hParams : frame.params.length = 2) (hLocals : frame.locals.length = 102)
    (hValues : frame.values = [.i64 (Initial.weighted x.val y.val).mx])
    (hX : frame.locals[2]? = some (.i64 (Initial.fifths x.val)))
    (hY : frame.locals[5]? = some (.i64 (Initial.fifths y.val)))
    (hDensity : frame.locals[98]? = some (.i64 (Initial.weighted x.val y.val).density))
    (Q : Assertion Unit)
    (hNext : ∀ resultFrame, resultFrame.values = stateValues (Initial.weighted x.val y.val) →
      Q (.Fallthrough initial resultFrame)) :
    wp Project.EulerRiemann.«module» (func86.drop 95) Q initial frame env := by
  unfold func86
  dsimp only
  weighted_call (bottomLeft_exact env initial)
  weighted_call (bottomRight_exact env initial)
  weighted_call (topLeft_exact env initial)
  weighted_call (topRight_exact env initial)
  weighted_call (weightedWord_exact env initial _ _ _ _ _ _)
  weighted_call (bottomLeft_exact env initial)
  weighted_call (bottomRight_exact env initial)
  weighted_call (topLeft_exact env initial)
  weighted_call (topRight_exact env initial)
  weighted_call (weightedWord_exact env initial _ _ _ _ _ _)
  wp_run [stateValues, List.set, List.length_set, List.getElem?_set,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
  apply hNext
  simp [Initial.weighted, stateValues]

theorem weighted_exact (env : HostEnv Unit) (initial : Store Unit) (x y : Fin 6) :
    TerminatesWith env Project.EulerRiemann.«module» 86 initial
      [.i64 (UInt64.ofNat y.val), .i64 (UInt64.ofNat x.val)]
      (fun final values => final = initial ∧ values = stateValues (Initial.weighted x.val y.val)) := by
  refine TerminatesWith.of_wp_entry_for (f := func86Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func86 _ initial
    (func86Def.toLocals [.i64 (UInt64.ofNat x.val), .i64 (UInt64.ofNat y.val)]) env
  unfold func86
  weighted_call (fifths_exact env initial x)
  weighted_call (fifths_exact env initial y)
  weighted_call (bottomLeft_exact env initial)
  weighted_call (bottomRight_exact env initial)
  weighted_call (topLeft_exact env initial)
  weighted_call (topRight_exact env initial)
  weighted_call (weightedWord_exact env initial _ _ _ _ _ _)
  weighted_call (bottomLeft_exact env initial)
  weighted_call (bottomRight_exact env initial)
  weighted_call (topLeft_exact env initial)
  weighted_call (topRight_exact env initial)
  weighted_call (weightedWord_exact env initial _ _ _ _ _ _)
  change wp _ (func86.drop 95) _ initial _ env
  apply weighted_tail_spec env initial x y
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro resultFrame hValues
    simp [hValues, stateValues]

#print axioms weighted_tail_spec
#print axioms weighted_exact

end Project.EulerRiemann.Execution
