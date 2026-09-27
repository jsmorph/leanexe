import Project.Beck.ExecutionRoundsState

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def roundsPreparedLocals (locals : List Value) (input : Input) (point : Point) (inputRoot pointRoot : UInt64) : List Value :=
  let l := (((locals.set 10 (.i64 input.status)).set 11 (.i64 input.jobs.toUInt64)).set 12 (.i64 input.categories.toUInt64)).set 13 (.i64 input.overlap.toUInt64)
  let l := (((l.set 14 (.i64 inputRoot)).set 15 (.i64 inputRoot)).set 16 (.i64 point.denominator)).set 17 (.i64 pointRoot)
  l.set 18 (.i64 pointRoot)

def roundsReadLocals (locals : List Value) (point : Point) (root : UInt64) : List Value :=
  (((((locals.set 21 (.i64 root)).set 20 (.i64 root)).set 19 (.i64 point.denominator)).set
    22 (.i64 point.denominator)).set 23 (.i64 root)).set 24 (.i64 root)

set_option maxRecDepth 4096 in
theorem roundsPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel : Nat) (input : Input) (point : Point) (inputRoot pointRoot : UInt64) (size : locals.length = 61)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := roundsParams fuel input point inputRoot pointRoot
        locals := roundsPreparedLocals locals input point inputRoot pointRoot
        values := (matrixParams input point inputRoot inputRoot pointRoot pointRoot).reverse })) :
    wp Project.Beck.«module» (roundsAdvancing.take 27) Q initial
      { params := roundsParams fuel input point inputRoot pointRoot, locals := locals } env := by
  simp only [roundsAdvancing, roundsBody, func34, List.getElem?_cons_zero, List.getElem?_cons_succ, List.take]
  wp_run [roundsParams, matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem roundsRead_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (point : Point) (root : UInt64) (paramsSize : params.length = 10) (size : locals.length = 61)
    (nonzero : point.denominator ≠ 0) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := roundsReadLocals locals point root, values := [.i32 0] })) :
    wp Project.Beck.«module» ((roundsAdvancing.drop 28).take 19) Q initial
      { params := params, locals := locals, values := pointValues point root root } env := by
  simp only [roundsAdvancing, roundsBody, func34, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  repeat' first
    | wp_run [pointValues, paramsSize, size, List.length_set, List.getElem?_set,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, nonzero,
        show (1 : UInt64) ≠ 0 by decide, show (0 : UInt64) ≠ 1 by decide, show (1 : UInt32) ≠ 0 by decide,
        ne_eq, not_true_eq_false, not_false_eq_true, List.take, List.drop, List.append_nil, reduceIte]
    | (try simp only [wp_iff_control_types]
       refine wp_iff_cons rfl ?_
       simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  exact next

set_option maxRecDepth 4096 in
theorem rounds_call_shape : roundsAdvancing.take 47 =
    roundsAdvancing.take 27 ++ (.call 33 :: (roundsAdvancing.drop 28).take 19) := rfl

theorem roundsPrepared_state {locals : List Value} {stopped : Bool} {point : Point} {root internal : UInt64}
    (state : RoundsLocals locals stopped point root internal) (input : Input) (inputRoot : UInt64) :
    RoundsLocals (roundsPreparedLocals locals input point inputRoot root) stopped point root internal := by
  apply state.preserved
  · simp [roundsPreparedLocals]
  · intro k bound
    simp (discharger := omega) only [roundsPreparedLocals, List.getElem?_set_ne]

theorem roundsRead_state {locals : List Value} {stopped : Bool} {point : Point} {root internal : UInt64}
    (state : RoundsLocals locals stopped point root internal) (nextPoint : Point) (nextRoot : UInt64) :
    RoundsLocals (roundsReadLocals locals nextPoint nextRoot) stopped point root internal := by
  apply state.preserved
  · simp [roundsReadLocals]
  · intro k bound
    simp (discharger := omega) only [roundsReadLocals, List.getElem?_set_ne]

set_option maxRecDepth 4096 in
theorem roundsCall_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (fuel : Nat) (input : Input) (point : Point) (inputRoot pointRoot : UInt64) (roundNumber remaining pageLimit : Nat)
    (size : locals.length = 61) (valid : heap.At initial) (supported : Project.Beck.State.Supported input)
    (pointValid : Project.Beck.State.Valid input.jobs point roundNumber) (roundBound : roundNumber ≤ 5)
    (nonempty : (Project.Beck.Counting.live input point).Nonempty)
    (pointAt : UInt64Array.At initial pointRoot point.numerators)
    (pointProtected : heap.Protects pointRoot.toNat (pointRoot.toNat + 8 * (point.numerators.size + 1)))
    (inputAt : UInt64Array.At initial inputRoot input.incidence)
    (inputProtected : heap.Protects inputRoot.toNat (inputRoot.toNat + 8 * (input.incidence.size + 1)))
    (inputSize : input.incidence.size = input.jobs * input.categories)
    (categories : input.categories ≤ 8) (overlap : input.overlap ≤ 8)
    (budget : OutputBudget initial heap (roundMaxBytes + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap node, finalHeap.At final →
      finalHeap.OwnsWords final node (LeanExe.Examples.Beck.round input point).numerators →
      heap.Frame initial finalHeap final → FreshFor heap node →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      Q (.Fallthrough final
        { params := roundsParams fuel input point inputRoot pointRoot
          locals := roundsReadLocals (roundsPreparedLocals locals input point inputRoot pointRoot) (LeanExe.Examples.Beck.round input point) node.root
          values := [.i32 0] })) :
    wp Project.Beck.«module» (roundsAdvancing.take 47) Q initial
      { params := roundsParams fuel input point inputRoot pointRoot, locals := locals } env := by
  have nextValid := (Project.Beck.SourceRound.round_valid_progress input point roundNumber supported pointValid roundBound nonempty).1
  have nonzero : (LeanExe.Examples.Beck.round input point).denominator ≠ 0 := by
    intro zero
    have positive := nextValid.positive
    simp [zero] at positive
  rw [rounds_call_shape]
  refine Sequence.wp_append (P := fun store frame => store = initial ∧ frame =
    { params := roundsParams fuel input point inputRoot pointRoot
      locals := roundsPreparedLocals locals input point inputRoot pointRoot
      values := (matrixParams input point inputRoot inputRoot pointRoot pointRoot).reverse }) ?_ ?_
  · exact roundsPrepare_exact env initial locals fuel input point inputRoot pointRoot size _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  refine wp_call_tw (round_exact env initial heap input point inputRoot inputRoot pointRoot pointRoot roundNumber remaining pageLimit
    valid supported pointValid roundBound nonempty pointAt pointProtected inputAt inputProtected inputSize categories overlap budget) ?_
  rintro final values ⟨finalHeap, node, finalValid, finalOwned, finalFrame, fresh, finalBudget, rfl⟩
  apply roundsRead_exact env final _ _ (LeanExe.Examples.Beck.round input point) node.root
    (by simp [roundsParams, matrixParams, inputValues, pointValues]) (by simp [roundsPreparedLocals, size]) nonzero
  exact next final finalHeap node finalValid finalOwned finalFrame fresh finalBudget

#print axioms roundsCall_exact

end Project.Beck.Execution
