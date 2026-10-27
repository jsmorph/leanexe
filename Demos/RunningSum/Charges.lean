import Demos.RunningSum.Limits
import Demos.RunningSum.Module
import Verified.LoopCostLast
import Verified.Wasi.ResourceRules

/-! The allocation charges of the integer running sum's `begin` and steps, and their bounds for
states within the limits. -/

namespace Demos.RunningSum

open Verified Verified.Wasi Verified.Wasi.Resource LeanExe LeanExe.Wasi
open Demos.StreamFold (StreamPosition StreamHost observedStreamRep)

theorem allocationCost_le (count : Nat) : Bytes.allocationCost count ≤ count + 55 := by
  unfold Bytes.allocationCost
  split
  · omega
  · rw [Nat.max_def]
    split <;> omega

theorem allocationCost_mono {small large : Nat} (le : small ≤ large) :
    Bytes.allocationCost small ≤ Bytes.allocationCost large := by
  unfold Bytes.allocationCost
  split
  · omega
  · split
    · omega
    · rw [Nat.max_def, Nat.max_def]
      split <;> split <;> omega

/-- The bytes of a copy of a state whose total has `total` digits, whose line has `line` words,
and whose buffers have `input` and `output` bytes. -/
def copyBytes (total line input output : Nat) : Nat :=
  8 * total + 8 * line + Bytes.allocationCost input + Bytes.allocationCost output + 112

theorem state_copyCost (state : State) :
    stateTy.copyCost (sourceState state) = copyBytes state.total.digits.size state.line.size
      state.input.data.size state.output.data.size := by
  simp only [stateTy, sourceState, Ty.copyCost, Elem.width, copyBytes, allocCost]
  omega

/-- A bound on the copy of a state within the limits. -/
def copyLimit (L D : Nat) : Nat := 9 * D + 8 * L + 4320

theorem Sized.copyCost {L D : Nat} {state : State} (sized : Sized L D state) :
    stateTy.copyCost (sourceState state) ≤ copyLimit L D := by
  rw [state_copyCost]
  have input := allocationCost_le state.input.data.size
  have output := allocationCost_le state.output.data.size
  have := sized.total
  have := sized.line
  have := sized.input
  have := sized.output
  unfold copyBytes copyLimit
  omega

theorem finishDigits_size_le (raw : Array UInt64) (bound : raw.size < UInt64.size) :
    (Magnitude.finishDigits raw).size ≤ raw.size := by
  have trimmed := (Magnitude.trimSize_spec raw raw.size).1
  unfold Magnitude.finishDigits
  rw [Magnitude.reverseAscii_size raw _ (by omega)]
  exact trimmed

theorem fold_push_size {α β : Type} {F : UInt64 → Array α × β → Array α × β}
    (pushes : ∀ i state, (F i state).1.size = state.1.size + 1) (init : Array α × β) :
    ∀ count : Nat,
      (Nat.fold count (fun i _ state => F (UInt64.ofNat i) state) init).1.size =
        init.1.size + count
  | 0 => by simp
  | count + 1 => by
      simp only [Nat.fold_succ, pushes, fold_push_size pushes init count]
      omega

theorem loop_push_size {α β : Type} {F : UInt64 → Array α × β → Array α × β}
    (pushes : ∀ i state, (F i state).1.size = state.1.size + 1) (count : UInt64)
    (init : Array α × β) : (LeanExe.loop count init F).1.size = init.1.size + count.toNat :=
  fold_push_size pushes init count.toNat

theorem repeatWhile_pred_le (fuel start : UInt64) (cond : UInt64 → Bool)
    (positive : ∀ size, cond size = true → 0 < size.toNat) :
    (LeanExe.repeatWhile fuel start cond (fun size => size - 1)).toNat ≤ start.toNat := by
  unfold LeanExe.repeatWhile
  generalize fuel.toNat = steps
  induction steps generalizing start with
  | zero => simp [LeanExe.repeatWhile.go]
  | succ steps ih =>
      simp only [LeanExe.repeatWhile.go]
      split
      · rename_i holds
        have startPositive := positive start holds
        have one : (1 : UInt64) ≤ start :=
          UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_one]; omega)
        have previous := ih (start - 1)
        rw [UInt64.toNat_sub_of_le _ _ one] at previous
        omega
      · exact Nat.le_refl _

theorem combineMagnitude_size_le (a b : Array UInt64) (subtract : Bool)
    (bound : max a.size b.size + 1 < UInt64.size) :
    (combineMagnitude a b subtract).size ≤ max a.size b.size + 1 := by
  rw [combineMagnitude_eq a b subtract bound]
  dsimp only
  split
  · refine le_trans (finishDigits_size_le _ ?_) ?_ <;>
      simp only [Array.size_push, Magnitude.digitPrefix_size] <;> omega
  · refine le_trans (finishDigits_size_le _ ?_) ?_ <;>
      simp only [Magnitude.digitPrefix_size] <;> omega

theorem add_digits_le (a b : Decimal)
    (bound : max a.digits.size b.digits.size + 1 < UInt64.size) :
    (add a b).digits.size ≤ max a.digits.size b.digits.size + 1 := by
  unfold add
  split
  · exact combineMagnitude_size_le _ _ _ bound
  · split
    · have := combineMagnitude_size_le b.digits a.digits true (by omega)
      change (combineMagnitude b.digits a.digits true).size ≤ _
      omega
    · exact combineMagnitude_size_le _ _ _ bound

theorem blockCost_le_of_le {small large : Nat} (le : small ≤ large) :
    blockCost small ≤ blockCost large := by
  rw [blockCost_eq, blockCost_eq]
  omega

theorem parse_bound_le (line : Array UInt64) (bound : line.size < UInt64.size) :
    io.pureSources.parse.bound line ≤ blockCost line.size := by
  have digits := parse_digits_size_le line bound
  unfold parse at digits
  simp only [LeanExe.IR.build_size] at digits
  rw [io.pureSources.parse.bound_eq]
  exact blockCost_le_of_le digits

theorem render_bound_le (value : Decimal) (fits : value.digits.size + 2 < UInt64.size) :
    io.pureSources.render.bound value ≤ value.digits.size + 57 := by
  have sizeNat : value.digits.size.toUInt64.toNat = value.digits.size :=
    UInt64.toNat_ofNat_of_lt' (by omega)
  rw [io.pureSources.render.bound_eq]
  split
  · have cost := allocationCost_le 2
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
    omega
  · have cost := allocationCost_le
      (value.digits.size.toUInt64 + (if value.negative then 1 else 0) + 1).toNat
    have length : (value.digits.size.toUInt64 + (if value.negative then (1 : UInt64) else 0) +
        1).toNat ≤ value.digits.size + 2 := by
      cases value.negative <;> simp [UInt64.toNat_add, sizeNat] <;> omega
    omega

theorem remainingOutput_bound_le (state : State) (pending : state.written < state.output.size) :
    io.pureSources.remainingOutput.bound state ≤ Bytes.allocationCost state.output.data.size := by
  rw [io.pureSources.remainingOutput.bound_eq]
  apply allocationCost_mono
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt pending)]
  have size : state.output.size.toNat ≤ state.output.data.size := by
    simp only [LeanExe.Bytes.size, UInt64.toNat_ofNat']
    exact Nat.mod_le _ _
  omega

theorem afterWrite_bound_le (state : State) (reply : WriteResult) :
    io.pureSources.afterWrite.bound (state, reply) ≤ stateTy.copyCost (sourceState state) := by
  rw [io.pureSources.afterWrite.bound_eq, state_copyCost]
  simp only [LeanExe.Pipeline.Flat.flat, Ty.copyCost, blockCost_eq, copyBytes]
  split
  · omega
  · split <;> omega

theorem afterRead_bound_le (state : State) (reply : ReadResult) :
    io.pureSources.afterRead.bound (state, reply) ≤ stateTy.copyCost (sourceState state) +
      copyBytes state.total.digits.size state.line.size reply.bytes.data.size
        state.output.data.size := by
  rw [io.pureSources.afterRead.bound_eq, state_copyCost]
  unfold afterRead
  split <;>
    simp only [LeanExe.Pipeline.Flat.flat, Ty.copyCost, blockCost_eq, copyBytes] <;>
    omega

/-- The charge of `begin`: the initial state's arrays. -/
def beginCharge : Nat := io.pureSources.initial.bound ()

theorem beginCharge_le : beginCharge ≤ 4320 := by
  unfold beginCharge
  rw [io.pureSources.initial.bound_eq, io.pureSources.zero.bound_eq]
  simp only [blockCost_eq, UInt64.reduceToNat]
  omega

theorem max_toNat_le (a b : Array UInt64) (bound : a.size + b.size < UInt64.size) :
    (max a.size.toUInt64 b.size.toUInt64).toNat ≤ a.size + b.size := by
  have aNat : a.size.toUInt64.toNat = a.size := UInt64.toNat_ofNat_of_lt' (by omega)
  have bNat : b.size.toUInt64.toNat = b.size := UInt64.toNat_ofNat_of_lt' (by omega)
  change (if a.size.toUInt64 ≤ b.size.toUInt64 then b.size.toUInt64 else a.size.toUInt64).toNat ≤ _
  split <;> omega

theorem toUInt64_toNat_le (n : Nat) : n.toUInt64.toNat ≤ n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_le _ _

theorem ite_zero_le (condition : Prop) [Decidable condition] (x : Nat) :
    (if condition then x else 0) ≤ x := by
  split <;> omega

theorem ite_push_size_le {α : Type} (condition : Prop) [Decidable condition] (xs : Array α)
    (x : α) : (if condition then xs.push x else xs).size ≤ xs.size + 1 := by
  split <;> simp

/-- A bound on `combineMagnitude`'s charge for arrays of `m` words in all. -/
def combineCost (m : Nat) : Nat := 104 * m + 232

theorem combineMagnitude_bound_le (a b : Array UInt64) (subtract : Bool)
    (bound : a.size + b.size + 2 < UInt64.size) :
    io.pureSources.combineMagnitude.bound (a, (b, subtract)) ≤ combineCost (a.size + b.size) := by
  have count := max_toNat_le a b (by omega)
  rw [io.pureSources.combineMagnitude.bound_eq]
  refine le_trans (Nat.add_le_add_right (Nat.min_le_right _ _) _) ?_
  refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (ite_zero_le _ _) _) _) ?_
  refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left (blockCost_le_of_le
    (le_trans (repeatWhile_pred_le _ _ _ ?positive)
      (le_trans (toUInt64_toNat_le _) (ite_push_size_le _ _ _)))) _) _) ?_
  case positive =>
    intro size holds
    simp only [Bool.and_eq_true, decide_eq_true_eq] at holds
    exact UInt64.lt_iff_toNat_lt.mp holds.1
  rw [loopCost_const, loop_push_size]
  · simp only [List.size_toArray, List.length_nil, Nat.zero_add, blockCost_eq, creditCost,
    paidGrowCost, growCost, allocCost, UInt64.toNat_zero]
    unfold combineCost
    omega
  · intro i state
    simp

/-- A bound on `add`'s charge for totals of `m` digits in all. -/
theorem add_bound_le (a b : Decimal) (bound : a.digits.size + b.digits.size + 2 < UInt64.size) :
    io.pureSources.add.bound (a, b) ≤ combineCost (a.digits.size + b.digits.size) := by
  rw [io.pureSources.add.bound_eq]
  split
  · exact combineMagnitude_bound_le _ _ _ bound
  · split
    · have := combineMagnitude_bound_le b.digits a.digits true (by omega)
      unfold combineCost at this ⊢
      omega
    · exact combineMagnitude_bound_le _ _ _ bound

/-- A bound on `completeLine`'s charge for a state whose total has `t` digits and whose line,
input, and output have `l`, `i`, and `o` bytes. -/
def completeCost (t l i o : Nat) : Nat :=
  8 * l + 56 + copyBytes t l i o + combineCost (t + l) + (8 * (t + l + 1) + 56) + 56 +
    Bytes.allocationCost i + (t + l + 58)

theorem completeLine_bound_le (state : State)
    (small : state.total.digits.size + state.line.size + 4 < UInt64.size) :
    io.pureSources.completeLine.bound state ≤ completeCost state.total.digits.size
      state.line.size state.input.data.size state.output.data.size := by
  have parsed := parse_digits_size_le state.line (by omega)
  have sum := add_digits_le state.total
    ⟨(parse state.line).value.negative, (parse state.line).value.digits⟩ (by dsimp only; omega)
  dsimp only at sum
  have parseCost := parse_bound_le state.line (by omega)
  have addCost := add_bound_le state.total
    ⟨(parse state.line).value.negative, (parse state.line).value.digits⟩ (by dsimp only; omega)
  have renderCost := render_bound_le
    ⟨(add state.total
        ⟨(parse state.line).value.negative, (parse state.line).value.digits⟩).negative,
      (add state.total
        ⟨(parse state.line).value.negative, (parse state.line).value.digits⟩).digits⟩
    (by dsimp only; omega)
  dsimp only at addCost renderCost
  rw [blockCost_eq] at parseCost
  rw [io.pureSources.completeLine.bound_eq]
  simp only [LeanExe.Pipeline.Flat.flat, Ty.copyCost, blockCost_eq, UInt64.toNat_zero]
  unfold completeCost copyBytes combineCost at *
  split <;> omega

/-- The credits of the state that `completeLine` returns. -/
theorem completeLine_credit_le (state : State)
    (small : state.total.digits.size + state.line.size + 4 < UInt64.size) :
    creditCost (completeLine state).state.total.digits.size +
        creditCost (completeLine state).state.line.size ≤
      16 * (2 * (state.total.digits.size + state.line.size) + 3) := by
  have parsed := parse_digits_size_le state.line (by omega)
  have sum := add_digits_le state.total (parse state.line).value (by omega)
  unfold completeLine creditCost
  dsimp only
  split <;> dsimp only
  · omega
  · simp only [List.size_toArray, List.length_nil]
    omega

/-- A bound on `consumeInput`'s charge for a state whose total has `t` digits and whose line,
input, and output have `l`, `i`, and `o` bytes. -/
def consumeCost (t l i o : Nat) : Nat :=
  copyBytes t l i o + 16 * (t + l + 2) + 80 * i + completeCost t (l + i) i o +
    16 * (2 * (t + l + i) + 3)

theorem consumeInput_bound_le (state : State) (remaining : state.cursor < state.input.size)
    (small : state.total.digits.size + state.line.size + state.input.data.size + 4 < UInt64.size) :
    io.pureSources.consumeInput.bound state ≤ consumeCost state.total.digits.size
      state.line.size state.input.data.size state.output.data.size := by
  have count : (state.input.size - state.cursor).toNat ≤ state.input.data.size := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt remaining)]
    have size : state.input.size.toNat ≤ state.input.data.size := by
      simp only [LeanExe.Bytes.size, UInt64.toNat_ofNat']
      exact Nat.mod_le _ _
    omega
  rw [io.pureSources.consumeInput.bound_eq]
  refine le_trans (Nat.min_le_right _ _) ?_
  refine le_trans (Nat.add_le_add_left (loopCost_le_last
    (fun left (current : ProcessStep State) => current.running = true ∧
      current.state.total = state.total ∧ current.state.input = state.input ∧
      current.state.output = state.output ∧
      current.state.line.size + left ≤ state.line.size + (state.input.size - state.cursor).toNat)
    80 (completeCost state.total.digits.size (state.line.size + state.input.data.size)
      state.input.data.size state.output.data.size +
      16 * (2 * (state.total.digits.size + state.line.size + state.input.data.size) + 3))
    ?pass _ _ _ ?start) _) ?_
  case start => exact ⟨rfl, rfl, rfl, rfl, Nat.le_refl _⟩
  case pass =>
    intro left index current holds _
    obtain ⟨running, total, input, output, line⟩ := holds
    simp only [LeanExe.Pipeline.Flat.flat]
    by_cases newline : current.state.input.get current.state.cursor = 10
    · right
      have isNewline : (current.state.input.get current.state.cursor == 10) = true := by
        simpa using newline
      simp only [isNewline, ↓reduceIte]
      have lineSize : current.state.line.size ≤ state.line.size + state.input.data.size := by
        omega
      have advanced :
          ({ current.state with cursor := current.state.cursor + 1 } : State).total.digits.size +
            ({ current.state with cursor := current.state.cursor + 1 } : State).line.size + 4 <
            UInt64.size := by
        dsimp only
        rw [total]
        omega
      refine ⟨?_, ?_⟩
      · have bound := completeLine_bound_le
          { current.state with cursor := current.state.cursor + 1 } advanced
        have credit := completeLine_credit_le
          { current.state with cursor := current.state.cursor + 1 } advanced
        show io.pureSources.completeLine.bound
            { current.state with cursor := current.state.cursor + 1 } +
          (creditCost (completeLine
              { current.state with cursor := current.state.cursor + 1 }).state.total.digits.size +
            (creditCost (completeLine
              { current.state with cursor := current.state.cursor + 1 }).state.line.size +
              (Ty.credit .bytes _ + Ty.credit .bytes _))) ≤ _
        simp only [Ty.credit, Nat.add_zero]
        dsimp only at bound credit
        have totalSize : current.state.total.digits.size = state.total.digits.size := by rw [total]
        have inputSize : current.state.input.data.size = state.input.data.size := by rw [input]
        have outputSize : current.state.output.data.size = state.output.data.size := by rw [output]
        rw [totalSize, inputSize, outputSize] at bound
        rw [totalSize] at credit
        unfold completeCost copyBytes combineCost at *
        omega
      · have sumSmall := add_digits_le current.state.total (parse current.state.line).value
          (by have := parse_digits_size_le current.state.line (by omega); rw [total]; omega)
        have parsed := parse_digits_size_le current.state.line (by omega)
        unfold completeLine
        dsimp only
        split
        · rfl
        · rw [total] at sumSmall
          have fits : (add current.state.total (parse current.state.line).value).Fits := by
            change _ + 2 < UInt64.size
            rw [total]
            omega
          have positive := render_nonempty _ fits
          have below := render_size_lt _ fits
          have sizeNat := LeanExe.Bytes.size_toNat
            (render (add current.state.total (parse current.state.line).value)) below
          have nonzero :
              (render (add current.state.total (parse current.state.line).value)).size ≠ 0 := by
            intro zero
            have zeroNat := congrArg UInt64.toNat zero
            rw [sizeNat, UInt64.toNat_zero] at zeroNat
            omega
          simp [nonzero]
    · left
      have notNewline : (current.state.input.get current.state.cursor == 10) = false := by
        simpa using newline
      simp only [notNewline, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      simp only [Array.size_push, total, input, output, true_and, paidGrowCost, allocCost]
      omega
  · simp only [LeanExe.Pipeline.Flat.flat, Ty.copyCost, Ty.credit, blockCost_eq, creditCost]
    unfold consumeCost copyBytes
    omega

section Bodies

local notation "pureContext" => Resource.PureContext.ofProg io.pure.program io.pure.funs

/-- Proves that a condition of an effect body finds its frames: it calls no function that takes
the call depth. -/
local macro "condition_fits" : tactic =>
  `(tactic| exact Expr.fits_of_depthCalls _ _ _ (by decide) _)

theorem stepModes : entryModes io.step.func.params io.step.func.modes = [.borrowed] := by
  decide

theorem readModes : entryModes io.readStep.func.params io.readStep.func.modes = [.borrowed] := by
  decide

theorem writeModes : entryModes io.writeStep.func.params io.writeStep.func.modes = [.borrowed] := by
  decide

/-- The charge of the write step from `state`: the remaining output and a copy of the state. -/
def writeCharge (state : State) : Nat :=
  io.pureSources.remainingOutput.bound state + stateTy.copyCost (sourceState state)

/-- The charge of the read step from `state`: the read and the copies of the state and of the
state with the bytes read. -/
def readCharge (state : State) : Nat :=
  Verified.Wasi.readCost 4096 + (stateTy.copyCost (sourceState state) +
    copyBytes state.total.digits.size state.line.size 4096 state.output.data.size)

/-- The charge of the step from `state` at the end of the input. -/
def endCharge (state : State) : Nat :=
  if state.line.size.toUInt64 = 0 then stateTy.copyCost (sourceState state)
  else io.pureSources.completeLine.bound state

/-- The charge of the step from `state` when no output is pending. -/
def inputCharge (state : State) : Nat :=
  if state.cursor < state.input.size then io.pureSources.consumeInput.bound state
  else if state.eof = true then endCharge state else readCharge state

/-- The charge of the step from `state`, by its branches. -/
def stepBudget (state : State) : Nat :=
  if state.written < state.output.size then writeCharge state else inputCharge state

set_option maxHeartbeats 4000000 in
theorem writeStep_bounded {World : Type} (host : Host World) (depth : UInt64) (state : State) :
    Bounded host pureContext .nil depth
      (entryModes io.writeStep.func.params io.writeStep.func.modes) (fun _ => false)
      io.writeStep.func.body (.cons (sourceState state) .nil) (writeCharge state) := by
  rw [writeModes]
  apply bounded_of_rule
  intro spent fits rule
  refine rule (io.pureSources.remainingOutput.bound state) (stateTy.copyCost (sourceState state))
    (Nat.le_refl _) ?_ ?_
  · apply bounded_of_rule
    intro spent fits rule
    refine rule (io.pureSources.remainingOutput.bound state) 0 (Nat.le_of_eq (Nat.add_zero _)) ?_ ?_
    · apply bounded_of_rule
      intro spent fits rule
      refine rule ?_ rfl
      simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg,
        Expr.allocs, Var.cost, Expr.mode, argsSum, callCredits, ↓reduceIte, Nat.add_zero,
        Nat.zero_add, coerceCost]
      show io.pureSources.remainingOutput.bound state ≤ _
      exact Nat.le_refl _
    · intro value _
      apply bounded_of_rule
      intro spent fits rule
      exact rule
  · intro value _
    apply bounded_of_rule
    intro spent fits rule
    refine rule ?_ rfl
    simp only [bindModes, ResultTy.bindEnv]
    simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg, Expr.allocs,
      Var.cost, Expr.mode, argsSum, callCredits, Args.get_cons_zero', Args.get_cons_succ,
      Ty.copyCost_of_scalar, ↓reduceIte, Nat.add_zero, Nat.zero_add, coerceCost]
    show io.pureSources.afterWrite.bound (state, ⟨value.1, value.2⟩) ≤ _
    exact afterWrite_bound_le state _

set_option maxHeartbeats 4000000 in
theorem readStep_bounded {World : Type} (host : Host World) (depth : UInt64) (state : State) :
    Bounded host pureContext (.cons io.writeStep.func .nil) depth
      (entryModes io.readStep.func.params io.readStep.func.modes) (fun _ => false)
      io.readStep.func.body (.cons (sourceState state) .nil) (readCharge state) := by
  rw [readModes]
  apply bounded_of_rule
  intro spent fits rule
  refine rule (Verified.Wasi.readCost 4096) _ (Nat.le_refl _) ?_ ?_
  · apply bounded_of_rule
    intro spent fits rule
    refine rule ?_ rfl
    simp +decide only [PureContext.readCost, PureContext.exprCost, PureContext.ofProg, Expr.allocs,
      Var.cost, ↓reduceIte, Nat.add_zero, Nat.zero_add]
    show Verified.Wasi.readCost 4096 ≤ _
    exact Nat.le_refl _
  · intro value returns
    have size : value.2.data.size ≤ 4096 := Returns.read_size returns
    apply bounded_of_rule
    intro spent fits rule
    refine rule ?_ rfl
    simp only [bindModes, ResultTy.bindEnv]
    simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg, Expr.allocs,
      Var.cost, Expr.mode, argsSum, callCredits, ↓reduceIte, Nat.add_zero, Nat.zero_add, coerceCost]
    show io.pureSources.afterRead.bound (state, ⟨value.1, value.2⟩) ≤ _
    refine le_trans (afterRead_bound_le state _) ?_
    have bytes := allocationCost_mono size
    dsimp only
    unfold copyBytes
    omega

set_option maxHeartbeats 4000000 in
theorem step_body_bounded {World : Type} (host : Host World) (state : State) :
    Bounded host pureContext (.cons io.readStep.func (.cons io.writeStep.func .nil)) 0
      (entryModes io.step.func.params io.step.func.modes) (fun _ => false) io.step.func.body
      (.cons (sourceState state) .nil) (stepBudget state) := by
  rw [stepModes]
  apply bounded_of_rule
  intro spent fits rule
  refine rule (writeCharge state) (inputCharge state) ?_ rfl ?_ ?_
  · simp +decide only [PureContext.exprCost, PureContext.ofProg, Expr.allocs, Var.cost, ↓reduceIte,
    Nat.add_zero, Nat.zero_add]
    show (if decide (state.written < state.output.size) = true then writeCharge state
      else inputCharge state) ≤ stepBudget state
    simp only [stepBudget, decide_eq_true_eq, Nat.le_refl]
  · intro _
    apply bounded_of_rule
    intro spent fits rule
    refine rule (writeCharge state) ?_ rfl ?_
    · simp +decide only [PureContext.argumentCost, PureContext.exprCost, PureContext.ofProg,
      argsSum, ↓reduceIte, Nat.add_zero, Nat.zero_add]
      exact Nat.le_refl _
    · show CallBounded host pureContext (.cons io.readStep.func (.cons io.writeStep.func .nil))
        (.there .here) (0 + 1) (.cons (sourceState state) .nil) (writeCharge state)
      exact callBounded_there (callBounded_here (by decide) (writeStep_bounded host _ state))
  · intro _
    apply bounded_of_rule
    intro spent fits rule
    refine rule (io.pureSources.consumeInput.bound state)
      (if state.eof = true then endCharge state else readCharge state) ?_ rfl ?_ ?_
    · simp +decide only [PureContext.exprCost, PureContext.ofProg, Expr.allocs, Var.cost,
      ↓reduceIte, Nat.add_zero, Nat.zero_add]
      show (if decide (state.cursor < state.input.size) = true then
        io.pureSources.consumeInput.bound state
        else if state.eof = true then endCharge state else readCharge state) ≤ inputCharge state
      simp only [inputCharge, decide_eq_true_eq, Nat.le_refl]
    · intro _
      apply bounded_of_rule
      intro spent fits rule
      refine rule ?_ rfl
      simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg,
        Expr.allocs, Var.cost, Expr.mode, argsSum, callCredits, ↓reduceIte, Nat.add_zero,
        Nat.zero_add, coerceCost]
      show io.pureSources.consumeInput.bound state ≤ _
      exact Nat.le_refl _
    · intro _
      apply bounded_of_rule
      intro spent fits rule
      refine rule (endCharge state) (readCharge state) ?_ (by condition_fits) ?_ ?_
      · simp +decide only [PureContext.exprCost, PureContext.ofProg, Expr.allocs, Var.cost,
        ↓reduceIte, Nat.add_zero, Nat.zero_add, ite_self, coerceCost]
        show (if (if state.eof = true then true else !true) = true then endCharge state
          else readCharge state) ≤ if state.eof = true then endCharge state else readCharge state
        by_cases eof : state.eof = true <;> simp [eof]
      · intro _
        apply bounded_of_rule
        intro spent fits rule
        refine rule (stateTy.copyCost (sourceState state)) (io.pureSources.completeLine.bound state)
          ?_ (by condition_fits) ?_ ?_
        · simp +decide only [PureContext.exprCost, PureContext.ofProg, Expr.allocs, Var.cost,
          ↓reduceIte, Nat.add_zero, Nat.zero_add, ite_self, coerceCost]
          show (if (if (state.line.size.toUInt64 == 0) = true then true else !true) = true then
            stateTy.copyCost (sourceState state)
            else io.pureSources.completeLine.bound state) ≤ endCharge state
          unfold endCharge
          by_cases zero : state.line.size.toUInt64 = 0 <;> simp [zero]
        · intro _
          apply bounded_of_rule
          intro spent fits rule
          refine rule ?_ rfl
          simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg,
            Expr.allocs, Var.cost, ↓reduceIte, Nat.add_zero, Nat.zero_add, coerceCost]
          show Ty.copyCost (.pair .bool (.pair .word stateTy)) (false, 0, sourceState state) ≤ _
          simp only [Ty.copyCost, Nat.zero_add, Nat.le_refl]
        · intro _
          apply bounded_of_rule
          intro spent fits rule
          refine rule ?_ rfl
          simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg,
            Expr.allocs, Var.cost, Expr.mode, argsSum, callCredits, ↓reduceIte, Nat.add_zero,
            Nat.zero_add, coerceCost]
          show io.pureSources.completeLine.bound state ≤ _
          exact Nat.le_refl _
      · intro _
        apply bounded_of_rule
        intro spent fits rule
        refine rule (readCharge state) ?_ rfl ?_
        · simp +decide only [PureContext.argumentCost, PureContext.exprCost, PureContext.ofProg,
          argsSum, ↓reduceIte, Nat.add_zero, Nat.zero_add]
          exact Nat.le_refl _
        · show CallBounded host pureContext (.cons io.readStep.func (.cons io.writeStep.func .nil))
            .here (0 + 1) (.cons (sourceState state) .nil) (readCharge state)
          exact callBounded_here (by decide) (readStep_bounded host _ state)

/-- The step from `state` spends at most `stepBudget state` and finds its frames. -/
theorem step_bounded {World : Type} (host : Host World) (state : State) :
    CallBounded host pureContext io.program entry.step 0 (.cons (sourceState state) .nil)
      (stepBudget state) :=
  callBounded_there (callBounded_here (by decide) (step_body_bounded host state))

set_option maxHeartbeats 4000000 in
theorem begin_bounded {World : Type} (host : Host World) :
    CallBounded host pureContext io.program entry.begin 0 .nil beginCharge := by
  apply callBounded_here (by decide)
  apply bounded_of_rule
  intro spent fits rule
  refine rule ?_ rfl
  simp +decide only []

theorem begin_prefix_bound {World : Type} (host : Host World) (world : World) :
    CallPrefixBound host pureContext io.program entry.begin 0 .nil world beginCharge :=
  (begin_bounded host).2 world

end Bodies

/-- A bound on the charge of every step from a state within the limits `L` and `D`. -/
def stepCharge (L D : Nat) : Nat := 200 * (L + D) + 1000500

theorem stepBudget_le {L D : Nat} {state : State} (sized : Sized L D state)
    (small : L + D + 4100 < UInt64.size) : stepBudget state ≤ stepCharge L D := by
  have total := sized.total
  have line := sized.line
  have input := sized.input
  have output := sized.output
  have copy := sized.copyCost
  have inputCost := allocationCost_le state.input.data.size
  have outputCost := allocationCost_le state.output.data.size
  have readFull : Verified.Wasi.readCost 4096 = 4144 := by decide
  have bufferCost : Bytes.allocationCost 4096 = 4144 := by decide
  unfold stepBudget inputCharge endCharge
  split
  · rename_i pending
    have remaining := remainingOutput_bound_le state pending
    unfold writeCharge copyLimit stepCharge at *
    omega
  · split
    · rename_i remaining
      have consume := consumeInput_bound_le state remaining (by omega)
      unfold consumeCost completeCost copyBytes combineCost stepCharge at *
      omega
    · split
      · split
        · unfold copyLimit stepCharge at *
          omega
        · have complete := completeLine_bound_le state (by omega)
          unfold completeCost copyBytes combineCost stepCharge at *
          omega
      · unfold readCharge copyBytes copyLimit stepCharge at *
        omega

theorem step_prefix_bound {World : Type} (host : Host World) {L D : Nat}
    (small : L + D + 4100 < UInt64.size) {state : State} (sized : Sized L D state) (world : World) :
    CallPrefixBound host (Resource.PureContext.ofProg io.pure.program io.pure.funs) io.program
      entry.step 0 (.cons (sourceState state) .nil) world (stepCharge L D) :=
  ((step_bounded host state).mono (stepBudget_le sized small)).2 world

end Demos.RunningSum
