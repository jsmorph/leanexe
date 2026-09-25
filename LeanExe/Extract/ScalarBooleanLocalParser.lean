import LeanExe.Source.ScalarBooleanLocal
import LeanExe.Extract.ScalarPropositionGuard
import LeanExe.Extract.ScalarBooleanProofBodies

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def booleanLocalOperands? : Lean.Expr → Option BooleanLocal
  | .app (.app (.const ``Bool.and []) left) right => do
      let a ← booleanLocalOperands? left
      let b ← booleanLocalOperands? right
      pure (.junction 0 .conjunction a b)
  | .app (.app (.const ``Bool.or []) left) right => do
      let a ← booleanLocalOperands? left
      let b ← booleanLocalOperands? right
      pure (.junction 0 .disjunction a b)
  | .app (.const ``Bool.not []) inner => (booleanLocalOperands? inner).map BooleanLocal.negate
  | .const ``Bool.true [] => some (.literal 0 true)
  | .const ``Bool.false [] => some (.literal 0 false)
  | .bvar index => some (.var 0 index)
  | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) (.const ``Bool []))
      (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) left) right)) evidence) yes) no =>
      if LeanExe.Source.ExprEquality.same evidence (booleanRelationEvidence false left right) then do
        let a ← booleanLocalOperands? left
        let b ← booleanLocalOperands? right
        let t ← booleanLocalOperands? yes
        let e ← booleanLocalOperands? no
        pure (.choice 0 false a b t e)
      else none
  | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) (.const ``Bool []))
      (.app (.app (.app (.const ``Ne [.succ .zero]) (.const ``Bool [])) left) right)) evidence) yes) no =>
      if LeanExe.Source.ExprEquality.same evidence (booleanRelationEvidence true left right) then do
        let a ← booleanLocalOperands? left
        let b ← booleanLocalOperands? right
        let t ← booleanLocalOperands? yes
        let e ← booleanLocalOperands? no
        pure (.choice 0 true a b t e)
      else none
  | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) (.const ``Bool [])) condition) evidence) yes) no => do
      let guard ← propositionGuard? condition evidence
      let t ← booleanLocalOperands? yes
      let e ← booleanLocalOperands? no
      pure (.proposition 0 guard t e)
  | .app (.app (.app (.app (.app (.const ``dite [.succ .zero]) (.const ``Bool []))
      (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) left) right)) evidence)
      (.lam tn td yesBody ti)) (.lam fn fd noBody fi) =>
      if LeanExe.Source.ExprEquality.same evidence (booleanRelationEvidence false left right) then
        match _bodies : booleanProofBodies? (booleanRelationCondition false left right) td yesBody fd noBody with
        | none => none
        | some (yes, no) => do
          let a ← booleanLocalOperands? left
          let b ← booleanLocalOperands? right
          let t ← booleanLocalOperands? yes
          let e ← booleanLocalOperands? no
          pure (.dependentChoice 0 ⟨tn, fn, ti, fi⟩ false a b t e)
      else none
  | .app (.app (.app (.app (.app (.const ``dite [.succ .zero]) (.const ``Bool []))
      (.app (.app (.app (.const ``Ne [.succ .zero]) (.const ``Bool [])) left) right)) evidence)
      (.lam tn td yesBody ti)) (.lam fn fd noBody fi) =>
      if LeanExe.Source.ExprEquality.same evidence (booleanRelationEvidence true left right) then
        match _bodies : booleanProofBodies? (booleanRelationCondition true left right) td yesBody fd noBody with
        | none => none
        | some (yes, no) => do
          let a ← booleanLocalOperands? left
          let b ← booleanLocalOperands? right
          let t ← booleanLocalOperands? yes
          let e ← booleanLocalOperands? no
          pure (.dependentChoice 0 ⟨tn, fn, ti, fi⟩ true a b t e)
      else none
  | .app (.app (.app (.app (.app (.const ``dite [.succ .zero]) (.const ``Bool [])) condition) evidence)
      (.lam tn td yesBody ti)) (.lam fn fd noBody fi) =>
      match _bodies : booleanProofBodies? condition td yesBody fd noBody with
      | none => none
      | some (yes, no) => do
        let guard ← propositionGuard? condition evidence
        let t ← booleanLocalOperands? yes
        let e ← booleanLocalOperands? no
        pure (.dependentProposition 0 ⟨tn, fn, ti, fi⟩ guard t e)
  | .app (.app (.const ``Decidable.decide [])
      (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) left) right)) evidence =>
      if LeanExe.Source.ExprEquality.same evidence (booleanRelationEvidence false left right) then do
        let a ← booleanLocalOperands? left
        let b ← booleanLocalOperands? right
        pure (.relationDecision 0 false a b)
      else none
  | .app (.app (.const ``Decidable.decide [])
      (.app (.app (.app (.const ``Ne [.succ .zero]) (.const ``Bool [])) left) right)) evidence =>
      if LeanExe.Source.ExprEquality.same evidence (booleanRelationEvidence true left right) then do
        let a ← booleanLocalOperands? left
        let b ← booleanLocalOperands? right
        pure (.relationDecision 0 true a b)
      else none
  | .app (.app (.const ``Decidable.decide []) condition) evidence =>
      (propositionGuard? condition evidence).map (.decision 0)
  | .app (.app (.app (.app (.const ``BEq.beq [.zero]) (.const ``Bool []))
      (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``Bool []))
        (.const ``instDecidableEqBool []))) left) right => do
      let a ← booleanLocalOperands? left
      let b ← booleanLocalOperands? right
      pure (.equality 0 false a b)
  | .app (.app (.app (.app (.const ``_root_.bne [.zero]) (.const ``Bool []))
      (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``Bool []))
        (.const ``instDecidableEqBool []))) left) right => do
      let a ← booleanLocalOperands? left
      let b ← booleanLocalOperands? right
      pure (.equality 0 true a b)
  | .letE name (.const ``Bool []) value body nondep => do
      let v ← booleanLocalOperands? value
      let b ← booleanLocalOperands? body
      pure (.binding 0 name nondep v b)
  | .letE name (.const ``UInt64 []) value body nondep => do
      let b ← booleanLocalOperands? body
      pure (.wordBinding 0 name nondep value b)
  | expression => (booleanComparisonOperands? expression).map fun (op, a, b) => .compare op a b
termination_by expression => sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have bounds := booleanProofBodies_sizes _bodies; omega)

end LeanExe.Extract.Core
