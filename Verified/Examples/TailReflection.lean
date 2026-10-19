import Verified.Reflect.TailTermination
import Verified.Reflect.TailState

namespace Verified.Examples.TailReflection

open Lean Meta Elab Command Term Verified.Reflect

def tailCount (n acc : UInt64) : UInt64 :=
  if n = 0 then acc else tailCount (n - 1) (acc + n)
termination_by n.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega

def tailGrow (weights : Array UInt64) (n : UInt64) (xs : Array UInt64) : Array UInt64 :=
  if n = 0 then xs else tailGrow weights (n - 1) (xs.push weights[n.toNat]!)
termination_by n.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega

structure Entry where
  key : UInt64
  value : Float

instance : LeanExe.Pipeline.Flat Entry (UInt64 × Float) := ⟨fun e => (e.key, e.value)⟩

def tailEntries (n : UInt64) (xs : Array Entry) : Array Entry :=
  if n = 0 then xs else tailEntries (n - 1) (xs.push ⟨n, n.toFloat⟩)
termination_by n.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega

def tailScalarPair (n : UInt64) (p : UInt64 × Float) : UInt64 × Float :=
  if n = 0 then p else tailScalarPair (n - 1) (p.1 + n, p.2 + n.toFloat)
termination_by n.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega

private def checkTailReflection (name : Name) : TermElabM Unit := do
  let some eqName ← getUnfoldEqnFor? name | throwError "no unfolding equation"
  withRecursiveInput (name ++ `probe) name eqName fun input => do
    let state ← tailState name input
    addTheorem (name ++ `stateLeft) (← inferType state.left) state.left
    addTheorem (name ++ `stateRight) (← inferType state.right) state.right
  forallTelescope (← inferType (mkConst eqName)) fun params eqn => do
    let some (_, _, rhs) := eqn.eq? | throwError "no RHS"
    let types ← params.toList.mapM fun p => do tyOf (← inferType p)
    let resultType ← inferType rhs
    let sh ← shapeOf resultType
    let stateType ← tupleType (← params.toList.mapM fun p => inferType p)
    let φ ← withLocalDeclD `state stateType fun state => do
      let values ← argProjsE state (types.map fun _ => .borrowed) types.length
      mkLambdaFVars #[state] (← envExpr (values.zip types))
    let meaning ← withLocalDeclD `state stateType fun state => do
      let values ← argProjsE state (types.map fun _ => .borrowed) types.length
      mkLambdaFVars #[state] (mkAppN (mkConst name) values.toArray)
    let (ctx, env) ← ctxEnvExpr (params.toList.zip types)
    let sig : Sig := ⟨types, sh.ty, true, types.map fun _ => .owned, false⟩
    let t : TailContext := ⟨name, sig, stateType, resultType, φ, ← sh.fn resultType, meaning⟩
    let c : Ctx :=
      { base := name
        sigs := listExpr (mkConst ``Sig) []
        funs := mkConst ``Funs.nil
        callees := []
        vars := params.toList.zip types
        ctx
        env
        tables :=
          { sigs := listExpr (mkConst ``Sig) []
            prog := mkConst ``Prog.nil
            funs := mkConst ``Funs.nil
            fuel := mkNatLit 0 } }
    let r ← reflectTailSplit t c params.toList rhs
    let proof ← mkLambdaFVars params r.proof
    addTheorem (name ++ `tailEq) (← inferType proof) proof
    let fixed ← transHint (mkAppN (mkConst eqName) params) r.fixed
    let fixed ← mkLambdaFVars params fixed
    addTheorem (name ++ `tailFixed) (← inferType fixed) fixed
    let stepFn ← mkLambdaFVars params r.step
    let step ← withLocalDeclD `state stateType fun state => do
      let values ← argProjsE state (types.map fun _ => .borrowed) types.length
      mkLambdaFVars #[state] (stepFn.beta values.toArray)
    addDefinition (name ++ `tailStep) (← inferType step) step
    enableRealizationsForConst (name ++ `tailStep)
    let acc ← deriveTailAcc name (name ++ `tailStep) params stateType resultType
    let wf ← tailWellFounded (mkConst (name ++ `tailStep)) params types stateType resultType acc
    addTheorem (name ++ `tailWf) (← inferType wf) wf
    logInfo m!"{name}: accepted meaning and fixed-point equations"

run_cmd liftTermElabM do
  for name in [``tailCount, ``tailGrow, ``tailEntries, ``tailScalarPair] do
    checkTailReflection name

#print axioms tailCount.tailEq
#print axioms tailGrow.tailEq
#print axioms tailCount.tailFixed
#print axioms tailGrow.tailFixed
#print axioms tailCount.tailWf
#print axioms tailGrow.tailWf
#print axioms tailEntries.tailWf
#print axioms tailScalarPair.tailWf
#print axioms tailEntries.stateLeft
#print axioms tailEntries.stateRight

theorem countAcc (n acc : UInt64) :
    Acc (fun next state => tailCount.tailStep state = .inl next) (n, acc) := by
  fun_induction tailCount n acc <;>
    (refine Acc.intro _ ?_; intro next hs; simp_all [tailCount.tailStep])

theorem growAcc (weights : Array UInt64) (n : UInt64) (xs : Array UInt64) :
    Acc (fun next state => tailGrow.tailStep state = .inl next) (weights, n, xs) := by
  fun_induction tailGrow weights n xs <;>
    (refine Acc.intro _ ?_; intro next hs; simp_all [tailGrow.tailStep])

#print axioms countAcc
#print axioms growAcc

end Verified.Examples.TailReflection
