module

public import Verified.Wasi.SysRule
public import Verified.Wasi.BudgetAttr

@[expose] public section

/-! Tactics for the budget proofs of WASI commands, which bound the charge of a command's body by
the rules of `Verified/Wasi/ResourceRules.lean`.  `envGet` reads a variable of an environment
given as a chain of `Env.cons`.  `rule_charge` proves a bound on the charge of an expression: it
evaluates the liveness tests, reads the variables, rewrites the charges of the command's pure
functions, which the budget proof gives the simp attribute `charge_eqs`, and leaves the copies to
`omega`.  `rule_init_charge` does the same for a loop's initial state and sums the constant charge
of a built buffer with `sumBelow_const`.  `rule_fits` proves the frames of an expression that calls
no function that takes the call depth.  `rule_ret`, `rule_write`, `rule_bind`, `rule_sys`,
`rule_ite`, and `rule_free` apply the rules of a `ret`, a `write`, a `bind`, a `sys` command, an
`if`, whose branches take the same budget through `ite_cost` of `ResourceRules.lean`, and a command
of `bind`s, `ret`s, and `sys` commands that charge nothing. -/

namespace Verified.Wasi.Resource

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime Verified Verified.Wasi

open Lean Meta in
/-- The value at `index` of an environment given as a chain of `Env.cons`. -/
private meta partial def envValueAt (env : Lean.Expr) (index : Nat) : MetaM (Option Lean.Expr) := do
  match (← whnfD env).getAppFnArgs with
  | (``Env.cons, #[_, _, value, rest]) =>
    if index == 0 then return some value else envValueAt rest (index - 1)
  | _ => return none

open Lean Meta Simp in
/-- Reads `Env.get env (Var.ofIndex Γ i h)` as the `i`-th value of `env` when `env` is a chain of
`Env.cons`, a definitional step.  The types of the chain's `Env.cons` nodes are those of the
commands that bound the values, such as `SysForm.reported.ty`, and the list `Γ` of the reflected
variable states them in another form, so a rewriting lemma for `Env.get` of `Env.cons` does not
match. -/
dsimproc_decl envGet (Env.get _ (Var.ofIndex _ _ _)) := fun e => do
  let (``Env.get, #[_, _, env, reference]) := e.getAppFnArgs | return .continue
  let (``Var.ofIndex, #[_, _, index, _]) := reference.getAppFnArgs | return .continue
  let some index := index.rawNatLit? <|> index.nat? | return .continue
  let some value ← envValueAt env index | return .continue
  return .done value

/-- Proves a bound on the charge of an expression: evaluates its liveness tests, reads its
variables, rewrites the charges of the pure functions that `charge_eqs` holds, and leaves the
copies to `omega`. -/
macro "rule_charge" : tactic => `(tactic|
  (simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.loopInitCost,
      PureContext.loopCountCost, PureContext.loopTestCost, PureContext.argumentCost, Expr.allocs,
      Var.cost, Var.ownedCost, Expr.ownedCost, Expr.mode, coerceCost, Ty.copyCost, envGet,
      Expr.denote, Args.get_cons_zero', Args.get_cons_zero, Args.get_cons_succ, Env.ofFn, argsSum,
      callCredits, ResultTy.bindEnv, loopEnv, loopModes, letPairEnv, letPairModes, modeAt,
      sysTakeLive, List.get_cons_zero, List.get_cons_succ', charge_eqs, allocCost, Elem.width,
      sumBelow, UInt64.reduceToNat, Nat.add_zero, Nat.zero_add, ↓reduceIte, ite_self] <;>
   omega))

/-- Proves a bound on the charge of a loop's initial state, whose built buffers `rule_charge`
would unfold byte by byte: sums the constant charge of their bytes with `sumBelow_const`. -/
macro "rule_init_charge" : tactic => `(tactic|
  (simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.loopInitCost,
      PureContext.loopCountCost, PureContext.argumentCost, Expr.allocs, Var.cost, Var.ownedCost,
      Expr.ownedCost, Expr.mode, coerceCost, Ty.copyCost, envGet, Expr.denote, Args.get_cons_zero',
      Args.get_cons_zero, Args.get_cons_succ, Env.ofFn, argsSum, callCredits, ResultTy.bindEnv,
      letPairEnv, letPairModes, modeAt, charge_eqs, allocCost, Elem.width, sumBelow_const,
      UInt64.reduceToNat, Nat.add_zero, Nat.zero_add, Nat.mul_zero, ↓reduceIte, ite_self] <;>
   omega))

/-- Proves the frames of an expression that calls no function that takes the call depth. -/
macro "rule_fits" : tactic => `(tactic| exact Expr.fits_of_depthCalls _ _ _ (by decide) _)

/-- Proves `Bounded` of a `ret`. -/
macro "rule_ret" : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   exact rule (by rule_charge) (by rule_fits)))

/-- Proves `Bounded` of a `write`, which charges nothing. -/
macro "rule_write" : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   exact rule))

/-- Reduces `Bounded` of a `bind` to its parts with the budgets `first` and `next`. -/
macro "rule_bind " first:term:max next:term:max : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   refine rule $first $next (by omega) ?_ ?_))

/-- Proves `Bounded` of a `sys` command whose call charges nothing and whose take moves its
buffer or has none. -/
macro "rule_sys" : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   exact rule (fun _ _ _ _ _ => by simp only [sysCost, PureContext.sysTakeCost]; rule_charge)
     (fun _ _ _ _ _ => by simp only [sysCost, PureContext.sysTakeCost]; rule_charge)))

/-- Proves `Bounded` of a command of `bind`s, `ret`s, and `sys` commands that charge nothing. -/
macro "rule_free" : tactic => `(tactic|
  (repeat (first
    | (apply bounded_of_rule; intro _ _ rule; refine rule 0 0 (by omega) ?_ ?_)
    | (intro _ _)
    | rule_ret
    | rule_sys)))

/-- Reduces `Bounded` of an `ite` to its branches with the budget `branch` for each. -/
macro "rule_ite " branch:term:max : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   refine rule $branch $branch (ite_cost (by rule_charge)) (by rule_fits) (fun _ => ?_)
     (fun _ => ?_)))

end Verified.Wasi.Resource
