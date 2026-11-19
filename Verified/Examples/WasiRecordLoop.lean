import Verified.Wasi.ReflectCommand
import Verified.Wasi.ResourceRules

/-! A loop of record calls whose charge does not grow with the number of passes.  `stat count`
calls `fd_fdstat_get` on the preopened directory `count` times and returns the errno of the last
call, or 0 when `count` is 0.  Each call places its record in the call area and allocates
nothing, so every run and every prefix of `stat` spends no heap, whatever `count` is
(`body_bounded` and `call_prefix_bound`). -/

namespace Verified.Examples.WasiRecordLoop

open LeanExe LeanExe.Wasi Verified Verified.Wasi Verified.Wasi.Resource

def stat (count : UInt64) : Action UInt64 :=
  loop count 0 (fun _ _ => true) fun _ _ => do
    let status ← fdFdstatGet .preopened
    pure status.errno

verified_compile_wasi compiled := [stat]

/-- The step of the loop, which `verified_compile_wasi` reflects from `stat`: the record call on
descriptor 3 and the errno, the first word of its result. -/
def step : Command [] [] [.word, .word, .word] (.value .word) :=
  .bind (.bind (.ret (.word 3)) (.sys Call.fdFdstatGet (.record 4) [.here] [] []))
    (.ret (.proj .here (.fst .here)))

def body : Command [] [] [.word] (.value .word) :=
  .loop (.var .here) (.word 0) (.bool true) step

theorem source_body : compiled.stat.func.body = body := by rfl

/-- A variable of an element type costs nothing to read, in either mode. -/
private theorem var_cost_elem {modes : List Mode} {live : Nat → Bool} {Γ : List Ty} {e : Elem}
    (x : Var Γ (.elem e)) (v : (Ty.elem e).denote) : Var.cost modes live x v = 0 := by
  unfold Var.cost
  split <;> rfl

/-- Closes a goal about the charge of an expression or a `sys` command by unfolding the charge's
definitions. -/
local macro "charge" : tactic => `(tactic|
  (simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.loopInitCost,
      PureContext.loopCountCost, PureContext.loopTestCost, PureContext.sysTakeCost, Expr.allocs,
      var_cost_elem, Expr.mode, coerceCost, Ty.copyCost, Expr.denote, loopEnv, loopModes, modeAt,
      sysTakeLive, sysCost, sumBelow, Nat.add_zero, Nat.zero_add, ↓reduceIte, ite_self] <;>
   omega))

/-- Every run and every prefix of the step spends nothing. -/
private theorem step_bounded {World : Type} (host : Host World) (pure : PureContext [])
    (depth : UInt64) (modes : List Mode) (live : Nat → Bool) (env : Env [.word, .word, .word]) :
    Bounded host pure .nil depth modes live step env 0 := by
  apply bounded_of_rule
  intro _ _ rule
  refine rule 0 0 (by omega) ?_ ?_
  · apply bounded_of_rule
    intro _ _ rule
    refine rule 0 0 (by omega) ?_ ?_
    · apply bounded_of_rule
      intro _ _ rule
      exact rule (by charge) rfl
    · intro _ _
      apply bounded_of_rule
      intro _ _ rule
      exact rule (fun _ _ _ _ _ => by charge) (fun _ _ _ _ _ => by charge)
  · intro _ _
    apply bounded_of_rule
    intro _ _ rule
    exact rule (by charge) rfl

/-- Every run and every prefix of the body of `stat` spends nothing, for every number of passes.
-/
theorem body_bounded {World : Type} (host : Host World) (pure : PureContext []) (depth : UInt64)
    (modes : List Mode) (live : Nat → Bool) (env : Env [.word]) :
    Bounded host pure .nil depth modes live body env 0 := by
  apply bounded_of_rule
  intro _ _ rule
  refine rule 0 (by charge) rfl ?_
  exact (loop_bounded (fun _ => True) (t := 0) (s := 0) (fun _ _ _ => by charge)
    (fun _ _ _ => rfl) (fun _ _ _ => step_bounded host pure depth _ _ _)
    (fun _ _ _ _ _ => trivial) _ 0 _ trivial).mono (by simp)

/-- Every prefix of a call of `stat` spends nothing, for every `count`. -/
theorem call_prefix_bound {World : Type} (host : Host World) (env : Env [.word])
    (world : World) :
    CallPrefixBound host (.ofProg compiled.pure.program compiled.pure.funs) compiled.program
      compiled.stat.callee 0 env world 0 := by
  intro trace residual final spent fits progress
  refine call_prefix_rule 0 progress rfl ?_
  rw [source_body]
  exact (body_bounded host _ 0 _ _ env).2 world

end Verified.Examples.WasiRecordLoop
