import Verified.ListFoldCode
import Verified.ListFoldStep
import Verified.ListFoldResource
import Verified.ListFoldBorrowed
import Verified.TailWhile

namespace Verified.ListFold

open Wasm LeanExe.Pipeline

theorem loop_spec {S : List Sig} {e : Elem} {captures : List Ty}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (body : Expr S (context e captures) (.elem e)) (place : body.placeArgs = true)
    (bodySpec : ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv body env slots paid live)
    (h stateBase : Nat) (env : Env (params e captures))
    (heap : Heap) (store : Store Unit) (s : Locals) (ws : List Value)
    (hh : s.positions = h) (hpv : s.params = pv)
    (rep : Env.Rep (paramMode (params e captures) []) heap store ws env)
    (sep : Separate store (Env.moves store (paramMode (params e captures) []) ws env)
      (Env.reads store (paramMode (params e captures) []) ws env))
    (hold : LocalsHold s stateBase ((params e captures).flatMap Ty.types) ws)
    (at_ : heap.At store)
    (input : @Bytes.LiteralPool.Input (Env (params e captures))
      (Env.represent (params e captures) []) pool heap store ws env)
    (cap : store.memoryCap m 0 ≤ 65535)
    (low : s.params.length ≤ stateBase)
    (room : stateBase + widthSum (params e captures) + e.width + (tailBody body).width [] ≤ h)
    (rest : Program) (Q : Assertion Unit)
    (trap : TrapOK (!(func body place).fits funs fits env ||
      !decide (heap.Within store m ((func body place).bound funs flags bounds env))) Q)
    (next : ∀ heap' store' s' words,
      Step heap store (Apart store (Env.moves store (paramMode (params e captures) []) ws env))
        heap' store' [] →
      Frame stateBase s s' → (.elem e : Ty).Rep .owned heap' store' words (meaning body funs env) →
      LocalsHold s' (stateBase + widthSum (params e captures)) e.types words →
      ((func body place).fits funs fits env = true →
        heap'.top.toNat ≤ heap.top.toNat + (func body place).bound funs flags bounds env) →
      wp m rest Q store' { s' with values := s.values } host) :
    wp m (loopCode body h stateBase (fun slots base live => body.code (pool := pool) h slots base live) ++ rest)
      Q store s host := by
  rw [loopCode_eq]
  simp only [List.singleton_append]
  refine wp_block_cons ?_
  refine tail_loop_spec hm (func body place) (func_decreases body place funs)
    (meaning body funs) (fixed body funs) (step_spec hm body bodySpec)
    h stateBase (stateBase + widthSum (params e captures))
    (stateBase + widthSum (params e captures) + e.width) env heap store s ws hh hpv rep sep hold
    at_ input cap low le_rfl le_rfl room _ ?_ ?_
  · simp only [func_aborts, Bool.true_and, argPot_eq_zero, Nat.zero_add]
    cases hb : (!(func body place).fits funs fits env ||
        !decide (heap.Within store m ((func body place).bound funs flags bounds env))) with
    | false => trivial
    | true =>
      intro st
      rw [hb] at trap
      exact trap st
  · intro heap' store' s' words step frame result held top
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    apply next heap' store' s' words step frame result held
    simpa only [func_paidResult, Bool.false_eq_true, ↓reduceIte, argPot_eq_zero,
      Nat.add_zero] using top

#print axioms loop_spec

end Verified.ListFold
