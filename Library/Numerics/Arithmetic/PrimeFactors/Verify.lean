import Library.Numerics.Arithmetic.PrimeFactors.Proof
import Library.Numerics.Arithmetic.PrimeFactors.Module
import Library.Numerics.Arithmetic.PrimeFactors.Spec
import LeanExe.IR.TailLoop
import LeanExe.IR.Live
import LeanExe.IR.Words
import LeanExe.Encoding.RoundTrip
import Mathlib.Data.Nat.Factors

/-! The bytes of `primeFactors.module` compute the specification `expected`: the number of prime
factors of a word, counted with multiplicity. -/

namespace Library.Numerics.Arithmetic.PrimeFactors

open Wasm LeanExe.Pipeline LeanExe.IR LeanExe.Runtime Library.Numerics.Arithmetic.PrimeFactors

theorem countTuple_injective (x y : UInt64 × UInt64 × UInt64)
    (h : Scalar.values x = Scalar.values y) : x = y := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨d, e, f⟩ := y
  simp [Scalar.values] at h
  simp [h]

set_option maxHeartbeats 1000000 in
/-- One iteration of the compiled loop: it stores the count when `countFactors` returns, and
otherwise moves to the arguments of its recursive call, which have the same result and a smaller
measure. -/
theorem countFactors_step {m : Module} : TailStep (α := UInt64 × UInt64 × UInt64) m
    (match primeFactors.countFactors.ir.body with | .while _ step => step | _ => .skip)
    primeFactors.countFactors.ir.scratch 5 countTuple countMeasure := by
  rintro initial ⟨r, d, c⟩ result others hLength
  match others, hLength with
  | [v5, v6, v7, v8, v9], _ =>
    refine Stmt.run_triple ?_
    by_cases h1 : r ≤ 1 ∨ d ≤ 1
    · eval_state [tailState, primeFactors.countFactors.ir, Func.scratch, State.get, State.update,
        countTuple, countFactors_stop h1, h1]
    have ha : ¬r ≤ 1 := fun h => h1 (.inl h)
    have hb : ¬d ≤ 1 := fun h => h1 (.inr h)
    by_cases h2 : r / d < d
    · eval_state [tailState, primeFactors.countFactors.ir, Func.scratch, State.get, State.update,
        countTuple, countFactors_last h1 h2, ha, hb, h2]
    by_cases h3 : r % d = 0
    · eval_state [tailState, primeFactors.countFactors.ir, Func.scratch, State.get, State.update,
        countTuple, countFactors_div h1 h2 h3, measure_div h1 h2, ha, hb, h2, h3]
    · eval_state [tailState, primeFactors.countFactors.ir, Func.scratch, State.get, State.update,
        countTuple, countFactors_next h1 h2 h3, measure_next h1 h2, ha, hb, h2, h3]

theorem countFactors_implements : Implements primeFactors.module 2 countTuple :=
  Func.tail_implements primeFactors.funcs 0 primeFactors.countFactors.ir "countFactors" rfl
    countTuple countMeasure _ (fun _ => rfl) countTuple_injective (k := 3) rfl rfl rfl
    countFactors_step

theorem compute_implements : Implements primeFactors.module 3 compute := by
  refine Func.implements_heap primeFactors.funcs 1 primeFactors.compute.ir "compute" rfl compute
    (by rintro _ _ _ _ rfl; rfl) ?_
  rintro n heap initial _ hHeap rfl hCap
  let start := primeFactors.compute.ir.state [.i64 n]
  refine (Stmt.callImplements_spec countFactors_implements rfl rfl rfl (x := (n, 2, 0))
    (before := start) (afterArgs := start) (by simp [Expr.evalResults, Expr.eval, start, State.get,
      Func.state, Scalar.values]) hHeap rfl Separate.nil hCap
    (by rintro _ _ _ rfl; exact ⟨_, rfl⟩)).mono (fun _ _ h => h) ?_
  rintro store state ⟨heap', values, hAt, rfl, hCaps, hKeeps, hState⟩
  refine ⟨heap', hAt, hCaps, [.i64 (compute n)], state, ?_, rfl, hKeeps⟩
  simp [State.setAll, State.set?, start, Func.state, Scalar.values] at hState
  obtain ⟨-, rfl⟩ := hState
  eval_body [primeFactors.compute.ir, countTuple, compute]

/-- `encode` succeeds on `primeFactors.module`, and its bytes decode to a module that computes
the specification `expected`. -/
theorem primeFactors_bytes : ∃ bytes, Wasm.Encoding.encode primeFactors.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 3 expected := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip primeFactors.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, primeFactors.module, decoded,
    compute_implements.congr fun _ _ _ n _ => compute_eq n⟩

#print axioms primeFactors_bytes

end Library.Numerics.Arithmetic.PrimeFactors
