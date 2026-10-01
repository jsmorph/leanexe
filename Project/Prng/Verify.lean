import Project.Prng.Module
import Project.IR.Correct
import Project.IR.Run
import Project.Encoding.RoundTrip

/-! The compiled SplitMix64 step and the conversion to `[0, 1)` compute their Lean
definitions exactly and keep the store.  The theorems hold in any module whose function
list contains the compiled function, so the GPT module, which samples with them, uses
the same proofs. -/

namespace Project.Prng

open Project.Pipeline Project.IR Project.ProofKit LeanExe.Examples.Prng

/-- `splitMix` keeps the store and returns its state and word in any module whose
function `i` is its compiled form. -/
theorem splitMix_pure (funcs : List (Func × String)) (i : Nat)
    (hFunc : funcs[i]? = some (prng.splitMix.ir, "splitMix")) :
    ImplementsPure (compile funcs) (2 + i) splitMix := by
  refine Func.implementsPure funcs i prng.splitMix.ir "splitMix" hFunc splitMix (fun _ => rfl)
    fun x initial => ?_
  let s := x + 0x9e3779b97f4a7c15
  let a := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let b := (a ^^^ (a >>> 27)) * 0x94d049bb133111eb
  let start : State := { params := [.i64 x], locals := [.i64 0, .i64 0, .i64 0] }
  let s1 := start.update 1 (.i64 s)
  let s2 := s1.update 2 (.i64 a)
  let s3 := s2.update 3 (.i64 b)
  have hParams : start.params.length = 1 := rfl
  have hLocals : start.locals.length = 3 := rfl
  have hGet0 : start.get 0 = some (.i64 x) := rfl
  show Triple _ (.seq (.assign 1 (.bin .add (.get 0) (.const 11400714819323198485)))
    (.seq (.assign 2 (.bin .mul (.bin .bitXor (.get 1) (.bin .shiftRight (.get 1) (.const 30)))
      (.const 13787848793156543929)))
    (.assign 3 (.bin .mul (.bin .bitXor (.get 2) (.bin .shiftRight (.get 2) (.const 27)))
      (.const 10723151780598845931))))) 4
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) <|
    (Stmt.run_spec (final := s3) ?_).mono (fun _ _ h => h) ?_
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, hGet0, s1, s, U64Op.apply]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2, a, U64Op.apply]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2, s3, b,
      U64Op.apply]
  rintro store state ⟨rfl, rfl⟩
  refine ⟨rfl, [.i64 s, .i64 (b ^^^ (b >>> 31))], s3, ?_, rfl⟩
  simp [prng.splitMix.ir, Func.scratch, Expr.evalResults, Expr.eval, s3, s2, s1, hParams,
    hLocals, U64Op.apply]

/-- `unitFloat` keeps the store and returns its float in any module whose function `i`
is its compiled form. -/
theorem unitFloat_pure (funcs : List (Func × String)) (i : Nat)
    (hFunc : funcs[i]? = some (prng.unitFloat.ir, "unitFloat")) :
    ImplementsPure (compile funcs) (2 + i) unitFloat := by
  refine Func.implementsPure funcs i prng.unitFloat.ir "unitFloat" hFunc unitFloat
    (fun _ => rfl) fun x initial => ?_
  have k53 : (9007199254740992.0 : Float).toBits = 4845873199050653696 := by decide +kernel
  show Triple _ .skip _ _ _
  refine Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, ?_⟩) fun _ _ h => h
  subst hState
  simp [prng.unitFloat.ir, Func.scratch, Func.state, Func.locals, Func.width, Expr.evalResults,
    Expr.eval, Expr.scratchWidth, Stmt.scratchWidth, State.get, U64Op.apply, F64Op.apply, Scalar.values,
    unitFloat, F64Bits.toBits_div, F64Convert.toBits_toFloat, k53]

theorem splitMix_implements : Implements prng.module 2 splitMix :=
  (splitMix_pure prng.funcs 0 rfl).implements

theorem unitFloat_implements : Implements prng.module 3 unitFloat :=
  (unitFloat_pure prng.funcs 1 rfl).implements

/-- `encode` succeeds on `prng.module`, and its bytes decode to a module that computes
`splitMix` and `unitFloat` exactly. -/
theorem prng_bytes : ∃ bytes, Wasm.Encoding.encode prng.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 splitMix ∧
      Implements m 3 unitFloat := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip prng.module (by decide +kernel) (by decide +kernel)
  exact ⟨bytes, success, prng.module, decoded, splitMix_implements, unitFloat_implements⟩

end Project.Prng
