import Examples.Mean.Module
import LeanExe.IR.Correct
import LeanExe.ProofKit.F64Convert
import LeanExe.Encoding.RoundTrip

namespace Examples.Mean

open Wasm LeanExe.Pipeline LeanExe.IR LeanExe.ProofKit

theorem sum_bits (xs : Array Float) :
    (xs.map Float.toBits).foldl IEEE64.add 0 = (xs.foldl (· + ·) 0.0).toBits := by
  have hZero : (0.0 : Float).toBits = 0 := by decide
  rw [← hZero, Array.foldl_map]
  exact Array.foldl_hom Float.toBits fun a x => by simp [F64Bits.toBits_add]

theorem mean_bits (xs : Array Float) :
    IEEE64.div ((xs.map Float.toBits).foldl IEEE64.add 0)
      (IEEE64.convertI64U (UInt64.ofNat (xs.map Float.toBits).size)) =
      (Examples.Mean.mean xs).toBits := by
  rw [Examples.Mean.mean, F64Bits.toBits_div, F64Convert.toBits_toFloat, sum_bits,
    Array.size_map]

theorem mean_implements :
    Implements mean.module 2 Examples.Mean.mean := by
  refine Func.implements [(mean.ir, "mean")] 0 mean.ir "mean" rfl _ (by rintro _ _ _ _ ⟨ptr, rfl, -⟩; rfl) ?_
  rintro xs heap initial _ - ⟨ptr, rfl, hBorrowed⟩
  let start : State :=
    { params := [.i64 ptr], locals := [.f64 0, .i64 0, .i64 0, .f64 0, .i64 0] }
  show Triple _ (.seq (.assign 1 (.constF 0))
    (.seq (.fold .f64 0 1 2 3 4 (.binF .add (.getF 1) (.getF 4))) (.arraySize 5 0))) 6
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = start) ?_ ?_
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨0, start, start, rfl, rfl, rfl, rfl⟩
  refine Stmt.seq_spec ((Stmt.fold_spec (elementType := .f64) (accType := .f64)
    (initial := initial) (before := start) (ptr := ptr) (start := 0) IEEE64.add (by decide) (by decide) (by simp [start]) hBorrowed.values rfl rfl
    fun state a e _ hA hE => ⟨state, by simp [Expr.eval, hA, hE, F64Op.apply]⟩).mono
      (fun _ _ h => h) (R' := fun store state => store = initial ∧
        State.Frame 6 [1, 2, 3, 4] start state ∧
        state.get 1 = some (.f64 ((xs.map Float.toBits).foldl IEEE64.add 0))) fun _ _ h => h) ?_
  apply Triple.of_forall
  rintro store s2 ⟨hStore, hFrame2, hAcc⟩
  subst store
  have hPtr2 : s2.get 0 = some (.i64 ptr) := (hFrame2.get 0 (by decide) (by decide)).trans rfl
  have hLength2 : s2.params.length + s2.locals.length = 6 := by
    rw [hFrame2.params, hFrame2.locals]; simp [start]
  refine (Stmt.arraySize_spec hBorrowed.values hPtr2 (by omega)).mono (fun _ _ h => h) ?_
  rintro store s3 ⟨hStore, hSet3⟩
  have hSum : s3.get 1 = some (.f64 ((xs.map Float.toBits).foldl IEEE64.add 0)) := by
    rw [State.get_set?_ne (by decide) hSet3, hAcc]
  have hSize := State.get_set?_same hSet3
  refine ⟨hStore, [.f64 (IEEE64.div ((xs.map Float.toBits).foldl IEEE64.add 0)
      (IEEE64.convertI64U (UInt64.ofNat (xs.map Float.toBits).size)))], s3, by
    simp [mean.ir, Func.scratch, Expr.evalResults, Expr.eval, hSum, hSize, F64Op.apply],
    congrArg (fun word => [Value.f64 word]) (mean_bits xs)⟩

/-- `encode` succeeds on `mean.module`, and its bytes decode to a module that
computes `mean` bit for bit. -/
theorem mean_bytes : ∃ bytes, Encoding.encode mean.module = .ok bytes ∧
    ∃ m, Encoding.decode bytes = .ok m ∧
      Implements m 2 Examples.Mean.mean := by
  obtain ⟨bytes, success, decoded⟩ :=
    Encoding.round_trip mean.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, mean.module, decoded, mean_implements⟩

end Examples.Mean
