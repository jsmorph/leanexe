import Examples.SumSquares.Module
import Project.IR.Correct
import Project.ProofKit.F64Bits
import Project.Encoding.RoundTrip

namespace Examples.SumSquares

open Project.Pipeline Project.IR Project.ProofKit

/-- One step of the compiled fold on bit patterns. -/
def step (a e : UInt64) : UInt64 := Wasm.IEEE64.add a (Wasm.IEEE64.mul e e)

theorem sumSquares_bits (xs : Array Float) :
    (xs.map Float.toBits).foldl step 0 =
      (Examples.SumSquares.sumSquares xs).toBits := by
  have hZero : (0.0 : Float).toBits = 0 := by decide
  rw [← hZero, Array.foldl_map]
  exact Array.foldl_hom Float.toBits fun a x => by
    simp [step, F64Bits.toBits_add, F64Bits.toBits_mul]

theorem sumSquares_implements :
    Implements sumSquares.module 2 Examples.SumSquares.sumSquares := by
  refine Func.implements [(sumSquares.ir, "sumSquares")] 0 sumSquares.ir "sumSquares" rfl _ (by rintro _ _ _ _ ⟨ptr, rfl, -⟩; rfl) ?_
  rintro xs heap initial _ - ⟨ptr, rfl, hBorrowed⟩
  let start : State := { params := [.i64 ptr], locals := [.f64 0, .i64 0, .i64 0, .f64 0] }
  show Triple _ (.seq (.assign 1 (.constF 0))
    (.fold .f64 0 1 2 3 4 (.binF .add (.getF 1) (.binF .mul (.getF 4) (.getF 4))))) 5
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = start) ?_
    ((Stmt.fold_spec (initial := initial) (before := start) (ptr := ptr) (start := 0) step
      (by decide) (by decide) (by simp [start]) hBorrowed.values rfl rfl
      fun state a e _ hA hE => ⟨state, by simp [Expr.eval, hA, hE, F64Op.apply, step]⟩).mono
        (fun _ _ h => h) ?_)
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨0, start, start, rfl, rfl, rfl, rfl⟩
  · rintro store state ⟨hStore, -, hAcc⟩
    refine ⟨hStore, [.f64 ((xs.map Float.toBits).foldl step 0)], state, by
      simp [sumSquares.ir, Func.scratch, Expr.evalResults, Expr.eval, hAcc],
      congrArg (fun word => [Wasm.Value.f64 word]) (sumSquares_bits xs)⟩

/-- `encode` succeeds on `sumSquares.module`, and its bytes decode to a module that
computes `sumSquares` bit for bit. -/
theorem sumSquares_bytes : ∃ bytes, Wasm.Encoding.encode sumSquares.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧
      Implements m 2 Examples.SumSquares.sumSquares := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip sumSquares.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, sumSquares.module, decoded, sumSquares_implements⟩

end Examples.SumSquares
