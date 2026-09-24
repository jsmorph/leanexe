import Project.EulerCertificate.TotalsLoop
import Project.EulerCertificate.SolverScalars

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerRiemann
open Project.EulerCertificateFlux.Execution (boundsValues vectorValues)

set_option maxRecDepth 32768
set_option maxHeartbeats 400000

def totalsHead : Wasm.Program := func74.take 80
def totalsTail : Wasm.Program := func74.drop 81

theorem totals_shape :
    func74 = totalsHead ++ [.block 0 0 [.loop 0 0 totalsLoop]] ++ totalsTail := by
  have tail : func74.drop 37 = AnnotationMatches.function_74_array_fold_0_program ++
      func74.drop 105 := AnnotationMatches.function_74_array_fold_0_tail_eq
  calc
    func74 = func74.take 37 ++ func74.drop 37 := (List.take_append_drop 37 func74).symm
    _ = func74.take 37 ++ (AnnotationMatches.function_74_array_fold_0_program ++
        func74.drop 105) := by rw [tail]
    _ = totalsHead ++ [.block 0 0 [.loop 0 0 totalsLoop]] ++ totalsTail := rfl

theorem totals_sum_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (grid : Array Traversal.Cell)
    (hGrid : Memory.GridAt initial pointer grid) :
    TerminatesWith env Project.EulerCertificate.«module» 74 initial
      [.i64 pointer, .i64 owner]
      (fun final values => final = initial ∧ values = vectorValues (Totals.sum grid)) := by
  have hLength := hGrid.lengthRead
  have hBound := Nat.not_lt.mpr hGrid.lengthBound
  refine TerminatesWith.of_wp_entry_for (f := func74Def) rfl ?_ (by decide)
  change wp Project.EulerCertificate.«module» func74 _ initial
    (func74Def.toLocals [.i64 owner, .i64 pointer]) env
  rw [totals_shape]
  unfold totalsHead func74
  dsimp only
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  wp_run [func74Def]
  refine wp_call_tw (vector_zero_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  simp only [vectorValues, boundsValues, Vectors.zero, List.append]
  wp_run [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    ← Project.ProofKit.Memory.toUInt32_eq_ofNat, UInt32.add_zero, UInt32.toNat_zero,
    Nat.add_zero, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, hLength, hBound]
  totals_peel
  change wp _ _ _ _
    (totalsFrame owner pointer grid.size 0 Vectors.zero { borrowed := pointer }) _
  nth_rw 1 [← totalsPrefix_zero grid]
  apply totals_loop_spec env initial owner pointer grid hGrid 0 (Nat.zero_le _)
    { borrowed := pointer }
  intro scratch
  unfold func74
  dsimp only
  totals_peel
  simp [totalsPrefix_size]

theorem totals_physical_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (owner pointer : UInt64) (grid : Array Traversal.Cell)
    (hn : n ≤ 800) (hGrid : Memory.GridAt initial pointer grid) :
    TerminatesWith env Project.EulerCertificate.«module» 75 initial
      [.i64 pointer, .i64 owner, .i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧ values = vectorValues (Totals.physical n grid)) := by
  have sumCall := totals_sum_exact env initial owner pointer grid hGrid
  generalize hs : Totals.sum grid = total at sumCall
  have firstCall := vector_divPositive_exact env initial total (Time.smallNaturalBits n)
  generalize hf : Vectors.divPositive total (Time.smallNaturalBits n) = first at firstCall
  have secondCall := vector_divPositive_exact env initial first (Time.smallNaturalBits n)
  generalize ho : Vectors.divPositive first (Time.smallNaturalBits n) = out at secondCall
  simp only [Totals.physical, hs, hf, ho]
  refine TerminatesWith.of_wp_entry_for (f := func75Def) rfl ?_ (by decide)
  change wp Project.EulerCertificate.«module» func75 _ initial
    (func75Def.toLocals [.i64 (UInt64.ofNat n), .i64 owner, .i64 pointer]) env
  unfold func75
  wp_run [func75Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  guard_call (smallNaturalBits_exact env initial n hn)
  guard_call sumCall
  guard_call firstCall
  guard_call secondCall
  simp [vectorValues, boundsValues]

#print axioms totals_shape
#print axioms totals_sum_exact
#print axioms totals_physical_exact
end Project.EulerCertificate.Execution
