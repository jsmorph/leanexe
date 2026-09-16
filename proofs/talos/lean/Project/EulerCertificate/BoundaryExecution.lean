import Project.EulerCertificate.BoundaryLoop

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerRiemann
open Project.EulerCertificateFlux.Execution (boundsValues vectorValues)
open Project.EulerRiemann.Execution (boolWord)

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def boundaryHead : Wasm.Program := func173.take 78
def boundaryTail : Wasm.Program := func173.drop 79

theorem boundary_shape :
    func173 = boundaryHead ++ [.block 0 0 [.loop 0 0 boundaryLoop]] ++ boundaryTail := by
  have tail : func173.drop 37 = AnnotationMatches.function_173_array_fold_0_program ++
      func173.drop 103 := AnnotationMatches.function_173_array_fold_0_tail_eq
  calc
    func173 = func173.take 37 ++ func173.drop 37 := (List.take_append_drop 37 func173).symm
    _ = func173.take 37 ++ (AnnotationMatches.function_173_array_fold_0_program ++
        func173.drop 103) := by rw [tail]
    _ = boundaryHead ++ [.block 0 0 [.loop 0 0 boundaryLoop]] ++ boundaryTail := rfl

theorem boundary_sum_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (trials : UInt64) (axis : Bool) (owner pointer : UInt64)
    (grid : Array Traversal.Cell) (hn : 2 ≤ n ∧ n ≤ 800)
    (hIndexed : Traversal.Indexed n grid) (hGrid : Memory.GridAt initial pointer grid) :
    TerminatesWith env Project.EulerCertificate.«module» 173 initial
      [.i64 pointer, .i64 owner, .i64 (boolWord axis), .i64 trials, .i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧
        values = vectorValues (Boundary.sum n trials.toNat axis grid)) := by
  have hLength := hGrid.lengthRead
  have hBound := Nat.not_lt.mpr hGrid.lengthBound
  have hnSize : n < grid.size := by rw [hIndexed.1]; nlinarith [hn.1]
  have hn64 : n < UInt64.size := lt_trans hnSize hGrid.size_lt
  have hEncoded : UInt64.ofNat n < UInt64.ofNat grid.size := by
    simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hn64,
      UInt64.toNat_ofNat_of_lt' hGrid.size_lt] using hnSize
  refine TerminatesWith.of_wp_entry_for (f := func173Def) rfl ?_ (by decide)
  change wp Project.EulerCertificate.«module» func173 _ initial
    (func173Def.toLocals [.i64 (UInt64.ofNat n), .i64 trials,
      .i64 (boolWord axis), .i64 owner, .i64 pointer]) env
  rw [boundary_shape]
  unfold boundaryHead func173
  dsimp only
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  wp_run [func173Def]
  refine wp_call_tw (vector_zero_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  simp only [vectorValues, boundsValues, Vectors.zero, List.append]
  wp_run [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    ← Project.ProofKit.Memory.toUInt32_eq_ofNat, UInt32.add_zero, UInt32.toNat_zero,
    Nat.add_zero, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, hLength, hBound]
  boundary_loop_peel
  change wp _ _ _ _
    (boundaryFrame n trials axis owner pointer grid.size 0 Vectors.zero {}) _
  nth_rw 1 [← boundaryPrefix_zero n trials.toNat axis grid]
  apply boundary_loop_spec env initial n trials axis owner pointer grid hn hIndexed hGrid
    0 (Nat.zero_le _) {}
  intro scratch
  unfold func173
  dsimp only
  boundary_loop_peel
  simp [boundaryPrefix_complete]

theorem boundary_physicalStep_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (trials dt : UInt64) (owner pointer middleOwner middlePointer : UInt64)
    (grid middle : Array Traversal.Cell) (hn : 2 ≤ n ∧ n ≤ 800)
    (hIndexed : Traversal.Indexed n grid) (hMiddleIndexed : Traversal.Indexed n middle)
    (hGrid : Memory.GridAt initial pointer grid) (hMiddle : Memory.GridAt initial middlePointer middle) :
    TerminatesWith env Project.EulerCertificate.«module» 175 initial
      [.i64 middlePointer, .i64 middleOwner, .i64 pointer, .i64 owner,
        .i64 dt, .i64 trials, .i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧
        values = vectorValues (Boundary.physicalStep n trials.toNat dt grid middle)) := by
  have xCall := boundary_sum_exact env initial n trials false owner pointer grid hn hIndexed hGrid
  have yCall := boundary_sum_exact env initial n trials true middleOwner middlePointer middle
    hn hMiddleIndexed hMiddle
  generalize hx : Boundary.sum n trials.toNat false grid = x at xCall
  generalize hy : Boundary.sum n trials.toNat true middle = y at yCall
  have addCall := vector_add_exact env initial x y
  generalize hSum : Vectors.add x y = flux at addCall
  have scaleCall := vector_scale_exact env initial flux dt
  generalize hScale : Vectors.scale flux dt = scaled at scaleCall
  have divCall := vector_divPositive_exact env initial scaled (Time.smallNaturalBits n)
  generalize hDiv : Vectors.divPositive scaled (Time.smallNaturalBits n) = out at divCall
  simp only [Boundary.physicalStep, hx, hy, hSum, hScale, hDiv]
  refine TerminatesWith.of_wp_entry_for (f := func175Def) rfl ?_ (by decide)
  change wp Project.EulerCertificate.«module» func175 _ initial
    (func175Def.toLocals [.i64 (UInt64.ofNat n), .i64 trials, .i64 dt,
      .i64 owner, .i64 pointer, .i64 middleOwner, .i64 middlePointer]) env
  unfold func175
  wp_run [func175Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  boundary_face_call xCall
  boundary_face_call yCall
  boundary_face_call addCall
  boundary_face_call scaleCall
  boundary_face_call (smallNaturalBits_exact env initial n hn.2)
  boundary_face_call divCall
  simp

#print axioms boundary_shape
#print axioms boundary_sum_exact
#print axioms boundary_physicalStep_exact
end Project.EulerCertificate.Execution
