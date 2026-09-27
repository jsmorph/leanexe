import Project.Beck.ExecutionDirectionSupported

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionMaxBytes : Nat := 37290440

theorem directionBytes_bound (input : Input) (point : Point) (supported : Project.Beck.State.Supported input)
    (categories : input.categories ≤ 8) (nonempty : (Project.Beck.Counting.live input point).Nonempty) :
    directionBytes input point ≤ directionMaxBytes := by
  let basis := Project.Beck.Direction.sourceBasis input point
  have complete := Project.Beck.ProtectedMatrix.source_basis_complete input point supported.overlap nonempty
  have rank : basis.rows.size ≤ 6 := (Nat.le_of_lt complete.2.2).trans supported.capacity
  have columns : basis.columns.size ≤ 6 := by rw [← complete.1.square]; exact rank
  have matrixRows : (protectedMatrix input point).size / input.jobs ≤ 5 := by
    have short := (direction_matrix_bounds input point supported nonempty).2
    omega
  have search : directionSearchBytes input point ≤ 36088024 := by
    unfold directionSearchBytes findBasisRoundBytes
    calc
      _ ≤ 280 + 448 * 6 * 8 + 200368 * 6 * 5 * 6 := by gcongr <;> exact supported.capacity
      _ = 36088024 := by decide
  have coefficient : directionCofactorBytes basis input.jobs ≤ 200368 := by
    have det := determinantBytes_bound basis.rows.size rank
    unfold directionCofactorBytes
    have := supported.capacity
    omega
  have assembly : directionAssemblyBytes basis input.jobs ≤ 1202416 := by
    unfold directionAssemblyBytes
    calc
      _ ≤ 2 * (48 + 8 * (6 + 1)) + 200368 * 6 := by gcongr <;> exact supported.capacity
      _ = 1202416 := by decide
  unfold directionBytes directionMaxBytes
  change directionSearchBytes input point + directionAssemblyBytes basis input.jobs ≤ 37290440
  omega

#print axioms directionBytes_bound

end Project.Beck.Execution
