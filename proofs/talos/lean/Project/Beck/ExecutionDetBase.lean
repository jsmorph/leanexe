import Project.Beck.ExecutionScalar
import Project.ProofKit.BlockLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit

def determinantOuter : Wasm.Program :=
  match (func24[8]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def determinantParams (fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer : UInt64) :
    List Value := [.i64 fuel, .i64 width, .i64 matrixOwner, .i64 matrixPointer,
      .i64 rowOwner, .i64 rowPointer, .i64 columnOwner, .i64 columnPointer]

def determinantZeroFrame (width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer : UInt64) : Locals :=
  { params := determinantParams 0 width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
    locals := List.replicate 52 (.i64 0) }

set_option maxHeartbeats 600000 in
theorem determinant_zero_exact (env : HostEnv Unit) (initial : Store Unit)
    (width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer : UInt64) :
    TerminatesWith env Project.Beck.«module» 24 initial
      (determinantParams 0 width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer).reverse
      (fun final values => final = initial ∧ values = [.i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func24Def) rfl ?_
  change wp Project.Beck.«module» func24 _ initial
    (determinantZeroFrame width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer) env
  simp only [func24, determinantZeroFrame, determinantParams]
  wp_fixed_frame
  change wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 determinantOuter]] ++ func24.drop 9) _ initial
    (determinantZeroFrame width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer) env
  let inv : AssertionF Unit := fun store frame => store = initial ∧
    frame = determinantZeroFrame width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
  apply BlockLoop.program_spec Project.Beck.«module» env initial _ determinantOuter inv inv (fun _ _ => 0)
  · rintro store frame ⟨_, rfl⟩; rfl
  · rintro store frame ⟨_, rfl⟩; rfl
  · exact ⟨rfl, rfl⟩
  · rintro store frame ⟨rfl, rfl⟩
    simp only [determinantOuter, func24, List.getElem?_cons_zero, List.getElem?_cons_succ,
      determinantZeroFrame, determinantParams]
    wp_fixed_frame
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide)]
    wp_fixed_frame [List.take, List.append_nil, BlockLoop.stepPost]
    exact ⟨rfl, rfl⟩
  · rintro store frame ⟨rfl, rfl⟩
    simp only [func24, List.drop, determinantZeroFrame, determinantParams]
    wp_fixed_frame
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by decide)]
    wp_fixed_frame [List.take, List.append_nil, func24Def, determinantParams]
    simp

#print axioms determinant_zero_exact

end Project.Beck.Execution
