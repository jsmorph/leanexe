import Project.Gcd.Module
import Project.IR.TailLoop
import Project.Encoding.RoundTrip

namespace Project.Gcd

open Wasm Project.Pipeline Project.IR

/-- `gcd` with its two arguments as one pair. -/
def gcdTuple (x : UInt64 × UInt64) : UInt64 := LeanExe.Examples.Gcd.gcd x.1 x.2

theorem source_zero (a : UInt64) : LeanExe.Examples.Gcd.gcd a 0 = a := by
  rw [LeanExe.Examples.Gcd.gcd.eq_def]
  simp

theorem source_step (a b : UInt64) (h : b ≠ 0) :
    LeanExe.Examples.Gcd.gcd a b = LeanExe.Examples.Gcd.gcd b (a % b) := by
  rw [LeanExe.Examples.Gcd.gcd.eq_def]
  simp [h]

theorem gcdTuple_injective (x y : UInt64 × UInt64) (h : Scalar.values x = Scalar.values y) :
    x = y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp [Scalar.values] at h
  simp [h]

/-- One iteration of the compiled loop: at `b = 0` it stores `a`, and otherwise it
moves to `(b, a % b)`, which has the same gcd and a smaller `b`. -/
theorem gcd_step {m : Module} : TailStep (α := UInt64 × UInt64) m
    (match gcd.ir.body with | .while _ step => step | _ => .skip) gcd.ir.scratch 4 gcdTuple
    (fun x => x.2.toNat) := by
  rintro initial ⟨a, b⟩ result others hLength
  match others, hLength with
  | [v0, v1, v2, v3], _ =>
    refine (Stmt.ite_spec (Stmt.seq_spec Stmt.assign_spec Stmt.assign_spec)
      (Stmt.seq_spec Stmt.assign_spec (Stmt.seq_spec Stmt.assign_spec
        (Stmt.seq_spec Stmt.assign_spec Stmt.assign_spec)))).mono ?_ fun _ _ h => h
    rintro store state ⟨rfl, rfl⟩
    by_cases hZero : b = 0
    · subst hZero
      simp [tailState, Scalar.values, Expr.eval, State.get, State.set?, gcd.ir, Func.scratch,
        gcdTuple, source_zero]
    · simp [tailState, Scalar.values, Expr.eval, State.get, State.set?, U64Op.apply, hZero,
        gcd.ir, Func.scratch]
      refine ⟨by simp [gcdTuple, source_step a b hZero], Nat.mod_lt _ ?_⟩
      apply Nat.pos_of_ne_zero
      intro h
      exact hZero (UInt64.toNat_inj.mp (by simpa using h))

theorem gcd_implements : Implements gcd.module 0 gcdTuple (fun _ => 0) :=
  Func.tail_implements gcd.ir "gcd" gcdTuple (fun x => x.2.toNat) _ (fun _ => rfl)
    gcdTuple_injective (k := 2) rfl rfl rfl gcd_step

/-- The bytes `encode` produces for `gcd.module` decode to a module that
computes `gcd` exactly. -/
theorem gcd_bytes (bytes : ByteArray) (success : Wasm.Encoding.encode gcd.module = .ok bytes) :
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 0 gcdTuple (fun _ => 0) :=
  ⟨gcd.module, Wasm.Encoding.decode_encode gcd.module bytes (by decide) success,
    gcd_implements⟩

end Project.Gcd
