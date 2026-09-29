import Project.Gcd.Module
import Project.IR.Correct
import Project.Encoding.RoundTrip

namespace Project.Gcd

open Wasm Project.Pipeline Project.IR Project.ProofKit.ScalarTransition

/-- `gcd` with its two arguments as one pair. -/
def gcdTuple (x : UInt64 × UInt64) : UInt64 := LeanExe.Examples.Gcd.gcd x.1 x.2

theorem source_zero (a : UInt64) : LeanExe.Examples.Gcd.gcd a 0 = a := by
  rw [LeanExe.Examples.Gcd.gcd.eq_def]
  simp

theorem source_step (a b : UInt64) (h : b ≠ 0) :
    LeanExe.Examples.Gcd.gcd a b = LeanExe.Examples.Gcd.gcd b (a % b) := by
  rw [LeanExe.Examples.Gcd.gcd.eq_def]
  simp [h]

/-- The loop's local state: the parameters `a` and `b`, then `result`, `done`,
the two temporaries, and the two scratch locals of `%`. -/
def loopState (a b result done t0 t1 s0 s1 : UInt64) : State :=
  { params := [.i64 a, .i64 b],
    locals := [.i64 result, .i64 done, .i64 t0, .i64 t1, .i64 s0, .i64 s1] }

/-- The loop invariant for the call `gcd a₀ b₀`: the store is unchanged, and
either the loop continues with arguments whose gcd is the answer, or it has
stored the answer and set `done`. -/
def Invariant (initial : Store Unit) (a₀ b₀ : UInt64) (store : Store Unit) (state : State) :
    Prop :=
  store = initial ∧ ∃ a b result done t0 t1 s0 s1,
    state = loopState a b result done t0 t1 s0 s1 ∧
      ((done = 0 ∧ LeanExe.Examples.Gcd.gcd a b = LeanExe.Examples.Gcd.gcd a₀ b₀) ∨
        (done = 1 ∧ result = LeanExe.Examples.Gcd.gcd a₀ b₀))

def word (state : State) (index : Nat) : UInt64 :=
  match state.get index with
  | some (.i64 value) => value
  | _ => 0

/-- `b + 1` while the loop runs, and 0 once `done` is set. -/
def measure (_ : Store Unit) (state : State) : Nat :=
  if word state 3 = 0 then (word state 1).toNat + 1 else 0

theorem gcd_implements : Implements gcd.module 0 gcdTuple (fun _ => 0) := by
  refine Func.implements gcd.ir "gcd" gcdTuple (fun _ => rfl) fun ⟨a₀, b₀⟩ initial => ?_
  simp only [gcd.ir, Func.scratch]
  refine (Stmt.while_spec (Invariant initial a₀ b₀) measure ?_ fun n =>
    (Stmt.ite_spec (Stmt.seq_spec Stmt.assign_spec Stmt.assign_spec)
      (Stmt.seq_spec Stmt.assign_spec (Stmt.seq_spec Stmt.assign_spec
        (Stmt.seq_spec Stmt.assign_spec Stmt.assign_spec)))).mono ?_ fun _ _ h => h).mono ?_ ?_
  · rintro store state ⟨-, a, b, result, done, t0, t1, s0, s1, rfl, -⟩
    simp [loopState, Expr.eval, State.get]
  · rintro store state ⟨before, ⟨rfl, a, b, result, done, t0, t1, s0, s1, rfl, hInv⟩, hMeasure,
      hCondition⟩
    simp [loopState, Expr.eval, State.get] at hCondition
    obtain ⟨hDone, rfl⟩ := hCondition
    subst hDone
    have hContinue : LeanExe.Examples.Gcd.gcd a b = LeanExe.Examples.Gcd.gcd a₀ b₀ := by
      simpa using hInv
    subst hMeasure
    by_cases hZero : b = 0
    · subst hZero
      simp [Expr.eval, State.get, State.set?]
      refine ⟨⟨rfl, a, 0, a, 1, t0, t1, s0, s1, rfl, Or.inr ⟨rfl, ?_⟩⟩, ?_⟩
      · rw [← hContinue, source_zero]
      · simp [measure, word, loopState, State.get]
    · simp [Expr.eval, State.get, State.set?, hZero]
      have hMod : U64Op.remU.apply a b = a % b := by simp [U64Op.apply, hZero]
      rw [hMod]
      refine ⟨⟨rfl, b, a % b, result, 0, b, a % b, a, b, rfl, Or.inl ⟨rfl, ?_⟩⟩, ?_⟩
      · rw [← hContinue, source_step a b hZero]
      · have hPositive : 0 < b.toNat := by
          apply Nat.pos_of_ne_zero
          intro h
          exact hZero (UInt64.toNat_inj.mp (by simpa using h))
        have hLess := Nat.mod_lt a.toNat hPositive
        simp [measure, word, loopState, State.get, UInt64.toNat_mod]
        omega
  · rintro store state ⟨rfl, rfl⟩
    refine ⟨rfl, a₀, b₀, 0, 0, 0, 0, 0, 0, ?_, Or.inl ⟨rfl, rfl⟩⟩
    simp [Func.state, Func.width, loopState, IR.Stmt.scratchWidth, Expr.scratchWidth,
      Scalar.values]
  · rintro store state ⟨before, ⟨rfl, a, b, result, done, t0, t1, s0, s1, rfl, hInv⟩,
      hCondition⟩
    simp [loopState, Expr.eval, State.get] at hCondition
    obtain ⟨hDone, rfl⟩ := hCondition
    refine ⟨rfl, ?_⟩
    rcases hInv with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact absurd rfl hDone
    · simp [loopState, Expr.eval, State.get, gcdTuple]

/-- The bytes `encode` produces for `gcd.module` decode to a module that
computes `gcd` exactly. -/
theorem gcd_bytes (bytes : ByteArray) (success : Wasm.Encoding.encode gcd.module = .ok bytes) :
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 0 gcdTuple (fun _ => 0) :=
  ⟨gcd.module, Wasm.Encoding.decode_encode gcd.module bytes (by decide) success,
    gcd_implements⟩

end Project.Gcd
