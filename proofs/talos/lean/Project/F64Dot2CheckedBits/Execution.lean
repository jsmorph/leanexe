import Project.F64Dot2CheckedBits.Program
import Project.F64Dot2CheckedBits.Numerical
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Call

/-!
# Fuel-independent execution of the guarded binary64 dot product

The helper theorem gives the compiler-generated raw-bit guard its exact
integer meaning.  The exported-entry theorem composes four calls to that
helper and follows both the accepted and rejected branches.  Floating-point
instructions occur only in the accepted branch; their numerical meaning is
then supplied by `dot2CheckedBits_source_real_error`.
-/

namespace Wasm

/-! The upstream WP rule predates proof-visible block type annotations.  The
interpreter ignores those annotations at execution time, so this local rule is
the same theorem with the two annotation lists made explicit. -/

private theorem exec_iff_typed_cons
    {m : Module} {env : HostEnv α} {st : Store α} {s : Locals}
    {ps rs : Nat} {thn els rest : Program} {fuel : Nat}
    {paramTypes resultTypes : List ValueType}
    {c : UInt32} {vs : List Value}
    (hStack : s.values = .i32 c :: vs) :
    exec (fuel + 1) m st s
        (.iff ps rs thn els paramTypes resultTypes :: rest) env =
      (match exec fuel m st { s with values := vs }
                (if c ≠ 0 then thn else els) env with
       | .Break 0 st' s'       =>
         exec (fuel + 1) m st'
           { s' with values := s'.values.take rs ++ vs.drop ps } rest env
       | .Break (k + 1) st' s' => .Break k st' s'
       | .Fallthrough st' s'   =>
         exec (fuel + 1) m st'
           { s' with values := s'.values.take rs ++ vs.drop ps } rest env
       | other                 => other) := by
  simp only [exec, execOne.eq_def, hStack]
  by_cases hc : c ≠ 0
  · simp only [if_pos hc]
    cases exec fuel m st { s with values := vs } thn env with
    | Fallthrough _ _ => rfl
    | Break n _ _ => cases n <;> rfl
    | Return _ _ => rfl
    | Trap _ _ => rfl
    | Invalid _ => rfl
    | OutOfFuel => rfl
    | ReturnCall _ _ _ => rfl
    | Throwing _ _ _ _ => rfl
  · simp only [if_neg hc]
    cases exec fuel m st { s with values := vs } els env with
    | Fallthrough _ _ => rfl
    | Break n _ _ => cases n <;> rfl
    | Return _ _ => rfl
    | Trap _ _ => rfl
    | Invalid _ => rfl
    | OutOfFuel => rfl
    | ReturnCall _ _ _ => rfl
    | Throwing _ _ _ _ => rfl

private theorem wp_iff_typed_cons
    {env : HostEnv α} {m : Module} {st : Store α} {s : Locals}
    {ps rs : Nat} {thn els rest : Program} {Q : Assertion α}
    {paramTypes resultTypes : List ValueType}
    {c : UInt32} {vs : List Value}
    (hStack : s.values = .i32 c :: vs)
    (hBody : wp m (if c ≠ 0 then thn else els)
              (fun cont => match cont with
                | .Fallthrough st' s'   =>
                  wp m rest Q st'
                    { s' with values := s'.values.take rs ++ vs.drop ps } env
                | .Break 0 st' s'       =>
                  wp m rest Q st'
                    { s' with values := s'.values.take rs ++ vs.drop ps } env
                | .Break (k + 1) st' s' => Q (.Break k st' s')
                | other                 => Q other)
              st { s with values := vs } env) :
    wp m (.iff ps rs thn els paramTypes resultTypes :: rest) Q st s env := by
  refine wp_of_body_dispatch hBody ?_ ?_ ?_ ?_ ?_
  · intro f cont hcont hbody
    cases cont <;>
      first
        | exact (hcont : False).elim
        | rw [exec_iff_typed_cons hStack, hbody]
  · intro cont hcont hQ
    cases cont <;>
      first
        | exact (hcont : False).elim
        | exact hQ
  · intro N st' s' hQ hstable
    refine wp_of_eventually_eq (N := N + 1) ?_ hQ
    intro fuel hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [exec_iff_typed_cons hStack, hstable f (by omega)]
  · intro N st' s' hQ hstable
    refine wp_of_eventually_eq (N := N + 1) ?_ hQ
    intro fuel hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [exec_iff_typed_cons hStack, hstable f (by omega)]
  · intro N k st' s' hQ hstable
    refine wp_of_eventually_const (N := N + 1)
      (cont := .Break k st' s') ?_ hQ
    intro fuel hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [exec_iff_typed_cons hStack, hstable f (by omega)]

end Wasm

namespace Project.F64Dot2CheckedBits.Spec

open Wasm

/-- Exact i64 result returned by the generated raw-bit guard helper. -/
private def guardResultModel (bits : UInt64) : UInt64 :=
  if Bounds.f64AbsBits bits ≤ 0x3FE0000000000000 then 1 else 0

/-- The generated helper returns one exactly when the sign-cleared encoding
is at most the encoding of one half, and otherwise returns zero. -/
theorem func0_exact
    (env : HostEnv Unit) (initial : Store Unit) (bits : UInt64) :
    TerminatesWith env Project.F64Dot2CheckedBits.«module» 0 initial
      [.i64 bits]
      (fun final values =>
        final = initial ∧ values = [.i64 (guardResultModel bits)]) := by
  apply TerminatesWith.of_wp_entry_for
    (f := Project.F64Dot2CheckedBits.func0Def)
  · simp [Project.F64Dot2CheckedBits.«module»]
  · change wp Project.F64Dot2CheckedBits.«module»
      Project.F64Dot2CheckedBits.func0 _ initial
      { params := [.i64 bits], locals := [.i64 0], values := [] } env
    unfold Project.F64Dot2CheckedBits.func0
    wp_run
    apply wp_iff_typed_cons <;> try rfl
    by_cases hguard :
        Bounds.f64AbsBits bits ≤ (0x3FE0000000000000 : UInt64)
    · rw [if_pos (by simpa [Project.ProofKit.F64Bounds.f64AbsBits] using hguard)]
      wp_run
      simp [Project.F64Dot2CheckedBits.func0Def, guardResultModel, hguard]
    · rw [if_neg (by
        have hnat :
            (0x3FE0000000000000 : UInt64).toNat <
              (Bounds.f64AbsBits bits).toNat := by
          rw [← Nat.not_le]
          intro hle
          exact hguard (UInt64.le_iff_toNat_le.mpr hle)
        have hlt :
            (0x3FE0000000000000 : UInt64) < Bounds.f64AbsBits bits :=
          UInt64.lt_iff_toNat_lt.mpr hnat
        simpa [Project.ProofKit.F64Bounds.f64AbsBits] using hlt)]
      wp_run
      simp [Project.F64Dot2CheckedBits.func0Def, guardResultModel, hguard]

/-- Fuel-independent exact behavior of the generated exported entry.  Wasm's
operand stack is top-first, so the source structure fields `status, bits`,
pushed in that order, are observed as `bits, status`. -/
def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
    (a₀ b₀ a₁ b₁ : UInt64),
    TerminatesWith env m 1 initial
      [.i64 b₁, .i64 a₁, .i64 b₀, .i64 a₀]
      (fun final values =>
        final = initial ∧
          values =
            [.i64 (dot2ResultBitsModel a₀ b₀ a₁ b₁),
             .i64 (dot2StatusModel a₀ b₀ a₁ b₁)])

/-- The exact generated-WAT result additionally satisfies the total source
contract: accepted inputs carry the finite/error theorem, while rejected
inputs return status one and zero result bits. -/
noncomputable def RealErrorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
    (a₀ b₀ a₁ b₁ : UInt64),
    TerminatesWith env m 1 initial
      [.i64 b₁, .i64 a₁, .i64 b₀, .i64 a₀]
      (fun final values =>
        final = initial ∧
          values =
            [.i64 (dot2ResultBitsModel a₀ b₀ a₁ b₁),
             .i64 (dot2StatusModel a₀ b₀ a₁ b₁)] ∧
          CheckedResult a₀ b₀ a₁ b₁
            (dot2StatusModel a₀ b₀ a₁ b₁)
            (dot2ResultBitsModel a₀ b₀ a₁ b₁))

/-- Every input takes one of five paths: the first failing guard rejects, or
all four guards pass and the two multiplications and final addition execute.
All paths preserve the complete WebAssembly store. -/
theorem dot2CheckedBits_exact :
    ExactSpecFor Project.F64Dot2CheckedBits.«module» := by
  intro env initial a₀ b₀ a₁ b₁
  apply TerminatesWith.of_wp_entry_for
    (f := Project.F64Dot2CheckedBits.func1Def)
  · simp [Project.F64Dot2CheckedBits.«module»]
  · change wp Project.F64Dot2CheckedBits.«module»
      Project.F64Dot2CheckedBits.func1 _ initial
      { params := [.i64 a₀, .i64 b₀, .i64 a₁, .i64 b₁],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold Project.F64Dot2CheckedBits.func1
    wp_run
    refine wp_call_tw (func0_exact env initial a₀) ?_
    rintro st₁ values₁ ⟨hst₁, rfl⟩
    subst st₁
    wp_run
    apply wp_iff_typed_cons <;> try rfl
    by_cases ha₀ :
        Bounds.f64AbsBits a₀ ≤ (0x3FE0000000000000 : UInt64)
    · rw [if_pos (by simp [guardResultModel, ha₀])]
      wp_run
      refine wp_call_tw (func0_exact env initial b₀) ?_
      rintro st₂ values₂ ⟨hst₂, rfl⟩
      subst st₂
      wp_run
      refine wp_iff_typed_cons rfl ?_
      by_cases hb₀ :
          Bounds.f64AbsBits b₀ ≤ (0x3FE0000000000000 : UInt64)
      · rw [if_pos (by simp [guardResultModel, hb₀])]
        wp_run
        refine wp_call_tw (func0_exact env initial a₁) ?_
        rintro st₃ values₃ ⟨hst₃, rfl⟩
        subst st₃
        wp_run
        refine wp_iff_typed_cons rfl ?_
        by_cases ha₁ :
            Bounds.f64AbsBits a₁ ≤ (0x3FE0000000000000 : UInt64)
        · rw [if_pos (by simp [guardResultModel, ha₁])]
          wp_run
          refine wp_call_tw (func0_exact env initial b₁) ?_
          rintro st₄ values₄ ⟨hst₄, rfl⟩
          subst st₄
          wp_run
          refine wp_iff_typed_cons rfl ?_
          by_cases hb₁ :
              Bounds.f64AbsBits b₁ ≤ (0x3FE0000000000000 : UInt64)
          · rw [if_pos (by simp [guardResultModel, hb₁])]
            wp_run
            refine wp_iff_typed_cons rfl ?_
            rw [if_pos (by simp)]
            wp_run
            refine wp_iff_typed_cons rfl ?_
            rw [if_pos (by simp)]
            wp_run
            simp [Project.F64Dot2CheckedBits.func1Def,
              dot2ResultBitsModel, dot2StatusModel, dot2Guard,
              Project.ProofKit.F64Bounds.boundedByHalfBits,
              dot2BitsModel, Wasm.f64Mul,
              Wasm.f64Add, ha₀, hb₀, ha₁, hb₁]
          · rw [if_neg (by simp [guardResultModel, hb₁])]
            wp_run
            refine wp_iff_typed_cons rfl ?_
            rw [if_neg (by simp)]
            wp_run
            refine wp_iff_typed_cons rfl ?_
            rw [if_neg (by simp)]
            wp_run
            simp [Project.F64Dot2CheckedBits.func1Def,
              dot2ResultBitsModel, dot2StatusModel, dot2Guard,
              Project.ProofKit.F64Bounds.boundedByHalfBits, hb₁]
        · rw [if_neg (by simp [guardResultModel, ha₁])]
          wp_run
          refine wp_iff_typed_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          refine wp_iff_typed_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          refine wp_iff_typed_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          simp [Project.F64Dot2CheckedBits.func1Def,
            dot2ResultBitsModel, dot2StatusModel, dot2Guard,
            Project.ProofKit.F64Bounds.boundedByHalfBits, ha₁]
      · rw [if_neg (by simp [guardResultModel, hb₀])]
        wp_run
        refine wp_iff_typed_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        refine wp_iff_typed_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        refine wp_iff_typed_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        refine wp_iff_typed_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        simp [Project.F64Dot2CheckedBits.func1Def,
          dot2ResultBitsModel, dot2StatusModel, dot2Guard,
          Project.ProofKit.F64Bounds.boundedByHalfBits, hb₀]
    · rw [if_neg (by simp [guardResultModel, ha₀])]
      wp_run
      refine wp_iff_typed_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      refine wp_iff_typed_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      refine wp_iff_typed_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      refine wp_iff_typed_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      refine wp_iff_typed_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      simp [Project.F64Dot2CheckedBits.func1Def,
        dot2ResultBitsModel, dot2StatusModel, dot2Guard,
        Project.ProofKit.F64Bounds.boundedByHalfBits, ha₀]

/-- The decoded compiler-generated WAT has exactly the source contract on all
inputs, independently of interpreter fuel. -/
theorem dot2CheckedBits_wat_real_error :
    RealErrorSpecFor Project.F64Dot2CheckedBits.«module» := by
  intro env initial a₀ b₀ a₁ b₁
  refine TerminatesWith.mono
    (dot2CheckedBits_exact env initial a₀ b₀ a₁ b₁) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl,
    dot2CheckedBits_source_real_error a₀ b₀ a₁ b₁⟩

#print axioms func0_exact
#print axioms dot2CheckedBits_exact
#print axioms dot2CheckedBits_wat_real_error

end Project.F64Dot2CheckedBits.Spec
