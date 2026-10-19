import Verified.ExprSpec
import Verified.Float32Facts
import LeanExe.ProofKit.F32Nearest

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit}
  {pv : List Value}

/-- A float constant, from its bit pattern. -/
theorem spec_float32 {Γ : List Ty} (bits : UInt32) :
    ∀ env slots paid live,
      CodeSpec m funs flags bounds fits host pv (Expr.float32 (S := S) (Γ := Γ) bits) env slots
          paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt _ _ _ _ rest Q _ hNext
  have hNext0 := fun store' s' ws a =>
    hNext heap store' s' ws a (fun _ => Nat.le_add_right _ _)
  simpa [Expr.code, Expr.usesFast_eq, Expr.denote, F32Bits.toBits_ofBits] using
    hNext0 store s [.f32 (Float32.ofBits bits).toBits] (After.refl hAt hVars
      (by intro i h; simp [h]) rfl (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .float32 rfl] at hb; exact nomatch hb)


/-- An operation on floats. -/
theorem spec_fbin32 {Γ : List Ty} (op : FBinOp) {left right : Expr S Γ .float32}
    (leftSpec : ∀ env slots paid live, CodeSpec m funs flags bounds fits host pv left env slots paid live)
    (rightSpec : ∀ env slots paid live, CodeSpec m funs flags bounds fits host pv right env
        slots paid live) :
    ∀ env slots paid live, CodeSpec m funs flags bounds fits host pv (Expr.fbin32 op left right) env
        slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  refine seq_spec leftSpec rightSpec env slots paid live h base heap store s hh hpv
      hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a (fitsOf hTop)
  have hR1' : ws1 = [.f32 (left.denote funs env).toBits] := hR1
  have hR2' : ws2 = [.f32 (right.denote funs env).toBits] := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 store2 s2 [.f32 ((Expr.fbin32 op left right).denote funs env).toBits]
    (After.ofScalar rfl hStep' rfl hF hH rfl)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hv ⊢
  cases op <;>
    simpa [FBinOp.instr32, Expr.denote, FBinOp.apply32, f32Add, f32Sub, f32Mul, f32Div,
      F32Bits.toBits_add, F32Bits.toBits_sub, F32Bits.toBits_mul, F32Bits.toBits_div] using hv


/-- A comparison of floats. -/
theorem spec_fcmp32 {Γ : List Ty} (op : FCmpOp) {left right : Expr S Γ .float32}
    (leftSpec : ∀ env slots paid live, CodeSpec m funs flags bounds fits host pv left env slots paid live)
    (rightSpec : ∀ env slots paid live, CodeSpec m funs flags bounds fits host pv right env
        slots paid live) :
    ∀ env slots paid live, CodeSpec m funs flags bounds fits host pv (Expr.fcmp32 op left right) env
        slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  refine seq_spec leftSpec rightSpec env slots paid live h base heap store s hh hpv
      hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a (fitsOf hTop)
  have hR1' : ws1 = [.f32 (left.denote funs env).toBits] := hR1
  have hR2' : ws2 = [.f32 (right.denote funs env).toBits] := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hv ⊢
  cases op <;>
    simp only [FCmpOp.instr32, wp_f32Lt_cons, wp_f32Le_cons, wp_f32Eq_cons, wp_extendUI32_cons]
  · cases hc : IEEE32.lt (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply32, F32Bits.decide_lt, f32Lt, boolWord] using hv
  · cases hc : IEEE32.le (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply32, F32Bits.decide_le, f32Le, boolWord] using hv
  · cases hc : IEEE32.eq (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply32, F32Bits.beq_eq, f32Eq, boolWord] using hv


/-- An operation on one float.  The negation subtracts from negative zero, pushed first. -/
theorem spec_funary32 {Γ : List Ty} (op : F32UnOp) {e : Expr S Γ .float32}
    (eSpec : ∀ env slots paid live, CodeSpec m funs flags bounds fits host pv e env slots paid live) :
    ∀ env slots paid live, CodeSpec m funs flags bounds fits host pv (Expr.funary32 op e) env
        slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  simp only [Expr.code, Expr.usesFast_eq]
  cases op with
  | neg =>
    simp only [F32UnOp.code, List.cons_append, List.append_assoc, wp_f32Const_cons]
    refine eSpec env slots paid live h base heap store { s with values := .f32 0x80000000 ::
      s.values } hh hpv (hVars.agree Frame.ofValues) hAt hCap hBase hRoom hPlace _ _
      (by rw [dyingPot_values]; exact hTrap)
      fun heap1 store1 s1 ws a1 hTop => ?_
    have hNext1 := fun store' s' ws a =>
      hNext heap1 store' s' ws a fun hf => top_part rfl (dyingPot_values _ _ _).le (hTop hf)
    have hR : ws = [.f32 (e.denote funs env).toBits] := a1.rep
    subst hR
    have hStep := a1.step
    rw [Mode.fresh_scalar rfl] at hStep
    have hv := hNext1 store1 s1 [.f32 (-(e.denote funs env)).toBits]
      (After.ofValues (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl))
    simpa [Expr.denote, F32UnOp.apply, f32Sub, F32Bits.toBits_neg] using hv
  | sqrt | abs | nearest =>
    simp only [F32UnOp.code, List.append_assoc, List.cons_append, List.nil_append]
    refine eSpec env slots paid live h base heap store s hh hpv hVars hAt hCap hBase
        hRoom hPlace _ _
        hTrap
      fun heap1 store1 s1 ws a1 hTop => ?_
    have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a fun hf => top_part rfl
        le_rfl (hTop hf)
    have hR : ws = [.f32 (e.denote funs env).toBits] := a1.rep
    subst hR
    have hStep := a1.step
    rw [Mode.fresh_scalar rfl] at hStep
    have hv := hNext1 store1 s1 [.f32 ((Expr.funary32 _ e).denote funs env).toBits]
      (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
    simpa [Expr.denote, F32UnOp.apply, f32Sqrt, f32Abs, F32Bits.toBits_sqrt, F32Bits.toBits_abs, f32Nearest, F32Nearest.toBits_nearest]
      using hv


/-- A conversion of a word to a float. -/
theorem spec_toFloat32 {Γ : List Ty} (op : ToFloat32) {e : Expr S Γ .word}
    (eSpec : ∀ env slots paid live, CodeSpec m funs flags bounds fits host pv e env slots paid live) :
    ∀ env slots paid live, CodeSpec m funs flags bounds fits host pv (Expr.toFloat32 op e) env
        slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  refine eSpec env slots paid live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace _ _
      hTrap
    fun heap1 store1 s1 ws a1 hTop => ?_
  have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a fun hf => top_part
      rfl le_rfl (hTop hf)
  have hR : ws = [.i64 (e.denote funs env)] := a1.rep
  subst hR
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  have hv := hNext1 store1 s1 [.f32 ((Expr.toFloat32 op e).denote funs env).toBits]
    (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
  cases op <;>
    simpa [ToFloat32.code, Expr.denote, ToFloat32.apply, f32ConvertI64U, f32Add,
      Float32Facts.toBits_toFloat32, F32Bits.toBits_ofBits, Float32Facts.add_negZero,
      wrap_toUInt32_num, f32ConvertI32S, Float32Facts.signed32_toFloat] using hv


/-- A conversion of a float to a word. -/
theorem spec_toWord32 {Γ : List Ty} (op : ToWord32) {e : Expr S Γ .float32}
    (eSpec : ∀ env slots paid live, CodeSpec m funs flags bounds fits host pv e env slots paid live) :
    ∀ env slots paid live, CodeSpec m funs flags bounds fits host pv (Expr.toWord32 op e) env
        slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  refine eSpec env slots paid live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace _ _
      hTrap
    fun heap1 store1 s1 ws a1 hTop => ?_
  have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a fun hf => top_part
      rfl le_rfl (hTop hf)
  have hR : ws = [.f32 (e.denote funs env).toBits] := a1.rep
  subst hR
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  have hv := hNext1 store1 s1 [.i64 ((Expr.toWord32 op e).denote funs env)]
    (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
  cases op <;>
    simpa [ToWord32.code, Expr.denote, ToWord32.apply, i64TruncSatF32U, Float32Facts.toUInt64_eq, Float32Facts.to_signed32, i32TruncSatF32S]
      using hv


end Cases

#print axioms spec_float32
#print axioms spec_fbin32
#print axioms spec_fcmp32
#print axioms spec_funary32
#print axioms spec_toFloat32
#print axioms spec_toWord32

end Verified
