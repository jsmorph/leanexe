namespace LeanExe.WGSL

/-- The specification revision used by the experimental subset. -/
def wgslRevision : String := "2026-08-17"

inductive Rounding where
  | nearestEven | towardNegative | towardPositive
  deriving DecidableEq, Repr

inductive Subnormals where
  | preserve | flush
  deriving DecidableEq, Repr

inductive SignedZero where
  | ieee | eitherSign
  deriving DecidableEq, Repr

inductive Exceptional where
  | ieee | finiteOnly
  deriving DecidableEq, Repr

/-- Choices for one scalar operation; expression fusion is a separate choice. -/
structure ScalarChoice where
  rounding : Rounding
  operands : Subnormals
  results : Subnormals
  zero : SignedZero
  exceptional : Exceptional
  deriving DecidableEq, Repr

inductive Evaluation where
  | separate | fused
  deriving DecidableEq, Repr

/-- V1 keeps source order. This record does not admit general reassociation. -/
structure Profile where
  scalar : ScalarChoice → Prop
  evaluation : Evaluation → Prop

def ieeeChoice : ScalarChoice :=
  ⟨.nearestEven, .preserve, .preserve, .ieee, .ieee⟩

def restricted : Profile :=
  ⟨fun c => c = ieeeChoice, fun e => e = .separate⟩

def fusion : Profile :=
  ⟨fun c => c = ieeeChoice, fun _ => True⟩

def restrictedProfileId : String := "leanexe-f32-rne-separate-v1"
def fusionProfileId : String := "leanexe-f32-rne-fusion-v1"
def profileRevision : Nat := 1

def Profile.Refines (narrow broad : Profile) : Prop :=
  (∀ c, narrow.scalar c → broad.scalar c) ∧
  (∀ e, narrow.evaluation e → broad.evaluation e)

theorem Profile.Refines.refl (p : Profile) : p.Refines p :=
  ⟨fun _ h => h, fun _ h => h⟩

theorem Profile.Refines.trans {p q r : Profile}
    (hpq : p.Refines q) (hqr : q.Refines r) : p.Refines r :=
  ⟨fun c h => hqr.1 c (hpq.1 c h), fun e h => hqr.2 e (hpq.2 e h)⟩

theorem restricted_refines_fusion : restricted.Refines fusion :=
  ⟨fun _ h => h, fun _ _ => True.intro⟩

/-- Scalar interpretation is a separate obligation, not an axiom about hardware.
    The first profile lemmas are parametric in this interpretation. -/
structure ScalarSemantics where
  add : ScalarChoice → UInt32 → UInt32 → UInt32 → Prop
  mul : ScalarChoice → UInt32 → UInt32 → UInt32 → Prop
  fma : ScalarChoice → UInt32 → UInt32 → UInt32 → UInt32 → Prop

inductive Expr where
  | literal : UInt32 → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  /-- The source expression `a * b + c`, with local fusion permitted by profile. -/
  | madd : Expr → Expr → Expr → Expr

/-- Source-ordered scalar evaluation. Each operation may select an allowed
    scalar choice; local multiply-add evaluation may be fused or separate. -/
inductive Eval (s : ScalarSemantics) (p : Profile) : Expr → UInt32 → Prop where
  | literal (v) : Eval s p (.literal v) v
  | add {a b x y z c} : Eval s p a x → Eval s p b y →
      p.scalar c → s.add c x y z → Eval s p (.add a b) z
  | mul {a b x y z c} : Eval s p a x → Eval s p b y →
      p.scalar c → s.mul c x y z → Eval s p (.mul a b) z
  | separate {a b d x y z product result cm ca} :
      Eval s p a x → Eval s p b y → Eval s p d z →
      p.evaluation .separate → p.scalar cm → p.scalar ca →
      s.mul cm x y product → s.add ca product z result →
      Eval s p (.madd a b d) result
  | fused {a b d x y z result c} :
      Eval s p a x → Eval s p b y → Eval s p d z →
      p.evaluation .fused → p.scalar c → s.fma c x y z result →
      Eval s p (.madd a b d) result

theorem Eval.refines {s p q e v} (hpq : p.Refines q)
    (h : Eval s p e v) : Eval s q e v := by
  induction h with
  | literal v => exact .literal v
  | add _ _ hc hop ih₁ ih₂ => exact .add ih₁ ih₂ (hpq.1 _ hc) hop
  | mul _ _ hc hop ih₁ ih₂ => exact .mul ih₁ ih₂ (hpq.1 _ hc) hop
  | separate _ _ _ he hm ha hmul hadd ih₁ ih₂ ih₃ =>
      exact .separate ih₁ ih₂ ih₃ (hpq.2 _ he) (hpq.1 _ hm) (hpq.1 _ ha) hmul hadd
  | fused _ _ _ he hc hop ih₁ ih₂ ih₃ =>
      exact .fused ih₁ ih₂ ih₃ (hpq.2 _ he) (hpq.1 _ hc) hop

/-- Universal bounds transfer to a narrower profile, including fusion choices. -/
theorem Eval.bound_of_refines {s p q e} (hpq : p.Refines q)
    (bound : UInt32 → Prop) (hb : ∀ v, Eval s q e v → bound v) :
    ∀ v, Eval s p e v → bound v :=
  fun v h => hb v (h.refines hpq)

/-- Nonemptiness has to be supplied independently of a universal output claim. -/
def ScalarTotal (s : ScalarSemantics) (c : ScalarChoice) : Prop :=
  (∀ x y, ∃ z, s.add c x y z) ∧
  (∀ x y, ∃ z, s.mul c x y z) ∧
  (∀ x y z, ∃ result, s.fma c x y z result)

theorem Eval.exists_of_total {s p c} (hc : p.scalar c)
    (he : p.evaluation .separate) (ht : ScalarTotal s c) (e : Expr) :
    ∃ v, Eval s p e v := by
  induction e with
  | literal v => exact ⟨v, .literal v⟩
  | add a b iha ihb =>
      obtain ⟨x, hx⟩ := iha
      obtain ⟨y, hy⟩ := ihb
      obtain ⟨z, hz⟩ := ht.1 x y
      exact ⟨z, .add hx hy hc hz⟩
  | mul a b iha ihb =>
      obtain ⟨x, hx⟩ := iha
      obtain ⟨y, hy⟩ := ihb
      obtain ⟨z, hz⟩ := ht.2.1 x y
      exact ⟨z, .mul hx hy hc hz⟩
  | madd a b d iha ihb ihd =>
      obtain ⟨x, hx⟩ := iha
      obtain ⟨y, hy⟩ := ihb
      obtain ⟨z, hz⟩ := ihd
      obtain ⟨product, hm⟩ := ht.2.1 x y
      obtain ⟨result, ha⟩ := ht.1 product z
      exact ⟨result, .separate hx hy hz he hc hc hm ha⟩

end LeanExe.WGSL
