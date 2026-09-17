import LeanExe.WGSL.Profile
import LeanExe.WGSL.Generate

namespace LeanExe.WGSL

/-- The parsed body's accumulator update preserves the source addition operand
order. Fusion is the only permitted transformation in the v1 profiles. -/
inductive Accumulate (s : ScalarSemantics) (p : Profile)
    (acc x y : UInt32) : UInt32 → Prop where
  | separate {product result cm ca} :
      p.evaluation .separate → p.scalar cm → p.scalar ca →
      s.mul cm x y product → s.add ca acc product result →
      Accumulate s p acc x y result
  | fused {result c} : p.evaluation .fused → p.scalar c →
      s.fma c x y acc result → Accumulate s p acc x y result

theorem Accumulate.refines {s p q acc x y z} (hpq : p.Refines q)
    (h : Accumulate s p acc x y z) : Accumulate s q acc x y z := by
  cases h with
  | separate he hm ha mul add =>
      exact .separate (hpq.2 _ he) (hpq.1 _ hm) (hpq.1 _ ha) mul add
  | fused he hc op => exact .fused (hpq.2 _ he) (hpq.1 _ hc) op

theorem Accumulate.exists_of_total {s p c} (hc : p.scalar c)
    (he : p.evaluation .separate) (ht : ScalarTotal s c) (acc x y : UInt32) :
    ∃ z, Accumulate s p acc x y z := by
  obtain ⟨product, hm⟩ := ht.2.1 x y
  obtain ⟨result, ha⟩ := ht.1 acc product
  exact ⟨result, .separate he hc hc hm ha⟩

/-- Source-ordered matrix computation relation, independent of the invocation
machine. The initial word is positive zero, including its sign bit. -/
inductive Dot (s : ScalarSemantics) (p : Profile) (config : GemmConfig)
    (a b : WordBuffer) (row col : Nat) : Nat → UInt32 → Prop where
  | zero : Dot s p config a b row col 0 0
  | next {k acc result} : Dot s p config a b row col k acc →
      Accumulate s p acc (a (row * config.inner + k))
        (b (k * config.cols + col)) result →
      Dot s p config a b row col (k + 1) result

theorem Dot.refines {s p q config a b row col k z} (hpq : p.Refines q)
    (h : Dot s p config a b row col k z) : Dot s q config a b row col k z := by
  induction h with
  | zero => exact .zero
  | next _ update ih => exact .next ih (update.refines hpq)

/-- A concrete interpretation must prove this graph property; the structure
does not assert anything about native floating-point hardware. -/
structure SeparateInterpretation (s : ScalarSemantics) (arithmetic : ScalarArithmetic) : Prop where
  add : ∀ x y z, s.add ieeeChoice x y z ↔ z = arithmetic.add x y
  mul : ∀ x y z, s.mul ieeeChoice x y z ↔ z = arithmetic.mul x y

theorem Accumulate.restricted_exact {s arithmetic acc x y z}
    (hs : SeparateInterpretation s arithmetic)
    (h : Accumulate s restricted acc x y z) :
    z = arithmetic.add acc (arithmetic.mul x y) := by
  cases h with
  | separate _ hm ha mul add =>
      change _ = ieeeChoice at hm ha
      subst hm; subst ha
      rw [(hs.mul _ _ _).1 mul] at add
      exact (hs.add _ _ _).1 add
  | fused he _ _ => cases he

theorem Dot.restricted_exact {s arithmetic config a b row col k z}
    (hs : SeparateInterpretation s arithmetic)
    (h : Dot s restricted config a b row col k z) :
    z = gemmAccum arithmetic config a b row col k := by
  induction h with
  | zero => rfl
  | next _ update ih =>
      rw [update.restricted_exact hs, ih]
      rfl

#print axioms Accumulate.restricted_exact
#print axioms Dot.restricted_exact

end LeanExe.WGSL
