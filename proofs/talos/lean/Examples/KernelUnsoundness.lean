import Lean

/-!
# A kernel-level unsoundness, reduced to a general exploit

This file derives `False` in Lean 4.31.0 with no axioms and no `sorry`.
It exists to demonstrate what the execution gate catches that the proof
gate cannot, and nothing in the `Project` library imports it.  Keep it
that way: importing this module makes every statement in the importing
module provable.

The construction is taken from the CollatzLean development
(https://github.com/xrchz/CollatzLean), which uses it to derive
`¬ Collatz.Conjecture`.  The Collatz content plays no part.  Retargeting
the same machinery at a `Bool`-indexed family whose `false` index is
empty yields `False` directly, so the development establishes nothing
about the Collatz conjecture.

Two ingredients combine, and measurement shows both are required.

The first is `addDecl` with a hand-built `.inductDecl`.  The constructor
type of `ProfileEnvelope` below contains the projection chain
`orbit.1.1`, which reads a `Bool` field out of an `OrbitCarrier` whose
`observed` constructor carries a `Prop`.  Source-level Lean rejects that
projection, and so does the kernel when it type-checks a definition
containing one, but the inductive declaration path admits it.

The second is a hash collision.  The parity summaries are
`(fun _stage => false) 78670` and `(fun _stage => true) 24083`, chosen so
that `Expr.hash` and `Expr.approxDepth` agree on two structurally
different terms.  Replacing the literals with non-colliding ones makes
the kernel reject the final declaration with "invalid projection", so
hash equality between distinct terms is defeating a kernel check.
-/

open Lean Elab Command

namespace Examples.KernelUnsoundness

inductive OrbitToken : Prop where
  | record (parity : Bool)

structure NormalizedStep where
  parity : Bool

inductive OrbitCarrier : Type where
  | normalized (value : NormalizedStep)
  | observed (token : OrbitToken)

inductive DescentLayer (α : Type) (parity : Bool) (carrier : OrbitCarrier) :
    Type where
  | mk

def OrbitCarrier.fromToken (token : OrbitToken) : OrbitCarrier :=
  OrbitCarrier.observed token

def exceptionalState : Bool := false

def descendingState : Bool := true

/-- The target family: inhabited at `true`, empty at `false`. -/
inductive DescentProfile : Bool → Prop
  | descending : DescentProfile descendingState

theorem stableDescentProfile : DescentProfile descendingState :=
  DescentProfile.descending

theorem exceptional_absurd : DescentProfile exceptionalState → False := by
  intro h
  cases h

def stableParity : Bool := descendingState

namespace Construction

structure OrbitStages where
  exceptionalParity : Expr
  descendingParity : Expr
  exceptionalOrbit : Expr
  descendingOrbit : Expr

private def stageParity (value : Expr) (n : Nat) : Expr :=
  mkApp (mkLambda `_stage .default (mkConst ``Nat) value) (.lit (.natVal n))

private def ns : Name := `Examples.KernelUnsoundness

/-- The colliding parity summaries, with the collision asserted. -/
def collectOrbitStages : CommandElabM OrbitStages := do
  let exceptionalParity := stageParity (mkConst ``Bool.false) 78670
  let descendingParity := stageParity (mkConst ``Bool.true) 24083
  unless exceptionalParity.hash == descendingParity.hash &&
      exceptionalParity.approxDepth == descendingParity.approxDepth do
    throwError "parity summaries do not collide"

  let exceptionalToken := mkApp (mkConst (ns ++ `OrbitToken.record)) exceptionalParity
  let descendingToken := mkApp (mkConst (ns ++ `OrbitToken.record)) descendingParity
  let exceptionalOrbit := mkApp (mkConst (ns ++ `OrbitCarrier.fromToken)) exceptionalToken
  let descendingOrbit := mkApp (mkConst (ns ++ `OrbitCarrier.fromToken)) descendingToken
  unless exceptionalOrbit.hash == descendingOrbit.hash &&
      exceptionalOrbit.approxDepth == descendingOrbit.approxDepth do
    throwError "orbit carriers do not collide"

  return { exceptionalParity, descendingParity, exceptionalOrbit, descendingOrbit }

def checkProjectionCollision (stages : OrbitStages) : CommandElabM Unit := do
  let exceptionalProjection :=
    mkProj (ns ++ `NormalizedStep) 0
      (mkProj (ns ++ `NormalizedStep) 0 stages.exceptionalOrbit)
  let descendingProjection :=
    mkProj (ns ++ `NormalizedStep) 0
      (mkProj (ns ++ `NormalizedStep) 0 stages.descendingOrbit)
  unless exceptionalProjection.hash == descendingProjection.hash &&
      exceptionalProjection.approxDepth == descendingProjection.approxDepth do
    throwError "parity projections do not collide"

/-- Declare `ProfileEnvelope` with `orbit.1.1` in its constructor type.
Source-level Lean cannot express this. -/
private def addEnvelopeType : CommandElabM Unit := do
  let envelopeName := ns ++ `ProfileEnvelope
  let envelopeCtorName := ns ++ `ProfileEnvelope.mk
  let orbit := mkBVar 0
  let envelopeAtOrbit := mkApp (mkConst envelopeName) orbit
  let normalized := mkProj (ns ++ `NormalizedStep) 0 orbit
  let parity := mkProj (ns ++ `NormalizedStep) 0 normalized
  let layerType :=
    mkApp3 (mkConst (ns ++ `DescentLayer)) envelopeAtOrbit parity orbit
  let envelopeType :=
    mkForall `orbit .default (mkConst (ns ++ `OrbitCarrier)) (mkSort 1)
  let ctorResult := mkApp (mkConst envelopeName) (mkBVar 1)
  let envelopeCtorType :=
    mkForall `orbit .default (mkConst (ns ++ `OrbitCarrier)) <|
      mkForall `layer .default layerType ctorResult
  liftCoreM <| addDecl <| .inductDecl [] 1 [{
    name := envelopeName
    type := envelopeType
    ctors := [{ name := envelopeCtorName, type := envelopeCtorType }]
  }] false

private def addSynchronizedProfile (stages : OrbitStages) : CommandElabM Unit := do
  liftCoreM <| addDecl <| .defnDecl {
    name := ns ++ `synchronizedDescentProfile
    levelParams := []
    type := mkApp (mkConst (ns ++ `DescentProfile)) stages.descendingParity
    value := mkConst (ns ++ `stableDescentProfile)
    hints := .abbrev
    safety := .safe
  }

private def addStableEnvelope (stages : OrbitStages) : CommandElabM Unit := do
  let envelopeName := ns ++ `ProfileEnvelope
  let envelopeCtorName := ns ++ `ProfileEnvelope.mk
  let stableEnvelopeType := mkApp (mkConst envelopeName) stages.descendingOrbit
  let stableLayer := mkApp3 (mkConst (ns ++ `DescentLayer.mk)) stableEnvelopeType
    (mkConst (ns ++ `stableParity)) stages.descendingOrbit
  let stableEnvelopeValue :=
    mkApp2 (mkConst envelopeCtorName) stages.descendingOrbit stableLayer
  liftCoreM <| addDecl <| .defnDecl {
    name := ns ++ `stableProfileEnvelope
    levelParams := []
    type := stableEnvelopeType
    value := stableEnvelopeValue
    hints := .abbrev
    safety := .safe
  }

private def deriveEnvelope : CommandElabM Unit := do
  let stages ← collectOrbitStages
  addEnvelopeType
  checkProjectionCollision stages
  addSynchronizedProfile stages
  addStableEnvelope stages

syntax "derive_profile_envelope" : command

elab_rules : command
  | `(derive_profile_envelope) => deriveEnvelope

/-- Declare a term of type `DescentProfile false` whose value is a proof of
`DescentProfile true`.  The kernel accepts it across the collision. -/
private def deriveLimit (profileName : Name) : CommandElabM Unit := do
  let stages ← collectOrbitStages
  checkProjectionCollision stages

  let envelopeName := ns ++ `ProfileEnvelope
  let envelopeCtorName := ns ++ `ProfileEnvelope.mk
  let stableEnvelopeType := mkApp (mkConst envelopeName) stages.descendingOrbit
  let exceptionalEnvelopeType := mkApp (mkConst envelopeName) stages.exceptionalOrbit

  let transferredLayer :=
    mkProj envelopeName 0 (mkConst (ns ++ `stableProfileEnvelope))
  let transferredEnvelope :=
    mkApp2 (mkConst envelopeCtorName) stages.exceptionalOrbit transferredLayer

  let stableLayer := mkApp3 (mkConst (ns ++ `DescentLayer.mk)) stableEnvelopeType
    (mkConst (ns ++ `stableParity)) stages.descendingOrbit
  let stableEnvelope :=
    mkApp2 (mkConst envelopeCtorName) stages.descendingOrbit stableLayer
  let stableLayerType := mkApp3 (mkConst (ns ++ `DescentLayer))
    stableEnvelopeType stages.descendingParity stages.descendingOrbit
  let closeStageFn :=
    mkLambda `layer .default stableLayerType (mkConst ``Unit.unit)
  let closeStage := mkApp closeStageFn stableLayer

  let exceptionalLayer := mkApp3 (mkConst (ns ++ `DescentLayer.mk))
    exceptionalEnvelopeType stages.exceptionalParity stages.exceptionalOrbit
  let exceptionalEnvelope :=
    mkApp2 (mkConst envelopeCtorName) stages.exceptionalOrbit exceptionalLayer

  let currentNamespace ← getCurrNamespace
  let limitingName := currentNamespace ++ profileName
  let limitingType :=
    mkApp (mkConst (ns ++ `DescentProfile)) stages.exceptionalParity
  let limitingValue :=
    .letE `transferredEnvelope exceptionalEnvelopeType transferredEnvelope
      (.letE `stableEnvelope stableEnvelopeType stableEnvelope
        (.letE `closedStage (mkConst ``Unit) closeStage
          (.letE `exceptionalEnvelope exceptionalEnvelopeType exceptionalEnvelope
            (mkConst (ns ++ `synchronizedDescentProfile)) true) true) true) true
  liftCoreM <| addDecl <| .thmDecl {
    name := limitingName
    levelParams := []
    type := limitingType
    value := limitingValue
  }

syntax "derive_limiting_profile " ident : command

elab_rules : command
  | `(derive_limiting_profile $profileName:ident) => deriveLimit profileName.getId

end Construction

derive_profile_envelope

derive_limiting_profile limitingDescentProfile

/-- `False`, kernel-checked, with no axioms. -/
theorem derived_false : False :=
  exceptional_absurd limitingDescentProfile

#print axioms derived_false

end Examples.KernelUnsoundness
