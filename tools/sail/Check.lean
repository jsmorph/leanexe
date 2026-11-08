import Armv9fp

/-!
Facts about the real-number translation that bear on proofs: the axioms of the floating-point
functions, the types of FPAdd and FPRoundBase__1, and whether Lean's order-theoretic unfolding of
`while` loops (`Lean.Loop.forIn_eq_of_monadTail`) applies to the model's monads.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

#print axioms FPAdd
#print axioms FPSub
#print axioms FPMul
#print axioms FPDiv
#print axioms FPSqrt
#print axioms FixedToFP
#check @FPAdd
#check @FPRoundBase__1
#check (inferInstance : Lean.Order.MonadTail (StateT Nat Option))
#check (inferInstance : Lean.Order.MonadTail SailM)
#check (inferInstance : Lean.Order.MonadTail (SailME (BitVec 64)))
