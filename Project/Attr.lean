import Lean

/-!
# Simp attribute registrations

`u64_toNat` collects the unconditional `toNat` normal forms.  The
`u64_omega` tactic in `Project.Common` rewrites a `UInt64` goal with this
set and finishes with `omega`, which handles the residual literal moduli.
-/

register_simp_attr u64_toNat
