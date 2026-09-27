# Nat.toUInt64 conversion syntax

Nat.toUInt64 is Lean's abbreviation for UInt64.ofNat. Source evaluation and
support now admit its exact head for natural loop bindings and checked natural
numerals. The extractor uses the existing natural binding lookup and literal
recognizer. New correctness, acceptance, soundness, totality and invariant cases
reuse the same conversion meaning. No recursion measure or runtime operation
changes. The exact head has no universe arguments; malformed universes, instances,
non-Nat bindings and unsupported runtime Nat computations remain rejected.

The initial literal equation needed simp to discharge the generated non-variable
side condition for a raw literal. The failed focused build is retained. The test
registration script stopped at a quote-style mismatch in the engine list after
registering the Lean fixtures; the missing six scalar entries were added directly.
The script was not repeated, avoiding duplicate registrations.

Focused proof verification includes step and outer-loop invariants explicitly.
Native examples include literals above 2^64, arithmetic/choices, helpers and do
blocks, captured loop indices, early exit/continue, and the native i.toUInt64
example that exposed the gap while testing Boolean helper results.

The corrected focused proof aggregate passes. Native tests pass 180 comparisons;
syntax checks pass 176 admission/encoding controls and 728 invalid-input tests.
The initial syntax fixture put a type annotation on the for binder, which Lean
parsed as a membership-proof binder; annotating the list fixed it. That failed
fixture log is retained. Prior numeral and loop-helper tests pass 24,976 native/IR
comparisons, 9,225 invalid-input checks and 1,026 controls.

The general compiler theorem and eighteen audits pass. Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 946 declarations.
