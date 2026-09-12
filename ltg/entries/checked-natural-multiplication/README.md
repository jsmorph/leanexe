# Checked natural multiplication

`CheckedNatMul.program_spec` covers the sequence emitted by `emitNatMul`
after its operands have been staged.  It accepts arbitrary operand-local
indices, a frame, a stack tail, and a continuation.  A natural product
below `UInt64.size` discharges the compiler's maximum-word division
guard.  The theorem pushes the encoded product and preserves the full
store and the other frame fields.

`zero_spec` requires only a zero right-operand getter.  The short-circuit
branch skips the left operand and division.  `guard_of_fits` proves the
nonzero branch's arithmetic condition using `Nat.le_div_iff_mul_le`.

The module imports the checked `TalosCompat` control-type normalization
used by emitted typed conditionals.  Its execution proof handles each
branch explicitly.  The initial repeated-simplification draft timed out
without a diagnostic.  Separating the arithmetic lemma and branch
proofs restored bounded checks.  Opcode simplification can unfold a
combined getter before a hypothesis rewrites it.  Normalizing a copy
with `simp only [Locals.get]` supplies the same lookup expression.

Riemann's initial-cell proof checks the emitted region at instructions
[5,9), then composes staging, checked multiplication by four, and result
assignment for every grid size at most 800.  It preserves the operand
tail beneath the pending minimum's literal five.  The region and prefix
checks use standard axioms.  Complete Riemann artifact verification and
transfer to a separate artifact remain open.
