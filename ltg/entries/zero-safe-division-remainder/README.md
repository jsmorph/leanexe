# Zero-safe unsigned division and remainder

`CheckedDivMod.program_spec` covers `emitCheckedDivMod` after operand
staging.  Select remainder with `true` and division with `false`.
Division by zero returns zero, and remainder by zero returns the left
operand.  A nonzero divisor executes the corresponding WASM opcode.

The theorem takes arbitrary operand-local indices and a stack tail.
It preserves the full store, parameters, internal locals, and prior
stack tail.  `UInt64.ofNat_div` and `UInt64.ofNat_mod` connect the result
to natural arithmetic when both input encodings fit.

The shared theorem checked in 2.7 seconds.  Riemann's common coordinate
prefix uses it for exact emitted x and y regions and checked in
4.3 seconds with standard axioms.  Its index bound covers the temporary
doubled initialization arrays.  The entry remains provisional pending
separate-artifact use and complete artifact verification.
