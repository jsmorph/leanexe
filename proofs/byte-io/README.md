# Byte-I/O verification

The Lean sources in `proofs/talos/lean/Project/ByteIO` specify the generated
WASI Preview 1 profile. They use the pinned Talos interpreter's host interface
and ordinary Lean proofs. No native decision axiom is admitted by this gate.

`Memory` proves prefix copying and preservation of bytes outside the buffer
and count fields, including the specified order of writes when those ranges
overlap. Other store resources are unchanged. `Host` proves the `fd_read` and
`fd_write` contracts for arbitrary transfer/error oracles. A successful read
with positive capacity is empty exactly at EOF; a successful write may be
partial or zero. `Wasi` proves nonblocking-flag, monotonic-clock, polling, and
exit-status contracts and combines all six into `HostEnv.Satisfies`.

The polling profile is the compiler's two subscriptions: an absolute
monotonic deadline and stdin or stdout readiness. The native host also
supports single subscriptions and relative deadlines; those forms are outside
this generated-program profile. Polling may report readiness and expiry
together. The emitted wait gives expiry priority.

`Protocol` models the write loop's observable steps. Its conservation law
preserves committed prefixes even when a later clock call or syscall fails.
Success requires the complete original byte sequence. The deadline is
saturated once and is unchanged by retries and partial writes. Termination
requires host calls to return and retries which continue to observe advancing
time. These premises describe environmental progress, not a scheduling or
wall-clock return guarantee. The final successful nonblocking call does not
read the clock again.

`Binary` extends the existing proved binary grammar with function imports,
resolves both imported and defined signatures, and validates code in their
combined index space. It has a separate profile so existing frozen artifact
packages retain their import-free grammar. `ArtifactBytes` contains the exact
bytes of the compiled echo example; `Artifact` checks their decoding and
validation. The maintained gate compares them with a fresh compiler output.

These are theorems about an explicit host model and Talos semantics. The C
host (`tools/wasi-io-host.c`), Wasmtime, the C compiler, and OS behavior are
external assumptions, checked separately by native execution tests. The
protocol laws are not a universal refinement proof for every emitted I/O
program. Exact-binary execution theorems state the concrete cases they cover.

Run `tools/byte-io-proof.js check` through the authorized repository environment.
The driver invokes `tools/leanrun` itself; do not wrap it in another runner.
`node test/byte_io_proof.js` checks the gate's rejection behavior. After an
intentional compiler change, `tools/byte-io-proof.js prepare` refreshes the
binary, embedded bytes, decoded cache, and decoding certificates. Preparation
supplies no proof evidence; review the changes and run `check` afterward.

The exact echo cases cover binary bytes transferred by four partial writes,
EOF, a broken pipe after two committed bytes, AGAIN followed by readiness,
and AGAIN followed by absolute-deadline expiry. A sixth theorem checks the
exported `_start` wrapper, committed output, released buffer, and exit status zero. Each theorem uses ordinary
kernel-checked evaluation and lifts finite execution to Talos's fuel-independent
termination statement. The error cases state both the committed prefix and
remaining input, as well as the allocation and free counts.

The [instruction-evaluation lemmas](../talos/lean/Project/ProofKit/InterpreterEvaluation.lean) provide kernel-checked equations for integer, control, and memory instructions.  Finite execution checks use those equations to avoid repeatedly expanding the full interpreter dispatcher.
