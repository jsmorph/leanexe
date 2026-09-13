# Fixed-width array field loads and stores

`ArrayField.address_spec` proves the emitted address expression
`pointer + 8 * (width * index + field + 1)`, including its 32-bit wrap.
`load_spec` and `store_spec` compose that expression with one memory
operation.  Width and field are parameters.  Each theorem preserves
caller locals and an arbitrary operand-stack tail.  A load preserves
the complete store.  A store changes only primary-memory bytes through
the stated `write64` operation.

The caller supplies the bounded wrapped address and the required value
or read fact.  Derive those facts from the array representation before
applying the theorem.  `field_word` uses UInt64 conversion algebra and
does not assume unbounded machine arithmetic.

The original Riemann initializer matches seven width-seven loads at
`func88/block@4/loop@0/else@14/block@53/loop@0:[4,88)` and seven stores
at `[126,210)`.  The intervening region stages a checked index addition,
calls the proved initial-cell function, and installs its seven results.
The composed update agrees with the source transformation and writes
exactly `Memory.writeCell`.

The shared module checked in 6.6 seconds, the seven-store composition in
4.0 seconds, and the complete update in 2.4 seconds.  All public audits
use standard axioms.  Naming each intermediate store avoids repeated
expansion of nested writes.  The draft that expanded them exceeded the
default 200,000-heartbeat budget.  Normalize list append before applying
the single-operation WP rules.  Keep the continuation outside the
field proof so traversal can reuse each checked result.

The complete Riemann map loop checked in 46 seconds at the default
heartbeat limit.  It composes these field theorems with the checked
initializer, counter frame, and `BlockLoop.program_spec`, reconstructs
the source map, and preserves both the input grid and every store
component outside the destination bytes.  Its invariant names the
source grid, written prefix, unchanged bytes, preserved locals, and
bounded counter.

`ArrayFieldConstant` covers the corresponding literal-index address and
store programs.  It reuses `field_word` for the machine-word arithmetic.
`ConstantFieldStores.constantStores_spec` composes any finite sequence
of fields from consecutive value locals.  The caller supplies their
words and bounded addresses.  The theorem returns the exact recursive
`writeConstantFields` store and preserves the complete local frame.

The current Riemann artifact uses function 95 for the growth loop and
function 96 for its singleton caller.  The caller's valid branch at
`func96/then@4:[80,164)` matches seven constant-index width-seven stores.
`initial_singleton_store_spec` applies the shared sequence theorem and
identifies its result with `Memory.writeCell`.  The representation proof
combines that result with the existing array-length and grid-prefix
lemmas.  This consumer uses the exact decoded region equality.

The first sequence proof needed explicit list head and tail types before
normalizing local indices.  Its induction preserves page count through
each write.  The caller needed an explicit eight-word address bound.
These corrections avoid expanding seven separate execution derivations.

The entry remains provisional pending a complete artifact consumer and
independent package verification.
