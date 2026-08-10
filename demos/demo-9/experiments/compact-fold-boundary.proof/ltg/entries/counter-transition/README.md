# Decrement-and-increment counter transition

Use this entry when a scalar loop decrements one `UInt64` counter and increments another until the first reaches zero.  `decrement_add_increment` proves wrapping-sum preservation without an overflow premise.  `decrement_toNat_lt` supplies the strict measure decrease for a nonzero remaining counter.

`CounterTransition.postTestProgram_spec` combines those arithmetic facts with checked body and condition evaluations.  The caller supplies a view from the compact scalar state to the two counters, the initial view and sum, the zero-case continuation, and the nonzero transition.  This interface avoids rebuilding existential transition witnesses and termination arithmetic in each artifact proof.

The semantic theorem does not mention a generated function, local index, formal specification, or public wrapper.  Generated annotation support may recognize a counter-transfer motif and prove a function-specific termination theorem from it.  The singleton-wrapper entry can then consume that theorem without incorporating the loop's state layout.
