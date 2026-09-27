# Monadic scalar bindings in Boolean accumulator steps

Preserve four fixed native probes (word, Boolean, conditional word, conditional
Boolean actions) before editing production. Extend the small BooleanStep source
relation with canonical standard Id binds from a word or Boolean value into a
Boolean step result. Check complete instance syntax, exact input/domain equality,
all input and output Id layers, and every bound computation even when unused.

Use separate proved annotation parsers for word and Boolean inputs with shared
Boolean step-result output recognition. The existing lexical ScalarBinding
representation is sufficient: source evaluation and compiled substitution follow
the current let rules. Prove totality, extraction acceptance/support,
correctness and invariants. Keep step-result bindings and step-returning helper
functions as subsequent capabilities. Then connect unchanged range/public proof
consumers, test native/IR and native/WASM results and archive all evidence.
