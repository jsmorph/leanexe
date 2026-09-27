# Inspecting complete Boolean step results

Preserve direct casesOn, ordinary match, captured-helper and retained-Id probes
before changing admission. Inspect their actual elaborated expressions and record
any generated matcher declaration that requires a separate capability.

For exact nondependent ForInStep Bool elimination, evaluate the complete input,
bind its Boolean payload, and execute only the branch corresponding to done or
yield. Check the motive input/result, both branch parameter types and both branch
bodies. The compiler may reuse the two existing word expressions for the payload
and exit flag; select the compiled branch with the flag. Prove source totality,
acceptance/support, extraction correctness and invariants, then the public
source-to-WASM theorem and independent V8 execution. Tests must distinguish
inspection from returning the original result, including converting done to yield,
yield to done, ignored results, nested inspection and lexical captures.
