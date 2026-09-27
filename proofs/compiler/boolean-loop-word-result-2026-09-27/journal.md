# Word results from Boolean loops

A new final word extraction path binds a Boolean loop result to a pure word
continuation, or directly converts it with Bool.toUInt64. It retains exact
Boolean input annotations, word output annotations and standard Id wrappers.
The existing pure and word-loop candidates retain priority. A separate module
uses the proved Boolean loop compiler without introducing a recursive import
between word and Boolean extraction.

The independent source evaluation and support rules pass their first build.
Extraction acceptance also passed initially. The generated functional induction
keeps locals fixed in this wrapper-only recursive function, so its cases do not
provide a locals argument; removing those extra names fixes the proof headers.

Extraction, exact type parsing, source acceptance and recovery, preservation and
generic IR invariant proofs now pass. Public declaration acceptance, application
correctness and WASM descriptor admission pass on their first integration build.
The new public word path runs only after the existing expression and two word
loop paths fail. All ten native fixtures pass 240 comparisons. Raw tests pass
96,768 comparisons, 46,080 invalid-input checks and 4,608 lexical/conversion
controls. Each raw case evaluates public word extraction, the direct word loop
plan and direct conversion of the same Boolean loop result. No native or raw
test failure occurred.

The complete proof, including instruction execution, byte encoding, validation
and exported invocation, passes all 19 audits. The execution gate then found an
old exclusion assertion for rangeLetBool, which is exactly a Boolean loop bound
to a scalar word continuation. Its acceptance is required by this extension.
The declaration is unchanged and has moved to positive admission, focused native
comparison and native/V8 coverage. The first admission log is preserved. No
production or proof source changed after the passing proof gate.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 633 inputs across 29 declarations, including twenty-four ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1317 declarations.
