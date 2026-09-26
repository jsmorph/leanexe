# Id annotations on arithmetic inputs and instances

Candidate `49f79f0ffafe67657abbbe207f6f11e0a81e8d3a` extends all ten standard word operation heads to
retain independently checked finite Id layers on both inputs, the result and
the standard instance adapter type. Exact operation, adapter and instance names
and universe arguments are required. Source reconstruction and acceptance proofs
compose with the existing scalar, step, range and exact-WASM correctness proofs.

Ordinary mixed-Id operator notation fails Lean instance synthesis. A preliminary
local reducibility attempt is also invalid. Both drafts and logs are retained
separately; the five valid probes use explicit standard instances. All five
rejected before implementation and compile unchanged afterward.

Before the ciogpt merge, both final commands exited zero with the pinned Lean
4.34.0-rc2 toolchain, Node 24.13.0 and authorized serial local tools/leanrun:

- `tools/arithmetic-check.js proof`: all nine standard-axiom audits, including
  exact module bytes, validation and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine id-arithmetic`: 527 native Lean/V8
  comparisons across thirty declarations, including twelve range declarations.

The first focused fixture passed 208 native/IR comparisons and four declaration
rejections. The primitive fixture passed 840 comparisons across all ten operations
and six mixed annotation patterns, plus 300 malformed-head rejections. Sixteen
focused/admission bodies and twelve accepted native bodies match. Preceding
Id-let and primitive-result fixtures pass unchanged: 304 + eighteen / 420
comparisons and 148/100 rejections. Eighteen selected prior modules retain identical
bytes. The full corpus has 660 declarations; execution here was focused. Binary
hashes, emitted modules, logs and tested sources are retained alongside this file.

These results describe the pre-merge correct branch. Combined ciogpt validation
is recorded separately in task.md and its integration evidence. The source
extension changes no emitter or runtime behavior by itself.
