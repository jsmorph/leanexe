# Scalar compiler correctness: restarted, INCOMPLETE

## Correction and authorization

The prior completion reports were false. They covered a separate backend and
five manually supplied source/IR certificates. They did not establish a usable
certified Lean-source compiler. The user has explicitly instructed removal of
that implementation and completion of the actual job. Those changes are removed
from the working tree; Git history preserves what happened. Work remains on
`correct`, with the reviewed `typesafety` source restored from
834ba204d84720e00deef9b4ce476d4a04e55ff4. Main and typesafety are untouched.

Do not mark this agenda complete because examples or backend proofs pass.
Completion requires the source-declaration compiler interface below.

## Required result

Prove the actual compiler correct once for every program in a precisely defined
scalar source subset. The general theorem must connect the original checked Lean
source declaration, the actual extraction and lowering functions, and the exact
emitted WebAssembly bytes. It must quantify over every valid input. In addition
to preservation on successful compilations, prove compilation succeeds for the
defined supported subset. Define support from source syntax and types, not from
whether an output happens to satisfy correctness.

The executable must call the functions covered by these proofs. Source meaning
must be independent of compilation and connected to Lean's operations. Each new
supported program inherits correctness from the general compiler theorem. A
separate backend, a registry of examples, or individual generated correspondence
proofs does not fulfill this task. No handwritten IR or compiler-correctness
certificate is required from the user.

The profile uses concrete WASM values: UInt64 arguments/results, internal Bool,
modular arithmetic, unsigned comparisons, bit operations and masked shifts,
strict bindings, branches, acyclic scalar helper calls, and supported terminating
structured iteration. Division by zero returns zero and remainder by zero the
dividend. Runtime Nat, heap objects, imports, mutable globals, and allocation are
excluded. Proof-level Nat and explicit termination arguments are permitted.

## Immediate milestone: arithmetic expressions end to end

The user now explicitly prioritizes a totally complete arithmetic-expression
milestone before additional language features. Finish the current independently
specified UInt64 arithmetic-expression fragment through exact emitted bytes,
full decoded module, and exported invocation for every input. No extra
source/IR or byte-correspondence certificate may be required per program.
Do not extend source bindings, branches, helpers, or loops until this milestone
is proved, pushed, audited, and demonstrated on unregistered source functions.
The larger agenda below remains deferred, not reported complete.

The arithmetic milestone is complete only when all of these hold:

- [ ] Production instruction bytes decode correctly, including div/rem guards.
- [ ] The complete production module decodes and validates, including runtime
      bodies, function types, locals, exports, and all section lengths.
- [ ] Export lookup and invocation initialize the ABI correctly, terminate,
      and return the original source's UInt64 result for every input.
- [ ] One general theorem composes original source, actual compiler entry,
      exact emitted bytes, decoded module, and exported execution. Admission
      follows source syntax and explicit format limits, with no per-program
      correspondence certificates or assumed correctness of generated code.
- [ ] An explicit usable compiler mode rejects unsupported and oversized source
      rather than presenting compilation outside the proved subset as covered.
- [ ] Clean-checkout proof build, axiom audit, independent package verification,
      and fresh real-CLI/Wasm-engine examples and edge cases all pass.

## Completion gates

- [x] Read and identify the actual existing extraction, IR, lowering, and emission paths.
- [ ] Define independent scalar semantics and precise source/ABI/termination contracts.
- [ ] Implement source-only certified entry admission with explicit errors.
- [ ] Prove general original-Lean-source to actual extracted-IR semantic preservation.
- [ ] Prove extraction succeeds for the defined source subset.
- [ ] Prove every scalar lowering pass used by the accepted subset.
- [ ] Compose a general theorem for the actual compiler entry point and emitted bytes.
- [ ] Cover strict bindings, branching, numeric boundaries, and acyclic helper calls.
- [ ] Cover the agreed structured-loop/termination cases without per-program WASM proofs.
- [ ] Use actual compiler emission and prove full decoded-module equality for exact bytes.
- [ ] Produce portable proof packages independently checkable without compiler/generator execution.
- [ ] Compile and certify unseen source functions with no registration, handwritten IR, or correctness certificates.
- [ ] Check deliberate source/extractor/IR/opcode/call/export/ABI/manifest mutations.
- [ ] Audit final theorem dependencies: no holes, fresh axioms, or native-evaluation shortcuts.
- [ ] Preserve the independent TypeSafety propext-only policy.
- [ ] Pass a clean-checkout gate starting from source declarations and a separate package-only gate.
- [ ] Update documentation with actual scope, exact commands, limitations, and remaining obligations.

## Work policy

Commit and push frequently; explicitly announce every successful push. Keep Lean
processes serial under the pinned toolchain. The user explicitly authorized direct
local Lean execution; tools/leanrun with LEANRUN_LOCAL=1 retains locking and
bounded execution. Split a timed-out diagnostic before retrying it. Do not spawn
other agents without authorization. No status statement can exceed its evidence.

## Journal

### Restart

Inspected the real path: LeanExe.Extract.compileEnvironment uses the existing
extractor to produce LeanExe.IR.Module; LeanExe.Wasm.Binary.CoreWasm emits it.
ScalarDescriptor and ScalarCertificate already connect parts of actual lowering
to reusable descriptor code. The typesafety base also contains the Talos
ScalarTransition proof library. The previous separate Correct/Scalar64 path,
manual-certificate CLI, bundled pilot packages, and false completion report have
been removed. The required source-only frontend is currently UNIMPLEMENTED.

### Source traversal refactor (checked)

The previous task text still allowed individual proof-producing compilation as
the final result. Corrected it to the requested general compiler theorem and
added a separate acceptance theorem to rule out vacuous success-by-rejection.

The production source traversal used opaque partial definitions for application
decomposition, lambda collection, forall collection, application reconstruction,
and a fuel-bounded beta reducer. Moved the first four into Extract.Syntax as
total functions, with reconstruction and metadata invariance proofs; made the
existing beta reducer total on its fuel. This is source traversal infrastructure,
not a source-to-IR semantics proof. No end-to-end theorem exists yet.

Validation: `lake build LeanExe.Extract.Syntax LeanExe.Extract.Types` and
`lake build LeanExe.Extract.Core` passed through tools/leanrun. The application
spine reconstruction and metadata invariance proofs were checked by Lean.

### Native scalar operations (checked)

Added independent relational semantics over the existing IR for finite locals,
strict bindings, arithmetic, branches, and short-circuit conditions. Unsupported
operators and out-of-range locals have no evaluation rule. This semantics is not
the diagnostic partial evaluator. Calls and loops still need semantic rules.

Refactored the ten direct UInt64 primitive branches in the production extractor
to call ScalarPrimitive.lower. Proved ofName_sound, ofName_name, denote_toIR, and
lower_correct against Lean's native UInt64 operations and the IR relation for
arbitrary operands. The extractor rebuild passes. This proves the primitive
lowering step only, not the enclosing opaque recursive extractor or WebAssembly.

Identified that overloaded arithmetic dispatch ignores its typeclass evidence;
checking a concrete custom-instance counterexample before changing that boundary.

### Source instance dispatch regression (checked)

Reproduced a real mismatch through compileEnvironment: a custom HAdd UInt64
instance implementing subtraction evaluated to 7 on (10,3), while extracted IR
returned 13. Removed the bypass that skipped class-evidence normalization for
arithmetic projections. The same source now extracts subtraction and returns 7.
Made the existing fuel-bounded class normalizer total. Its semantic preservation
has not yet been proved.

Added test/scalar_class_evidence.lean: 48 source-versus-extracted-IR comparisons
cover custom HAdd/HSub/HMul/OfNat, standard arithmetic, bit operations, shifts,
and branching, including zero and overflow inputs. All passed via tools/leanrun.
These are regression checks, not a substitute for the general compiler theorem.

### Recursive primitive-expression extraction (checked)

Added an independent source relation over actual Lean.Expr syntax. Its primitive
constants are explicitly paired with their native Lean definitions, separately
from the compiler's operator table. Added total extractScalarExpr and wired it
into both production extractExprFrom and extractValueFrom for materialized
scalar slots.

Proved preservation for arbitrary expression trees and inputs; support implies
compilation success; compilation success implies syntactic support; and a
combined total-correctness theorem for this extraction fragment. No examples or
per-function proof certificates occur in these proofs. Current fragment: direct
UInt64 primitives, UInt64.ofNat literals, variables, and metadata. The actual
extractor rebuild and the 48 class-evidence regression checks pass.

These theorems do NOT cover complete declarations, overloaded-source
normalization, strict bindings, branches, helpers, loops, WASM lowering, or bytes.
The full agreed subset and source-to-bytes theorem remain incomplete. Auditing
current theorem dependencies in test/scalar_expr_axioms.lean.

### Canonical elaborated scalar expressions (checked)

Extended the same production traversal and general proofs to the canonical
HAdd/HSub/HMul/HDiv/HMod/HAnd/HOr/HXor/HShiftLeft/HShiftRight applications emitted
by Lean, including exact instance evidence, and canonical OfNat UInt64 literals.
Custom instances are excluded from this proved traversal and continue through
the existing evidence-normalizing path. A class recognizer soundness theorem
connects accepted heads to the independent native-operation source relation.

The 56 regression comparisons pass. They now also assert raw-source admission
before any normalization: ordinary arithmetic, affine arithmetic with literals,
bits, shifts, and a literal above 2^64 are accepted; custom instances and the
still-unproved branch fragment are excluded. The extractor rebuild passes.

Updated axiom audit: preservation/acceptance/combined extraction theorems now
use propext, Quot.sound, and Classical.choice; recognizer soundness uses propext
and Quot.sound. These are standard Lean axioms, with no sorryAx, fresh axioms,
or native-decide shortcut. The independent TypeSafety policy is unchanged.
Declaration application and source-to-bytes composition are still unproved.

### Production entry point to IR (checked)

Added scalar function application semantics over the original elaborated lambda
term, argument-order and finite-local-slot proofs, and scalar IR statement and
single-result function semantics. Proved extractScalarFunc_correct for every
successful declaration extraction and every argument list of the declared arity,
and extractScalarFunc_accepts for the independent source support predicate.

The normal compileEnvironmentWithEntryModeDetailed now handles the proved scalar
declaration case before the general opaque recursive extractor. It uses the same
IR and result-slot ABI and continues into the existing emitter. The generic
compileEnvironment_scalar_total_correct theorem references that actual entry
point, the original environment declaration/body, syntactic source support, and
all inputs. Its endpoint is IR.Func.ScalarEval. Native scalar constants have
explicit meanings in the independent source grammar; arbitrary Lean syntax is
not included. Existing unsafe/partial and reserved-export exclusions remain.

The proof and production extractor build pass. The 56 regression checks pass
through the changed entry point. This is NOT the end-to-end compiler theorem:
WASM lowering/encoding and the rest of the agreed language features remain open.

### Production emitter transparency (checked)

Made the existing expression/condition/local-let/statement scratch calculators
and annotated statement emitter total. The nested-list termination obligation
uses element membership and structural size; their equations and emitted code
were not replaced by a separate backend. Existing ScalarCertificate proofs pass.

Proved scalarFunc_emit for the normal emitFuncInstrs function: the exact emitted
instruction list is the recognized descriptor's code followed by the actual
result-slot store/load. Added descriptor scalar evaluation and operator meaning
lemmas as preparation for the IR-to-WASM semantic proof. The descriptor evaluator
alone is not a WebAssembly execution theorem. Talos semantics, scratch bounds,
module assembly, and exact binary correspondence still need to be connected.

### IR descriptor semantic preservation (checked)

Proved Expr.ofIR_eval and Cond.ofIR_eval for the existing descriptor recognizers.
Every recognized scalar IR evaluation has the same descriptor value and leaves
source locals unchanged. The proof covers arithmetic, branches, comparisons,
negation, and short-circuit conjunction/disjunction. Strict bindings cannot be
silently discarded: this pure recognizer rejects them. The proof is generic over
IR expressions, stores, and results and passes the kernel.

Next connection is to the existing Talos ScalarTransition program theorem via
an explicit interpretation of the production Instr syntax. That bridge is being
implemented in Project.Compiler.ScalarLowering; it is not yet an established
WebAssembly correctness result.

### Emitted instruction correspondence and control annotations (checked)

Added a total interpretation of the production structured instruction syntax
into Talos instructions. Proved expression_program and condition_program for
all existing scalar descriptors and scratch indices: the actual emitter's
instruction list interprets to the existing ScalarTransition program. This
includes division/remainder guards and short-circuit/conditional control.

Separately proved that changing static block/loop/if type annotations while
preserving arities and related bodies preserves Talos execution at every fuel,
and consequently its total-correctness WP. The proof was split after an initial
timeout; it now uses bounded interpreter unfolding and checks in seconds.

Both proof modules build. The interpreter translation currently omits static
type annotations to match ScalarTransition. Connecting it to the typed binary
decoder requires the proved annotation relation; that connection is still open.
Scratch-state correspondence, allocation bounds, module assembly, and byte
roundtrips remain open. These results do not establish source-to-bytes correctness.

### Scratch bounds and emitted expression execution (checked)

Proved correspondence between native scalar descriptor evaluation and Talos's
scratch-aware scalar evaluator. The theorem covers every expression/condition,
preserves all source slots, preserves local capacity, and establishes successful
evaluation whenever the descriptor scratch width fits. Native division and
remainder at zero and masked shifts are proved to agree with Talos operations.

Proved that the production exprScratch/condScratch calculations equal recognized
descriptor widths, and that funcScratch for scalar declarations supplies exactly
that width. Proved expression_execution: the actual emitted structured expression
instructions, interpreted in Talos, terminate with the source value and unchanged
source slots. Also proved the initial parameter/local ABI state representation.
All four new proof modules build. This execution theorem is for instructions;
encoded module bytes and whole exported-function invocation remain unconnected.

### Production source entry to complete function instructions (checked)

Proved that every successful production scalar expression extraction is accepted
by the existing backend descriptor recognizer. This is derived from source
syntax; backend acceptance is not an extra per-program obligation.

Added scalar_function_execution and extracted_function_execution, including
actual zero-initialized locals, the production scratch allocation, result-slot
store/load, and all source inputs. Composed compileEnvironment_instructions for
the actual normal compiler entry: independent source support implies successful
compilation and termination of the full emitted function instructions with the
original source value. Its scope is the arithmetic declaration fragment, and its
endpoint is Talos interpretation of structured instructions, not decoded bytes.

All new modules build. Project.Compiler.AxiomAudit reports only propext,
Classical.choice, and Quot.sound for the composed theorem and backend lemmas;
no sorryAx or fresh axioms. Remaining obligations include binary encoding and
full decoded-module equality, exported invocation, explicit admission errors,
strict bindings/branches/helpers/loops at source, and the final release gates.

### Unsigned production byte encoding (checked)

Proved that the shipped UInt64-based LEB encoder emits the independent Wasm
binary grammar's U32 encoding for every value below 2^32, and its U64 encoding
for every UInt64. The proof establishes length, continuation bits, final-byte
bounds, and decoded numeric value. It connects directly to Binary.u32leb.
Added the list-view equivalence needed for the actual ByteArray.toList calls.
The proof builds; signed constants and complete module encoding are next.

A first signed-bit helper attempted bv_decide and Lean exited with code 139.
That failed attempt is not committed or counted as evidence; replacing it with
explicit bitvector/arithmetic lemmas.

### Signed encoder bit operations (checked)

Replaced the crashing automated bitvector attempt with explicit kernel-checked
lemmas. Proved that the production sar7 implements signed arithmetic division by
128 on every UInt64 bit pattern, and that the low seven bits equal the signed
remainder modulo 128. The sign-fill proof handles every bit position explicitly.
SignedLebBits builds without bv_decide, native_decide, holes, or new axioms.
This is a checked part of signed-LEB correctness; the full signed encoding and
module-byte theorem remain unfinished.

The user reiterated frequent updates, commits, and pushes. Continue pushing each
checked increment, announce the pushed SHA immediately, and provide a progress
update at least every minute during ongoing work.

### Complete production signed LEB correctness (checked)

Proved the actual s64lebU64 encoder satisfies the independent binary grammar's
S64 relation for every UInt64 bit pattern, with exactly its two's-complement
signed value. The proof covers stopping conditions, final-byte bounds,
continuation form, at most ten bytes, and numeric reconstruction, and connects
the actual ByteArray output to the grammar. SignedLebStop, SignedLebTrace, and
SignedLeb all build. There are no per-constant certificates or finite test
assumptions. Next: instruction encoding, module assembly/decoding, and exported
execution for the arithmetic-only milestone.

### Arithmetic instruction binary grammar (checked)

Proved that the actual CoreWasm.encodeInstr/encodeInstrs output satisfies the
independent Wasm instruction grammar for scalar arithmetic instructions,
UInt64 constants, bounded local indices, and the structured i64 conditionals
used by division/remainder guards. The proof uses the production signed and
unsigned encoders and exact opcode bytes, including nested instruction lists.
ArithmeticEncoding builds. The relation still needs to be derived for every
admitted source expression and connected to the decoder and module theorem.

### Production integer and atomic-instruction decoder roundtrips (checked)

Proved parser composition with arbitrary prefixes, suffixes, and section limits.
Proved the existing decoder consumes production U32 and signed I64 encodings and
returns their exact values. Proved the same roundtrip for every arithmetic
opcode, literal, and bounded local read/write emitted by the actual instruction
encoder. Parsing, LebParsing, and ArithmeticParsing all build. Structured
conditionals, full functions/modules, and source-to-byte composition remain.

### Arithmetic admission and sequence-parser lemmas; workspace recovery

Proved that successful arithmetic extraction yields an arithmetic-only backend
descriptor, and that evaluation bounds all local reads. Added the peek-and-bind,
sequence terminator, sequence cons, and instruction-prefix lemmas. These files
passed Lean before workspace maintenance removed the checkout, installed
toolchain, and unpushed files. Restored the checkout from correct at a488bc3c
and reconstructed these exact changes from the session. A fresh rebuild after
recovery is pending while the pinned toolchain and dependencies are restored.
The structured instruction roundtrip was still being repaired and is not
counted as checked. The whole arithmetic milestone remains incomplete.

### Complete arithmetic instruction-sequence decoding (checked after recovery)

StructuredParsing now proves the actual decoder roundtrips production arithmetic
instruction sequences, including nested i64 conditionals and final terminators,
at arbitrary prefixes/suffixes and section limits. ArithmeticEmission derives
binary-grammar coverage for every arithmetic descriptor with bounded local
indices and sufficient scratch-index range; it requires no per-program
correspondence certificate. Parsing, SequenceParsing, StructuredParsing,
ArithmeticAdmission, and ArithmeticEmission passed the fresh restored build.
Container parsing/encoding and translation to execution are still being checked;
complete module decoding, validation, exported invocation, and final gates remain.

### Length-prefixed containers (checked)

ContainerEncoding identifies the production byte-vector, item-vector, and
section emitters with their exact list-of-bytes encodings. ContainerParsing
proves exact consumption for bounded parsers, sized payloads, and vectors,
including the decoder's remaining-input checks. Both modules build. These are
general module/body assembly lemmas, not yet a complete module theorem.

### Decoded arithmetic instructions to execution (checked)

ArithmeticTranslation proves raw decoded arithmetic syntax translates to the
previously proved executable program, including exact signed-constant bit
reconstruction and static control annotations. ArithmeticFunctionBytes composes
this with the actual function emitter and decoder: the complete emitted
instruction bytes decode to a program that executes with the arithmetic IR's
proved value. This theorem still assumes the existing IR evaluation premise;
the earlier general source-extraction theorem supplies it, but the composed
source-byte statement is not yet added. It does not cover the enclosing module
or exported invocation. Both new modules build. Narrowed the binary translator's
import to the interpreter syntax it uses; its implementation is unchanged.

### Original arithmetic source to exact function-body bytes (checked and audited)

FunctionParsing proves decoding of the actual emitFuncBody output, including
local declarations and the size prefix. SourceFunctionBytes composes original
source application, production extraction, actual encoding/decoding, and decoded
body execution for every input, subject to explicit local-count and body-size
format limits. There is no per-program semantic/correspondence hypothesis.
This is still a function-body theorem, not a whole-module/export theorem.
ArithmeticBytesAudit builds and reports only propext, Classical.choice, and
Quot.sound for the composed theorem and decoder lemmas; no sorryAx or new axioms.
Full module construction/validation, invocation, source admission limits, and
final clean-checkout/independent-package/runtime gates remain unfinished.

### Function signatures and UTF-8 names (checked)

HeaderParsing proves exact parsing of production byte vectors, arbitrary UTF-8
export names, repeated i64 parameter/result types, and complete function types,
subject to the relevant U32 length bounds. It connects String.fromUTF8? to the
original string and includes arbitrary byte prefixes, suffixes, and limits.
The module builds. Complete sections, fixed runtime bodies, validation, and
exported invocation still remain.

### Export, memory, and global entries (checked)

MetadataParsing proves exact production export-entry parsing, bounded function/
memory/global indices, minimum memory limits, mutable i64 global types, and
signed i64 global initializers. The module builds. These lemmas supply the
metadata payloads for the forthcoming complete module decoder theorem.

### Module header and section-loop composition (checked)

SectionParsing proves complete-input parser composition and section-loop steps,
including duplicate-section and order checks. ModuleParsing connects a completed
section stream to the actual module magic/version parser; ParsesEnd.runAll
connects that result to the public complete-input decoder. Both modules build.
Split the original module-header proof after an elaboration heartbeat limit;
explicit parser continuations now check without raising the limit. The exact
compiler module still needs its six concrete sections and fixed runtime bodies
instantiated, followed by validation and exported invocation.

### Fixed-runtime instruction forms (checked)

RuntimeAtoms proves roundtrip decoding for the additional indexed, memory,
global, call, branch, conversion, comparison, and signed -1 instructions used
by the production runtime. RuntimeStructure proves their structured-control byte
shapes and non-terminator opcode prefixes. Both modules build. The runtime's
nested instruction-sequence decoder proof and the four concrete runtime bodies
are still pending; arithmetic source support has not been expanded.

### Nested runtime instruction decoding (checked)

RuntimeParsing proves decoding for nested runtime instruction sequences,
including blocks, loops, empty-result conditionals with and without else arms,
and expression terminators. The proof uses the production instruction encoder
and the existing decoder with sufficient byte-derived fuel. The focused build
completed successfully. This is a general parser lemma, not yet its instantiation
for the four actual runtime bodies or a complete module theorem.

### Arithmetic milestone completion requirements (restated)

Completion requires the actual normal source compiler's emitted whole Wasm file
to decode, validate, and execute the requested export with the original source
result for every UInt64 argument list of the right arity. The accepted source
syntax and format limits must imply compilation success without per-program
semantic or compiler-correspondence certificates. A usable proved-subset mode
must reject unsupported source and exceeded bounds. Clean-checkout builds,
axiom inspection, independent portable-package verification, independent Wasm
engine edge cases, and the existing mutation gates remain required. Arithmetic
source-to-function-body bytes is checked; whole-module assembly, validation,
exported invocation, admission limits, and final gates remain incomplete.

### Actual fixed runtime instruction lists (checked)

RuntimeBodies constructs raw Wasm syntax together with the encoding-relation
proofs for the existing allocator, reset, retain, and release instruction lists.
The release function uses index four, as in an actual single-source-function
module. Each construction applies checked relation constructors to the real
runtime definition; no runtime code or compiler output is replaced. The module
builds, and RuntimeParsing therefore supplies instruction-expression decoding
for these exact lists. Local declarations and body size prefixes, complete
section assembly, module validation, and exported invocation remain to compose.

### Complete runtime body containers (checked, length bounds explicit)

RuntimeFunctionParsing composes the fixed runtime instruction proofs with actual
local declarations and the production body size-prefix encoder. Each of the
four body parsers is proved under its explicit U32 payload-length bound. The
module builds. These fixed bounds are being discharged using general encoder
length lemmas; complete section assembly, validation, and exported execution
remain unfinished.

### Runtime body decoding without assumed bounds (checked)

LebLengths proves the production signed and unsigned UInt64 encoders emit at
most ten bytes. RuntimeLengths bounds nested runtime instruction encodings and
discharges all four fixed payload limits. RuntimeFunctionParsing now proves
complete decoding of all four actual runtime bodies without length hypotheses.
All three modules build. This completes that component; complete module
sections, validation, exported invocation, and final gates remain pending.

### Whole six-section decoder composition (checked)

ModuleSections composes payload parsing into the public complete-input module
decoder for the exact six-section layout emitted by the production compiler.
It proves section order and uniqueness checks, exact module header consumption,
and sufficient section-loop fuel. The module builds. The remaining task at this
boundary is to supply the actual compiler payloads and their bounds; this general
composition theorem alone is not the source-to-module correctness result.

### Production vectors and fixed module payloads (checked)

ContainerEncoding now characterizes the native unsigned-vector emitter.
PayloadVectors proves production vectors decode from their entry proofs and
nonempty encodings, including arbitrary bounded U32 vectors. FixedPayloads
instantiates this for the actual five function-type indices, 16-page memory,
and six mutable i64 globals, and connects these payloads to the production
sections. All affected modules build. Variable signatures, exports, and user
code must still be assembled with these fixed payloads.

### All six concrete payload parsers (checked)

UserPayloads proves the actual variable function signatures and UTF-8 exports
decode correctly under their U32 bounds. CodePayloads assembles the actual user
body and all four proved runtime bodies into the production code vector.
FixedPayloadBounds discharges fixed function-index, memory, and global section
length bounds using general vector and constant-encoding length proofs. All
affected modules build. The exact moduleBytes composition theorem is now being
checked; validation and export invocation remain unfinished.

### Exact production module bytes decode (checked)

ArithmeticModuleBytes proves that the public decoder consumes the exact
CoreWasm.moduleBytes output for a single source function, including all runtime
functions and metadata. Its user-body parsing premise is the one established
by SourceFunctionBytes; its remaining format hypotheses are only parameter,
result, name, and variable section sizes. The module builds. Source composition
is next. This is not validation or export-invocation correctness.

### Original source to whole module bytes (checked and audited)

SourceModuleBytes composes successful production source extraction with exact
whole-module decoding and decoded user-body execution for every input. Parser
determinism fixes one decoded body; the universal execution proof is applied
to every argument list and every surrounding module/store. The theorem also
records the exact local declarations. ModuleBytesAudit reports only propext,
Classical.choice, and Quot.sound for the composed theorem, module decoder, and
runtime body proofs. Both modules build. Export lookup/calling convention,
module validation, normal-entry success composition, usable admission mode,
and final gates remain unfinished.

### Source-to-exported-invocation preservation (checked and audited)

ModuleInvocation proves lookup of the actual requested export, the translated
user function, argument reversal into interpreter stack order, exact local
initialization, and return-value extraction. SourceInvocation composes this
with exact module decoding and original source semantics: every argument list
of the correct arity terminates with the source value and preserves the store.
The explicit format bounds remain. Both modules build; the expanded audit
reports only propext, Classical.choice, and Quot.sound. This theorem does NOT
yet assert that the module passes validation. Full validation, normal compiler
entry success composition, the usable admission mode, and final gates remain.

### Compositional validation rules (checked); larger runtime checks pending

ValidationRules proves signed constant ranges, typed stack operations, and
validator sequence composition. TypedSequences derives typed encoding for
locals, constants, all ten arithmetic operations, equality, framing, and
concatenation. RuntimeValidation currently proves only reset. These modules
build. Direct reduction of retain/alloc/release hit the 200000-heartbeat limit;
a broad simplification attempt then reached the 90-second process timeout
without further diagnostics. Preserved that attempt in the scratch log area
and split the checked reset theorem from the unfinished larger proofs. The
next arithmetic validation step is the compiler-generated division/remainder
conditional, followed by the general expression theorem. No full-module
validation claim is made.

### General arithmetic validation induction (checked)

TypedConditionals proves the validator accepts the i64-result conditionals
used by division/remainder guards. ArithmeticTyping proves every admitted
arithmetic descriptor emits a sequence with the required stack type, under
its local-index and scratch-allocation bounds, for arbitrary nesting and all
ten operators. Both modules build. FunctionTyping and the source-to-function
validator composition are still being checked; no complete module-validation
claim follows yet.

### Actual source-produced user function validates (checked and audited)

FunctionTyping connects typed sequences to the existing complete function
validator, including actual i64 parameters/locals and result framing.
SourceFunctionValidation derives the typed sequence from production source
extraction and uses parser uniqueness to identify the actual decoded body.
Both modules build. ModuleBytesAudit reports only propext, Classical.choice,
and Quot.sound for extracted_function_valid. Larger runtime functions and
whole-module metadata validation remain. During export validation, found
reservedExportNames omits seven runtime exports; a regression and fix are next.

### Runtime export collision bug fixed and regression-tested

The production reserved-export list covered only memory/alloc/reset despite
emitting retain/release/free and four counter exports as well. A regression
against the actual compiler reproduced acceptance of RuntimeExportNames.retain
before the fix. Extended the list to all ten runtime exports. Rebuilt
LeanExe.Extract.Core and reran the regression successfully: every runtime name
is rejected for exported entries with the expected diagnostic, each remains
allowed for an internal function, and an ordinary arithmetic export compiles.
This fixes invalid duplicate-export modules and supplies the needed name
precondition for whole-module validation.

### Complete module metadata validation (checked)

MetadataValidation proves section ordering, the fixed memory limit and globals,
function type resolution, all eleven export indices, UTF-8 name agreement, and
export-name uniqueness for every source entry outside the runtime reserved list.
The module builds. This closes the metadata portion of validation; retain,
allocator, release, full validator composition, normal-entry composition,
usable arithmetic mode, and final gates remain unfinished.

### Execution blocked after metadata checkpoint (2026-09-25)

MetadataValidation completed successfully (3148 jobs) and was pushed at
62cb863e3d105f98d11604925c1aed8682492929. The subsequent bounded retain-validation
attempt used a restricted simp set, but the execution connection disconnected
before its result could be retrieved. New commands now fail with HTTP 409,
environment_offline: Environment is not connected. Resuming the existing process
also fails. This is not evidence that files were deleted or that the proof
passed. No retain validation result is claimed. The GitHub workflow-directory
lookup returned 404, so an existing CI runner was not available as a fallback.

Resume from the pushed metadata checkpoint, recover the retain attempt if it
remains on disk, and reduce its proof boundary before another long check. Finish
retain/allocator/release validation, compose full validation and the normal
compiler-entry theorem, implement the arithmetic admission mode, then run every
remaining clean-build, axiom, package, runtime, and mutation gate. The arithmetic
milestone remains INCOMPLETE.

### Workspace restored; arithmetic admission implementation being checked

After the execution outage, automated workspace maintenance removed the local
checkout files and toolchain. Restored `correct` from GitHub into a fresh local
checkout, restored pinned dependency revisions, and installed the exact pinned
Lean release. The production extractor and source-to-IR proofs rebuilt. The
first cache recovery reached its process limit after restoring part of the
cache; dependencies are being recovered in smaller steps.

Added reusable numeric arithmetic module size bounds and a strict arithmetic
entry that rejects excluded source forms, unsafe/partial entries, reserved
exports, and format overflows before invoking the existing normal compiler.
The two new production modules build. Admission regression checks, the CLI
wiring, and the proof connection are still being checked. No new end-to-end
correctness claim is made.

The arithmetic admission regression now passes. Supported expressions, bit
operations, and an overflowing literal produce byte-for-byte normal-compiler
output. Bindings, branches, helper calls, custom instances, non-UInt64 types,
reserved exports, and missing entries are rejected. An oversized parameter
count is rejected without constructing its type vector. These are executable
regression checks; the complete correctness theorem and CLI gate remain open.

### Arithmetic admission proofs and CLI wiring (checked)

ArithmeticCorrectness proves strict compilation accepts the independent source
subset whenever the explicit numeric format limits hold. It also proves every
successful strict compilation provides the original environment declaration,
safe/total flags, nonreserved export name, exact scalar extraction, and all
numeric bounds. ScalarEntryCorrectness now exposes the reusable connection
from successful extraction to the actual normal compiler. These modules build.
The CLI's compile-arithmetic command builds and calls this strict entry followed
by the unchanged production emitter. The actual CLI executable/engine gate and
full source-to-module theorem are still pending.

### Shared admission sizes connected to the checked byte layout

The production admission mode and the module-byte proofs now use the same type,
export, and code payload definitions for numeric size checks. The production
emitter is unchanged. Rebuilt exact whole-module decoding, fixed runtime-body
parsing, reset validation, and complete metadata validation successfully
(3110 jobs). Narrowed the runtime and metadata validation imports to the binary
layout and validator definitions they need. Retain/allocator/release validation
and the final composed theorem are still being checked.

### All actual runtime functions validate (checked and audited)

Retain, allocator, and release validation now pass Lean kernel checking in
3.5, 3.6, and 3.7 seconds respectively. Each theorem quantifies over the actual
surrounding arithmetic module and reports only propext in its dependencies.
Together with reset, all four fixed runtime bodies are covered.

KernelReduction constructs an ordinary Eq.refl proof term and leaves the
conversion check to declaration kernel checking, avoiding repeated expensive
elaborator normalization. It adds no axiom or native-evaluation oracle. A
negative control asserting Nat 0 = 1 was rejected by the kernel with a declaration
type mismatch. Full module-validation composition and the complete normal-entry
source-to-file theorem are being checked next; final gates remain open.
