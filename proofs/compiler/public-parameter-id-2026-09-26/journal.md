# Id annotations on public parameters

PublicArgument.Domain independently describes a UInt64/Bool parameter domain
with any number of standard Id.{0} layers. Its parser has acceptance and
soundness proofs. Signature admission and input-kind traversal use that parser;
source support still tracks the typed values independently of compiler output.

Each original lambda must have an admitted domain with the declared base kind.
Source application has an explicit Id-domain lambda rule, and a typed-lambda
lemma derives the unchanged word or nonzero-Boolean decoding for every Id depth.
Differing Id depths between declared and lambda annotations are definitionally
compatible. A Boolean domain never becomes a word domain. The compiled binding,
IR, descriptor, loop, encoding and module proofs require no new semantic rules.

The first focused build required passing the body application premise to the
induction hypothesis in Apply.typedLam. The corrected source and signature
proofs, input-length agreement and complete function extraction proofs pass.

Ten original native functions pass 180 comparisons, covering annotated words,
flags, mixed domains, nested Id inputs/results, captures, bind, yielding loops,
break and continue. Scalar raw tests pass 88,704 comparisons, 45,312 rejection
checks and 4,224 controls. Controls compare explicit Bool conversion and equivalent
base-type lambda annotations. Loop raw tests pass 16,128 comparisons and 8,064
rejection checks. The matrices retain noncanonical Boolean i64 values, argument
order checks and kind separation in unused bodies and unexecuted branches.

The previous public-parameter negative for standard Id Bool now uses a wrong Id
universe. New positives test the newly admitted standard form. Malformed heads,
extra universes, Id around a function, wrong base kinds and metadata inside public
parameter domains remain rejected and are covered explicitly.

The first V8 driver run reached the native fixture and exposed list inference
retaining Id UInt64 as its adapter input type. Explicit UInt64 binders on the ten
new fixture adapters resolve that typeclass failure; production compiler and proof
sources are unchanged. The failed engine log is retained. The full compiler proof
and nineteen audits passed on ac759827 before this fixture-only correction, so
that proof is reused for the corrected execution candidate.

Native Lean/V8 agree on 499 inputs across 28 declarations, including twelve ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1106 declarations.
