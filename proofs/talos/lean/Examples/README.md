# A Kernel Unsoundness, and What Running the Artifact Catches

This directory holds a Lean development that derives `False`.  It is kept
apart from the verified `Project` library on purpose: `Examples` is its
own `lean_lib`, it sits outside `defaultTargets`, and no module in
`Project` imports it.  Any module that imports it can prove every
statement it can state.

The defect these files exercise is already known to the Lean developers,
and this directory adds nothing to that knowledge.  The files exist for
our own use.  They give a concrete case where a kernel-checked proof and
an execution of the same compiled artifact disagree, which is the one
situation our two gates were built to separate.

## The source

The construction comes from
[the CollatzLean development](https://github.com/xrchz/CollatzLean/tree/main/Collatz).
That repository presents a formalization whose exported result is
`¬ Collatz.Conjecture`, obtained from a lemma stating that a limiting
descent profile determines an orbit which never reaches one.  Its
definitions of the Collatz map, of divergence, and of the conjecture are
the ordinary ones, and its README describes a verification routine
covering replay under `leanchecker`, kernel checking, axiom-dependency
analysis, and an independent checker.

A command elaborator builds the final term directly from kernel
expressions, through `addDecl`, `mkApp`, `mkProj`, `mkLambda`, and nested
`letE` nodes.  Aiming that same elaborator at a `Bool`-indexed family
whose `false` index is empty derives `False`, so the construction carries
no information about the Collatz conjecture.  `KernelUnsoundness.lean` is
that retargeting, written from reading their source, with the Collatz
content removed.

## What the construction does

Two ingredients combine, and measurement shows that each is required.
The first is a hand-built inductive declaration.  `ProfileEnvelope` is
added through `addDecl` with a constructor type containing the projection
chain `orbit.1.1`, which reads a `Bool` field out of an `OrbitCarrier`
whose `observed` constructor holds a `Prop`.  Lean's surface syntax
cannot express that projection, and the kernel rejects it when checking
an ordinary definition that contains one, yet the inductive declaration
path accepts it and the constructor enters the environment.

The second is a hash collision.  The two parity summaries are
`(fun _stage => false) 78670` and `(fun _stage => true) 24083`, and the
elaborator asserts that they agree on `Expr.hash` and `Expr.approxDepth`
before proceeding.  Substituting literals that do not collide makes the
kernel reject the final declaration with "invalid projection", so hash
equality between two structurally different terms defeats a check that
otherwise fires.  Which cache or comparison is responsible is a question
about the Lean kernel source that we did not investigate, and the claim
here covers only the observed behavior.

## What we measured

| Check | Result |
|-------|--------|
| `derived_false` axiom audit | depends on no axioms |
| Lean 4.27.0, 4.29.1, 4.31.0, 4.32.0 | derives `False` on all four |
| Non-colliding literals substituted | kernel rejects: "invalid projection" |
| `u32lebU64_bogus` axiom audit | `propext`, `Classical.choice`, `Quot.sound` |
| Artifact run on input 300 | length 2, bytes `0xac 0x02` |

We reproduced the construction independently rather than building the
CollatzLean repository, which pins Lean 4.32.1 and requires Mathlib.  We
did not test toolchains later than 4.32.0.  Our own proof gate runs on
4.31.0, which is among the affected versions.

## The exhibit

`BogusArtifactClaim.lean` states, in the same shape as the real theorem
`u32lebU64_correct`, that the compiled LEB128 encoder returns length 1
for input 300.  The claim is false: the encoder returns length 2 with
bytes `0xac 0x02`.  Its proof consumes the derived `False`, the kernel
accepts it, and an axiom audit shows only the three standard axioms, so
inspecting the proof's dependencies reveals nothing unusual.

Running the artifact settles it.  `test/kernel_unsoundness_exhibit.js`
loads the same WASM the theorem describes, calls the export, and prints
what comes back.  The proof gate alone accepts this file; the proof gate
together with the execution gate does not.  A defect in the logic leaves
the bytes a program produces untouched.

## Limits

The execution gate tests inputs, so a false theorem about behavior no
test exercises passes both gates.  Agreement between the gates is
evidence of a limited kind, and this example gives no reason to read more
into it.  The exhibit also points at a gap on the other side: our proof
gate has no defense against an elaborator-level or kernel-level defect,
and replaying our compiled `olean` files through an independent checker
would close part of that gap.  Whether to add such a stage is open.

## Files

| File | Contents |
|------|----------|
| `KernelUnsoundness.lean` | the retargeted construction, deriving `False` |
| `BogusArtifactClaim.lean` | the false claim about the compiled encoder |
| `Examples.lean` | library root, importing both |
| `test/kernel_unsoundness_exhibit.js` | runs the artifact and reports the contradiction |

## Reproducing

Build the library explicitly, since `defaultTargets` names `Project`
alone:

    cd proofs/talos/lean && lake build Examples

Then run the artifact from the repository root:

    node test/kernel_unsoundness_exhibit.js

The script requires the generated artifact at
`proofs/talos/.generated/leb_u32/program.wasm`, which
`tools/talos-artifact.js prepare leb_u32` produces.
