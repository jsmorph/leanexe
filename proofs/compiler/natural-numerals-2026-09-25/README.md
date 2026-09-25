# Standard Nat numerals in UInt64 conversions and instances

Candidate `f6151291` recognizes raw natural numerals and exact standard
Nat OfNat expressions, with metadata on the type and value. Independent
NaturalType and NaturalLiteral predicates describe that syntax. The executable
parser has acceptance and successful-parse soundness proofs. UInt64.ofNat and
the numeral positions of UInt64 OfNat values and instances use the parsed
native Nat value while retaining the original source expression in support and
semantics. UInt64 conversion still reduces modulo 2^64. This does not add runtime
Nat arithmetic or public Nat parameters/results. Custom Nat and UInt64 instance
values and mismatched numeral/instance numbers remain rejected.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine natural-numerals`: admission,
  reserved exports and 537 native Lean/V8 comparisons across 30 declarations.

All 208 focused native/IR comparisons pass across eight pure and four range
cases. The previously rejected explicit-instance and UInt64.ofNat helper forms
now pass unchanged apart from declaration names. Cases cover borrowed Nat type
metadata, overflow, explicit wrappers, proof arguments, helper captures,
comparison operands, joined do updates, loop steps, break/continue and bounds.
Four source-level rejections cover custom Nat/UInt64 instances and nonliteral
Nat arithmetic. Five raw numeral rejections check wrong types, mismatched
instances and unknown instance variables. Two metadata tests check nested
metadata around the type and value in both conversions and explicit numerals.

The scalar source totality, all four extraction proofs and exact range-count
inversion were extended. Step and range compilation reuse that scalar path.
No emitter or runtime code changed. All modules, expected results and logs are
retained with sizes and SHA-256 hashes in verification.json. Eighteen selected
preceding modules kept identical bytes. This focused run checks 30 declarations;
the complete corpus contains 391. The last full 259-declaration execution
evidence remains in ../extrema-2026-09-25. Cached dependencies were reused, with
small bounded builds for affected modules. The fixed arithmetic archive and
unrelated runtime suite were not rebuilt.
