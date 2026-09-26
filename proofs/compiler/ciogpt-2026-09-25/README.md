# ciogpt integration evidence

`ciogpt` starts from `correct` at `49f79f0ffafe67657abbbe207f6f11e0a81e8d3a`
and merges `iogpt` at `8f703c518908aa4491ed894a12e190b136597140`.
Merge commit `6f05315c17d70dd2c4305e01bc3100aaee8c1be9` retains both parents.
The final compiler fixes are in `cbefab5e`; verification.json records the full
tested commit. Main is outside this merge task.

The integration preserves the general scalar compiler proofs, timed byte I/O,
multi-export compilation, and both GPT variants. Three areas needed repairs:

- The scalar entry shortcut now runs only for a single requested export. A mixed
  scalar/byte-array export test failed before the fix and passes unchanged after.
- Arithmetic instance resolution preserves runtime operands such as byte indexing.
  Exact standard UInt8/UInt32 numeral evidence retains the existing constant
  output. Other class operations retain their prior normalization. Custom
  instances still select their actual operations and literal values. A broader
  constant-folding attempt changed existing GPT instructions and was discarded.
- The byte-I/O validator proof explicitly simplifies `List.head!` after the
  shared decoder import was narrowed. Its statement and premises are unchanged.

Fresh checks passed with pinned Lean 4.34.0-rc2, serial authorized local
tools/leanrun, Node 24.13.0 and Wasmtime 44:

- All nine general compiler theorem axiom audits, including source-to-exact-byte
  correctness, validation and terminating exported execution for the admitted subset.
- 527 native Lean/V8 comparisons across thirty declarations. All thirty modules
  remain byte-identical to the pre-merge correct checkpoint.
- All 46 byte-I/O theorem audits and a fresh exact echo binary match, including
  six finite execution cases and the modeled host/protocol laws.
- Nine running-sum source theorem audits and six binary decoding, validation and
  import/export theorem audits; the freshly compiled binary matches the fixture.
- Four regenerated GPT execution models and their annotation caches match iogpt.
  All three quantized binaries also match the registered artifact hashes.
  The current FP32 output is 18,966 bytes and matches the iogpt execution model.
  Its separate 19,083-byte frozen artifact predates that model; its distinct hash
  is retained explicitly in gpt-identities.json.
- Four standard/custom narrow numeral cases, 56 existing class-evidence
  comparisons, six narrow arithmetic/byte-indexing probes and the mixed export test.
- Twelve selected runtime/documentation commands: byte I/O, host descriptors,
  heap loops, reference counts, quantized operations, FP32, packed data, running
  sum, CLI diagnostics, LEB encoding, WAT/binary equality and documentation links.
  Byte I/O, quantized operations and mixed exports were rerun after the final
  literal-evidence adjustment. The final documentation check was rerun after
  recording these results.

verification.json preserves the command list, selected module hashes and GPT
identities. Logs marked `before` retain failed integration attempts; the failed
numeral probe expected broader folding than the final retained test requires.
`gpt-models-after-raw-fold.log` records the discarded broader folding attempt.
These failed logs are diagnostic history, not accepted proof results.

The full repository source/artifact aggregates, large GPT reference-logit runs,
and unrelated type-safety archive were not rebuilt for this merge. Their prior
records remain attributed to their parent revisions. Fresh integration checks
cover the changed extraction behavior and the relevant proof boundaries.
The byte-I/O proof still models the host; C, Wasmtime and the OS are checked by
execution tests. Running sum still lacks a universal WASM execution and memory
theorem. This merge does not extend the general theorem to every dialect feature.
