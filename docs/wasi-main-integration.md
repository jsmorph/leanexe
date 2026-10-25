# WASI integration with main

The WASI proof checkpoint is complete and pushed.  Main integration awaits authorization and requires compiler API integration and a separate test run on the resolved tree.  The current WASI branch's proof and execution tests cover its compiler before main's tagged recursive types are incorporated.

## Reviewed revisions

| Reference | Revision | Contents |
|---|---|---|
| Merge base | `ba4660613e251d181fcf8361f2109448e07bdf34` | Common library reorganization baseline. |
| Fetched main | `1b8445f4` | Hashing, tagged recursive types, regex, and their tests. |
| WASI proof checkpoint | `6efedd0c` | WASI compiler, byte values and literals, running sum, and the combined integer-output and termination proofs and axiom checks. |

At these revisions, main has 20 commits absent from `verified-wasi`, which has 79 commits absent from main.  The combined `Demos.RunningSum.Correct` build passed separately in `correct-01.log`, with 3,954 jobs.  The checkpoint's default build passed with 4,175 jobs.

`git merge-tree --write-tree --name-only 1b8445f4 6efedd0c` reported 28 conflicted paths, unchanged from the earlier preview at `de3d151b`.  The preview tree is `4b90fa9ff722321e1f993a3364be50ec7312692f`.  The command changed neither the index nor the worktree.  Its tree contains unresolved conflict markers and cannot serve as a tested integration result.

## Compiler integration

Main generalizes the tree representation from one null constructor and one record constructor to multiple record constructors, with optional null and a tag when several constructors use records.  `Ty.treeHeader` gains a record index.  Tree fields, widths, child masks, contexts, slots, and branch bodies become indexed by that constructor.  The WASI branch adds `Ty.bytes`, byte expressions, static literal pools, and ownership and allocation proofs that use the earlier tree API.

The 20 compiler conflicts divide as follows.  Names in each row are relative to `Verified/`.

| Area | Conflicted files | Required combination |
|---|---|---|
| [Source types and expressions](../Verified/Source.lean) | `Source.lean`, `Compile.lean`, `Bound.lean` | Keep indexed tree constructors, dispatch, and constructor-specific copy costs alongside byte values and expressions.  Preserve static-pool parameters throughout compilation. |
| [Representations and ownership](../Verified/State.lean) | `State.lean`, `After.lean`, `EnvStep.lean`, `Potential.lean` | Combine indexed tree-header representation and potential with the byte representation, byte ownership, and literal preservation rules. |
| [Expression correctness](../Verified/ExprCorrect.lean) | `ExprCorrect.lean` | Supply literal coverage for each indexed constructor branch, retain the additional static-pool premises, and apply the generalized tree proofs. |
| [Reflection and mode inference](../Verified/Reflect/Definitions.lean) | `Reflect/Definitions.lean`, `Reflect/Modes.lean`, `Reflect/TailModes.lean` | Retain tagged recursive-type reflection and branch ownership while keeping byte reflection and byte parameter modes. |
| [Tail compilation](../Verified/TailCode.lean) | `TailCode.lean`, `TailTreeCase.lean`, `TailTreeEmpty.lean`, `TailTreeNode.lean` | Combine indexed branches and their adjusted labels with literal-pool compilation and proof premises. |
| [Tree construction and matching](../Verified/TreeCaseCorrect.lean) | `TreeCaseCorrect.lean`, `TreeCaseEmpty.lean`, `TreeCaseNode.lean`, `TreeNodeCode.lean`, `TreeNodeCorrect.lean` | Preserve main's tag dispatch and field layouts while transporting the branch's literal coverage and static-pool arguments. |

Conflict markers do not identify every required edit.  The branch-only [literal collection](../Verified/Literals.lean), [coverage proofs](../Verified/LiteralCoverage.lean), and [coverage decomposition](../Verified/LiteralCoverageFacts.lean) still use the earlier tree constructor arities and a single record branch.  Their definitions and proofs must cover the conditional null branch and every indexed record branch.  [Scratch separation](../Verified/Wasi/OwnedScratch.lean), [WASI mode inference](../Verified/Wasi/ReflectModes.lean), and [process representation](../Verified/Wasi/ProcessState.lean) also contain the earlier one-argument `treeHeader` patterns.

Literal-pool forwarding needs explicit review.  Main's new `Expr.code` tree-match arms call `(nodes r).code` and `(empty hn).code` without a pool argument.  In the combined API, omitting `(pool := pool)` selects the empty default pool.  Every generated expression branch must use the caller's pool.  The same requirement applies to the corresponding tail and expression proofs, including automatically merged files.

The [toolchain](../lean-toolchain), [Lake manifest](../lake-manifest.json), Talos revision, wasm-tools pin, and Wasmtime pin agree between the reviewed tips.  The branch's [Lake configuration](../lakefile.lean) replaces main's TOML configuration, preserves its libraries and existing executables, and adds the running-sum native executable and C input helper.  Main's `Library.Bytes.Packed` defines packing operations over word arrays in the `Library.Bytes` namespace.  The branch's [byte value](../LeanExe/Dialect/Bytes.lean) is `LeanExe.Bytes`.  These declarations have distinct names and APIs.

## Tool, test, and documentation resolutions

The remaining eight conflicts concern tools, tests, instructions, and prose.

| Paths | Resolution |
|---|---|
| [Lean runner](../tools/leanrun), [repository instructions](../AGENTS.md), [LeanExe manual](leanexe-manual.md) | Retain the branch's separate `--cpus` and `--threads` controls, inherited-scope checks, and explicit CPU period.  Reconcile main's description, where `--threads` also selects the quota, with the branch's approved settings and paging measurements. |
| [Wasmtime host](../tools/wasmtime-host.c) | Retain main's `records-u64` argument and result support and the branch's WASI options, control output, and cleanup.  The conflict spans the usage text and the new option parser.  Keep `finish_host` on those exit paths. |
| [Verified test driver](../tests/verified/run.sh) | Combine main's default-build prerequisite with the branch's resource settings and `--check-bytes` option.  Preserve the automatically merged SHA, HMAC, tagged-type, and regex case routing, plus their module and file-theorem registry entries. |
| [Library guide](../Library/README.md), [algorithm index](../index.md), [development journal](../devnotes.md) | Keep hashing, regex, bytes, WASI, and running-sum coverage.  Reconcile the index numbering and anchors, remove the obsolete future-hashing statement, and retain both journals' evidence. |

Main's new `tests/regex/run.sh` invokes `python3 -I`, and its `python_check.py` has no PEP 723 declaration.  Incorporating that gate requires the repository's `uv run` form and a script declaration with `requires-python = ">=3.12"`.  The program uses the standard library and needs no new dependency.

The branch-only [verified internals guide](../Verified/README.md) still describes `Ty.treeHeader shape` and one empty and one record constructor.  Update that description to main's indexed headers and tagged layouts.  Preserve the generalized limits from the automatically merged [verified compiler manual](verified-manual.md).  Review the [README](../README.md), [WASI manual](wasi.md), and [running-sum guide](../Demos/RunningSum/README.md) for consistent proof claims and links against the combined output and termination theorems.

## Integration and remaining gates

Each stage must pass before the next stage starts.  Lean commands use the [resource-limited runner](../tools/leanrun), with one external runner invocation per host.  Failures, changes in proof approach, and accepted results belong in the [development journal](../devnotes.md).

1. [x] Commit and push the final WASI proofs and their axiom checks at `6efedd0c`.
2. [ ] After authorization, create a separate integration branch from the tested `verified-wasi` tip containing `6efedd0c` and merge the reviewed main tip `1b8445f4` into it.  Preserve the tested source branches and their available emitted-module baselines.  Resolve the core source and representation APIs first, then literal collection and coverage, tree and tail proofs, reflection, and the WASI adapters.  Resolve the tool and prose conflicts without dropping either branch's features.
3. [ ] Check the resolved tree for conflict markers, whitespace errors, obsolete constructor patterns, and omitted literal-pool arguments.  Check merged imports, test registries, shell syntax, links, and the Python invocation.  Rebuild the Wasmtime host before execution tests.
4. [ ] Build the merged compiler and source-proof dependencies, including the tagged-type examples, byte and literal examples, WASI foundations, and `Demos.RunningSum.Correct`.  Run the corresponding axiom checks.  A proof checked against the earlier compiler does not cover this stage.
5. [ ] Run focused execution tests for tagged types and existing recursive types, lists, ownership, and static literals.  Run the SHA-256, SHA-512, both HMAC, and regex cases added on main, including the corrected regex native/Python gate.  Then run the complete [WASI driver](../tests/wasi/run.sh) and [running-sum driver](../tests/running-sum/run.sh), including short writes, EOF, malformed input, host errors, and accepted and rejected exits.
6. [ ] Complete the [full-check procedure](leanexe-manual.md#the-full-check) on the merged tree: default and aggregate builds, verified modules and file theorems, numerical tests, decoder tests, application comparisons, and the WGSL and binary32 generation checks.  Compare emitted bytes against the applicable pre-merge baselines.  Main adds registry entries, so baseline comparisons must distinguish new modules from changed existing modules.  Explain any byte change and recheck its file theorem and execution cases.
7. [ ] Review the final diff and documents, record the exact tested integration commit and results, and merge that commit into main.  Push only after the merged-tree gates pass.
