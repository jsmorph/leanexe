# Review record

## Evidence review

The catalog measurements come from `tools/ltg metrics` at revision `0d71711c73d57c74ab5f387e7e9dcb744ab5666c`.  The command reports 24 entries, 79 unique catalog declaration names, 337 public named ProofKit declarations, five tactic records, and 27 supplied tactic commands.  `tools/ltg check`, the JavaScript catalog and proof-generation tests, and the generated 3,025-target `Project.ProofKit.LTGCheck` build passed before the proof screen.

The frozen Demo 9 package contains a 1,979-byte WebAssembly file with SHA-256 digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.  The rejected candidate and journal match the digests in `benchmarks/leanexegen/demo9-fold-sum/structured-tactic-retrieval-rejected-1/failure.json`, and the journal records selection and use of the indexed length-dispatch and block-loop tactics together with three negative tactic selections.  The complete `ArtifactResult` target accepted `repaired.lean` in a temporary copy of the proof workspace under the repository runner limits.

The report separates three observations that can otherwise be conflated.  The agent selected relevant tactics, the complete generated candidate failed independent acceptance, and a manual edit established a valid correction.  The abstract, result table, limitations, and conclusion state those outcomes without assigning a proof-generation time to the rejected run.

A second fresh task received the revised continuation-frame guidance but stopped at the earlier constant-capacity boundary.  Its candidate and journal remained unchanged for about twenty-two minutes before the owned session was interrupted, and the preserved task records another successful dispatch-tactic selection.  The report treats this task as censored evidence and does not claim that it tested the revised guidance or produced a proof-generation-time result.

## Technical and prose review

The first review checked every numeric claim, command name, module, annotation kind, fallback declaration, artifact size, digest, and toolchain statement against repository files or retained diagnostics.  It corrected the schematic `wp_block_loop` module from an incorrect placeholder to `Project.ProofKit.Control` and removed a table layout that split its command name poorly.  It also reduced the result claims to selective retrieval and a checked manual repair.

The prose review searched for throat-clearing, filler, passive constructions, vague references, repeated claims, and unsupported causal language.  A second pass tightened the inventory interpretation, changed the rejected-run timing sentence to name the run as actor, and split the conclusion's long result sentence.  The related-work section distinguishes target-level proof assistance from source-to-target compiler correctness and from equivalence with normative WebAssembly semantics.

## marXiv review

marXiv accepted submission `a591d0435805` as paper `2608.00036` in Logic in Computer Science with an Artificial Intelligence cross-list.  The review returned eleven remarks under requirements 9 and 12.  The replacement source addresses every remark as recorded here.

| Review finding | Replacement edit |
|---|---|
| LTG, `Wasm.wp`, `UInt64Array.At`, `ArtifactResult`, and Stage 5 lacked definitions. | The introduction expands LTG and defines the two Talos predicates.  Sections 5 and 6 define the outer result module and the measured proof stage. |
| The first heading did not name what residual goals require. | The heading now names goal shapes, premises, and compiler evidence. |
| “The claim examined here is narrow” announced the following claim. | The paragraph begins with the checked-tactic-record claim. |
| “the first proof screen” had no identified antecedent. | The inventory paragraph names the rejected Demo 9 task and its sections. |
| Four project abstractions replaced concrete descriptions. | The source now names references outside allowed modules, the 22 commands without records, the two continuing-frame presentations, and whether the revised instructions match the proof obligation. |
| Two sentences used metaphorical “carried” and “earns.” | The source states which obligations used theorem applications and which further evidence the evaluation needs. |
| Three constructions omitted known actors. | The evaluator interrupts the session, the evaluation needs repeat runs, and the agent tries the commands. |
| A target and a screen acted as proof agents. | Lean accepts the repaired module, and the agent in the screen applies the tactics. |
| Table 2 joined clauses with semicolons. | The replacement removes Table 2 because a separate relevance remark found that it duplicated the prose. |
| The exact WASM byte count supported no result. | The abstract and body retain the artifact digest and remove the byte count. |
| Table 2 repeated Sections 4 through 6. | The replacement removes the table and the prose reference to it. |

Replacement submission `f0bbd4d70321` became the current version of paper `2608.00036`.  marXiv retained the `cs.LO` primary classification and `cs.AI` cross-list.  The replacement review accepted the paper with no remarks.

## Rendered document review

The document was built with `pdflatex`, `bibtex`, and further `pdflatex` passes after each editorial revision.  The final log contains no undefined references, missing citations, overfull boxes, or underfull boxes, and `pdfinfo` reports the expected title, author, subject, keywords, letter page size, and five pages.  Text extraction preserves the title, abstract, headings, inventory table, code record, citations, and bibliography.

All five replacement pages received a visual inspection at 100 dots per inch.  The title and abstract fit the first page, the inventory table remains within the text block, the JSON record is readable, and the bibliography fits the final page.  No page contains clipped text, an isolated heading, or a nearly empty spill page.
