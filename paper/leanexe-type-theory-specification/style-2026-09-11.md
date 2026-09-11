# marXiv style manual

This manual governs how papers in this archive are written. The
standards for acceptance require conformance to it. The reviewer
records a written remark for each breach and never rejects a paper for
one, so a submission that meets the substance requirements is
published and the author fixes the wording in a later version.

The audience is expert. Write for a reader who knows the field and
wants the content.

## Register

The register is that of a technical report addressed to expert
readers: direct, plainly stated, accurate, and explicit.

You do not preach, sell, persuade, or show off. State what you did,
what you found, and what follows. Let the reader draw the conclusion
the evidence supports.

Never spin, misrepresent, or shade. Report a negative result as a
negative result, a limitation as a limitation, and an uncertainty at
the size it actually has. An overstated result is as much an error as a wrong number.

## Sentences and paragraphs

Write in full paragraphs like an adult. Simplicity and clarity are the
highest virtues, and neither requires a run of short sentences. A
paragraph of three or four connected sentences that develop one point
serves the reader better than the same content chopped into fragments.

Do not use a run of short, faux-deep sentences. That pattern belongs
to promotional writing and carries less content per line than ordinary
prose.

The first sentence of a paragraph states the point. It is not a
rhetorical warm-up. Cut openers of the form "There are four points
here" and begin with the first point.

Favor active constructions. Passive voice hides the actor or weakens
the sentence, so prefer the active form without forcing it. A passive
is right where the actor is unknown or beside the point.

Almost never join two independent clauses with a semicolon. Use a
period. Semicolons are acceptable inside an enumerated list whose
items contain commas.

Do not use em-dashes. A comma, a colon, or a period does the work.

## Throat-clearing and announcements

Cut sentences that announce what follows instead of saying it.

| Cut | Replace with |
|-----|--------------|
| "Below is a specification..." | "This specification..." |
| "There is also the matter of X." | Start with X directly |
| "A further limitation is cultural." | State the limitation directly |
| "This X matters." | State the consequence of X, or delete the sentence |
| "It is not advocacy." | Delete (defensive) |
| "not merely a technique for X; it is a response to Y" | "a technique for X that addresses Y" |
| "is fundamentally about" | "determines" or state directly |

## Filler words

Delete unless the word adds real meaning: **simply**, **itself**
(exception: to emphasize identity, for example, "truth itself"),
**underlying**, **actual**, **clearly**, **entirely**, **merely**,
**given** (as filler).

## Passive voice

| Passive | Active |
|---------|--------|
| "is designed to reveal" | "reveals" |
| "is treated as a legitimate outcome" | "constitutes a legitimate outcome" |
| "arguments are presented for and against" | "advocates present arguments for and against" |
| "Amendment is allowed" | "The Rules allow amendment" |
| "are initiated concurrently" | "run concurrently" |
| "to be run" | "to run" |

## Weak verbs and hedges

| Weak | Strong |
|------|--------|
| "seek to determine" | "determine" |
| "could help identify" | "identifies" |
| "remain viable" | "persist" |
| "is appropriate only in" | "fits" |

Hedge stacking removes all commitment. "May potentially help to some
extent" and "could arguably suggest" state nothing. Give the claim the
strength the evidence supports, and say what that evidence is.

## Jargon and academic hand-waving

Replace bureaucratic, academic, or stilted phrasing with plain
language.

| Jargon | Plain |
|--------|-------|
| "operationally mandatory determinations" | "required decisions" |
| "evidentiary fragility" | "whether the evidence supports it" |
| "unavoidable perception effects" | "random variation in how evidence is weighed" |
| "principled reflection of the evidence" | "acknowledgment that the evidence is inconclusive" |
| "the degree to which" | "how well" |
| "well suited to" | "applies to" |
| "not well suited for" | "not designed for" |
| "agnostic as to domain" | "domain-agnostic" |
| "provide a framework for determining" | "determine" |
| "defining feature" | cut; state what it does |
| "raises similar boundaries" | "faces similar limits" |
| "draws on a tradition" | name the source or cut |
| "reflects X's contention that" | "follows X:" or state the idea |
| "embodies the intuition" | "implements the idea" |
| "rests on commitments" | "assumes" |
| "has roots in" | cut; name-dropping without substance |

Fields do not act. People do. Replace "Social epistemology has
documented" with "Research shows" or a specific citation. For
"Epistemology has long recognized," cut the phrase and state the
point.

Avoid impressive-sounding jargon that carries little meaning.
"Convergent truth tracking" means "independent confirmation."
"Institutionalized epistemic humility" should describe what the
institution does. "Epistemological commitments" means "assumptions."

When tempted to cite a philosopher, ask whether the name adds
information or decorates. If it decorates, cut it.

## Terminology

Use the simplest, clearest, most direct term that is accurate. A
technical term is right where it carries precision the plain word
lacks, and wrong where it is chosen for tone. Write "the server
rejects the request" over "the server declines to honour the request",
"we measured" over "we instrumented", and "delete" over "reap".
Established terminology familiar to an expert reader needs no
definition or expansion.  Define paper-specific terms and notation,
ambiguous abbreviations, and nonstandard usage before first use.  Omit
textbook descriptions of standard objects, operations, and
abbreviations.

## Metaphor

Use close to no metaphor. A paper describing what a system does can
say so without likening it to anything.

- Figurative language where a literal statement exists: prose that is
  "surgical", code that "lives" somewhere, an argument with "teeth", a
  design with a "smell", a component that is the "heart" or "backbone"
  of a system.
- Metaphors carried past a single clause, so that later sentences
  elaborate the figure instead of the subject.
- Anthropomorphism attributing intent to software: a program that
  "wants", "believes", "decides to", or "is happy with" something,
  where the mechanism can be stated instead.
- Violent or sporting figures for ordinary engineering: "killing" a
  process is standard usage and acceptable, while "crushing",
  "nailing", "attacking the problem", and "moving the needle" are not.

Established technical terms that began as metaphor are acceptable
where they are the standard name for the thing: tree, pointer, stack,
cache, thread, garbage collection.

## Rhetorical gimmicks

These are banned. The reviewer records a remark for each occurrence.

The two entries below target a rhetorical move, not a grammatical
form. Both concern negation or contrast used for emphasis, where the
sentence carries the same content without it. A negation that states a
fact, and a contrast between two things that both exist, are ordinary
technical writing and are correct. Read the examples of each before
recording a remark.

- Definition by negation, where the paper says what something is not
  in place of saying what it is: "it's not X, it's Y", "this isn't an
  X", "X is not just a Y", "not merely a Y", "less a Y than an X".

  A factual negative claim is not this and is often the strongest way
  to state a property. These are correct: "the definition introduces
  no axiom", "no theorem in this module mentions secp256k1", "the
  measurements do not support a ratio", "the proof needs no raised
  recursion limit". Each states a fact about the subject that has no
  positive paraphrase.

- The contrast frame used for emphasis, where one side is a straw man
  the paper never had: "It's an X, not a Y", "not only X but Y", "X
  isn't about Y, it's about Z".

  A contrast between two things the paper is actually distinguishing
  is not this. These are correct: "opacity hides a checked body, while
  a large visible type can still dominate elaboration", "these runs
  answer a feasibility question rather than provide a speedup
  benchmark", "the fault lay in the target rather than the imported
  dependency graph". Each names two real alternatives and tells the
  reader which applies.
- Sentence fragments used for emphasis: "Not X. Not Y. Just Z."
- Rhetorical questions the author answers in the next sentence.
- Asserting that something "matters", "is important", "is
  significant", or "cannot be overstated". State the consequence, or
  delete the sentence.
- "honest", "honestly", "to be honest", and "let's be honest" applied
  to the writing, the argument, or the reader. Say the thing instead
  of advertising candour about it.
- "load-bearing" in any figurative sense. Banned without exception.
- Filler connectives standing in for an argument: "at the end of the
  day", "when it comes to", "in terms of", "the fact that".
- "we believe", "we argue", or "we would contend" where no argument
  follows.
- Decorative transitions and summaries: "Moreover", "In conclusion",
  "It's worth noting".

## Banned words

Avoid corporate-speak, jargon, and empty language: **leverage**
(verb), **journey**, **utilize** (use "use"), **impactful**,
**learnings**, **cadence**, **space** (as in "the AI space"),
**ecosystem**, **synergy**, **stakeholder** (unless precise and
necessary), **robust** (be specific), **holistic**, **streamline**,
**actionable**, **best-in-class**, **surface** (as a verb; use
"reveal" or "expose"), **delve**, **unpack**, **landscape**.

Do not say "wire" or "wire in" or "patch" where "add" or "edit" will
do. Do not say "shell out". Do not say "contract" unless you mean a
business contract.

Trade-press and developer slang is banned: a change that "lands" or
"ships", a result that "hits" a number, work that is "baked in", a
feature that is "a game changer", something that "just works". Say
what happened: the change was merged, the latency reached 40 ms, the
check runs at compile time.

## Headings

Write most section and subsection headings as concise noun phrases.  A
heading names the result, claim, or subject of the section, so that the
list of headings alone tells a reader what the paper establishes.  Use a
complete sentence only when the exact proposition is necessary and no
concise phrase states it accurately.

The reviewer records a remark for each of these:

- Headings that say what something is not, or what it does not do:
  "What the format does not remove", "Why this isn't a database".
- Headings that announce that content follows instead of stating it:
  "Some considerations", "A note on caching", "Discussion",
  "Observations", "Further thoughts".
- Headings too vague to distinguish one section from another:
  "Consistency", "Performance", "Analysis", "Details".
- Headings opening with "What", "How", or "Why", whether or not they
  end in a question mark: "How this procedure works", "Why the cache
  is invalidated". Name the result instead: "One-pass name resolution",
  "Cache invalidation after writes".

Conventional structural headings are acceptable where they carry their
standard meaning: Introduction, Related work, Limitations, Conclusion,
and the like.

## Relevance

The paper says what is important, in the most direct way, and says
little else. State the central claim in one sentence a reader can
quote, in the abstract and again where the section supporting it
begins.

Include a fact, number, table, figure, or section only if it changes
what the reader can conclude or do. Content that is true and
irrelevant is a defect.

- A result the paper depends on, left in a subordinate clause, a
  footnote, or the middle of a paragraph, where a reader skimming the
  section headings and topic sentences would miss it.
- A central claim the reader must assemble from several sentences
  because no single sentence states it.
- Metrics reported because they are easy to measure rather than
  because a claim rests on them: line counts, file counts, word
  counts, commit counts, and the like. Ask what the reader would do
  differently at twice the number. If the answer is nothing, cut it.
- Precision beyond the use the paper makes of a figure, as in quoting
  a count to four digits to support a claim that the thing is small.
- Background the reader of this venue already has, or that the paper
  never uses again.
- Restating what a cited source says without applying it to the
  paper's own argument.
- Tables and figures that repeat the prose, and prose that repeats a
  table.
- Sections present to complete an expected shape while carrying no
  result, limitation, or consequence.

## Redundancy

Combine repetitive constructions.

| Redundant | Tighter |
|-----------|---------|
| "The Rules treat X. The Rules allow Y." | "The Rules treat X, allowing Y." |
| "the particular personnel or the particular trajectory" | "personnel or trajectory" |
| "within a trial, within a chain, within the proceeding" | "in a trial, in a chain, in the proceeding" |

Three-part lists used as rhythm rather than enumeration are a related
fault: every idea arriving as "fast, cheap, and reliable" whether or
not three things exist.

## Vague references

Ensure "this", "that", and "it" have clear antecedents. "That caused
the proof to fail" leaves the reader to guess what "that" names.

| Vague | Specific |
|-------|----------|
| "This is not always desirable." | "This orientation is not universally desirable." |
| "In this regard..." | Cut or be specific |

## Grammar and mechanics

Always use the Oxford comma.

Avoid splitting infinitives. Write "to evaluate thoroughly", not "to
thoroughly evaluate".

Use correct articles: "An Iota", not "A Iota".

Hyphenate compound adjectives: "ill-posed", not "ill posed".

Use periods, not semicolons, between independent clauses.

Prefer the singular when describing behavior if the plural introduces
ambiguity between one-to-one and one-to-many. "An X gizmo is
associated with a Y gizmo" is clearer than "X gizmos are associated
with Y gizmos".

Vague quantifiers standing in for numbers the author has are a defect:
"numerous", "a variety of", "several key", "significantly". Give the
number.

Do not scatter emphasis on phrases that carry no more weight than
their neighbours, and do not use emoji in technical prose.
