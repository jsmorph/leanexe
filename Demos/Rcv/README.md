# Ranked-choice tabulation

This demo is a tabulator for single-winner ranked-choice contests under Oakland City Charter §1105, the rule that Alameda County misconfigured in the November 2022 count of the Oakland Unified School District 4 board race.  The module fixes the charter's rule at compile time, so no setting can be chosen wrong at run time, and its theorems connect the module's bytes to a Lean transcription of the charter.  [The requirements](requirements.md) state the canonical ballot file, the interpretation of a ballot, the rounds, the report, and the theorems, and [the review](review.md) records each reading of the governing texts and the reviews' findings.

[The test corpus](../../tests/rcv/README.md) fetches Alameda County's official round-by-round reports for Oakland's ranked-choice contests from 2022 to 2026 and the cast vote records published for them, and recounts the records under the county's settings.
