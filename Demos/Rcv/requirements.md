# Oakland ranked-choice tabulator requirements

## Purpose and scope

The demo is a tabulator for single-winner ranked-choice contests, also called instant-runoff voting, and its first module implements Section 1105 of the Oakland City Charter as written.  The module reads a canonical ballot file, counts the contest in rounds under the charter's rules, and writes a report of every round, and theorems connect its bytes to a Lean transcription of these requirements.  Its first use is an audit: anyone who holds a contest's published cast vote records can convert them to the canonical file and recount the contest in a browser, at a command line, or in C.  The module covers the single-winner offices that §1105 governs.  A converter writes the canonical file from the ballot image report of §1105(i)(2), the county's cast vote record export, or D. Otis's standardized form of the county's records.  The module leaves out the reports of §1105(i) broken down by precinct, the manual tally of §1105(j), and the changes that §1105(k) lets the City Clerk make, since the review found none published.  [The review](review.md) records each decision, each reading of the governing texts with its reason, the departures of county practice with their evidence, and the review of these requirements.

## Governing texts

| Text | Version | Copy read | Read |
|---|---|---|---|
| Oakland City Charter §1103 and §1105 | §1105 added and §1103 amended by the voters in February 2007.  Neither copy records a later amendment | The City of Oakland's copy of the charter "as amended through and including March, 2020", a PDF of 2023-05-19 in the City's document store.  It agrees word for word, over §§1103 to 1105, with GoCodebook's copy of the Oakland Municipal Code, 2026-10 edition, text as of 2026-10-19.  Municode, the City's codifier, returned HTTP 403 | 2026-11-09 |
| Cal. Elec. Code §15341 | Updated 1999-01-01, by the copy's note, which gives no history | California.Public.Law's copy, which cites the Legislature's site.  leginfo.legislature.ca.gov returned HTTP 403 | 2026-11-09 |
| Cal. Elec. Code §15342(d) | Updated 2012-01-01, by the copy's note, which gives no history | As for §15341 | 2026-11-09 |

§1103 makes state law govern every election procedure that the charter and the City's ordinances do not provide.  Of the state provisions read, §15341 and §15342(d) reach the count.  §15341 counts a written name only for a candidate who complied with Part 3 of Division 8 of the Elections Code, which begins at §8600 and sets the filings of a write-in candidate, and §15342(d) counts no vote at all when the voter, "by a combination of marking and writing", indicates more names than there are candidates to elect.  The charter decides every tie through §1105(d)(2) and (e), so §15651, the state's rule for ties, does not enter the count, as [the review](review.md#readings-of-the-governing-texts) records.  The charter's provisions below are quoted from the City's copy with its punctuation, and the state's from the copy read.

> **§1105(a)** In each round of counting: (1) "continuing ballot" shall mean a ballot that counts towards some candidate; (2) "continuing candidate" shall mean a candidate that has not been eliminated; and (3) "majority of votes" shall mean more than fifty percent of the votes coming from continuing ballots.
>
> **§1105(c)** The ranked choice voting ballot shall allow voters to rank as many choices as there are candidates.  The ballot shall not interfere with a voter's ability to rank a write-in candidate.
>
> **§1105(d)** The ballots shall be counted in rounds: (1) in the first round, every ballot shall count as a vote towards the first choice candidate.  (2) After every round, if any candidate receives a majority of votes from the continuing ballots, that candidate shall be declared the winner, If no candidate receives a majority, the candidate receiving the smallest number of votes shall be eliminated, and every ballot counting towards that candidate shall be advanced to the next-ranked continuing candidate.  All the ballots shall be counted again in a new round.
>
> **§1105(e)** In the event that two or more candidates tie for the smallest number of votes, the candidate to eliminate shall be chosen by lot.
>
> **§1105(f)** During the elimination stage of any round, in the event that any candidate has more votes than the combined vote total of all candidates with fewer votes. all the candidates with fewer votes shall be eliminated simultaneously, and those ballots advanced to the next ranked continuing candidate.
>
> **§1105(g)** In the first or any round, in the event that any ballot reaches a ranking with no candidate indicated, that ballot shall immediately be advanced to the next ranking.
>
> **§1105(h)** After each round, any ballot that is not continuing is an undervote, overvote, or exhausted ballot, as follows: Any ballot that has no candidates indicated at any ranking shall be declared an "undervote."  In the event that any ballot reaches a ranking with more than one candidate indicated, that ballot shall immediately be declared an "overvote."  In the event that any ballot cannot be advanced because no further candidates are ranked on that ballot, that ballot shall immediately be declared "exhausted" Any ballot that has been declared an undervote, overvote. or exhausted shall remain so and shall not count towards any candidate in that round or in subsequent rounds.
>
> **Cal. Elec. Code §15341** Notwithstanding any other provision of law, no name written upon a ballot in any election shall be counted for an office or nomination unless the candidate whose name has been written on the ballot has complied with Part 3 (commencing with Section 8600) of Division 8.
>
> **Cal. Elec. Code §15342(d)** Neither a vote cast for a candidate whose name appears on the ballot nor a vote cast for a write-in candidate shall be counted if the voter has indicated, by a combination of marking and writing, a choice of more names than there are candidates to be nominated or elected to the office.

The module compiles in the rule identifier below, a line of ASCII text, and prints it on the second line of every report.  The identifier names each governing text with its version, the date on which the texts were read, and a revision number.  A change of a governing text, or of a reading that the review records, requires a new module with a new identifier, and a change of reading alone raises the revision.  The module's digest, published with it, identifies the module itself.

```
oakland-1105 revision 1, Oakland City Charter sections 1103 and 1105 (February 2007), Cal. Elec. Code sections 15341 (updated 1999-01-01) and 15342(d) (updated 2012-01-01), texts read 2026-11-09
```

## The canonical ballot file

### Lines and header

The file is a sequence of bytes divided into lines, each of which ends with the byte LF, `0x0A`, and the last line of a well-formed file ends with LF as well.  A final run of bytes without LF is a line that fails every form, and the file holds no byte below `0x20` other than the LF that ends each line, and no `0x7F`.  Numbers are decimal without leading zeros: `0`, or a nonzero digit followed by digits.  The header comes first, in the order of the table, where `n` is the number of candidates, `k` the number of ranking positions, and `N` the number of ballots.

| Line | Form | Constraint |
|---|---|---|
| 1 | `rcv-ballots 1` | These bytes |
| 2 | `contest ` and an identifier | An identifier has 1 to 64 bytes from `A`–`Z`, `a`–`z`, `0`–`9`, `-`, `_`, `.`, and `:` |
| 3 | `positions ` and `k` | 1 ≤ `k` ≤ 63 |
| 4 | `candidates ` and `n` | 1 ≤ `n` ≤ 63 |
| 4 + `i`, for `i` from 1 to `n` | `candidate `, `i`, a space, a kind word, a space, and a name | The index is `i` itself.  A name has 1 to 255 bytes, each from `0x20` to `0x7E` or from `0x80` to `0xFF` |
| 5 + `n` | `order`, then a space and an index for each of the `n` candidates | A permutation of 1 to `n`, the tie-break order, earliest first |
| 6 + `n` | `ballots ` and `N` | 0 ≤ `N` ≤ 2^32 − 1 |

The kind of a candidate decides whether the count counts rankings of that candidate.  A counted candidate can receive votes, and an uncounted one never does.  The converter assigns the kinds from the records and from the filings of write-in candidates, which lie outside the theorems.  The kind `aggregate-writein` fits only when the aggregate holds no vote for a write-in candidate who complied with Part 3 of Division 8, and records that combine such votes with others must be adjudicated before conversion, so that each qualified candidate's votes take a `named-writein` kind while the remaining write-ins stay `aggregate-writein`.

| Kind word | Candidate | Counted |
|---|---|---|
| `listed` | A candidate printed on the ballot | Yes |
| `named-writein` | A write-in candidate who complied with Part 3 of Division 8 and whom the records name | Yes |
| `aggregate-writein` | The write-ins of the records that do not name the person written in | No |
| `excluded` | A person named in the records who did not comply with Part 3 of Division 8, so that §15341 forbids counting the name | No |

### Ballot lines

Lines 7 + `n` to 6 + `n` + `N` hold one ballot each, and the converter writes one line for each ballot card that carries the contest and no line for any other card.  A ballot line holds fields separated by commas: either `k` fields, one for each ranking position in order, or `k` + 1 fields, of which the first is an identifier with the alphabet and length of the contest identifier and the others are the positions.  The count ignores the identifier, which lets a reader trace a line to its vendor record.  A line whose `k` position fields are all empty is a blank ballot, and for `k` = 1 the blank ballot without an identifier is the empty line.

| Position field | Meaning | Word |
|---|---|---|
| empty | No mark | 0 |
| `i` | A mark for candidate `i`, 1 ≤ `i` ≤ `n` | 2^(`i` − 1) |
| `i₁|i₂|…|iₘ`, `m` ≥ 2, `i₁ < i₂ < … < iₘ` | Marks for `m` candidates at one position | The sum of 2^(`iⱼ` − 1) |
| `*` | An overvote whose candidates the records do not name | 2^63 |

The word column gives each position's 64-bit word, the form in which [the count's words](#word-forms-of-the-count) and the program hold it.  A position word is 0, 2^63, or a nonzero sum of distinct powers 2^(`i` − 1) with `i` from 1 to `n`, and each such word has exactly one field.  The bound of 63 candidates keeps bit 63 free for the unnamed overvote.

### Grammar

The grammar below, in the notation of RFC 5234, states the forms of the lines.  It leaves to the tables the ranges of `k`, `n`, and `N`, the index of each candidate line, the permutation, the number of candidate and ballot lines, the number of fields in a ballot line, and the bounds and order of indices within a field.  A ballot line with `k` + 1 fields takes its first field as the identifier, which settles the one choice that the grammar leaves open.

```
file      = %s"rcv-ballots 1" LF contest positions candidates 1*candidate order ballots *ballot
contest   = %s"contest " ident LF
positions = %s"positions " number LF
candidates= %s"candidates " number LF
candidate = %s"candidate " number SP kind SP name LF
kind      = %s"listed" / %s"named-writein" / %s"aggregate-writein" / %s"excluded"
name      = 1*255namebyte
namebyte  = %x20-7E / %x80-FF
order     = %s"order" 1*(SP number) LF
ballots   = %s"ballots " number LF
ballot    = [ident ","] field *("," field) LF
field     = "" / number *("|" number) / "*"
ident     = 1*64(ALPHA / DIGIT / "-" / "_" / "." / ":")
number    = "0" / %x31-39 *DIGIT
LF        = %x0A
SP        = %x20
```

### The contest structure

The reader's result is a contest structure with the fields of the table, and `write` prints a structure as the tables and the grammar state, with the indices of a multiple position in increasing order and a ballot's identifier field present exactly when the structure holds one.  A structure meets the constraints when `k`, `n`, and `N` lie in the header's ranges, its identifiers and names have their alphabets and lengths, its order is a permutation of 1 to `n`, and each ballot holds `k` position words, each 0, 2^63, or a nonzero sum of distinct powers 2^(`i` − 1) with `i` ≤ `n`.  The count reads `k`, the kinds, the order, and the position words, and the report also prints the contest identifier and the names.

| Field | Content |
|---|---|
| Contest | The contest identifier, as bytes |
| Positions | `k` |
| Candidates | For each candidate in index order, its kind and its name as bytes, `n` in all |
| Order | The tie-break order, a list of `n` indices |
| Ballots | For each ballot line in file order, its identifier or none, and its `k` position words, `N` in all |

### Malformed files and the error report

Each line number `j` has a role that the header determines: `format` for line 1, `contest` for 2, `positions` for 3, `candidates` for 4, `candidate` for 5 to 4 + `n`, `order` for 5 + `n`, `ballots` for 6 + `n`, `ballot` for 7 + `n` to 6 + `n` + `N`, and `end` for 7 + `n` + `N`.  A line meets its role when it has that role's form in the tables and the grammar, and no line meets the role `end`.  A file is well formed when each of its lines meets its role, it holds exactly 6 + `n` + `N` lines, and its last byte is LF.  The reader reports, for every other file, the smallest `j` such that line `j` is absent, lacks its LF, or fails its role, together with that role.  Line `j` counts as absent only for `j` ≤ 6 + `n` + `N`.  The role of a line after line 4 depends on `n`, and that of a line after line 6 + `n` on `N` as well, and lines 4 and 6 + `n` meet their roles whenever the error lies beyond them, so the role of the reported line is always defined.

A malformed file yields the three lines below and no count.  An empty file gives `error 1 format`, a file whose ballot lines stop early gives the number of the first missing line with the role `ballot`, and a file with a line after the last ballot gives `error <7 + n + N> end`.  A line that fails gives its own number even when an earlier line holds a value that the failing line contradicts, such as a ballot count above the number of ballot lines.

```
rcv-report 1
rule <the rule identifier>
error <j> <role>
```

## Interpretation of a ballot

The candidates of kinds `listed` and `named-writein` form the counted set `K`, and the continuing set `C` of a round is a subset of `K`.  A position is empty when its word is 0, single when it marks exactly one candidate, and multiple when it marks two or more candidates or holds the unnamed overvote.  The interpretation of a ballot against `C` examines its positions from the first, by these rules in order:

1. An empty position passes to the next position, by §1105(g).
2. A multiple position ends the examination: the ballot is inactive with the reason `overvote`, by §1105(h) and §15342(d).
3. A single position for a candidate in `C` ends the examination: the ballot counts for that candidate.
4. A single position for any other candidate passes to the next position.  The candidate is either a counted candidate eliminated in an earlier round, from whom §1105(d)(2) and (f) advance the ballot, or an uncounted candidate, whose ranking the count passes over as it passes over an empty position, since §15341 forbids counting it.

When the examination passes the last position, the ballot is inactive with one of the first three reasons of the table, which depend on the ballot alone, and rule 2 gives the fourth.  An inactive ballot counts for no candidate in the round, and §1105(h) names its kind.  The table gives each reason with the charter's term and the category of Alameda County's reports.

| Reason | Condition | §1105(h) | Alameda's category |
|---|---|---|---|
| `blank` | Every position is empty | Undervote | Blanks |
| `uncounted` | Some position is single, and every single position marks an uncounted candidate | Undervote | Blanks |
| `exhausted` | Some single position marks a counted candidate | Exhausted | Exhausted |
| `overvote` | The examination reaches a multiple position | Overvote | Overvotes |

The reasons cover every inactive ballot, and each of Alameda County's categories is a sum of them: Blanks is `blank` plus `uncounted`, Overvotes is `overvote`, and Exhausted is `exhausted`.  The interpretation depends on the ballot, the candidates' kinds, and `C` alone, which is the locality that the theorems state.  A ballot that ranks one candidate at several positions needs no rule of its own, since after the candidate's elimination rule 4 passes over each of its rankings.  The examination declares an overvote at a multiple position whether or not the marked candidates continue, which is the ballot that "reaches a ranking with more than one candidate indicated", and a position that marks a counted candidate together with a write-in is multiple under §15342(d).

The rules give the stability that §1105(h) states as "shall remain so".  Let `S′ ⊆ S` be continuing sets.  A ballot that counts for `w` against `S` counts for `w` against `S′` whenever `w ∈ S′`, because every position before `w`'s passed against `S` and still passes against `S′`.  A ballot that is inactive against `S` is inactive against `S′` with the same reason, because the examination against `S′` passes every position that the examination against `S` passed.

## Rounds

Round 1 has the continuing set `C₁ = K`.  In round `r`, every ballot is interpreted against `Cᵣ`, the votes `vᵣ(i)` of a candidate `i ∈ Cᵣ` are the number of ballots that count for it, the continuing ballots `Tᵣ` are the sum of the votes, and the inactive ballots are counted by reason.  After the counts, the first of these rules that applies ends the round:

1. **Majority.**  If a candidate `i ∈ Cᵣ` has 2 `vᵣ(i)` > `Tᵣ`, the count ends with `i` as the winner, by §1105(a)(3) and (d)(2).  At most one candidate meets the test.
2. **No continuing ballot.**  If `Tᵣ` = 0, the count ends with no winner.
3. **Batch.**  For `X ∈ Cᵣ`, let `L(X)` be the candidates of `Cᵣ` with fewer votes than `X`.  `X` qualifies when `L(X)` is not empty and `vᵣ(X)` exceeds the sum of the votes of `L(X)`, the strict test of §1105(f).  If some qualifying `X` has two or more candidates in `L(X)`, the round eliminates the largest such `L(X)`.
4. **Lowest.**  Otherwise let `Z` be the candidates of `Cᵣ` with the fewest votes.  If `Z` has one candidate, the round eliminates it, by §1105(d)(2).  If `Z` has two or more, the round eliminates the candidate of `Z` that comes latest in the tie-break order, as the drawing by lot of §1105(e), and the report marks the tie.

The next round has `Cᵣ₊₁ = Cᵣ` minus the eliminated candidates.  The sets `L(X)` are nested, since `L(X) ⊆ L(Y)` whenever `vᵣ(X) ≤ vᵣ(Y)`, so the largest qualifying set is defined, and it is `L(X)` for the qualifying `X` with the most votes.  A batch never divides candidates with equal votes, and a batch whose members tie needs no drawing.  When rule 3 finds only sets of one candidate, that candidate is the only one with the fewest votes, so rule 4 eliminates the same candidate.  The rules read the votes of the current round, the continuing set, and the tie-break order, and no earlier round.

Every round that does not end the count eliminates at least one candidate, so the count has at most the larger of 1 and the size of `K` rounds.  A tied final round arises when two candidates continue with `Tᵣ`/2 votes each: neither holds a majority, rule 4 eliminates the one later in the order and marks the tie, and in the next round the other holds every continuing ballot, a majority.  `Tᵣ` = 0 in round 1 when no ballot counts for anyone, as in a contest with no ballots or no counted candidate.  By the stability of the interpretation a round with no continuing ballot can be followed only by such rounds, in which no candidate can reach §1105(a)'s majority, so rule 2 ends the count at the first of them.  When `T₁` > 0, every later round has a continuing ballot and the count ends with a winner.

## The report

The report is text in lines that end with LF, printed by the proved printer, with numbers in the decimal form of the ballot file.  The tables give its lines in order.  The candidates of `Cᵣ` appear in increasing index, and so do the members of a batch and of a tied set.

| Lines | Form | Content |
|---|---|---|
| 1 | `rcv-report 1` | Format and version |
| 2 | `rule ` and the rule identifier | The rule compiled in |
| 3 to 7 + `n` | Lines 2 to 6 + `n` of the ballot file, byte for byte | Contest, positions, candidates, order, and ballot count |
| For each round `r` | `round r` | Round number, from 1 |
| | `continuing Tᵣ` | Continuing ballots |
| | `votes i vᵣ(i)` for each `i ∈ Cᵣ` | Votes of each continuing candidate |
| | `inactive blank x`, `inactive uncounted x`, `inactive overvote x`, `inactive exhausted x` | Inactive ballots by reason, cumulative as §1105(i)(1) requires |
| | In every round but the last, one of the forms below | The elimination |
| Last | `winner i`, or `winner none` | The winner of rule 1, or none under rule 2 |

| Elimination | Lines |
|---|---|
| Batch of rule 3 | `eliminate batch i₁ … iₘ` |
| Single candidate with the fewest votes | `eliminate lowest i` |
| Tie decided by the order | `tie j₁ … jₘ`, the tied set, then `eliminate order i` |

The ballot file below exercises every reason, a batch, a tie, and a tied final round, and the block after it gives its report without the first two lines.  Ballot 13 ranks only the aggregate write-in, and ballot 12 ranks only the named write-in `D`, which the batch of round 1 eliminates.  The order `2 1 3 4 5` decides the tie of round 2 against `A`.

```
rcv-ballots 1
contest example-1
positions 3
candidates 5
candidate 1 listed A
candidate 2 listed B
candidate 3 listed C
candidate 4 named-writein D
candidate 5 aggregate-writein Write-in
order 2 1 3 4 5
ballots 15
id-01,1,2,
1,,
5,1,
1|2,1,
1,3,2
1,1,
2,1,
2,,
,2,
2,3,1
3,2,
4,,
5,,
,,
*,2,
```

```
contest example-1
positions 3
candidates 5
candidate 1 listed A
candidate 2 listed B
candidate 3 listed C
candidate 4 named-writein D
candidate 5 aggregate-writein Write-in
order 2 1 3 4 5
ballots 15
round 1
continuing 11
votes 1 5
votes 2 4
votes 3 1
votes 4 1
inactive blank 1
inactive uncounted 1
inactive overvote 2
inactive exhausted 0
eliminate batch 3 4
round 2
continuing 10
votes 1 5
votes 2 5
inactive blank 1
inactive uncounted 1
inactive overvote 2
inactive exhausted 1
tie 1 2
eliminate order 1
round 3
continuing 7
votes 2 7
inactive blank 1
inactive uncounted 1
inactive overvote 2
inactive exhausted 4
winner 2
```

The 2022 contest for School Director, District 4, of the Oakland Unified School District has 30,983 ballots in D. Otis's standardized form of the county's records.  Converted with the candidates in the order of the county's report, `MIKE HUTCHINSON`, `PECOLIA MANIGO`, `NICK RESNICK`, and the aggregate `Write-in`, and with the order `1 2 3 4`, its report after the header lines is the one below, whose figures equal those of the county's corrected and certified report.  The report has no `tie` line, so by T9 every tie-break order gives the same rounds.

```
round 1
continuing 26432
votes 1 8227
votes 2 8190
votes 3 10015
inactive blank 4269
inactive uncounted 134
inactive overvote 148
inactive exhausted 0
eliminate lowest 2
round 2
continuing 24586
votes 1 12421
votes 3 12165
inactive blank 4269
inactive uncounted 134
inactive overvote 173
inactive exhausted 1821
winner 1
```

## Word forms of the count

The first increment's export takes the contest as an array of words and returns the count as an array of words, before the reader and the report's printer exist.  The reader's result determines these words, so the later byte-to-byte export composes the reader, the count over words, and the printer.  The contest's words hold the header's numbers and the ballots' position words and leave out the identifiers and names, which the count never reads.

| Words | Content |
|---|---|
| 0, 1, 2 | `n`, `k`, `N` |
| 2 + `i`, for `i` from 1 to `n` | The kind of candidate `i`: 0 `listed`, 1 `named-writein`, 2 `aggregate-writein`, 3 `excluded` |
| 2 + `n` + `j`, for `j` from 1 to `n` | The `j`-th candidate of the tie-break order |
| 3 + 2`n` + (`b` − 1)`k` + (`p` − 1) | The word of position `p` of ballot `b` |

An array is a valid contest when it has 3 + 2`n` + `Nk` words, `n`, `k`, and `N` lie in the header's ranges, each kind is below 4, the order is a permutation of 1 to `n`, and each position word is 0, 2^63, or a nonzero sum of distinct powers 2^(`i` − 1) with `i` ≤ `n`.  The export returns `[0]` for every other array.  For a valid contest it returns 1, the number `R` of rounds, `n` + 9 words for each round, and the winner's index or 0 for no winner, 3 + `R`(`n` + 9) words in all.

| Word of a round | Content |
|---|---|
| 0 | The mask of `Cᵣ`, with bit `i` − 1 for candidate `i` |
| 1 | `Tᵣ` |
| 1 + `i`, for `i` from 1 to `n` | `vᵣ(i)`, or 0 when `i ∉ Cᵣ` |
| `n` + 2 to `n` + 5 | Inactive ballots for `blank`, `uncounted`, `overvote`, and `exhausted` |
| `n` + 6 | The elimination: 0 none, in the last round, 1 lowest, 2 order, 3 batch |
| `n` + 7 | The mask of the eliminated candidates |
| `n` + 8 | The mask of the tied set when the elimination is 2, and 0 otherwise |

## Theorems

The theorems hold for every input, with the premises that each states, and depend on no axiom beyond `propext`, `Classical.choice`, and `Quot.sound`.  `read`, `count`, and `report` name the specification's reader, count, and report, and the terms continuing set, votes, `Tᵣ`, interpretation, qualifying set, tie-break order, and the reasons are those of the sections above.  The single count is the count without rule 3.  The county count, Alameda County's practice, interprets ballots in the same way, has no majority stop, no rule 2, and no rule 3, eliminates by rule 4 while three or more candidates continue, and ends at the first round with at most two: it names the candidate of that round with more votes, the candidate alone, or none when the two tie or none continues.

### Main theorems

| Theorem | Statement |
|---|---|
| T1 Bytes | For every byte string `b`, the module's export `tabulate`, called on `b` from a ready store with room for its generated bound, returns without a trap the bytes `report b`: the error report when `read b` fails, and the printed count otherwise.  The first increment states the same of its export over words with the count's word forms.  The WASI process, given `b` on its standard input, writes `report b` to its standard output, and the C translation carries the call theorem under the C items of the trusted base |
| T2 Reader | (a) For every [contest structure](#the-contest-structure) `f` that meets the constraints, `read (write f)` returns `f`.  (b) For every byte string `b`, if `read b` returns `f`, then `write f = b`, so each structure has exactly one canonical file.  (c) If `b` is the writing of no such structure, `read b` returns the line `j` and the role that [malformed files](#malformed-files-and-the-error-report) define, and the report is the error report.  (d) For every 64-bit value `v`, the number reader over packed bytes returns `v` on the decimal printer's text of `v`, and every text it accepts is the printer's text of the value it returns |
| T3 Winner | (a) The count names a winner exactly when `T₁` > 0.  (b) The winner holds more than half of the continuing ballots of the last round.  (c) A last round other than round 1 has a single continuing candidate exactly when the round before it had two continuing candidates with equal votes, and the report then marks that round's elimination as a tie.  (d) The count has at most the larger of 1 and the size of `K` rounds |
| T4 Elimination | In every round that eliminates, `Tᵣ` > 0, no candidate holds a majority, and the elimination is (a) a batch, the largest qualifying `L(X)`, with two or more candidates; (b) a lowest elimination, when no qualifying set has two or more candidates and one candidate alone has the fewest votes, which is the candidate eliminated; or (c) an elimination by order, when no qualifying set has two or more candidates and two or more candidates have the fewest votes, which form the tied set, and the eliminated candidate is the member latest in the order.  The last round eliminates no one and ends by rule 1 or rule 2 |

### Theorems of the count

| Theorem | Statement |
|---|---|
| T5 Conservation | In every round the votes of the continuing candidates and the inactive counts by reason sum to `N`, and `continuing` is the sum of the votes |
| T6 Locality | In every round `r`, `vᵣ(i)` is the number of ballots whose interpretation against `Cᵣ` counts for `i`, each inactive count is the number of ballots whose interpretation against `Cᵣ` has that reason, and `Cᵣ₊₁` is `Cᵣ` minus the candidates that round `r` eliminates |
| T7 Invariance | Two well-formed files that differ by a permutation of their ballot lines, or in the identifier fields of their ballot lines, added, removed, or changed, have the same report |
| T8 Stability | For every ballot and continuing sets `S′ ⊆ S`: if the ballot counts for `w` against `S` and `w ∈ S′`, it counts for `w` against `S′`, and if it is inactive against `S` with a reason, it is inactive against `S′` with the same reason.  Consequently, from each round to the next, each inactive count does not decrease, the votes of a candidate that continues do not decrease, and `T` does not increase |
| T9 Order | Let the count under the order `π` mark ties in some rounds, possibly none.  If an order `π′` makes the same choice at each of them, that is, if in each such round the eliminated candidate is the member of the tied set latest in `π′`, the counts under `π` and `π′` have the same rounds and the same winner, and their reports differ only in the `order` line |
| T10 Batch | For every interpretation function that, against each continuing set `S`, either counts a ballot for a member of `S` or makes it inactive with a reason, and that satisfies both statements of T8, counted by the rules of rounds with the strict test of rule 3: (a) the count and the single count name the same winner, or both none.  (b) The continuing set of each round of the count is the continuing set of a round of the single count, with the same votes and inactive counts, unless the single count ends earlier, in which case it names the count's winner.  (c) Once the single count reaches the continuing set of a round of the count that eliminates a batch, each of its rounds eliminates one member of the batch and no other candidate, until the batch is gone or the single count ends |
| T11 Majority holder | (a) If `w` holds a majority of the continuing ballots against `S`, it holds a majority against every `S′` with `w ∈ S′ ⊆ S`.  (b) A candidate that holds a majority in some round of the county count continues in every later round of it, and the county count names it.  (c) If the count names `w`, and its last round is round 1 or has two or more continuing candidates, the county count names `w`.  If the count's last round has `w` alone and is not round 1, the county count's last round has the continuing set and the votes of the count's round before it, the tied round.  (d) Every round of the count with two or more continuing candidates is a round of the county count with the same continuing set, votes, and inactive counts |

### Properties of instant runoff

The properties compare ballots through the interpretation.  For counted candidates `a` and `b`, `a` beats `b` when more ballots count for `a` than for `b` against the continuing set `{a, b}`.  Raising a candidate `w` on a ballot moves `w` to an earlier position and leaves the other positions in their order.

| Theorem | Statement |
|---|---|
| T12 Majority criterion | If more than half of the continuing ballots of round 1 count for `w`, the count ends after round 1 with `w`, and the single count and the county count name `w` |
| T13 Condorcet loser | If `K` has two or more candidates and every other candidate of `K` beats `ℓ`, the count does not name `ℓ` |
| T14 Later-no-harm | Let a ballot's position `p` mark only the counted candidate `w`, and replace the ballot with one whose positions 1 to `p` are the same.  If the count of the first contest names `w`, the count of the second has the same rounds and names `w` |
| T15 Monotonicity fails | The two contests below differ only in that two ballots raise `A` from second to first.  The count names `A` for the first and `B` for the second |

The contests of T15 have candidates `A`, `B`, and `C`, all `listed`, three positions, and the order `1 2 3`.  The first has 17 ballots: six `1,2,3`, five `2,1,3`, four `3,2,1`, and two `3,1,2`.  Its round 1 gives `A` 6, `B` 5, and `C` 6, rule 4 eliminates `B`, and round 2 gives `A` 11 of 17.  The second replaces the two `3,1,2` with `1,3,2`: round 1 gives `A` 8, `B` 5, and `C` 4, rule 4 eliminates `C`, and round 2 gives `B` 9 of 17.  Neither count marks a tie.

## What lies outside the theorems

| Item | Status |
|---|---|
| The converter | Turns a vendor's export into the canonical file without proof.  Publishing the canonical file beside the vendor's file and the comparison with the county's first round make it checkable |
| Kinds of candidates | The converter assigns them from the records, and whether a write-in candidate complied with Part 3 of Division 8 is a fact about filings |
| The tie-break order | The theorems hold for every order.  Whether the order came from a drawing by lot, and when, is outside them, and T9 shows which ties the order decided |
| The records | Whether the cast vote records agree with the paper ballots is the question of a risk-limiting audit |
| The transcription | Whether these requirements and the specification state §1105 and the state provisions correctly is a matter of review, which [the review](review.md) records |
| The page | The browser page's code, which reads the file and shows the report |
| The reference and the comparison scripts | The Python reference, its faulty setting, and the scripts that compare reports with the county's are tests without proof |
| Legal force | Official tabulation needs a certified system, so the module serves as an audit tool |

## Trusted base

The theorems about the module rest on the items of [the trusted base](../../docs/trusted-base.md) for WebAssembly modules: Lean's kernel, Talos's execution semantics and its store definitions, the binary decoder, the agreement of Wasmtime or the browser's engine with Talos, and the host's placement of the argument bytes.  The process theorem adds the items for WASI Preview 1 modules, among them the host specification and Wasmtime's Preview 1, and the C translation rests on the items for C files, CompCert and the Lean copy of Clight.  The specification's definitions are trusted to state these requirements, and a review checks them against the requirements before a program depends on them.

## Comparison with Alameda County's reports

The county reports each round's votes for every candidate and the categories Blanks, Overvotes, and Exhausted, all three cumulative.  This paragraph applies to reports without the 2022 suspension.  By T11(d), each round of the module's count with two or more continuing candidates is a round of the county count with the same continuing set, and the comparison tests that round against the county's report round with that set: the votes of every continuing candidate must be equal, Blanks must equal `blank` plus `uncounted`, Overvotes `overvote`, and Exhausted `exhausted`.  Before the module's first batch the matched rounds have the same numbers, and each matched round in which both counts eliminate one candidate must eliminate the same one.  A batch of `m` candidates advances the county's round numbers by `m` − 1 against the module's, since the county eliminates the batch's members one per round.  When the module's count names a winner and its last round is round 1 or holds two or more candidates, T11(c) gives the county's winner as the module's, and the county's rounds after the majority lie beyond the charter's count.

A tie that the module marks is compared after a rerun with an order that encodes the county's drawing, if its report states it.  After a tied final round the county's last round is the tied pair, which the county's own procedure decides, and the module's winner is compared with the county's choice in the same way.  A report whose settings record the 2022 suspension is compared round by round with the reference's count under the faulty setting of the case study below, and with the module by winner.

The county departs from the charter's text where it eliminates one candidate per round although §1105(f) requires a batch, and where it continues counting after a candidate holds a majority until two candidates remain.  It also allows five rankings in contests with six and with ten candidates, although §1105(c) requires as many rankings as candidates and the review found no published determination under §1105(k)(1), and in November 2022 its reports used a first-round suspension that departs from §1105(d)(1) and (g).  [The review](review.md#departures-of-county-practice) records each departure with its evidence.  The first two leave the winner unchanged whenever the module names a winner and its last round is round 1 or holds two or more candidates, by T11(c), which covers every contest of the corpus, since each has a continuing ballot and none has a tie.  The limit on rankings constrains the ballots and leaves the count of the records unchanged, and the suspension changed the winner of District 4, as the case study shows.

## Tests

**Python reference.**  `tests/rcv/reference.py`, with PEP 723 metadata, implements the reader, the count, the report, and the word forms from these requirements alone, written by an agent that has not read the Lean specification.  It is compared byte for byte with native Lean, the module, the WASI process, and C on every test input.  It also implements, as an option for the case study alone, the faulty setting defined below, which no module carries.

**Edge cases.**  `tests/rcv/edges.py` writes canonical files that cover an overvote at each position, named and unnamed; every pattern of empty positions for `k` up to 4; duplicate rankings; ballots that rank only uncounted candidates; ties at the lowest place in rounds with three or more candidates and in the final round; batches whose largest qualifying set has two or more members, at the boundary of the strict test where `vᵣ(X)` equals the batch's sum and exceeds it by one, and with tied members; every ballot inactive; no ballots; one candidate; no counted candidate; 63 candidates and 63 positions; identifiers of 1 and 64 bytes; two nested qualifying sets of two or more candidates each; a batch inside which the single count ends at a majority; and the two contests of T15.  Each file's expected report comes from the reference, and a reviewer checks the reports of the smallest files by hand.  It also writes malformed files that fail each role, among them leading zeros, an index of 0 or above `n`, a field with decreasing or repeated indices, a missing final LF, a carriage return, a ballot count above and below the number of lines, and a byte outside a name's or an identifier's alphabet.  For the word forms of increment 1 it writes invalid arrays: a wrong length, a kind of 4, an order that is not a permutation, a position word with bit 63 and another bit, and a position word with a bit at or above `n`.

**Corpus.**  [The Oakland RCV corpus](../../tests/rcv/README.md) pins by URL, size, and SHA-256 the county's reports of the 30 Oakland contests from November 2022 to November 2026, D. Otis's cast vote records of 19 of them, and the Registrar's presentation on the 2022 District 4 error, and its scripts fetch, parse, and recount them.  Increment 2 converts each of the 19 records to the canonical file, and the county's own exports, which the county releases on request, when they are obtained, and each contest is compared with the county's report by the rule of the previous section.  With the interpretation of these requirements, each report's own suspension setting, and each report's eliminations, `tests/rcv/recount.py` equals every round of the 15 reports whose records hold all of their ballots, while the records of the 2024 at-large, City Attorney, and District 7 contests and the 2025 mayoral contest lack 2 to 13 ballots.  No round of the corpus has a tie for the fewest votes, and no report lists a write-in candidate, so the edge cases supply both.

**Alameda 2022 case study.**  The case study counts District 4 under the charter, with the module, and under the faulty setting, with the reference.  The faulty setting is the county count with one change in round 1: a ballot whose first position is empty or holds a single uncounted candidate, and whose interpretation in round 1 counts for a candidate or is `overvote`, counts for no one and is reported as suspended, and from round 2 on every ballot is interpreted as the requirements state.  This is the rule of `recount.py --suspend`, which reproduces every round of the county's certified 2022 reports whose settings record the suspension, the mayor's nine rounds among them.  For District 4, `tests/rcv/district4.py` gives under it Hutchinson 8,112, Manigo 8,153, Resnick 9,954, and 235 suspended in round 1, and Resnick 12,352 against Manigo 11,753 in round 2, the figures of Table A on slide 6 of the Registrar's presentation, the count the county certified first.  Under the charter Hutchinson wins with 12,421 against 12,165, as the county's corrected report of 2023-03-10 states.

## Plan

Each increment reaches bytes and theorems, and each theorem is tested on a model built from these requirements before its proof.  The first three increments complete the Oakland module, and the last two add a second statute and the properties of instant runoff.  The Lean files are in `Demos/Rcv/`, the references and comparisons in `tests/rcv/`, and the page in `tests/web/`.

| Increment | Work | Done when |
|---|---|---|
| 1 | These requirements and the review.  The specification over lists: interpretation, rounds, and the count's word forms.  The program over arrays in the verified compiler's dialect, its refinement to the specification, and `verified_compile` with the call theorem of the export over words.  T4, T5, and T6.  The Python reference with its word forms | The call theorem and T4 to T6 hold with the allowed axioms.  A fresh agent has checked the specification's samples against these requirements.  The module, native Lean, and the reference agree on every edge case and on District 4 in word form |
| 2 | The reader and the writer over `LeanExe.Bytes` with T2, the report's printer with proved decimal printing, and the export `tabulate` with T1 over bytes.  T3, T7, T8, T9, T10, and T11.  The converters, unverified, of D. Otis's records and of the county's Dominion exports, and the corpus in canonical files | The theorems hold.  The module's reports equal the reference's bytes on every edge case and corpus file.  Each corpus contest agrees with the county's report under the comparison rule, or its difference is explained in the review |
| 3 | The WASI process with its refinement and termination theorems, the C translation, the browser page, the District 4 case study, and the README | The module, the WASI process, C, and native Lean agree byte for byte on the edge cases and the corpus.  The page recounts a local file.  The case study reproduces the county's corrected report under the charter and the first certified figures under the faulty setting |
| 4 | The Maine module, with its own requirements and review, sharing the file format, the report, and the theorems that T10 states for every interpretation | The criteria of its own requirements |
| 5 | T12 to T15.  RCTab v2.1.0, pinned by version and checksum, with each contest's configuration committed and a table in the review that maps each setting to the charter | The theorems hold.  RCTab's rounds agree with the module's or with the county count's, or each difference is explained in the review |

## References

- [Oakland City Charter, as amended through March 2020, City of Oakland](https://cao-94612.s3.amazonaws.com/documents/City-Charter-See-Article-II-Section-202-Council-Salaries-Section-603-Public-Ethics-Commission_2023-05-19-210220_yyug.pdf)
- [Oakland Municipal Code, Charter Article XI, GoCodebook, 2026-10 edition](https://gocodebook.com/library/us/ca/oakland/article-xi-elections)
- [Cal. Elec. Code §15341](https://leginfo.legislature.ca.gov/faces/codes_displaySection.xhtml?lawCode=ELEC&sectionNum=15341) and [the copy read](https://california.public.law/codes/elections_code_section_15341)
- [Cal. Elec. Code §15342](https://leginfo.legislature.ca.gov/faces/codes_displaySection.xhtml?lawCode=ELEC&sectionNum=15342) and [the copy read](https://california.public.law/codes/elections_code_section_15342)
- [Cal. Elec. Code §8600](https://leginfo.legislature.ca.gov/faces/codes_displaySection.xhtml?lawCode=ELEC&sectionNum=8600) and [the copy read](https://california.public.law/codes/elections_code_section_8600)
- [Cal. Elec. Code §8601, the copy read](https://california.public.law/codes/elections_code_section_8601)
- [Alameda County Registrar of Voters, RCV results, November 8, 2022](https://www.alamedacountyca.gov/rovresults/rcv/248/)
- [Alameda County Registrar of Voters, RCV results, November 5, 2024](https://www.alamedacountyca.gov/rovresults/rcv/252/)
- [Alameda County Registrar of Voters, RCV results, April 15, 2025](https://alamedacountyca.gov/rovresults/rcv/257)
- [Alameda County Registrar of Voters, RCV results, November 3, 2026](https://www.alamedacountyca.gov/rovresults/rcv/260/)
- [D. Otis, Single winner ranked choice voting CVRs, Harvard Dataverse, version 25](https://doi.org/10.7910/DVN/AMK8PJ)
- [Alameda County Registrar of Voters, Ranked-Choice Voting Tally presentation](https://www.acgov.org/board/bos_calendar/documents/RankedChoiceVotingTallyPresentation.pdf)
- [The Oakland RCV corpus](../../tests/rcv/README.md)
- [D. McCune, Ranked Choice Bedlam in a 2022 Oakland School Board Election, arXiv:2303.05985](https://arxiv.org/abs/2303.05985)
- [RFC 5234, Augmented BNF for Syntax Specifications](https://www.rfc-editor.org/rfc/rfc5234)
- [RFC 7405, Case-Sensitive String Support in ABNF](https://www.rfc-editor.org/rfc/rfc7405)
- [RCTab](https://github.com/BrightSpots/rcv)
- [Order book requirements](../OrderBook/requirements.md)
- [Decimal text of `Int64`](../../Library/Numerics/Decimal/Int64Text/README.md)
- [Trusted base](../../docs/trusted-base.md)
