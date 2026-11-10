# Maine ranked-choice tabulator requirements

## Purpose and scope

The Maine module is the tabulator's second module, and it implements the count of 21-A M.R.S. §723-A as PL 2025 c. 363 amended it, with the rules of 29-250 C.M.R. ch. 535 where the statute leaves the count to them.  It shares with [the Oakland module](../requirements.md) the canonical ballot file, its reader and writer, the tally of a round, the report's lines with one addition, the contest's word form, and the theorems that hold for every interpretation.  It differs in the interpretation of a ballot, which ends at two consecutive skipped rankings, in the initial test over all ballots that c. 363 added, and in the rounds, which eliminate one candidate at a time until two remain and have no majority stop and no batch.  Its first use is an audit: the Secretary of State posts the complete cast vote record of every ranked-choice count under §723-A(5-C), and anyone who holds the posted spreadsheets can convert them to the canonical file and recount the contest.  The module covers the single-winner contests that §1(27-C) makes ranked-choice contests: the primaries for United States Senator, Representative to Congress, Governor, State Senator, and State Representative, and the general and special elections for United States Senator and Representative to Congress.  It leaves out presidential electors and presidential primaries, whose tabulations §723-A(5-B) and (7) set apart, the recounts of chapter 536 and §737-A, and the municipal returns of chapter 535 §4(1).  [The review](review.md) records each reading of the governing texts with its reason, each difference between the statute and the rules and the text that governs it, the departures of official practice with their evidence, the recount of the corpus, and the review of these requirements.

## Governing texts

| Text | Version | Copy read | Read |
|---|---|---|---|
| 21-A M.R.S. §723-A | Amended by PL 2025 c. 363, §§5 to 8, effective 2025-09-24, after PL 2023 c. 304 and c. 628 | The Revisor of Statutes' online statutes, which state that they reflect the changes made through the Second Regular Session of the 132nd Legislature and are current through October 1, 2026.  The section's page was extracted on 2026-10-05 | 2026-11-10 |
| PL 2025 c. 363, LD 911 | Approved 2025-06-18 in the First Special Session of the 132nd Legislature, without an emergency clause, and effective on the session's general effective date, 2025-09-24 | The chaptered law, 132LR2208(05), from the Legislature's site, the bill's status page, and the Legislature's digest of the session's enacted laws for the effective date | 2026-11-10 |
| 21-A M.R.S. §1(11-A), (27-C), (45-A), and (51) | (27-C) amended by PL 2025 c. 363, §1 | As for §723-A | 2026-11-10 |
| 21-A M.R.S. §371(5) and (6) and §374-A(3) | Amended by PL 2025 c. 363, §§2 to 4 | As for §723-A | 2026-11-10 |
| 21-A M.R.S. §696(2) | (2)(E) as amended by PL 2017 c. 141, the section last amended by PL 2023 c. 304 | As for §723-A | 2026-11-10 |
| 21-A M.R.S. §722-A | Repealed and replaced by PL 2025 c. 397, §44, effective 2025-09-24 | As for §723-A | 2026-11-10 |
| 21-A M.R.S. §732 | Amended by PL 2025 c. 114, §1, effective 2025-09-24 | As for §723-A | 2026-11-10 |
| 29-250 C.M.R. ch. 535 | Filing 2018-230, effective 2018-11-07, after the emergency filing 2018-079 of 2018-05-11.  The Department's list of its rules links no later filing | The Department of the Secretary of State's Word copy, which records an accessibility check of 2026-04-08, linked from that list.  Cornell LII's copy of §4 agrees with it apart from spacing | 2026-11-10 |

§723-A(1)(H-1) defines the ranked-choice voting count as the process "described in this section and in rules adopted by the Secretary of State", and §723-A(5-A) requires the rules, so the count rests on both texts.  The statute governs where the two differ, and the rules govern the cases that the statute leaves open.  The rules predate the statute's amendments of 2019 to 2025, so they still permit batch elimination by reference to repealed paragraphs, send a tie in the final round to a drawing by lot where §723-A(3) sends it to §732, apply the first-choice test to the municipal returns without the statute's denominator, and do not mention excluded candidates.  Since 2018 they have also read an overvote more broadly than the statute and ended the count at two candidates where the statute ends it at two or fewer.  [The review](review.md#the-statute-and-the-rules) records each of these differences with the reading that the module implements and its reason.  The provisions below are quoted from the copies read, with the copies' non-breaking hyphens written as hyphens.

> **§723-A(1)** B. "Continuing ballot" means a ballot that is not an exhausted ballot.  C. "Continuing candidate" means a candidate who has not been removed from consideration and is not an excluded candidate.  C-1. "Excluded candidate" means a candidate who is listed on the ballot or has qualified as a declared write-in candidate, but has died, been disqualified or withdrawn less than 70 days before the election.  D. "Exhausted ballot" means a ballot that does not rank any continuing candidate, contains an overvote at the highest continuing ranking or contains 2 or more sequential skipped rankings before its highest continuing ranking.  E. "Highest continuing ranking" means the highest ranking on a voter's ballot for a continuing candidate.  F. "Last-place candidate" means the candidate with the fewest votes in a round of the ranked-choice voting count.  H. "Overvote" means a circumstance in which a voter has ranked more than one candidate at the same ranking.  I. "Ranking" means the number assigned on a ballot by a voter to a candidate to express the voter's preference for that candidate.  Ranking number one is the highest ranking, ranking number 2 is the next-highest ranking and so on.  K. "Skipped ranking" means a circumstance in which a voter has left a ranking blank and ranks a candidate at a subsequent ranking.
>
> **§723-A(2)** Except as provided in subsections 2-A, 3, 4 and 7, the following procedures are used to determine the winner of an election determined by ranked-choice voting.  If a candidate has been assigned ranking number one on more than 50% of all ballots cast for the particular office for which the candidate is running, including but not limited to ballots on which ranking number one is blank, on which there is an overvote at ranking number one or on which ranking number one was assigned to an excluded candidate, that candidate is declared the winner of the election.  If no candidate has been assigned ranking number one on more than 50% of the ballots cast for that particular office, the ranked-choice voting count must proceed in rounds.  In each round, the number of votes for each continuing candidate must be counted.  Each continuing ballot counts as one vote for its highest-ranked continuing candidate for that round.  Exhausted ballots are not counted for any continuing candidate.  The round then ends with one of the following 2 potential outcomes.  A. If there are 2 or fewer continuing candidates, the candidate with the most votes is declared the winner of the election.  B. If there are more than 2 continuing candidates, the last-place candidate is removed from consideration and a new round begins.
>
> **§723-A(2-A)** In any round of the ranked-choice voting count, a ballot on which an excluded candidate is the highest-ranked candidate must be counted for the next-highest-ranked continuing candidate.
>
> **§723-A(3)** A tie under this section between last-place candidates in any round must be decided by lot, and the candidate chosen by lot is removed from consideration.  The result of the tie resolution must be recorded and reused in the event of a recount.  A tie between candidates for the most votes in the final round must be decided as provided in section 732.
>
> **§723-A(4)(A)** The number of allowable rankings may be limited to no fewer than 5.
>
> **§371(5)**, and in the same words for a withdrawn candidate **§371(6)** and **§374-A(3)(C)**: In an election determined by ranked-choice voting, a ranking for a candidate who has died or become disqualified is considered a ranking only for the purpose of determining whether the ballot is exhausted under section 723-A.  A candidate who has died or been disqualified cannot be determined the winner.
>
> **§696(2)(E)** If a voter writes in a write-in space the name of a person who has not filed a declaration of write-in candidacy as provided by section 722-A, the vote for that office may not be counted.
>
> **§732** When there is an apparent tie vote, the Secretary of State shall automatically initiate a recount.  If a recount confirms a tie vote, the following provisions apply.  1. In a primary election, the Secretary of State shall notify each person involved in the tie to be present at the Secretary of State's office at a certain time.  At that time, the Secretary of State shall select the nominee publicly by lot.  2. In any other election, the Governor shall issue a proclamation under section 366 declaring the tie and ordering a special election between the persons tied.  ...  B. This subsection does not apply to the election of the following offices which are governed by the Constitution of the State of Maine or the Constitution of the United States: United States Senator, Representative to Congress, Governor and members of the Legislature.
>
> **29-250 C.M.R. ch. 535 §4(2)(B)** (1) Overvote.  An overvote occurs when a voter marks more than one candidate for the same ranking (i.e., in the same ranking column).  An overvote invalidates the overvoted rankings and all subsequent rankings marked for that contest on the ballot.  (2) Single skipped ranking.  A single skipped ranking occurs when a voter does not mark (i.e., skips or leaves blank) a ranking but marks the subsequent ranking for a candidate.  The single skipped ranking is ignored, and the subsequent ranking is counted in the current round, as long as that ranking is for a continuing candidate.  ...  (3) Two consecutive skipped rankings.  When a voter does not mark (i.e., skips or leaves blank) two or more consecutive rankings, then the ballot is deemed exhausted for that contest, and no subsequent candidate rankings marked on that ballot are counted.  (4) Duplicate ranking for the same candidate.  ...  If a voter marks a duplicate ranking for one candidate but also ranks other candidates, and if the candidate with the duplicate ranking is defeated, then the vote for the next continuing candidate ranked by that voter will be counted in the next round.  (5) No ranking for a continuing candidate.  In any round, if a voter has not ranked any continuing candidate, the ballot is deemed exhausted for that contest, and no subsequent candidate rankings marked on that ballot are counted.

The module compiles in the rule identifier below and prints it on the second line of every report, under the conventions of the Oakland module's identifier: a change of a governing text requires a new module with a new identifier, and a change of a reading that the review records raises the revision.

```
maine-723a revision 1, 21-A M.R.S. sections 1, 371, 374-A, 696, 722-A, 723-A, and 732 as current through 2026-10-01 (section 723-A as amended by PL 2025 c. 363, effective 2025-09-24), 29-250 C.M.R. ch. 535 (effective 2018-11-07), texts read 2026-11-10
```

## The canonical ballot file

The module reads the canonical ballot file of [the Oakland requirements](../requirements.md#the-canonical-ballot-file) without change: its lines, grammar, contest structure, limits, and error report, with the error report's second line naming this module's rule.  The kinds keep their words and their counted set `K`, the candidates of kinds `listed` and `named-writein`.  The converter assigns the kinds from the records, the Secretary of State's lists of declared write-in candidates, and its notices of withdrawal, death, and disqualification, and these facts lie outside the theorems.  A ballot line holds one ballot card that carries the contest, so the ballots of the file are the "ballots cast for the particular office" of §723-A(2).

| Kind word | Candidate in Maine | Counted |
|---|---|---|
| `listed` | A candidate printed on the ballot | Yes |
| `named-writein` | A declared write-in candidate of §1(11-A), who filed under §722-A, and whom the records name | Yes |
| `aggregate-writein` | The write-ins of the records that do not name the person written in.  The kind fits only when the aggregate holds no vote for a declared write-in candidate, since §696(2)(E) forbids counting the others, and records that combine such votes with others must be adjudicated before conversion | No |
| `excluded` | An excluded candidate of §723-A(1)(C-1): a listed or declared write-in candidate who died, was disqualified, or withdrew less than 70 days before the election | No |

## Interpretation of a ballot

A position is empty, single, or multiple as in the Oakland requirements, and a position that is not empty is marked.  The interpretation of a ballot against the continuing set `C ⊆ K` examines its positions from the first, by these rules in order:

1. An empty position ends the examination when the next position is also empty and some later position is marked: the ballot is inactive with the reason `exhausted`, by §723-A(1)(D) and (K) and §4(2)(B)(3) of the rules.
2. Any other empty position passes to the next position, by §4(2)(B)(2).
3. A multiple position ends the examination: the ballot is inactive with the reason `overvote`, by §723-A(1)(H) and §4(2)(B)(1).
4. A single position for a candidate in `C` ends the examination: the ballot counts for that candidate.
5. A single position for any other candidate passes to the next position.  The candidate is a counted candidate eliminated in an earlier round, from whom §723-A(2) and §4(2)(A) and (B)(4) pass the ballot on, or an uncounted candidate: an excluded candidate, whose ranking §723-A(2-A) passes, or the aggregate write-in, whose rankings §696(2)(E) forbids counting.

When the examination passes the last position, the ballot is inactive with one of the reasons `blank`, `uncounted`, or `exhausted`, under the conditions of the Oakland requirements, which the ballot and the candidates' kinds determine.  The table gives each reason with the statute's term and the category of the Secretary of State's reports, which publish a single count of inactive ballots in every round.

| Reason | Condition | §723-A(1) | Secretary of State's category |
|---|---|---|---|
| `blank` | Every position is empty | Exhausted ballot: ranks no continuing candidate | Exhausted Ballots |
| `uncounted` | Some position is single, every single position marks an uncounted candidate, and the examination passes the last position | Exhausted ballot: ranks no continuing candidate | Exhausted Ballots |
| `exhausted` | Rule 1 ends the examination, or the examination passes the last position and some single position marks a counted candidate | Exhausted ballot: skipped rankings, or no continuing candidate ranked | Exhausted Ballots |
| `overvote` | The examination reaches a multiple position | Exhausted ballot: an overvote | Exhausted Ballots |

The reasons cover every inactive ballot, and the Secretary of State's category is their sum.  A ranking of an uncounted candidate is a marked position, so it ends a run of empty positions under rule 1 and makes a position multiple when another mark shares it, as §371(5) and (6) and §374-A(3)(C) require of an excluded candidate's ranking.  The module reads §696(2)(E) and §723-A(1)(K) in the same way for a write-in, since a voter who writes a name has not left the ranking blank.  The Secretary of State's 2024 count passes no write-in ranking as an empty position, while its RCV FAQ says that undeclared write-ins "will be recorded as blanks", so that the ballot `W,,A`, with `W` an undeclared write-in, would be exhausted under the FAQ and counts for `A` here, as [the review](review.md#readings-of-the-governing-texts) records.  Rule 1 looks beyond the run only for a marked position, so trailing empty positions end no examination, and a skipped ranking in the sense of §723-A(1)(K) always has a ranking after it.  A ballot that ranks one candidate at several positions needs no rule of its own: while the candidate continues, the first such position counts for it, and after its elimination rule 5 passes each of its rankings, which gives the results of §4(2)(B)(4).  The examination declares an overvote at a multiple position whether or not the marked candidates continue, which is the reading of §4(2)(B)(1), the only reading that records without the marked candidates' names support.

The interpretation depends on the ballot, the kinds, and `C` alone, and it counts a ballot only for a member of `C`.  It has the stability that T8 states.  Rules 1 and 3 end the examination at a position whatever the continuing set, and rules 2 and 5 pass a position against `S′ ⊆ S` whenever they pass it against `S`.  A ballot that counts for `w` against `S` therefore counts for `w` against `S′` whenever `w ∈ S′`, and a ballot inactive against `S` reaches the same ending against `S′` with the same reason.

## The initial test and the rounds

**Initial test.**  Let `N` be the number of ballots and, for `i ∈ K`, let `f(i)` be the number of ballots whose first position is single and marks `i`.  If some `i ∈ K` has 2 `f(i)` > `N`, the count ends with `i` as the winner and no rounds, by §723-A(2).  At most one candidate meets the test.  Ballots whose first position is empty, multiple, or single for an uncounted candidate count in `N` and for no candidate, as the statute's list of included ballots states.  An excluded candidate cannot win the test, since it lies outside `K`, by §371(5) and (6) and §374-A(3)(C).  When an excluded candidate is ranked first alone on more than half of the ballots, no candidate of `K` meets the test and the count proceeds in rounds, although the statute's condition for rounds speaks of any candidate.

**Rounds.**  Otherwise the count proceeds in rounds from `C₁ = K`.  In round `r` every ballot is interpreted against `Cᵣ`, the votes `vᵣ(i)` of `i ∈ Cᵣ` are the number of ballots that count for it, the continuing ballots `Tᵣ` are the sum of the votes, and the inactive ballots are counted by reason, as in the Oakland requirements.  The first rule that applies ends the round:

1. **Two or fewer.**  If `Cᵣ` has two candidates with equal votes, the round eliminates the one that comes later in the tie-break order, as the drawing by lot of §732(1) and §4(2)(B)(6), and the report marks the tie.  Otherwise, if `Cᵣ` has at most two candidates, the count ends, by §723-A(2)(A): with no winner when `Cᵣ` is empty, with its candidate when it has one, and with the candidate of more votes when it has two.
2. **Last place.**  Otherwise let `Z` be the candidates of `Cᵣ` with the fewest votes.  If `Z` has one candidate, the round eliminates it, by §723-A(1)(F) and (2)(B).  If `Z` has two or more, the round eliminates the candidate of `Z` that comes latest in the tie-break order, as the drawing by lot of §723-A(3), and the report marks the tie.

The next round has `Cᵣ₊₁ = Cᵣ` minus the eliminated candidate.  The rules read the votes of the current round, the continuing set, and the tie-break order, and no earlier round, and they form a decision of type `Tally → Decision`, since a round's votes list its continuing set.  The tie-break order encodes the recorded result of each drawing, which §723-A(3) requires to be "recorded and reused in the event of a recount", and T9 shows which ties it decided.  PL 2019 c. 320 struck the provision that let election officials "resolve prospective ties between candidates before the election", so a tie is drawn when it arises.  Officials draw lots for the earliest marked tie that no drawing decided, rerun with an order that encodes the drawings so far, and repeat until a drawing made for each marked tie decided it, since a later tie can depend on an earlier drawing, and T9 keeps the rounds up to each drawn tie the same across the reruns.  After a tied final pair, the next round has one candidate, who holds every continuing ballot of that round and is named by rule 1 of the rounds.  The order's choice is the drawing of §732(1) only in a primary, after the recount that §732 requires, and for a general election §732(2) provides no drawing, so the mark tells the reader that the module's winner rests on the order alone.

Every round that does not end the count eliminates one candidate, so a count with rounds has at most the larger of 1 and the size of `K` rounds.  A round with no continuing ballot ends the count only when it has at most two candidates: the statute provides no other end, so with three or more candidates all tie at zero votes, the order eliminates one per round, and the final pair ties at zero, which the order also decides.  The count therefore names a winner exactly when `K` is not empty, and the report marks every tie that the order decided.  The count has no majority stop and no batch: §723-A(2) proceeds until at most two candidates continue, and PL 2023 c. 304 repealed the batch elimination of §723-A(1)(A) and (G).

## The report

The report has the form of [the Oakland report](../requirements.md#the-report), printed by the same printer, with one addition and two of the three forms of elimination.  After the header lines and before round 1, the report holds the line `first i f(i)` for each candidate `i` of `K` in increasing index.  When the initial test elects `w`, the line `winner w` follows these lines and the report holds no round.  The rounds use the eliminations `eliminate lowest i` and, for a tie at the fewest votes or in the final pair, `tie j₁ … jₘ` followed by `eliminate order i`, and no round prints `eliminate batch`.  The format line stays `rcv-report 1`: the rule line names the module, and the `first` lines are a line form that Oakland's reports never hold.

The ballot file below exercises every reason, rule 1 of the interpretation after an elimination, the passing of an excluded candidate and of a write-in as rankings, a tie at the fewest votes, and a tied final pair.  Its report without the first two lines follows it.  Ballot 4 counts for `A` because the write-in at its first position leaves a single empty position before `A`, and ballot 6 is inactive from round 1 because positions 2 and 3 are empty and position 4 is marked.  Ballot 16 counts for `C` in round 1 and becomes inactive by rule 1 of the interpretation in round 2, and the order `1 2 3 4 5` decides the ties of rounds 1 and 2.

```
rcv-ballots 1
contest example-maine
positions 4
candidates 5
candidate 1 listed A
candidate 2 listed B
candidate 3 listed C
candidate 4 excluded D
candidate 5 aggregate-writein Write-in
order 1 2 3 4 5
ballots 17
id-01,1,2,,
1,1,1,1
,,1,
5,,1,
4,,2,
4,,,2
,3,,
1|2,3,,
*,1,,
5,,,
4,,,
,,,
2,,,
2,1,,
3,1,,
3,,,1
2,3,,
```

```
contest example-maine
positions 4
candidates 5
candidate 1 listed A
candidate 2 listed B
candidate 3 listed C
candidate 4 excluded D
candidate 5 aggregate-writein Write-in
order 1 2 3 4 5
ballots 17
first 1 2
first 2 3
first 3 2
round 1
continuing 10
votes 1 3
votes 2 4
votes 3 3
inactive blank 1
inactive uncounted 2
inactive overvote 2
inactive exhausted 2
tie 1 3
eliminate order 3
round 2
continuing 8
votes 1 4
votes 2 4
inactive blank 1
inactive uncounted 2
inactive overvote 2
inactive exhausted 4
tie 1 2
eliminate order 2
round 3
continuing 5
votes 1 5
inactive blank 1
inactive uncounted 2
inactive overvote 2
inactive exhausted 7
winner 1
```

A contest of three listed candidates, two positions, the order `1 2 3`, and the five ballots `1,2`, `1,`, `1,3`, `,1`, and `2,3` ends by the initial test.  `A` is ranked first alone on three of the five ballots, and the report after its header lines is `first 1 3`, `first 2 1`, `first 3 0`, and `winner 1`.  The fourth ballot counts for no one in the test, although round 1 would count it for `A`.

The Republican primary of June 9, 2026 for State Representative, District 58, has 1,407 ballots in the Secretary of State's five cast vote record spreadsheets.  Converted with the candidates in the order of the Secretary of State's summary report, `Bridges, Dexter E., Jr.`, `Bessey, Lawrence E.`, and `Harris, Jeffrey S.`, all `listed`, and the order `1 2 3`, its report after the header lines is the one below.  Its votes equal the summary report's, and the summary report's Exhausted Ballots, 174 and 379, equal the sums of the four reasons.

```
first 1 461
first 2 459
first 3 310
round 1
continuing 1233
votes 1 462
votes 2 459
votes 3 312
inactive blank 173
inactive uncounted 0
inactive overvote 0
inactive exhausted 1
eliminate lowest 3
round 2
continuing 1028
votes 1 540
votes 2 488
inactive blank 173
inactive uncounted 0
inactive overvote 0
inactive exhausted 206
winner 1
```

## Word forms of the count

The contest's words are those of the Oakland requirements, which the shared reader's result determines.  An array that is not a valid contest gives `[0]`.  For a valid contest the result is 1, the number `R` of rounds, the `n` words `f(1)` to `f(n)`, with 0 for a candidate outside `K`, the `n` + 9 words of each round in the Oakland layout, and the winner's index or 0 for no winner, 3 + `n` + `R`(`n` + 9) words in all.  `R` is 0 exactly when the initial test elects.  A round's elimination word is 0 in the last round, 1 for a lowest elimination, and 2 for an elimination by order, whose tied set is the round's last word, and it is never 3.

## Theorems

The theorems hold for every input, with the premises that each states, and depend on no axiom beyond `propext`, `Classical.choice`, and `Quot.sound`.  The count is the count of these requirements, and the terms continuing set, votes, `Tᵣ`, `f`, interpretation, tie-break order, and the reasons are those of the sections above.  The single count is the count of the Oakland requirements without its rule 3, with this module's interpretation: it eliminates the candidate with the fewest votes, by the order on a tie, until a candidate holds more than half of `Tᵣ` or `Tᵣ` is 0.  The table states which of the Oakland theorems carry over unchanged, which carry over with this module's interpretation or count in place of Oakland's, and which differ.

| Theorem | Maine | Statement |
|---|---|---|
| T1 Bytes | With this module | The statement of the Oakland requirements, for this module's export and its word forms |
| T2 Reader | Unchanged | The reader and the writer are the shared ones |
| T3 Winner | Differs | (a) The count names a winner exactly when `K` is not empty.  (b) A winner of the initial test is ranked first alone on more than half of the `N` ballots, and when the last round has a continuing ballot, the winner holds more than half of them.  (c) A last round other than round 1 has a single continuing candidate exactly when the round before it had two continuing candidates with equal votes, and the report then marks that round's elimination as a tie.  (d) The count has no rounds exactly when the initial test elects, and otherwise at most the larger of 1 and the size of `K` rounds |
| T4 Elimination | Differs | In every round that eliminates, either `Cᵣ` has three or more candidates and the elimination is (a) a lowest elimination of the candidate that alone has the fewest votes or (b) an elimination by order of the member latest in the order of the two or more candidates with the fewest votes, which form the tied set, or `Cᵣ` has two candidates with equal votes, which form the tied set, and the elimination is by order of the one later in the order.  The last round eliminates no one, has at most two candidates, and names the one of more votes, the one alone, or no one when `Cᵣ` is empty |
| T5 Conservation | Unchanged | In every round the votes and the inactive counts sum to `N`, and `continuing` is the sum of the votes |
| T6 Locality | With this interpretation | The statement of the Oakland requirements, and each `f(i)` is the number of ballots whose first position is single and marks `i` |
| T7 Invariance | Unchanged | Two well-formed files that differ by a permutation of their ballot lines or in their identifier fields have the same report |
| T8 Stability | With this interpretation | The statement of the Oakland requirements, for the interpretation of these requirements |
| T9 Order | Unchanged | The statement of the Oakland requirements, for this count |
| T10 Batch | With this interpretation | The Oakland theorem, which holds for every interpretation that counts a ballot against `S` only for a member of `S` and satisfies both statements of T8, applies to this interpretation.  The count has no batch, and no comparison of this module rests on T10 |
| T11 Majority holder | Differs | (a) If `w` holds a majority of the continuing ballots against `S`, it holds a majority against every `S′` with `w ∈ S′ ⊆ S`.  (b) A candidate that holds more than half of `Tᵣ` in some round of the count continues in every later round, and the count names it.  (c) If the initial test elects `w`, then `w` holds more than half of `T₁` in round 1 of the count without the initial test, and that count names `w`.  (d) If the single count names `w`, the count names `w` |
| T12 Majority criterion | Differs | If more than half of the ballots rank a candidate `w` of `K` first alone, the count ends by the initial test with `w` and no rounds.  If more than half of the continuing ballots of round 1 of the count without the initial test count for `w`, the count names `w` |
| T13 Condorcet loser | With this interpretation and count | If `K` has two or more candidates and every other candidate of `K` beats `ℓ`, where `a` beats `b` when more ballots count for `a` than for `b` against `{a, b}`, the count does not name `ℓ` |
| T14 Later-no-harm | With this interpretation and count | The statement of the Oakland requirements.  While `w` continues, rule 1 reads no position after the first position that marks `w` alone, since that position is marked |
| T15 Monotonicity fails | With this count | The contests of the Oakland requirements, whose counts under these rules name `A` and `B`, with the same rounds and the added `first` lines |

T11(c) states that the initial test of PL 2025 c. 363 changes no winner and only shortens the count, and T11(d) relates the count to a tabulation that stops at a majority of the continuing ballots, as RCTab does without its setting `continueUntilTwoCandidatesRemain`.  T13 follows from locality: the final pair `{x, ℓ}` is counted against `{x, ℓ}`, where `x` has more votes than `ℓ`, and the initial test cannot elect `ℓ`, since the ballots that rank `ℓ` first alone count for `ℓ` against every pair that holds it.

## What lies outside the theorems

| Item | Status |
|---|---|
| The converter | Turns the Secretary of State's spreadsheets into the canonical file without proof.  The round trip and the comparison with the summary reports make it checkable |
| Kinds of candidates | Whether a write-in candidate filed a declaration under §722-A and whether a candidate became excluded are facts about filings and notices, which the converter takes as inputs |
| The tie-break order | The theorems hold for every order.  Whether the order came from a drawing by lot, and when, is outside them, and T9 shows which ties the order decided |
| The records | Whether the spreadsheets agree with the paper ballots and with the records that the Secretary of State tabulated is a matter of audit.  [The review](review.md#facts-behind-the-requirements) records differences between the posted spreadsheets and the official rounds |
| The transcription | Whether these requirements and the specification state the governing texts correctly is a matter of review, which [the review](review.md) records |
| The page, the reference, and the scripts | As in the Oakland requirements |
| Legal force | The official count is the Secretary of State's, so the module serves as an audit tool |

## Trusted base

The theorems about the module rest on the items of [the trusted base](../../../docs/trusted-base.md) that the Oakland module's theorems rest on, for WebAssembly modules, WASI Preview 1 processes, and C files.  The specification's definitions are trusted to state these requirements, and a review checks them against the requirements before a program depends on them.  The shared definitions, the reader, the writer, the tally, and the printer, carry the reviews of the Oakland module, and this module's review covers the interpretation, the initial test, the rounds, and the report's addition.

## Comparison with the Secretary of State's reports

The Secretary of State's RCV summary report gives each round's votes for every continuing candidate and one cumulative figure of inactive ballots, Exhausted Ballots in 2026 and Ballots Exhausted in 2024, which the 2024 report defines as undervotes, overvotes, and ballots exhausted after an elimination.  The rules of the reports are the module's, one elimination per round and an end at two candidates, so the module's round `r` is the report's round `r`.  The comparison tests every round: the votes of every continuing candidate must be equal, the report's inactive figure must equal the sum of the four reasons, and the eliminated candidates and the winner must be the same.  A tie that the module marks is compared after a rerun with an order that encodes the Secretary of State's recorded drawing, and a tied final pair of a general election has no official drawing to compare with.

The rules base the official initial test on the first choices of the municipal returns, under §4(1) and (2)(A), and the Secretary of State's 2024 first-choice file holds the municipalities' figures.  Its 2026 files, titled "RCV Central Count first choice votes", have the records' totals, and for State Senate District 4 and House District 58 the records' first rankings.  The module computes `f` from the records, and the comparison tests whether the module's test and the published figures give the same outcome, and reports the differences of the figures.  A contest that the initial test decides has no ranked-choice count, and in 2026 the Secretary of State posted no cast vote record for such a contest, so the module cannot count it.  The 2024 contest was counted under the statute before PL 2025 c. 363, which had no initial test of its own and no excluded candidate.  The contest has no excluded candidate and the module's initial test elects no one in it, so its rounds compare with the report's, and T11(c) shows that the initial test changes no winner in any contest.

## Tests

**Python reference.**  A Maine mode of `tests/rcv/reference.py`, written from these requirements alone by an agent that has not read the Lean specification, prints the report and the word forms, sharing the reference's reader and writer.  It is compared byte for byte with native Lean, the module, the WASI process, and C on every test input.

**Edge cases.**  The edge cases add to the shared files of `tests/rcv/edges.py`: every pattern of empty and marked positions for `k` up to 4, with runs of empty positions at the start, between marks, at the end, before a multiple position, and before a mark of an uncounted candidate; a write-in mark and an excluded candidate's mark that end a run; rule 1 reached only after an elimination; duplicate rankings with and without other candidates; multiple positions named and unnamed; the initial test at 2 `f(i)` = `N` and `N` + 1, with blank, multiple, and uncounted first positions in `N`, and with an excluded candidate first alone on more than half of the ballots; a tie at the fewest votes among three or more candidates; a tied final pair, with and without continuing ballots; three or more candidates without a continuing ballot; no ballots; no counted candidate, one, and two; 63 candidates and 63 positions; and the contests of T15.  Each file's expected report comes from the reference, and a reviewer checks the reports of the smallest files by hand.

**Corpus.**  [The Maine corpus manifest](../../../tests/rcv/maine/manifest.json) pins by URL, size, and SHA-256 the Secretary of State's summary reports, first-choice results, and cast vote record spreadsheets of the five contests that the Secretary of State counted in rounds after the June 9, 2026 primaries, the 2024 general election for Representative to Congress, District 2, and the first-choice results of the two 2026 contests that the initial test decided.  `tests/rcv/maine/fetch.py` verifies the files, and `tests/rcv/maine/recount.py` counts each contest by these requirements and compares it with the summary report.  The recount equals every figure of the State Senate District 4 and House District 58 primaries and of the 2024 contest.  In the Democratic primaries for Governor and for Representative to Congress, District 2, and the Republican primary for Governor, it gives every elimination and winner of the report and each figure within 21 votes.  In every round, the report's figures minus the recount of the other spreadsheets are nonnegative, sum to the rows of the contest's third manual-entry spreadsheet, and do not decrease from round to round for any continuing candidate or for the inactive ballots, so the differences can lie in that spreadsheet's ballots alone, as [the review](review.md#facts-behind-the-requirements) records.  The corpus has no tie, no excluded candidate, and no contest decided by the initial test with records, so the edge cases supply them.

**Converter.**  `tests/rcv/maine/convert.py` writes the canonical file of a contest of the manifest from its spreadsheets, read in the manifest's order with Python's zip and XML modules.  The candidates are the summary report's in the report's order, of kind `listed`, followed by an aggregate write-in when a spreadsheet ranks `Write-in`, by `named-writein` candidates for declared write-ins whom adjudicated records name, and by `excluded` candidates that the command names from the Secretary of State's notices.  A ranking cell `undervote` or a missing cell gives an empty field, `overvote` gives `*`, a candidate's name with its surrounding spaces removed gives its index, and `Write-in` gives the aggregate's index.  Each line's identifier is the spreadsheet's manifest label, a colon, and its Cast Vote Record number without a trailing `.0`, such as `export-1:15876`, the contest identifier is the manifest key with `/` replaced by `:`, and the order is the command's or 1 to `n`.  The Cast Vote Record numbers repeat across spreadsheets, and a few repeat within the uniformed-service and overseas spreadsheets, so identifiers need not be unique.  The converter refuses, with a message and exit status 1, a ranking that names no candidate, spreadsheets whose ranking columns differ, more than 63 candidates or positions, and a name outside the file's alphabet.  The 2024 contest's write-ins include those of a declared write-in candidate, so the converter writes them as `aggregate-writein` only on a command that names the comparison with the Secretary of State's practice, which [the review](review.md#departures-of-official-practice) records.

## Plan

The module's increments follow the Oakland module's practice: each reaches bytes and theorems, and each theorem is tested on a model built from these requirements before its proof.  The Lean files are in `Demos/Rcv/Maine/`, and the converter, the corpus, and the reference's Maine mode are in `tests/rcv/`.

| Increment | Work | Done when |
|---|---|---|
| M1 | These requirements and the review.  The specification: the interpretation, the initial test, the decision of a round as `Tally → Decision` over the shared `run`, the report's `first` lines, and the word forms.  The reference's Maine mode, the edge cases, the converter, and the corpus in canonical files.  T4 to T9 for this count | A fresh agent has checked the specification against these requirements.  The specification and the reference agree byte for byte on every edge case and corpus file, and the corpus's reports agree with the Secretary of State's as the corpus paragraph states |
| M2 | The program over arrays, its refinement, `verified_compile`, and the call theorem over words.  The export over bytes with T1, using the shared reader and printer.  T3, T8, T10 for this interpretation, and T11 | The theorems hold with the allowed axioms.  The module and native Lean agree with the reference on every edge case and corpus file |
| M3 | The WASI process, the C translation, the module's choice on the browser page, T12 to T15 for this count, and RCTab configurations of the corpus's contests | The module, the WASI process, C, and native Lean agree byte for byte.  RCTab's rounds agree with the module's, or each difference is explained in the review |

## References

- [21-A M.R.S. §723-A, Maine Revisor of Statutes](https://legislature.maine.gov/statutes/21-A/title21-Asec723-A.html)
- [21-A M.R.S. §1](https://legislature.maine.gov/statutes/21-A/title21-Asec1.html)
- [21-A M.R.S. §371](https://legislature.maine.gov/statutes/21-A/title21-Asec371.html)
- [21-A M.R.S. §374-A](https://legislature.maine.gov/statutes/21-A/title21-Asec374-A.html)
- [21-A M.R.S. §696](https://legislature.maine.gov/statutes/21-A/title21-Asec696.html)
- [21-A M.R.S. §722-A](https://legislature.maine.gov/statutes/21-A/title21-Asec722-A.html)
- [21-A M.R.S. §732](https://legislature.maine.gov/statutes/21-A/title21-Asec732.html)
- [Maine Revised Statutes, currency statement](https://legislature.maine.gov/statutes/)
- [PL 2025 c. 363, LD 911, chaptered law](https://legislature.maine.gov/legis/bills/getPDF.asp?paper=SP0401&item=5&snum=132)
- [LD 911, status, 132nd Legislature](https://legislature.maine.gov/legis/bills/display_ps.asp?LD=911&snum=132)
- [PL 2019 c. 320, Law and Legislative Digital Library](https://lldc.mainelegislature.org/Open/Laws/2019/2019_PL_c320.pdf)
- [PL 2023 c. 628, chaptered law](https://legislature.maine.gov/legis/bills/getPDF.asp?paper=HP1023&item=4&snum=131)
- [Digest of laws enacted in the First Regular and First Special Sessions of the 132nd Legislature](https://legislature.maine.gov/doc/11927)
- [29-250 C.M.R. ch. 535, Department of the Secretary of State](https://www.maine.gov/sos/sites/maine.gov.sos/files/inline-files/250c535-2018-230%20ACK.docx)
- [Department of the Secretary of State, rules](https://www.maine.gov/sos/rulemaking/agency-rules/department-secretary-state-rules)
- [29-250 C.M.R. ch. 535 §4, Cornell LII](https://www.law.cornell.edu/regulations/maine/29-250-C-M-R-ch-535-SS-4)
- [Maine Secretary of State, election results](https://www.maine.gov/sos/elections-voting/election-results-data)
- [Maine Secretary of State, election results 2024](https://www.maine.gov/sos/elections-voting/election-results-data/election-results-2024)
- [The Maine corpus manifest](../../../tests/rcv/maine/manifest.json)
- [Oakland ranked-choice tabulator requirements](../requirements.md)
- [RCTab configuration documentation, v2.1.0](https://github.com/BrightSpots/rcv/blob/v2.1.0/config_file_documentation.txt)
- [Trusted base](../../../docs/trusted-base.md)
