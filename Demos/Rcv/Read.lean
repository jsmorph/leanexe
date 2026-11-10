import Demos.Rcv.Spec

/-!
The reader of the canonical ballot file that [the requirements](requirements.md) state in the
sections "The canonical ballot file" and "Malformed files and the error report".  `read` returns
the contest structure of a well-formed file, or the number and the role of the first line that is
absent, lacks its LF, or fails its role, and `reportFile` gives the bytes of the report of a file:
the error report for a malformed file, and `report` of the structure otherwise.

The file's lines are the pieces of `List.splitOn` at LF: line `j` is piece `j - 1`, and it ends
with LF exactly when another piece follows it, so the last piece is the bytes after the last LF.
`read` takes the lines in order, each with the role that the header gives it, and stops at the
first line that is absent or lacks its LF, which `takeLine` reports, or that fails its role, which
`readLine` reports.  The roles' forms follow the grammar: `number` is `"0" / %x31-39 *DIGIT`,
`parseCandidate` splits `number SP kind SP name` at the first two spaces, since neither a number nor
a kind holds a space, `parseOrder` and `parsePosition` split their numbers at the spaces and at `|`,
and `parseBallot` splits a ballot line at its commas and takes an identifier first exactly when it
finds `k + 1` fields.  The constraints of the requirements' tables follow each form: the ranges of
`k`, `n`, and `N`, the index of each candidate line, the permutation of the order, and the bounds
and the increasing order of the indices of a field.

After the last ballot line the rest of the file must be the empty piece after the final LF, which
gives the error of role `end` at line `7 + n + N` to a further line and to a final run of bytes
without LF.  Numbers are natural numbers, so a number of any length reads as its value, and the
ranges reject the large ones.
-/

namespace Demos.Rcv.Spec

open Demos.Rcv

/-! ## Roles and the reader's result -/

/-- The role of a line, which the header determines. -/
inductive Role where
  | format
  | contest
  | positions
  | candidates
  | candidate
  | order
  | ballots
  | ballot
  | «end»
  deriving DecidableEq, Repr

/-- The name of a role, as the error report prints it. -/
def Role.word : Role → String
  | .format => "format"
  | .contest => "contest"
  | .positions => "positions"
  | .candidates => "candidates"
  | .candidate => "candidate"
  | .order => "order"
  | .ballots => "ballots"
  | .ballot => "ballot"
  | .end => "end"

/-- The reader's result: the contest structure of a well-formed file, or the number and the role of
the first line that is absent, lacks its LF, or fails its role. -/
inductive Reading where
  | ok (c : Contest)
  | error (line : Nat) (role : Role)
  deriving DecidableEq, Repr

/-! ## Forms within a line -/

def lf : UInt8 := 0x0A

def sp : UInt8 := 0x20

def comma : UInt8 := 0x2C

def bar : UInt8 := 0x7C

/-- Whether a byte is a decimal digit, `0` to `9`. -/
def isDigit (x : UInt8) : Bool := (0x30 : UInt8) ≤ x && x ≤ (0x39 : UInt8)

/-- The value of decimal digits, most significant first. -/
def digitsValue (bs : List UInt8) : Nat :=
  bs.foldl (fun (v : Nat) (x : UInt8) => 10 * v + (x.toNat - 0x30)) 0

/-- `number = "0" / %x31-39 *DIGIT`: the value of the bytes `bs` when they have this form. -/
def number (bs : List UInt8) : Option Nat :=
  match bs with
  | [] => none
  | d :: ds =>
    if bs.all isDigit && (d != (0x30 : UInt8) || ds.isEmpty) then some (digitsValue bs) else none

/-- The bytes of `bs` after the prefix `p`, when `bs` starts with `p`. -/
def after (p bs : List UInt8) : Option (List UInt8) :=
  if p.isPrefixOf bs then some (bs.drop p.length) else none

/-- The number after the prefix `p`, when it lies in `[lo, hi]`. -/
def parseBounded (p : String) (lo hi : Nat) (l : List UInt8) : Option Nat :=
  match after (ascii p) l with
  | some rest =>
    match number rest with
    | some v => if lo ≤ v ∧ v ≤ hi then some v else none
    | none => none
  | none => none

/-- Line 1: `rcv-ballots 1`. -/
def parseFormat (l : List UInt8) : Option Unit :=
  if l = ascii "rcv-ballots 1" then some () else none

/-- Line 2: `contest ` and an identifier. -/
def parseContest (l : List UInt8) : Option (List UInt8) :=
  match after (ascii "contest ") l with
  | some id => if identOk id then some id else none
  | none => none

/-- The kind of a kind word. -/
def parseKind (bs : List UInt8) : Option Kind :=
  if bs = ascii "listed" then some .listed
  else if bs = ascii "named-writein" then some .namedWritein
  else if bs = ascii "aggregate-writein" then some .aggregateWritein
  else if bs = ascii "excluded" then some .excluded
  else none

/-- The line of candidate `i`: `candidate `, the index `i`, a space, a kind word, a space, and a
name.  The index and the kind word hold no space, so the first two spaces after `candidate `
delimit them, and the name is the rest of the line. -/
def parseCandidate (i : Nat) (l : List UInt8) : Option Candidate :=
  match after (ascii "candidate ") l with
  | some rest =>
    match rest.span (· != sp) with
    | (index, _ :: rest) =>
      match rest.span (· != sp) with
      | (word, _ :: name) =>
        if number index = some i ∧ nameOk name = true then
          (parseKind word).map fun k : Kind => { kind := k, name }
        else none
      | (_, []) => none
    | (_, []) => none
  | none => none

/-- The order line of a contest with `n` candidates: `order`, then a space and an index for each
candidate, the indices a permutation of 1 to `n`. -/
def parseOrder (n : Nat) (l : List UInt8) : Option (List Nat) :=
  match after (ascii "order ") l with
  | some rest =>
    match (rest.splitOn sp).mapM number with
    | some is => if is.Perm (List.range' 1 n) then some is else none
    | none => none
  | none => none

/-- Whether a list of numbers is strictly increasing. -/
def increasing : List Nat → Bool
  | a :: b :: rest => decide (a < b) && increasing (b :: rest)
  | _ => true

/-- The word of a position field of a contest with `n` candidates: 0 for the empty field, `2 ^ 63`
for `*`, and for the indices `i₁ | … | iₘ`, each from 1 to `n` and in increasing order, the sum of
`2 ^ (iⱼ - 1)`. -/
def parsePosition (n : Nat) (f : List UInt8) : Option UInt64 :=
  if f = [] then some 0
  else if f = ascii "*" then some unnamedOvervote
  else
    match (f.splitOn bar).mapM number with
    | some is =>
      if (is.all fun i : Nat => 1 ≤ i && i ≤ n) && increasing is then
        some (UInt64.ofNat (is.map fun i : Nat => (2 : Nat) ^ (i - 1)).sum)
      else none
    | none => none

/-- A ballot line of a contest with `k` positions and `n` candidates: `k` position fields, or an
identifier and `k` position fields, separated by commas. -/
def parseBallot (k n : Nat) (l : List UInt8) : Option Ballot :=
  match l.splitOn comma with
  | [] => none
  | first :: rest =>
    if (first :: rest).length = k then
      ((first :: rest).mapM (parsePosition n)).map fun ws : List UInt64 =>
        { ident := none, positions := ws }
    else if rest.length = k ∧ identOk first = true then
      (rest.mapM (parsePosition n)).map fun ws : List UInt64 =>
        { ident := some first, positions := ws }
    else none

/-! ## Lines in order -/

/-- The result of reading a part of the file: its value and the lines after it, or the number and
the role of the first line that is absent, lacks its LF, or fails its role. -/
abbrev Step (α : Type) := Except (Nat × Role) (α × List (List UInt8))

/-- Line `j`, of role `r`, from the pieces `ps` whose first is line `j`: the line, when another
piece follows it, and the pieces after it.  Otherwise line `j` is absent, as the empty last piece
after a final LF, or lacks its LF, as a nonempty last piece. -/
def takeLine (j : Nat) (r : Role) : List (List UInt8) → Step (List UInt8)
  | l :: p :: ps => .ok (l, p :: ps)
  | _ => .error (j, r)

/-- Line `j`, of role `r`, read by `parse`: its value, or the error of line `j` when the line is
absent, lacks its LF, or fails the form. -/
def readLine {α : Type} (j : Nat) (r : Role) (parse : List UInt8 → Option α)
    (ps : List (List UInt8)) : Step α :=
  match takeLine j r ps with
  | .ok (l, rest) =>
    match parse l with
    | some a => .ok (a, rest)
    | none => .error (j, r)
  | .error e => .error e

/-- The candidate lines `i` to `i + count - 1` of a contest, lines `4 + i` on, in order. -/
def readCandidates : Nat → Nat → List (List UInt8) → Step (List Candidate)
  | _, 0, ps => .ok ([], ps)
  | i, count + 1, ps =>
    match readLine (4 + i) .candidate (parseCandidate i) ps with
    | .ok (x, rest) =>
      match readCandidates (i + 1) count rest with
      | .ok (xs, rest) => .ok (x :: xs, rest)
      | .error e => .error e
    | .error e => .error e

/-- The `count` ballot lines from line `j` on of a contest with `k` positions and `n` candidates,
with the ballots `acc` of the lines before them, latest first.  The accumulator keeps the native
evaluation of a file of many ballots from deep recursion. -/
def readBallots (k n : Nat) : Nat → Nat → List Ballot → List (List UInt8) → Step (List Ballot)
  | _, 0, acc, ps => .ok (acc.reverse, ps)
  | j, count + 1, acc, ps =>
    match readLine j .ballot (parseBallot k n) ps with
    | .ok (x, rest) => readBallots k n (j + 1) count (x :: acc) rest
    | .error e => .error e

/-- The contest structure of the lines `ps` of a file, or the number and the role of the first line
that is absent, lacks its LF, or fails its role.  `n` and `N` come from lines 4 and `6 + n`, which
give the roles of the lines after them, and the pieces after the last ballot line must be the empty
piece after the final LF alone. -/
def readLines (ps : List (List UInt8)) : Except (Nat × Role) Contest := do
  let ((), ps) ← readLine 1 .format parseFormat ps
  let (contest, ps) ← readLine 2 .contest parseContest ps
  let (k, ps) ← readLine 3 .positions (parseBounded "positions " 1 maxIndex) ps
  let (n, ps) ← readLine 4 .candidates (parseBounded "candidates " 1 maxIndex) ps
  let (candidates, ps) ← readCandidates 1 n ps
  let (order, ps) ← readLine (5 + n) .order (parseOrder n) ps
  let (N, ps) ← readLine (6 + n) .ballots (parseBounded "ballots " 0 maxBallots) ps
  let (ballots, ps) ← readBallots k n (7 + n) N [] ps
  if ps = [[]] then pure { contest, positions := k, candidates, order, ballots }
  else throw (7 + n + N, .end)

/-- The reader: the contest structure of the file `b`, or the number and the role of its first
faulty line. -/
def read (b : List UInt8) : Reading :=
  match readLines (b.splitOn lf) with
  | .ok c => .ok c
  | .error (j, r) => .error j r

/-! ## The error rule by line number

The requirements' error rule names lines by number, and these definitions state it by number,
independently of the order in which `read` takes the lines.  T2(c) states that `read` reports the
smallest line number `j ≥ 1` that `faulty` finds, with the role that `roleAt` gives it.  Line
numbers start at 1, and `faulty b 0` holds for every `b`, so the statement excludes 0. -/

/-- Line `j` of `b`, counted from 1, without its LF: piece `j - 1` of the split at LF, when a piece
follows it, so that the line ends with LF.  Otherwise line `j` is absent or lacks its LF. -/
def lineOf (b : List UInt8) (j : Nat) : Option (List UInt8) :=
  if 1 ≤ j ∧ j < (b.splitOn lf).length then (b.splitOn lf)[j - 1]? else none

/-- `k`, `n`, and `N` of the header of `b`: the numbers of lines 3, 4, and `6 + n`, or 0 for a line
that is absent, lacks its LF, or fails its role. -/
def headerK (b : List UInt8) : Nat :=
  ((lineOf b 3).bind (parseBounded "positions " 1 maxIndex)).getD 0

def headerN (b : List UInt8) : Nat :=
  ((lineOf b 4).bind (parseBounded "candidates " 1 maxIndex)).getD 0

def headerBallots (b : List UInt8) : Nat :=
  ((lineOf b (6 + headerN b)).bind (parseBounded "ballots " 0 maxBallots)).getD 0

/-- The role of line `j` in a file with `n` candidates and `N` ballots. -/
def roleOf (n N j : Nat) : Role :=
  if j = 1 then .format
  else if j = 2 then .contest
  else if j = 3 then .positions
  else if j = 4 then .candidates
  else if j ≤ 4 + n then .candidate
  else if j = 5 + n then .order
  else if j = 6 + n then .ballots
  else if j ≤ 6 + n + N then .ballot
  else .end

/-- The role of line `j` of `b`, from its header. -/
def roleAt (b : List UInt8) (j : Nat) : Role := roleOf (headerN b) (headerBallots b) j

/-- Whether the line `l` has the form of the role `r` of line `j`, with `k` and `n` from the
header.  No line meets the role `end`. -/
def meets (k n j : Nat) (r : Role) (l : List UInt8) : Bool :=
  match r with
  | .format => (parseFormat l).isSome
  | .contest => (parseContest l).isSome
  | .positions => (parseBounded "positions " 1 maxIndex l).isSome
  | .candidates => (parseBounded "candidates " 1 maxIndex l).isSome
  | .candidate => (parseCandidate (j - 4) l).isSome
  | .order => (parseOrder n l).isSome
  | .ballots => (parseBounded "ballots " 0 maxBallots l).isSome
  | .ballot => (parseBallot k n l).isSome
  | .end => false

/-- Whether line `j` of `b` is absent, lacks its LF, or fails its role.  Line `j` counts as absent
only for `j ≤ 6 + n + N`. -/
def faulty (b : List UInt8) (j : Nat) : Bool :=
  match lineOf b j with
  | some l => !meets (headerK b) (headerN b) j (roleAt b j) l
  | none =>
    decide (j ≤ 6 + headerN b + headerBallots b) ||
      decide (j = (b.splitOn lf).length ∧ (b.splitOn lf).getLast? ≠ some [])

/-! ## The report of a file -/

/-- The error report: the format line, the rule line, and `error`, the line number, and the role.
-/
def errorReport (j : Nat) (r : Role) : List UInt8 :=
  text [ascii "rcv-report 1", spaced [ascii "rule", ascii ruleIdentifier],
    spaced [ascii "error", decimal j, ascii r.word]]

/-- The bytes of the report of the file `b`, which the requirements' T1 calls `report b`: the error
report when `read b` fails, and the report of the count otherwise. -/
def reportFile (b : List UInt8) : List UInt8 :=
  match read b with
  | .ok c => report c
  | .error j r => errorReport j r

end Demos.Rcv.Spec
