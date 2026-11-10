/-!
The contest structure of [the requirements](requirements.md), section "The contest structure": the
reader's result, which the count, the report, and the word forms read.  Identifiers and names are
lists of bytes, and each position of a ballot is its 64-bit word: 0 for no mark, `2 ^ (i - 1)` for
each candidate `i` that the position marks, and `2 ^ 63` for an overvote whose candidates the
records do not name.  `Contest.WellFormed` states the constraints that a structure meets.
-/

namespace Demos.Rcv

/-- The kind of a candidate, which decides whether the count counts rankings of the candidate. -/
inductive Kind where
  /-- A candidate printed on the ballot.  Counted. -/
  | listed
  /-- A write-in candidate who complied with Part 3 of Division 8 and whom the records name.
  Counted. -/
  | namedWritein
  /-- The write-ins of the records that do not name the person written in.  Not counted. -/
  | aggregateWritein
  /-- A person named in the records who did not comply with Part 3 of Division 8.  Not
  counted. -/
  | excluded
  deriving DecidableEq, Repr

structure Candidate where
  kind : Kind
  name : List UInt8
  deriving DecidableEq, Repr

/-- A ballot line: its identifier, if the line has one, and its position words in position
order. -/
structure Ballot where
  ident : Option (List UInt8)
  positions : List UInt64
  deriving DecidableEq, Repr

/-- The fields of the requirements' table.  Candidate `i` is the `i`-th element of `candidates`,
counted from 1, so `n` is `candidates.length` and `N` is `ballots.length`.  `positions` is `k`, and
`order` is the tie-break order, earliest first. -/
structure Contest where
  contest : List UInt8
  positions : Nat
  candidates : List Candidate
  order : List Nat
  ballots : List Ballot
  deriving DecidableEq, Repr

/-- The largest number of candidates and of positions. -/
def maxIndex : Nat := 63

/-- The largest number of ballots. -/
def maxBallots : Nat := 2 ^ 32 - 1

/-- The word of an overvote whose candidates the records do not name. -/
def unnamedOvervote : UInt64 := UInt64.ofNat ((2 : Nat) ^ 63)

/-- Whether a byte belongs to the identifiers' alphabet: `A`–`Z`, `a`–`z`, `0`–`9`, `-`, `_`,
`.`, and `:`. -/
def identByte (b : UInt8) : Bool :=
  ((0x41 : UInt8) ≤ b && b ≤ (0x5A : UInt8)) || ((0x61 : UInt8) ≤ b && b ≤ (0x7A : UInt8)) ||
    ((0x30 : UInt8) ≤ b && b ≤ (0x39 : UInt8)) || b == (0x2D : UInt8) || b == (0x5F : UInt8) ||
    b == (0x2E : UInt8) || b == (0x3A : UInt8)

/-- Whether bytes form an identifier: 1 to 64 bytes of the identifiers' alphabet. -/
def identOk (bs : List UInt8) : Bool :=
  1 ≤ bs.length && bs.length ≤ 64 && bs.all identByte

/-- Whether bytes form a name: 1 to 255 bytes, each from `0x20` to `0x7E` or from `0x80` to
`0xFF`. -/
def nameOk (bs : List UInt8) : Bool :=
  1 ≤ bs.length && bs.length ≤ 255 &&
    bs.all fun b : UInt8 => ((0x20 : UInt8) ≤ b && b ≤ (0x7E : UInt8)) || (0x80 : UInt8) ≤ b

/-- Whether `w` is a position word of a contest with `n` candidates: 0, `2 ^ 63`, or a nonzero sum
of distinct powers `2 ^ (i - 1)` with `1 ≤ i ≤ n`.  The nonzero sums of distinct powers from `2 ^ 0`
to `2 ^ (n - 1)` are the numbers from 1 to `2 ^ n - 1`. -/
abbrev ValidWord (n : Nat) (w : UInt64) : Prop :=
  w = (0 : UInt64) ∨ w = unnamedOvervote ∨ (0 < w.toNat ∧ w.toNat < (2 : Nat) ^ n)

/-- The constraints of a contest structure: `k`, `n`, and `N` in the header's ranges, the
identifiers and names with their alphabets and lengths, an order that is a permutation of 1 to `n`,
and `k` valid position words on each ballot. -/
abbrev Contest.WellFormed (c : Contest) : Prop :=
  1 ≤ c.positions ∧ c.positions ≤ maxIndex ∧
  1 ≤ c.candidates.length ∧ c.candidates.length ≤ maxIndex ∧
  c.ballots.length ≤ maxBallots ∧
  identOk c.contest = true ∧
  (∀ x ∈ c.candidates, nameOk x.name = true) ∧
  c.order.Perm (List.range' 1 c.candidates.length) ∧
  ∀ b ∈ c.ballots, b.ident.all identOk = true ∧ b.positions.length = c.positions ∧
    ∀ w ∈ b.positions, ValidWord c.candidates.length w

end Demos.Rcv
