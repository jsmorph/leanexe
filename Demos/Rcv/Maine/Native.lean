import Demos.Rcv.Maine.Rounds

/-!
Native runs of the Maine specification on canonical ballot files and word arrays, and native tests
of the statements of T4 to T9 of `Demos/Rcv/Maine/Rounds.lean` and
`Demos/Rcv/Maine/Stability.lean`, which ran before their proofs.  Word arrays are packed as the
reference packs them: little-endian 64-bit words.

`rcv-maine report FILE` writes `reportFile` of the file, `words FILE` the result words of
`countWords` on the file's contest words, and `array FILE` those of `countArray` on a packed word
array.  `compare FILE…` compares the report of each canonical file `X.rcv` with the reference's
report `X.report` beside it, and `compare-words FILE…` the result words of each word array `X.words`
with `X.result`.  Each prints the number of files and of differences, with status 1 when one
differs.

`check FILE…` decides the conclusions of T4 to T9 on the contest of each well-formed canonical
file, and `random SEED COUNT MAXN MAXK MAXB` on seeded random contests of up to `MAXN` candidates of
every kind, `MAXK` positions, and `MAXB` ballots.  T7 compares each contest with a shuffle of its
ballots whose identifiers change, and T9 tries random orders.  `pairs` decides both statements of
T8 for every ballot of up to four positions over the fields empty, each of five candidates of every
kind, a named overvote, and the unnamed one, against every pair `S' ⊆ S` of subsets of the five
candidates.  Each mode prints its counts, with the rejections of false variants of the statements,
and exits with status 1 when a statement fails.
-/

namespace Demos.Rcv.Maine.Native

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Rounds Demos.Rcv.Maine

instance (order : List Nat) (t : Tally) (e : Elimination) : Decidable (Eliminates order t e) := by
  unfold Eliminates
  infer_instance

instance (t : Tally) (w : Option Nat) : Decidable (Concludes t w) := by
  unfold Concludes
  infer_instance

def readBytes (path : String) : IO (List UInt8) := do
  return (← IO.FS.readBinFile path).toList

def writeBytes (bs : List UInt8) : IO Unit := do
  (← IO.getStdout).write ⟨bs.toArray⟩

def unpack (bs : ByteArray) : List UInt64 :=
  (List.range (bs.size / 8)).map fun j : Nat =>
    (List.range 8).foldr
      (fun (b : Nat) (acc : UInt64) => (acc <<< 8) ||| (bs.get! (8 * j + b)).toUInt64) 0

def pack (ws : List UInt64) : ByteArray :=
  ws.foldl (fun (acc : ByteArray) (w : UInt64) =>
    (List.range 8).foldl (fun (acc : ByteArray) (j : Nat) =>
      acc.push (w >>> (8 * j).toUInt64).toUInt8) acc) ByteArray.empty

def withExt (path ext : String) : String :=
  ((System.FilePath.mk path).withExtension ext).toString

def compare (paths : List String) : IO UInt32 := do
  let mut good : Nat := 0
  let mut differ : Nat := 0
  for path in paths do
    let b ← readBytes path
    if let .ok _ := read b then good := good + 1
    if reportFile b != (← readBytes (withExt path "report")) then
      differ := differ + 1
      IO.println s!"{path}: the report differs from the reference's"
  IO.println s!"{paths.length} files, {good} well formed, {differ} differ"
  return if differ == 0 then 0 else 1

def compareWords (paths : List String) : IO UInt32 := do
  let mut differ : Nat := 0
  for path in paths do
    let ws := unpack (← IO.FS.readBinFile path)
    let want := unpack (← IO.FS.readBinFile (withExt path "result"))
    if countWords ws != want then
      differ := differ + 1
      IO.println s!"{path}: the result words differ from the reference's"
  IO.println s!"{paths.length} word arrays, {differ} differ"
  return if differ == 0 then 0 else 1

/-! ## The statements -/

def okT4 (c : Contest) : Bool :=
  let k := countContest c
  (k.rounds.all fun rd : Round => match rd.elimination with
    | some e => decide (Eliminates c.order rd.tally e)
    | none => true) &&
  match k.rounds.getLast? with
  | some last => last.elimination == none && decide (Concludes last.tally k.winner)
  | none => true

def okT5 (c : Contest) : Bool :=
  (countContest c).rounds.all fun rd : Round =>
    (rd.tally.votes.map fun x : Nat × Nat => x.2).sum + rd.tally.blank + rd.tally.uncounted +
        rd.tally.overvote + rd.tally.exhausted == c.ballots.length &&
      rd.tally.continuing == (rd.tally.votes.map fun x : Nat × Nat => x.2).sum

def emptyRound : Round := ⟨⟨[], 0, 0, 0, 0⟩, none⟩

def okT6 (c : Contest) : Bool :=
  let k := countContest c
  let ballots := positionsOf c
  let interp := interpret (kindsOf c)
  let n := k.rounds.length
  (match k.rounds.head? with
    | some rd => continuingSet rd == countedSet (kindsOf c)
    | none => true) &&
  ((List.range n).all fun r : Nat =>
    let rd := k.rounds.getD r emptyRound
    let C := continuingSet rd
    rd.tally.votes ==
        C.map (fun i : Nat => (i, ballots.countP fun ps => interp C ps == .counts i)) &&
      rd.tally.blank == ballots.countP (fun ps => interp C ps == .inactive .blank) &&
      rd.tally.uncounted == ballots.countP (fun ps => interp C ps == .inactive .uncounted) &&
      rd.tally.overvote == ballots.countP (fun ps => interp C ps == .inactive .overvote) &&
      rd.tally.exhausted == ballots.countP (fun ps => interp C ps == .inactive .exhausted)) &&
  ((List.range (n - 1)).all fun r : Nat =>
    let rd := k.rounds.getD r emptyRound
    let rd' := k.rounds.getD (r + 1) emptyRound
    match rd.elimination with
    | some e =>
      continuingSet rd' == (continuingSet rd).filter fun i : Nat => decide (i ∉ e.eliminated)
    | none => false) &&
  firstContest c ==
    (countedSet (kindsOf c)).map fun i : Nat => (i, ballots.countP (FirstMarks i))

/-- T8's consequence for consecutive rounds. -/
def okT8 (c : Contest) : Bool :=
  let rds := (countContest c).rounds
  (List.range (rds.length - 1)).all fun r : Nat =>
    let a := rds.getD r emptyRound
    let b := rds.getD (r + 1) emptyRound
    decide (a.tally.blank ≤ b.tally.blank) && decide (a.tally.uncounted ≤ b.tally.uncounted) &&
      decide (a.tally.overvote ≤ b.tally.overvote) &&
      decide (a.tally.exhausted ≤ b.tally.exhausted) &&
      (a.tally.votes.all fun x : Nat × Nat => b.tally.votes.all fun y : Nat × Nat =>
        x.1 != y.1 || decide (x.2 ≤ y.2)) &&
      decide (b.tally.continuing ≤ a.tally.continuing)

/-! ## Random numbers -/

structure Gen where
  s : UInt64

def Gen.next (g : Gen) : Nat × Gen :=
  let s := g.s * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat, ⟨s⟩)

def Gen.below (g : Gen) (m : Nat) : Nat × Gen :=
  let (x, g) := g.next
  (if m = 0 then 0 else x % m, g)

def Gen.shuffle {α : Type} (g : Gen) (xs : List α) : List α × Gen := Id.run do
  let mut g := g
  let mut a := xs.toArray
  for i in (List.range a.size).reverse do
    let (j, g') := g.below (i + 1)
    g := g'
    a := a.swapIfInBounds i j
  return (a.toList, g)

/-- A random position word of a contest of `n` candidates: empty more often than in the Oakland
tests, so that runs of empty positions arise. -/
def Gen.word (g : Gen) (n : Nat) : UInt64 × Gen :=
  let (r, g) := g.below 100
  if r < 45 then (0, g)
  else if r < 92 then
    let (i, g) := g.below n
    ((2 : Nat) ^ i |>.toUInt64, g)
  else if r < 97 then
    let (i, g) := g.below n
    let (j, g) := g.below n
    (((2 : Nat) ^ i ||| (2 : Nat) ^ j).toUInt64, g)
  else (unnamedOvervote, g)

def Gen.kind (g : Gen) : Kind × Gen :=
  let (r, g) := g.below 10
  (if r < 7 then .listed else if r < 8 then .namedWritein else if r < 9 then .aggregateWritein
    else .excluded, g)

def Gen.contest (g : Gen) (maxN maxK maxBallots : Nat) : Contest × Gen := Id.run do
  let mut g := g
  let (n0, g1) := g.below maxN
  g := g1
  let n := n0 + 1
  let (k0, g2) := g.below maxK
  g := g2
  let k := k0 + 1
  let (nb, g3) := g.below (maxBallots + 1)
  g := g3
  let mut kinds : List Kind := []
  for _ in List.range n do
    let (x, g') := g.kind
    g := g'
    kinds := kinds ++ [x]
  let (order, g4) := g.shuffle (List.range' 1 n)
  g := g4
  -- A third of the contests lean toward one candidate first, so that the initial test elects.
  let (lean, g5) := g.below 3
  g := g5
  let (fav, g6) := g.below n
  g := g6
  let mut ballots : List Ballot := []
  for _ in List.range nb do
    let mut ps : List UInt64 := []
    for j in List.range k do
      let (w, g') := g.word n
      let (r, g'') := g'.below 10
      g := g''
      ps := ps ++ [if lean = 0 && j = 0 && r < 6 then ((2 : Nat) ^ fav).toUInt64 else w]
    let (r, g') := g.below 3
    g := g'
    let ident : Option (List UInt8) :=
      if r = 0 then some (ascii ("b" ++ toString ballots.length)) else none
    ballots := ballots ++ [{ ident, positions := ps }]
  let c : Contest :=
    { contest := ascii "random"
      positions := k
      candidates := (kinds.zipIdx 1).map fun p : Kind × Nat =>
        { kind := p.1, name := ascii s!"C{p.2}" }
      order
      ballots }
  return (c, g)

/-! ## T7 and T9 -/

def okT7 (c : Contest) (g : Gen) : Bool × Gen := Id.run do
  let (bs, g) := g.shuffle c.ballots
  let mut g := g
  let mut bs' : List Ballot := []
  for b in bs do
    let (r, g') := g.below 3
    g := g'
    let ident := if r = 0 then none else if r = 1 then b.ident else some (ascii "changed")
    bs' := bs' ++ [{ b with ident }]
  let c' := { c with ballots := bs' }
  return (countContest c' == countContest c && firstContest c' == firstContest c &&
    report c' == report c, g)

def orderLine (π : List Nat) : List UInt8 := spaced (ascii "order" :: π.map decimal)

def hypT9 (c : Contest) (π' : List Nat) : Bool :=
  (countContest c).rounds.all fun rd : Round => match rd.elimination with
    | some (.order Z i) => Z.all fun j : Nat => decide (π'.idxOf j ≤ π'.idxOf i)
    | _ => true

def conclT9 (c : Contest) (π' : List Nat) : Bool :=
  let c' := { c with order := π' }
  let L := reportLines c
  let L' := reportLines c'
  let m := 5 + c.candidates.length
  countContest c' == countContest c && L.length == L'.length && L.take m == L'.take m &&
    L.drop (m + 1) == L'.drop (m + 1) && L.getD m [] == orderLine c.order &&
    L'.getD m [] == orderLine π'

def ties (c : Contest) : Nat :=
  (countContest c).rounds.countP fun rd : Round => match rd.elimination with
    | some (.order _ _) => true
    | _ => false

/-! ## False variants -/

/-- T4 with the earliest member of the tied set in the order. -/
def faultT4 (c : Contest) : Bool :=
  (countContest c).rounds.all fun rd : Round => match rd.elimination with
    | some (.order Z i) => Z.all fun j : Nat => decide (c.order.idxOf i ≤ c.order.idxOf j)
    | _ => true

/-- T4 with a last round in which the winner holds more than half of the continuing ballots, which
a count without a counted candidate or with a tied final pair at zero votes contradicts. -/
def faultT4b (c : Contest) : Bool :=
  let k := countContest c
  match k.rounds.getLast? with
  | some last =>
    last.tally.votes.any fun x : Nat × Nat =>
      decide (last.tally.continuing < 2 * x.2) && k.winner == some x.1
  | none => true

/-- T6 with `f(i)` counting a first position that marks `i` among others. -/
def faultT6 (c : Contest) : Bool :=
  firstContest c == (countedSet (kindsOf c)).map fun i : Nat =>
    (i, (positionsOf c).countP fun ps : List UInt64 =>
      match ps with
      | w :: _ => decide (i ∈ marks w)
      | [] => false)

structure Tallies where
  contests : Nat := 0
  wellFormed : Nat := 0
  initial : Nat := 0
  rounds : Nat := 0
  lowest : Nat := 0
  orderElims : Nat := 0
  tiedPairs : Nat := 0
  noWinner : Nat := 0
  fail4 : Nat := 0
  fail5 : Nat := 0
  fail6 : Nat := 0
  fail7 : Nat := 0
  fail8 : Nat := 0
  t9orders : Nat := 0
  t9hyp : Nat := 0
  t9hypTied : Nat := 0
  fail9 : Nat := 0
  t9noHypDiffer : Nat := 0
  fault4 : Nat := 0
  fault4b : Nat := 0
  fault6 : Nat := 0
  deriving Repr

def record (s : Tallies) (c : Contest) (g : Gen) (orders : Nat) : Tallies × Gen := Id.run do
  let k := countContest c
  let mut s := { s with
    contests := s.contests + 1
    wellFormed := s.wellFormed + (if decide c.WellFormed then 1 else 0)
    initial := s.initial + (if k.rounds.isEmpty then 1 else 0)
    rounds := s.rounds + k.rounds.length
    lowest := s.lowest + k.rounds.countP (fun rd => match rd.elimination with
      | some (.lowest _) => true | _ => false)
    orderElims := s.orderElims + ties c
    tiedPairs := s.tiedPairs + k.rounds.countP (fun rd => match rd.elimination with
      | some (.order _ _) => rd.tally.votes.length == 2 | _ => false)
    noWinner := s.noWinner + (if k.winner.isNone then 1 else 0)
    fail4 := s.fail4 + (if okT4 c then 0 else 1)
    fail5 := s.fail5 + (if okT5 c then 0 else 1)
    fail6 := s.fail6 + (if okT6 c then 0 else 1)
    fail8 := s.fail8 + (if okT8 c then 0 else 1)
    fault4 := s.fault4 + (if faultT4 c then 0 else 1)
    fault4b := s.fault4b + (if faultT4b c then 0 else 1)
    fault6 := s.fault6 + (if faultT6 c then 0 else 1) }
  let (b7, g') := okT7 c g
  let mut g := g'
  s := { s with fail7 := s.fail7 + (if b7 then 0 else 1) }
  let n := c.candidates.length
  for _ in List.range orders do
    let (π', g') := g.shuffle (List.range' 1 n)
    g := g'
    let h := hypT9 c π'
    s := { s with
      t9orders := s.t9orders + 1
      t9hyp := s.t9hyp + (if h then 1 else 0)
      t9hypTied := s.t9hypTied + (if h && ties c > 0 && π' != c.order then 1 else 0)
      fail9 := s.fail9 + (if h && !conclT9 c π' then 1 else 0)
      t9noHypDiffer := s.t9noHypDiffer +
        (if !h && countContest { c with order := π' } != k then 1 else 0) }
  return (s, g)

def finish (label : String) (s : Tallies) : IO UInt32 := do
  IO.println (s!"{label}: {s.contests} contests, {s.wellFormed} well-formed, " ++
    s!"{s.initial} decided by the initial test, {s.rounds} rounds, " ++
    s!"{s.lowest} lowest eliminations, {s.orderElims} eliminations by order, " ++
    s!"{s.tiedPairs} of them tied pairs, {s.noWinner} counts without a winner")
  IO.println (s!"{label}: T9 orders {s.t9orders}, meeting the hypothesis {s.t9hyp}, " ++
    s!"with a marked tie and another order {s.t9hypTied}, " ++
    s!"failing the hypothesis and changing the count {s.t9noHypDiffer}")
  IO.println (s!"{label}: false variants rejected: T4 with the earliest tied member {s.fault4}, " ++
    s!"T4 with a majority in the last round {s.fault4b}, " ++
    s!"T6 with first positions that mark several candidates {s.fault6}")
  IO.println (s!"{label}: failing: T4 {s.fail4}, T5 {s.fail5}, T6 {s.fail6}, T7 {s.fail7}, " ++
    s!"T8 {s.fail8}, T9 {s.fail9}")
  return if s.fail4 + s.fail5 + s.fail6 + s.fail7 + s.fail8 + s.fail9 == 0 then 0 else 1

def runRandom (count maxN maxK maxBallots : Nat) (seed : UInt64) : Tallies := Id.run do
  let mut s : Tallies := {}
  let mut g : Gen := ⟨seed⟩
  for _ in List.range count do
    let (c, g') := g.contest maxN maxK maxBallots
    let (s', g'') := record s c g' 4
    s := s'
    g := g''
  return s

def check (paths : List String) : IO UInt32 := do
  let mut s : Tallies := {}
  let mut g : Gen := ⟨7⟩
  let mut malformed : Nat := 0
  for path in paths do
    match read (← readBytes path) with
    | .error _ _ => malformed := malformed + 1
    | .ok c =>
      let (s', g') := record s c g (if c.candidates.length ≤ 8 then 6 else 2)
      s := s'
      g := g'
  IO.println s!"files: {paths.length}, malformed: {malformed}"
  finish "files" s

/-! ## T8 on pairs of sets -/

/-- The interpretation with a false reading of the overvote, under which a multiple position that
marks no continuing candidate passes. -/
def faultyInterpret (kinds : List Kind) (C : List Nat) (ps : List UInt64) : Outcome :=
  let rec go : List UInt64 → Option Outcome
    | [] => none
    | w :: ws =>
      match position w with
      | .empty => if skipped ws then some (.inactive .exhausted) else go ws
      | .multiple =>
        if w.toNat.testBit 63 || (marks w).any (fun i : Nat => decide (i ∈ C)) then
          some (.inactive .overvote)
        else go ws
      | .single i => if i ∈ C then some (.counts i) else go ws
  (go ps).getD (.inactive (passedReason kinds ps))

def fields : List UInt64 := [0, 1, 2, 4, 8, 16, 3, unnamedOvervote]

def ballotsUpTo : Nat → List (List UInt64)
  | 0 => []
  | k + 1 => (ballotsUpTo k) ++
    ((List.range (k + 1)).foldl (fun (acc : List (List UInt64)) _ =>
      acc.flatMap fun b => fields.map fun w => w :: b) [[]])

def subsets : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (subsets xs) ++ (subsets xs).map (x :: ·)

/-- Whether `interp` satisfies both statements of T8 for the ballot `ps` and the sets `S' ⊆ S`. -/
def stableOn (interp : List Nat → List UInt64 → Outcome) (S S' : List Nat) (ps : List UInt64) :
    Bool :=
  match interp S ps with
  | .counts w => !(w ∈ S') || interp S' ps == .counts w
  | .inactive r => interp S' ps == .inactive r

def pairs : IO UInt32 := do
  let kinds : List Kind := [.listed, .listed, .namedWritein, .excluded, .aggregateWritein]
  let sets := subsets [1, 2, 3, 4, 5]
  let mut checked : Nat := 0
  let mut failed : Nat := 0
  let mut faultFailed : Nat := 0
  let mut closedFailed : Nat := 0
  for ps in ballotsUpTo 4 do
    for S in sets do
      match interpret kinds S ps with
      | .counts w => if !(w ∈ S) then closedFailed := closedFailed + 1
      | .inactive _ => pure ()
      for S' in sets do
        if S'.all (· ∈ S) then
          checked := checked + 1
          if !stableOn (interpret kinds) S S' ps then failed := failed + 1
          if !stableOn (faultyInterpret kinds) S S' ps then faultFailed := faultFailed + 1
  IO.println (s!"pairs: {(ballotsUpTo 4).length} ballots, {checked} pairs of a ballot and sets " ++
    s!"S' ⊆ S, failing: T8 {failed}, closed {closedFailed}; " ++
    s!"the false reading of the overvote rejected on {faultFailed}")
  return if failed + closedFailed == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["report", path] =>
      writeBytes (reportFile (← readBytes path))
      return 0
    | ["words", path] =>
      match read (← readBytes path) with
      | .ok c =>
        (← IO.getStdout).write (pack (countWords (contestWords c)))
        return 0
      | .error j r =>
        IO.eprintln s!"{path}: line {j} fails the role {r.word}"
        return 1
    | ["array", path] =>
      (← IO.getStdout).write (pack (countWords (unpack (← IO.FS.readBinFile path))))
      return 0
    | "compare" :: paths => compare paths
    | "compare-words" :: paths => compareWords paths
    | "check" :: paths => check paths
    | ["random", seed, n, maxN, maxK, maxB] =>
      finish "random"
        (runRandom n.toNat! maxN.toNat! maxK.toNat! maxB.toNat! seed.toNat!.toUInt64)
    | ["pairs"] => pairs
    | _ =>
      IO.eprintln ("usage: rcv-maine report FILE | words FILE | array FILE | compare FILE... | " ++
        "compare-words FILE... | check FILE... | random SEED COUNT MAXN MAXK MAXB | pairs")
      return 2
  catch e =>
    IO.eprintln s!"{e}"
    return 1

end Demos.Rcv.Maine.Native

def main (args : List String) : IO UInt32 := Demos.Rcv.Maine.Native.main args
