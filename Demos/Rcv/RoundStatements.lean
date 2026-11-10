import Demos.Rcv.Native

/-!
Native tests of the statements of T4, T5, T6, T7, and T9 of `Demos/Rcv/Rounds.lean`, which ran
before their proofs.  Each `ok` function decides one theorem's conclusion on a contest through the
specification, and `hypT9` decides T9's hypothesis for an order.  The run covers the well-formed
edge-case files that `tests/rcv/edges.py` writes and seeded random contests of every kind of
candidate and position, and it prints the counts of contests, rounds, eliminations by kind, and
failures.  The `fault` functions are false variants of the statements, which the run must reject on
some contests, and `t9noHypDiffer` counts the orders that fail T9's hypothesis and change the count.
The module reads files at elaboration, so no library imports it.  From the repository root:

```sh
uv run tests/rcv/edges.py
tools/leanrun --timeout 20m lake build rcv-spec
tools/leanrun --timeout 50m lake env lean Demos/Rcv/RoundStatements.lean
```
-/

open Demos.Rcv Demos.Rcv.Spec

namespace Demos.Rcv.RoundStatements

def setOf (rd : Round) : List Nat := rd.tally.votes.map fun x : Nat × Nat => x.1

def fewestOf (votes : List (Nat × Nat)) : List Nat :=
  (votes.filter fun x : Nat × Nat => votes.all fun y : Nat × Nat => decide (x.2 ≤ y.2)).map
    fun x : Nat × Nat => x.1

def noLargeSet (t : Tally) : Bool :=
  t.votes.all fun y : Nat × Nat => !qualifies t.votes y || decide ((lower t.votes y.2).length < 2)

/-- T4 for the elimination `e` of a round with the counts `t`. -/
def eliminates (order : List Nat) (t : Tally) (e : Elimination) : Bool :=
  decide (0 < t.continuing) && t.votes.all (fun x : Nat × Nat => decide (2 * x.2 ≤ t.continuing)) &&
    match e with
    | .batch s =>
      decide (2 ≤ s.length) &&
        t.votes.any (fun x : Nat × Nat =>
          qualifies t.votes x && s == (lower t.votes x.2).map fun y : Nat × Nat => y.1) &&
        t.votes.all fun y : Nat × Nat =>
          !qualifies t.votes y || (lower t.votes y.2).all fun z : Nat × Nat => decide (z.1 ∈ s)
    | .lowest z => noLargeSet t && fewestOf t.votes == [z]
    | .order Z i =>
      noLargeSet t && decide (2 ≤ (fewestOf t.votes).length) && decide (i ∈ fewestOf t.votes) &&
        Z == fewestOf t.votes &&
        Z.all fun j : Nat => decide (j ∈ order) && decide (order.idxOf j ≤ order.idxOf i)

def okT4 (c : Contest) : Bool :=
  let k := countContest c
  (k.rounds.all fun rd : Round => match rd.elimination with
    | some e => eliminates c.order rd.tally e
    | none => true) &&
  match k.rounds.getLast? with
  | some last =>
    last.elimination == none &&
      ((last.tally.votes.any fun x : Nat × Nat =>
          decide (last.tally.continuing < 2 * x.2) && k.winner == some x.1) ||
        (last.tally.continuing == 0 && k.winner == none))
  | none => false

def okT5 (c : Contest) : Bool :=
  (countContest c).rounds.all fun rd : Round =>
    (rd.tally.votes.map fun x : Nat × Nat => x.2).sum + rd.tally.blank + rd.tally.uncounted +
        rd.tally.overvote + rd.tally.exhausted == c.ballots.length &&
      rd.tally.continuing == (rd.tally.votes.map fun x : Nat × Nat => x.2).sum

def okT6 (c : Contest) : Bool :=
  let k := countContest c
  let ballots := c.ballots.map fun b : Ballot => b.positions
  let interp := interpret (kindsOf c)
  let n := k.rounds.length
  (match k.rounds.head? with
    | some rd => setOf rd == countedSet (kindsOf c)
    | none => false) &&
  ((List.range n).all fun r : Nat =>
    let rd := k.rounds.getD r ⟨⟨[], 0, 0, 0, 0⟩, none⟩
    let C := setOf rd
    rd.tally.votes == C.map (fun i : Nat => (i, ballots.countP fun ps => interp C ps == .counts i)) &&
      rd.tally.blank == ballots.countP (fun ps => interp C ps == .inactive .blank) &&
      rd.tally.uncounted == ballots.countP (fun ps => interp C ps == .inactive .uncounted) &&
      rd.tally.overvote == ballots.countP (fun ps => interp C ps == .inactive .overvote) &&
      rd.tally.exhausted == ballots.countP (fun ps => interp C ps == .inactive .exhausted)) &&
  ((List.range (n - 1)).all fun r : Nat =>
    let rd := k.rounds.getD r ⟨⟨[], 0, 0, 0, 0⟩, none⟩
    let rd' := k.rounds.getD (r + 1) ⟨⟨[], 0, 0, 0, 0⟩, none⟩
    match rd.elimination with
    | some e => setOf rd' == (setOf rd).filter fun i : Nat => decide (i ∉ e.eliminated)
    | none => false)

/-! ## Random numbers -/

structure Gen where
  s : UInt64

def Gen.next (g : Gen) : Nat × Gen :=
  let s := g.s * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat, ⟨s⟩)

def Gen.below (g : Gen) (m : Nat) : Nat × Gen :=
  let (x, g) := g.next
  (if m = 0 then 0 else x % m, g)

def Gen.shuffle (g : Gen) (xs : List α) : List α × Gen := Id.run do
  let mut g := g
  let mut a := xs.toArray
  for i in (List.range a.size).reverse do
    let (j, g') := g.below (i + 1)
    g := g'
    a := a.swapIfInBounds i j
  return (a.toList, g)

def Gen.word (g : Gen) (n : Nat) : UInt64 × Gen :=
  let (r, g) := g.below 100
  if r < 35 then (0, g)
  else if r < 85 then
    let (i, g) := g.below n
    ((2 : Nat) ^ i |>.toUInt64, g)
  else if r < 95 then
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
  let mut ballots : List Ballot := []
  for _ in List.range nb do
    let mut ps : List UInt64 := []
    for _ in List.range k do
      let (w, g') := g.word n
      g := g'
      ps := ps ++ [w]
    let (r, g') := g.below 3
    g := g'
    let ident : Option (List UInt8) := if r = 0 then some (ascii ("b" ++ toString ballots.length)) else none
    ballots := ballots ++ [{ ident, positions := ps }]
  let c : Contest :=
    { contest := ascii "random"
      positions := k
      candidates := kinds.map (fun x : Kind => { kind := x, name := ascii "C" })
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
  return (countContest c' == countContest c && report c' == report c, g)

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

/-! ## Seeded faults -/

/-- T6 with the next continuing set equal to the current one. -/
def faultT6 (c : Contest) : Bool :=
  let k := countContest c
  (List.range (k.rounds.length - 1)).all fun r : Nat =>
    setOf (k.rounds.getD (r + 1) ⟨⟨[], 0, 0, 0, 0⟩, none⟩) ==
      setOf (k.rounds.getD r ⟨⟨[], 0, 0, 0, 0⟩, none⟩)

/-- T4 with the earliest member of the tied set in the order. -/
def faultT4 (c : Contest) : Bool :=
  (countContest c).rounds.all fun rd : Round => match rd.elimination with
    | some (.order Z i) => Z.all fun j : Nat => decide (c.order.idxOf i ≤ c.order.idxOf j)
    | _ => true

/-- T4 with the smallest qualifying set of two or more. -/
def faultT4b (c : Contest) : Bool :=
  (countContest c).rounds.all fun rd : Round => match rd.elimination with
    | some (.batch s) =>
      let t := rd.tally
      t.votes.all fun y : Nat × Nat =>
        !qualifies t.votes y || (lower t.votes y.2).length < 2 || s.length ≤ (lower t.votes y.2).length
    | _ => true

/-- T5 with the continuing ballots counted twice. -/
def faultT5 (c : Contest) : Bool :=
  (countContest c).rounds.all fun rd : Round =>
    2 * rd.tally.continuing + rd.tally.blank + rd.tally.uncounted + rd.tally.overvote +
      rd.tally.exhausted == c.ballots.length

structure Tallies where
  contests : Nat := 0
  wellFormed : Nat := 0
  rounds : Nat := 0
  batches : Nat := 0
  lowest : Nat := 0
  orderElims : Nat := 0
  noWinner : Nat := 0
  fail4 : Nat := 0
  fail5 : Nat := 0
  fail6 : Nat := 0
  fail7 : Nat := 0
  t9orders : Nat := 0
  t9hyp : Nat := 0
  t9hypTied : Nat := 0
  t9hypChanged : Nat := 0
  fail9 : Nat := 0
  t9noHypDiffer : Nat := 0
  fault4 : Nat := 0
  fault4b : Nat := 0
  fault5 : Nat := 0
  fault6 : Nat := 0
  deriving Repr

def record (s : Tallies) (c : Contest) (g : Gen) (orders : Nat) : Tallies × Gen := Id.run do
  let k := countContest c
  let mut s := { s with
    contests := s.contests + 1
    wellFormed := s.wellFormed + (if decide c.WellFormed then 1 else 0)
    rounds := s.rounds + k.rounds.length
    batches := s.batches + k.rounds.countP (fun rd => match rd.elimination with
      | some (.batch _) => true | _ => false)
    lowest := s.lowest + k.rounds.countP (fun rd => match rd.elimination with
      | some (.lowest _) => true | _ => false)
    orderElims := s.orderElims + ties c
    noWinner := s.noWinner + (if k.winner.isNone then 1 else 0)
    fail4 := s.fail4 + (if okT4 c then 0 else 1)
    fail5 := s.fail5 + (if okT5 c then 0 else 1)
    fail6 := s.fail6 + (if okT6 c then 0 else 1)
    fault4 := s.fault4 + (if faultT4 c then 0 else 1)
    fault4b := s.fault4b + (if faultT4b c then 0 else 1)
    fault5 := s.fault5 + (if faultT5 c then 0 else 1)
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
      t9hypTied := s.t9hypTied + (if h && ties c > 0 then 1 else 0)
      t9hypChanged := s.t9hypChanged + (if h && ties c > 0 && π' != c.order then 1 else 0)
      fail9 := s.fail9 + (if h && !conclT9 c π' then 1 else 0)
      t9noHypDiffer := s.t9noHypDiffer +
        (if !h && countContest { c with order := π' } != k then 1 else 0) }
  return (s, g)

def runEdges (dir : System.FilePath) : IO Tallies := do
  let mut s : Tallies := {}
  let mut g : Gen := ⟨7⟩
  let entries ← dir.readDir
  let files := (entries.map (·.path)).filter (·.extension == some "rcv")
  let mut rejected := 0
  for p in files.qsort (fun a b => a.toString < b.toString) do
    match ← (Demos.Rcv.Native.load p.toString).toBaseIO with
    | .error _ => rejected := rejected + 1
    | .ok c =>
      let orders := if c.candidates.length ≤ 8 then 6 else 2
      let (s', g') := record s c g orders
      s := s'
      g := g'
  IO.println s!"edge files: {files.size}, rejected by load: {rejected}"
  return s

def runRandom (count maxN maxK maxBallots : Nat) (seed : UInt64) : Tallies := Id.run do
  let mut s : Tallies := {}
  let mut g : Gen := ⟨seed⟩
  for _ in List.range count do
    let (c, g') := g.contest maxN maxK maxBallots
    let (s', g'') := record s c g' 4
    s := s'
    g := g''
  return s

end Demos.Rcv.RoundStatements

open Demos.Rcv.RoundStatements in
#eval show IO Unit from do
  let s ← runEdges "tmp/rcv-edges"
  IO.println (repr s)
  IO.println (repr (runRandom 4000 5 4 12 1))
  IO.println (repr (runRandom 4000 6 4 30 2))
  IO.println (repr (runRandom 2000 8 5 60 3))
