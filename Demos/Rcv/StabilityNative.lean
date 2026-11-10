import Demos.Rcv.Variants
import Std.Data.HashSet

/-!
Native tests of the statements of T3, T8, T10, and T11 of [the requirements](requirements.md), and
the rounds of the single count and the county count for comparison with `tests/rcv/reference.py`.
Each check transcribes a theorem's conclusion as a Boolean function over the specification's
definitions and evaluates it on contests read from contest-word files, on random contests, on an
exhaustive set of small contests, and on random interpretations that satisfy T8.  The planted
checks evaluate statements known to be false, so that a run shows that the checks can fail.

`rcv-stability rounds MODE OUT FILE...` writes, for each contest-word file `NAME.words`, the round
lines and the winner line of the count, the single count, or the county count (`MODE` `charter`,
`single`, or `county`) to `OUT/NAME.MODE`.  `rcv-stability check FILE...` evaluates the statements
on each file's contest, `random SEED COUNT` on random contests, `general SEED COUNT` on random
interpretations that satisfy T8, `exhaustive` on every multiset of up to six ballots of a small
alphabet under two orders, and `planted SEED COUNT` evaluates the planted statements on random
contests.  Each mode prints its counts, and the exit status is 1 if a statement fails.
-/

namespace Demos.Rcv.StabilityNative

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Variants

abbrev Interp := List Nat → List UInt64 → Outcome

deriving instance Inhabited for Tally
deriving instance Inhabited for Round

def setOf (rd : Round) : List Nat := rd.tally.votes.map fun x : Nat × Nat => x.1

def countFrom (interp : Interp) (order : List Nat) (ballots : List (List UInt64)) (C : List Nat) :
    Count := run interp (rule order) ballots (C.length + 1) C

def singleFrom (interp : Interp) (order : List Nat) (ballots : List (List UInt64)) (C : List Nat) :
    Count := run interp (ruleSingle order) ballots (C.length + 1) C

def countyFrom (interp : Interp) (order : List Nat) (ballots : List (List UInt64)) (C : List Nat) :
    Count := run interp (ruleCounty order) ballots (C.length + 1) C

def subsets : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => let r := subsets xs; r.map (x :: ·) ++ r

structure Stats where
  contests : Nat := 0
  rounds : Nat := 0
  t8pairs : Nat := 0
  t8steps : Nat := 0
  batches : Nat := 0
  insideBatch : Nat := 0
  t10cRounds : Nat := 0
  t11aPairs : Nat := 0
  t11bRounds : Nat := 0
  t11cWinners : Nat := 0
  tiedFinal : Nat := 0
  t11dRounds : Nat := 0
  noWinner : Nat := 0
  failures : Nat := 0
  messages : List String := []

def Stats.need (s : Stats) (b : Bool) (msg : String) : Stats :=
  if b then s
  else { s with failures := s.failures + 1,
                messages := if s.messages.length < 20 then msg :: s.messages else s.messages }

def Stats.summary (s : Stats) : String :=
  s!"{s.contests} contests, {s.rounds} rounds, {s.t8pairs} T8 pairs, {s.t8steps} T8 steps, " ++
  s!"{s.batches} batches, {s.insideBatch} single counts ending inside a batch, " ++
  s!"{s.t10cRounds} T10(c) rounds, {s.t11aPairs} T11(a) pairs, {s.t11bRounds} T11(b) rounds, " ++
  s!"{s.t11cWinners} T11(c) winners, {s.tiedFinal} tied final rounds, " ++
  s!"{s.t11dRounds} T11(d) rounds, {s.noWinner} counts without a winner, {s.failures} failing"

/-! ## The statements -/

/-- Both statements of T8 for one ballot and sets `S' ⊆ S`, and that a ballot counts only for a
member of the set. -/
def t8At (interp : Interp) (S S' : List Nat) (ps : List UInt64) : Bool :=
  match interp S ps with
  | .counts w => decide (w ∈ S) && (!decide (w ∈ S') || interp S' ps == .counts w)
  | .inactive r => interp S' ps == .inactive r

/-- T8's consequence for consecutive rounds. -/
def stableStep (a b : Tally) : Bool :=
  a.blank ≤ b.blank && a.uncounted ≤ b.uncounted && a.overvote ≤ b.overvote &&
    a.exhausted ≤ b.exhausted && b.continuing ≤ a.continuing &&
    a.votes.all fun x : Nat × Nat => b.votes.all fun y : Nat × Nat => y.1 != x.1 || x.2 ≤ y.2

def steps (rs : List Round) : List (Round × Round) := rs.zip rs.tail

def holder (interp : Interp) (ballots : List (List UInt64)) (S : List Nat) : Option Nat :=
  let t := tally interp S ballots
  (t.votes.find? fun x : Nat × Nat => t.continuing < 2 * x.2).map fun x : Nat × Nat => x.1

def holds (interp : Interp) (ballots : List (List UInt64)) (S : List Nat) (w : Nat) : Bool :=
  let t := tally interp S ballots
  t.continuing < 2 * (ballots.map (interp S)).count (.counts w)

def lastStrict : Option Round → Option Round → Bool
  | some a, some b => (setOf a).all (· ∈ setOf b) && (setOf b).any (· ∉ setOf a)
  | _, _ => false

def tieOf (prev : Round) : Bool :=
  match prev.tally.votes with
  | [(_, va), (_, vb)] => va == vb
  | _ => false

def checkCounts (name : String) (interp : Interp) (order : List Nat)
    (ballots : List (List UInt64)) (C : List Nat) (smallSets : Bool) (s : Stats) : Stats :=
    Id.run do
  let cnt := countFrom interp order ballots C
  let sgl := singleFrom interp order ballots C
  let cty := countyFrom interp order ballots C
  let mut s := { s with contests := s.contests + 1, rounds := s.rounds + cnt.rounds.length }
  -- T8's consequence
  for (a, b) in steps cnt.rounds ++ steps sgl.rounds ++ steps cty.rounds do
    s := { s.need (stableStep a.tally b.tally) s!"{name}: T8 step" with t8steps := s.t8steps + 1 }
  -- T10
  s := s.need (sgl.winner == cnt.winner) s!"{name}: T10(a)"
  let ct := cnt.rounds.map Round.tally
  let st := sgl.rounds.map Round.tally
  let inside := !(ct.isSublist st)
  s := s.need (ct.isSublist st ||
      (ct.dropLast.isSublist st && sgl.winner == cnt.winner &&
        lastStrict cnt.rounds.getLast? sgl.rounds.getLast?)) s!"{name}: T10(b)"
  if inside then s := { s with insideBatch := s.insideBatch + 1 }
  for rd in cnt.rounds do
    match rd.elimination with
    | some (.batch B) =>
      s := { s with batches := s.batches + 1 }
      for j in List.range sgl.rounds.length do
        if setOf sgl.rounds[j]! == setOf rd then
          for sj in (sgl.rounds.drop j).take B.length do
            s := { s.need (sj.elimination == none || B.any fun b : Nat =>
                decide (b ∈ setOf sj) && sj.elimination.map Elimination.eliminated == some [b])
              s!"{name}: T10(c)" with t10cRounds := s.t10cRounds + 1 }
    | _ => pure ()
  -- T11(a)
  let sets : List (List Nat) :=
    (cnt.rounds ++ cty.rounds).map setOf ++ (if smallSets then subsets C else [])
  for S in sets do
    match holder interp ballots S with
    | some w =>
      if S.length ≤ 8 then
        for S' in subsets S do
          if w ∈ S' then
            s := { s.need (holds interp ballots S' w) s!"{name}: T11(a)" with
              t11aPairs := s.t11aPairs + 1 }
    | none => pure ()
  -- T11(b)
  for i in List.range cty.rounds.length do
    let rd := cty.rounds[i]!
    for (w, v) in rd.tally.votes do
      if rd.tally.continuing < 2 * v then
        s := { s.need (((cty.rounds.drop (i + 1)).all fun r : Round => decide (w ∈ setOf r)) &&
            cty.winner == some w) s!"{name}: T11(b)" with t11bRounds := s.t11bRounds + 1 }
  -- T11(c)
  match cnt.winner, cnt.rounds.getLast? with
  | some w, some last =>
    if cnt.rounds.length == 1 || 2 ≤ (setOf last).length then
      s := { s.need (cty.winner == some w) s!"{name}: T11(c) winner" with
        t11cWinners := s.t11cWinners + 1 }
  | _, _ => pure ()
  if 2 ≤ cnt.rounds.length then
    let prev := cnt.rounds[cnt.rounds.length - 2]!
    let last := cnt.rounds[cnt.rounds.length - 1]!
    if (setOf last).length == 1 then
      s := { s.need (cty.rounds.getLast?.map Round.tally == some prev.tally)
        s!"{name}: T11(c) tied round" with tiedFinal := s.tiedFinal + 1 }
  -- T11(d)
  let wide := (cnt.rounds.filter fun rd : Round => 2 ≤ (setOf rd).length).map Round.tally
  s := { s.need (wide.isSublist (cty.rounds.map Round.tally)) s!"{name}: T11(d)" with
    t11dRounds := s.t11dRounds + wide.length }
  -- T3
  match cnt.rounds.head? with
  | some rd => s := s.need (cnt.winner.isSome == decide (0 < rd.tally.continuing)) s!"{name}: T3(a)"
  | none => s := s.need false s!"{name}: T3(a) no round"
  if cnt.winner.isNone then s := { s with noWinner := s.noWinner + 1 }
  match cnt.winner with
  | some w =>
    s := s.need (match cnt.rounds.getLast? with
      | some rd => rd.tally.votes.any fun x : Nat × Nat => x.1 == w && rd.tally.continuing < 2 * x.2
      | none => false) s!"{name}: T3(b)"
  | none => pure ()
  if 2 ≤ cnt.rounds.length then
    let prev := cnt.rounds[cnt.rounds.length - 2]!
    let last := cnt.rounds[cnt.rounds.length - 1]!
    s := s.need (((setOf last).length == 1) == tieOf prev) s!"{name}: T3(c) single"
    match prev.tally.votes with
    | [(a, va), (b, vb)] =>
      if va == vb then
        s := s.need (match prev.elimination with
          | some (.order [a', b'] _) => a' == a && b' == b
          | _ => false) s!"{name}: T3(c) tie"
    | _ => pure ()
  s := s.need (cnt.rounds.length ≤ max 1 C.length) s!"{name}: T3(d)"
  return s

/-- T8 on every ballot of `ballots` for the pairs `pairs` of sets with `S' ⊆ S`. -/
def checkPairs (name : String) (interp : Interp) (ballots : List (List UInt64))
    (pairs : List (List Nat × List Nat)) (s : Stats) : Stats := Id.run do
  let mut s := s
  for (S, S') in pairs do
    for ps in ballots do
      s := { s.need (t8At interp S S' ps) s!"{name}: T8 at {S} {S'}" with t8pairs := s.t8pairs + 1 }
  return s

def allPairs (C : List Nat) : List (List Nat × List Nat) :=
  (subsets C).flatMap fun S : List Nat => (subsets S).map fun S' : List Nat => (S, S')

/-- The pairs of continuing sets of the rounds of the three counts with `S' ⊆ S`. -/
def roundPairs (interp : Interp) (order : List Nat) (ballots : List (List UInt64)) (C : List Nat) :
    List (List Nat × List Nat) :=
  let sets := ((countFrom interp order ballots C).rounds ++
    (singleFrom interp order ballots C).rounds ++
    (countyFrom interp order ballots C).rounds).map setOf
  sets.flatMap fun S : List Nat => (sets.filter fun S' : List Nat => S'.all (· ∈ S)).map (S, ·)

def dedup (bs : List (List UInt64)) : List (List UInt64) :=
  (bs.foldl (fun (acc : Std.HashSet (List UInt64)) b => acc.insert b) {}).toList

/-! ## Inputs -/

def wordsOf (bs : ByteArray) : List UInt64 :=
  (List.range (bs.size / 8)).map fun j : Nat =>
    (List.range 8).foldr
      (fun (b : Nat) (acc : UInt64) => (acc <<< 8) ||| (bs.get! (8 * j + b)).toUInt64) 0

structure Input where
  kinds : List Kind
  order : List Nat
  ballots : List (List UInt64)

def readInput (path : String) : IO Input := do
  let d := readWords (wordsOf (← IO.FS.readBinFile path))
  return { kinds := d.kinds.map kindOfCode, order := d.order, ballots := d.ballots }

/-- A generator of 64-bit words, the multiplier and increment of Knuth's MMIX. -/
structure Gen where
  x : UInt64

def Gen.next (g : Gen) (m : Nat) : Nat × Gen :=
  let x := g.x * 6364136223846793005 + 1442695040888963407
  ((x >>> 33).toNat % (max m 1), ⟨x⟩)

def shuffle (g : Gen) (l : List Nat) : List Nat × Gen := Id.run do
  let mut a := l.toArray
  let mut g := g
  for i in List.range a.size do
    let j := a.size - 1 - i
    let (r, g') := g.next (j + 1)
    g := g'
    a := a.swapIfInBounds j r
  return (a.toList, g)

def bit (i : Nat) : UInt64 := ((2 : Nat) ^ (i - 1)).toUInt64

/-- A random contest of up to `maxN` candidates of every kind, four positions, and 40 ballots, whose
first choices favor the candidates of low index. -/
def randomInput (g : Gen) (maxN : Nat) : Input × Gen := Id.run do
  let mut g := g
  let (n0, g1) := g.next maxN
  g := g1
  let n := n0 + 1
  let mut kinds : List Kind := []
  for _ in List.range n do
    let (r, g') := g.next 20
    g := g'
    kinds := kinds ++ [if r < 15 then .listed else if r < 17 then .namedWritein
      else if r < 19 then .aggregateWritein else .excluded]
  let (order, g2) := shuffle g (List.range' 1 n)
  g := g2
  let (k0, g3) := g.next 4
  g := g3
  let (nb, g4) := g.next 41
  g := g4
  let mut ballots : List (List UInt64) := []
  for _ in List.range nb do
    let mut ps : List UInt64 := []
    for _ in List.range (k0 + 1) do
      let (r, g') := g.next 40
      g := g'
      let (a, g'') := g.next n
      let (b, g''') := g''.next n
      g := g'''
      let i := min a b + 1
      let (c, g4') := g.next n
      g := g4'
      ps := ps ++ [if r < 8 then 0 else if r < 36 then bit i
        else if r < 39 then (if c + 1 == i then bit i else bit i ||| bit (c + 1))
        else unnamedOvervote]
    ballots := ps :: ballots
  return ({ kinds, order, ballots }, g)

/-- An interpretation that satisfies T8 and counts only for members of the set: a ballot's words
before the first word of 1000 or more name candidates in the ballot's order of preference, and that
word, 1000 plus a code, gives the reason when no named candidate continues. -/
def general (S : List Nat) : List UInt64 → Outcome
  | [] => .inactive .blank
  | w :: ws =>
    if 1000 ≤ w.toNat then
      .inactive (match w.toNat - 1000 with
        | 0 => .blank | 1 => .uncounted | 2 => .overvote | _ => .exhausted)
    else if w.toNat ∈ S then .counts w.toNat else general S ws

def randomGeneral (g : Gen) : (List Nat × List Nat × List (List UInt64)) × Gen := Id.run do
  let mut g := g
  let (n0, g1) := g.next 7
  g := g1
  let n := n0 + 1
  let (order, g2) := shuffle g (List.range' 1 n)
  g := g2
  let (nb, g3) := g.next 41
  g := g3
  let mut ballots : List (List UInt64) := []
  for _ in List.range nb do
    let (perm, g') := shuffle g (List.range' 1 n)
    let (len, g'') := g'.next (n + 1)
    let (a, g''') := g''.next n
    let (b, g4) := g'''.next n
    let (reason, g5) := g4.next 4
    g := g5
    -- favor the candidates of low index in the first place
    let first := min a b + 1
    let rest := (perm.filter (· != first)).take len
    let ranking := if len == 0 then [] else first :: rest
    ballots := ((ranking.map Nat.toUInt64) ++ [(1000 + reason).toUInt64]) :: ballots
  return ((List.range' 1 n, order, ballots), g)

/-- The alphabet of the exhaustive contests: three listed candidates and an aggregate write-in,
three positions, and the blank ballot, every ranking of the listed candidates, two overvotes, and
two ballots that rank the write-in. -/
def alphabet : List (List UInt64) :=
  let rankings : List (List Nat) :=
    [[1], [2], [3], [1, 2], [1, 3], [2, 1], [2, 3], [3, 1], [3, 2],
      [1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]]
  [[0, 0, 0], [unnamedOvervote, 0, 0], [bit 1, bit 2 ||| bit 3, 0], [bit 4, 0, 0],
      [bit 4, bit 1, 0]] ++
    rankings.map fun r : List Nat => (r.map bit) ++ List.replicate (3 - r.length) 0

/-- The multisets of `size` elements of `lo, …, m - 1`, as nondecreasing lists. -/
def multisets (m : Nat) : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | size + 1, lo =>
    (List.range' lo (m - lo)).flatMap fun i : Nat => (multisets m size i).map (i :: ·)

/-! ## Planted statements -/

/-- An interpretation under which a ballot whose words sum to a multiple of 3 counts, against a set
that holds the candidate `c`, for the candidate 1000, who is outside every set, and every other
ballot and set follow `interpret`.  The sets that hold `c` are closed under supersets, so the
interpretation satisfies both statements of T8, and it counts for a candidate outside the set, as
finding 1 of the review describes. -/
def outsider (kinds : List Kind) (c : Nat) (S : List Nat) (ps : List UInt64) : Outcome :=
  if c ∈ S && (ps.foldl (· + ·) 0).toNat % 3 == 0 then .counts 1000 else interpret kinds S ps

/-- An overvote only when two continuing candidates are marked, the reading that the review's
model rejected. -/
def continuingMarks (kinds : List Kind) (S : List Nat) : List UInt64 → Outcome
  | [] => .inactive (passedReason kinds [])
  | w :: ws =>
    let ms := (marks w).filter (· ∈ S)
    if w.toNat.testBit 63 then .inactive .overvote
    else match ms with
      | [] => continuingMarks kinds S ws
      | [i] => .counts i
      | _ => .inactive .overvote

/-! ## Main -/

def printStats (label : String) (s : Stats) : IO UInt32 := do
  for m in s.messages.reverse do IO.println s!"failure: {m}"
  IO.println s!"{label}: {s.summary}"
  return if s.failures == 0 then 0 else 1

def roundsText (k : Count) : List UInt8 :=
  text (((k.rounds.zipIdx 1).flatMap fun p : Round × Nat => roundLines p.2 p.1) ++
    [winnerLine k.winner])

def stem (path : String) : String :=
  let base := (path.splitOn "/").getLast!
  if base.endsWith ".words" then String.ofList (base.toList.take (base.length - 6)) else base

def main (args : List String) : IO UInt32 := do
  match args with
  | "rounds" :: mode :: out :: files =>
    for path in files do
      let x ← readInput path
      let k := match mode with
        | "single" => singleCount x.kinds x.order x.ballots
        | "county" => countyCount x.kinds x.order x.ballots
        | _ => count x.kinds x.order x.ballots
      IO.FS.writeBinFile s!"{out}/{stem path}.{mode}" ⟨(roundsText k).toArray⟩
    IO.println s!"{files.length} files"
    return 0
  | "check" :: files =>
    let mut s : Stats := {}
    for path in files do
      let x ← readInput path
      let K := countedSet x.kinds
      let interp := interpret x.kinds
      let small := K.length ≤ 5
      s := checkCounts path interp x.order x.ballots K small s
      let distinct := dedup x.ballots
      let pairs := if small then allPairs K else roundPairs interp x.order x.ballots K
      s := checkPairs path interp distinct pairs s
    printStats "check" s
  | ["random", seed, n] =>
    let mut g : Gen := ⟨seed.toNat!.toUInt64⟩
    let mut s : Stats := {}
    for i in List.range n.toNat! do
      let (x, g') := randomInput g 7
      g := g'
      let K := countedSet x.kinds
      let small := K.length ≤ 5
      s := checkCounts s!"random {i}" (interpret x.kinds) x.order x.ballots K small s
      s := checkPairs s!"random {i}" (interpret x.kinds) (dedup x.ballots)
        (if small then allPairs K else roundPairs (interpret x.kinds) x.order x.ballots K) s
    printStats "random" s
  | ["general", seed, n] =>
    let mut g : Gen := ⟨seed.toNat!.toUInt64⟩
    let mut s : Stats := {}
    for i in List.range n.toNat! do
      let ((C, order, ballots), g') := randomGeneral g
      g := g'
      let small := C.length ≤ 5
      s := checkCounts s!"general {i}" general order ballots C small s
      s := checkPairs s!"general {i}" general (dedup ballots)
        (if small then allPairs C else roundPairs general order ballots C) s
    printStats "general" s
  | ["exhaustive"] =>
    let kinds : List Kind := [.listed, .listed, .listed, .aggregateWritein]
    let K := countedSet kinds
    let mut s : Stats := {}
    s := checkPairs "alphabet" (interpret kinds) alphabet (allPairs [1, 2, 3, 4]) s
    for size in List.range 7 do
      for m in multisets alphabet.length size 0 do
        let ballots := m.map fun i : Nat => alphabet[i]!
        for order in [[1, 2, 3, 4], [3, 2, 1, 4]] do
          s := checkCounts s!"exhaustive {m} {order}" (interpret kinds) order ballots K false s
    printStats "exhaustive" s
  | ["planted", seed, n] =>
    let mut g : Gen := ⟨seed.toNat!.toUInt64⟩
    let mut t10 : Nat := 0
    let mut t10c : Nat := 0
    let mut t11c : Nat := 0
    let mut t8 : Nat := 0
    for _ in List.range n.toNat! do
      let (x, g') := randomInput g 7
      g := g'
      let K := countedSet x.kinds
      for c in K do
        let bad := outsider x.kinds c
        let cnt := countFrom bad x.order x.ballots K
        let sgl := singleFrom bad x.order x.ballots K
        if sgl.winner != cnt.winner then t10 := t10 + 1
      let cnt := count x.kinds x.order x.ballots
      let sgl := singleCount x.kinds x.order x.ballots
      let cty := countyCount x.kinds x.order x.ballots
      for rd in cnt.rounds do
        match rd.elimination with
        | some (.batch B) =>
          for j in List.range sgl.rounds.length do
            if setOf sgl.rounds[j]! == setOf rd then
              if ((sgl.rounds.drop j).take B.length).any
                  fun sj : Round => sj.elimination == none then
                t10c := t10c + 1
        | _ => pure ()
      match cnt.winner with
      | some w => if cty.winner != some w then t11c := t11c + 1
      | none => pure ()
      for (S, S') in (if K.length ≤ 5 then allPairs K else []) do
        for ps in dedup x.ballots do
          if !t8At (continuingMarks x.kinds) S S' ps then t8 := t8 + 1
    IO.println (s!"planted: T10(a) with a ballot counted outside the set fails {t10} cases, " ++
      s!"T10(c) without the end of the single count fails {t10c} batches, " ++
      s!"T11(c) without its premise fails {t11c} contests, " ++
      s!"T8 with an overvote of continuing marks only fails {t8} pairs")
    return if t10 == 0 || t10c == 0 || t11c == 0 || t8 == 0 then 1 else 0
  | _ =>
    IO.eprintln ("usage: rcv-stability rounds MODE OUT FILE... | check FILE... | " ++
      "random SEED COUNT | " ++
      "general SEED COUNT | exhaustive | planted SEED COUNT")
    return 2

end Demos.Rcv.StabilityNative

def main (args : List String) : IO UInt32 := Demos.Rcv.StabilityNative.main args
