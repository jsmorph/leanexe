import Demos.Rcv.ReadWords
import Demos.Rcv.PrintProgram

/-!
Native runs of the reader of `Demos/Rcv/Read.lean`, for comparisons with the Python reference and
for tests of the statements of T2 before their proofs.

`rcv-tabulate report FILE` writes `reportFile` of the file to standard output.  `rcv-tabulate
compare FILE …` reads each canonical file `X.rcv` and the reference's report `X.report` beside it,
prints each file whose report differs, and prints the number of files, of well-formed files, of
malformed files, and of differences, with status 1 when a report differs.

`rcv-tabulate programs FILE …` compares the reader program's words with `readResult` and the
report of the reader program, the specification's count over words, and the printer program with
the reference's report.  `rcv-tabulate summary FILE …` prints the reader's result for each file in one line.
`rcv-tabulate t2 FILE …` tests the statements of T2(a) to (c) on each file, and `rcv-tabulate
t2-random SEED COUNT` on `COUNT` random structures that meet the constraints and on ten mutations of
each one's file.  A file that `read` accepts must print as itself through `write`, and its structure
must meet the constraints and read back as itself.  For a file that `read` rejects, the line that
`read` reports must be the first line, by number, that `faulty` finds, with the role that `roleAt`
gives it.  Each mode prints its counts and exits with status 1 when a statement fails.
-/

namespace Demos.Rcv.TabulateNative

open Demos.Rcv Demos.Rcv.Spec

def readBytes (path : String) : IO (List UInt8) := do
  return (← IO.FS.readBinFile path).toList

def writeBytes (bs : List UInt8) : IO Unit := do
  (← IO.getStdout).write ⟨bs.toArray⟩

/-- The path of the reference's report beside a canonical file `X.rcv`. -/
def reportPath (path : String) : String :=
  ((System.FilePath.mk path).withExtension "report").toString

def compare (paths : List String) : IO UInt32 := do
  let mut good : Nat := 0
  let mut bad : Nat := 0
  let mut differ : Nat := 0
  for path in paths do
    let b ← readBytes path
    let want ← readBytes (reportPath path)
    match read b with
    | .ok _ => good := good + 1
    | .error _ _ => bad := bad + 1
    if reportFile b != want then
      differ := differ + 1
      IO.println s!"{path}: the report differs from the reference's"
  IO.println s!"{paths.length} files, {good} well formed, {bad} malformed, {differ} differ"
  return if differ == 0 then 0 else 1

/-- The reader's result for each file: `ok` with `k`, `n`, `N`, and the number of ballots with an
identifier, or `error` with the line and the role. -/
def summary (paths : List String) : IO UInt32 := do
  for path in paths do
    match read (← readBytes path) with
    | .ok f =>
      IO.println s!"{path}: ok k {f.positions} n {f.candidates.length} N {f.ballots.length} identifiers {(f.ballots.filter fun b : Ballot => b.ident.isSome).length}"
    | .error j r => IO.println s!"{path}: error {j} {r.word}"
  return 0

/-! ## The programs -/

/-- The report by the reader program, the specification's count over words, and the printer
program. -/
def programReport (b : List UInt8) : List UInt8 :=
  let bytes : LeanExe.Bytes := ⟨⟨b.toArray⟩⟩
  let ws := ReadProgram.readContest bytes
  let out :=
    if ws[(0 : UInt64).toNat]! == 0 then
      PrintProgram.printError ws[(1 : UInt64).toNat]! ws[(2 : UInt64).toNat]!
    else PrintProgram.printReport bytes ws[(0 : UInt64).toNat]! (countArray ws)
  out.data.toList

/-- For each file, the reader program's words against `readResult`, and the report of the reader
program, the specification's count, and the printer program against the reference's. -/
def comparePrograms (paths : List String) : IO UInt32 := do
  let mut wordsDiffer : Nat := 0
  let mut reportsDiffer : Nat := 0
  for path in paths do
    let b ← readBytes path
    if (ReadProgram.readContest ⟨⟨b.toArray⟩⟩).toList != readResult b then
      wordsDiffer := wordsDiffer + 1
      IO.println s!"{path}: the reader program's words differ from readResult"
    if programReport b != (← readBytes (reportPath path)) then
      reportsDiffer := reportsDiffer + 1
      IO.println s!"{path}: the programs' report differs from the reference's"
  IO.println s!"{paths.length} files, {wordsDiffer} with other words, {reportsDiffer} with another report"
  return if wordsDiffer + reportsDiffer == 0 then 0 else 1

/-! ## Statements of T2 on one file -/

/-- The first line, by number, that `faulty` finds among lines 1 to the number of pieces. -/
def firstFaulty (b : List UInt8) : Option Nat :=
  (List.range' 1 (b.splitOn lf).length).find? (faulty b)

/-- The counts of a test: files accepted, files rejected, and failures. -/
structure Counts where
  accepted : Nat := 0
  rejected : Nat := 0
  failed : Nat := 0

/-- T2(b) and the constraints for a file that `read` accepts, and T2(c)'s line and role for one that
it rejects.  T2(a) holds for the accepted structure when it reads back as itself. -/
def checkFile (label : String) (b : List UInt8) (c : Counts) : IO Counts := do
  match read b with
  | .ok f =>
    if write f == b && decide f.WellFormed && read (write f) == .ok f then
      return { c with accepted := c.accepted + 1 }
    IO.println s!"{label}: accepted, and the structure does not print as the file, breaks a constraint, or does not read back"
    return { c with accepted := c.accepted + 1, failed := c.failed + 1 }
  | .error j r =>
    if firstFaulty b == some j && roleAt b j == r then
      return { c with rejected := c.rejected + 1 }
    IO.println s!"{label}: error {j} {r.word}, and the first faulty line is {firstFaulty b}"
    return { c with rejected := c.rejected + 1, failed := c.failed + 1 }

def t2Files (paths : List String) : IO UInt32 := do
  let mut c : Counts := {}
  for path in paths do
    c ← checkFile path (← readBytes path) c
  IO.println s!"{paths.length} files, {c.accepted} accepted, {c.rejected} rejected, {c.failed} failed"
  return if c.failed == 0 then 0 else 1

/-! ## Random structures and mutations -/

/-- A generator of 64-bit words, xorshift64*. -/
structure Rng where
  s : UInt64

def Rng.next (g : Rng) : UInt64 × Rng :=
  let x := g.s ^^^ (g.s >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 0x2545F4914F6CDD1D, ⟨x⟩)

/-- A number below `m`, for `m > 0`. -/
def Rng.below (g : Rng) (m : Nat) : Nat × Rng :=
  let (x, g) := g.next
  (x.toNat % m, g)

def Rng.pick {α : Type} [Inhabited α] (g : Rng) (xs : List α) : α × Rng :=
  let (i, g) := g.below xs.length
  (xs.getD i default, g)

def identBytes : List UInt8 := ascii "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_.:"

/-- `m` values of `f`, threading the generator. -/
def Rng.many {α : Type} (g : Rng) (m : Nat) (f : Rng → α × Rng) : List α × Rng :=
  (List.range m).foldl (fun (acc : List α × Rng) _ => let (x, g) := f acc.2; (x :: acc.1, g)) ([], g)

def Rng.ident (g : Rng) : List UInt8 × Rng :=
  let (long, g) := g.below 4
  let (len, g) := if long = 0 then (64, g) else let (l, g) := g.below 12; (l + 1, g)
  g.many len fun g => g.pick identBytes

def Rng.name (g : Rng) : List UInt8 × Rng :=
  let (long, g) := g.below 20
  let (len, g) := if long = 0 then (255, g) else let (l, g) := g.below 12; (l + 1, g)
  g.many len fun g =>
    let (x, g) := g.below 190
    ((if x < 95 then x + 0x20 else x - 95 + 0x80).toUInt8, g)

/-- A random permutation of `xs`. -/
def Rng.shuffle (g : Rng) (xs : List Nat) : List Nat × Rng :=
  xs.foldl (fun (acc : List Nat × Rng) x =>
    let (i, g) := acc.2.below (acc.1.length + 1)
    (acc.1.take i ++ [x] ++ acc.1.drop i, g)) ([], g)

def Rng.word (g : Rng) (n : Nat) : UInt64 × Rng :=
  let (form, g) := g.below 20
  if form < 8 then (0, g)
  else if form < 15 then let (i, g) := g.below n; (UInt64.ofNat (2 ^ i), g)
  else if form < 19 then let (x, g) := g.below (2 ^ n); (UInt64.ofNat x, g)
  else (unnamedOvervote, g)

def Rng.contest (g : Rng) : Contest × Rng :=
  let (big, g) := g.below 25
  let (k, g) := if big = 0 then (63, g) else let (k, g) := g.below 5; (k + 1, g)
  let (n, g) := if big = 1 then (63, g) else let (n, g) := g.below 6; (n + 1, g)
  let (contest, g) := g.ident
  let (candidates, g) := g.many n fun g =>
    let (code, g) := g.below 4
    let (name, g) := g.name
    ({ kind := kindOfCode code, name }, g)
  let (order, g) := g.shuffle (List.range' 1 n)
  let (N, g) := g.below 12
  let (ballots, g) := g.many N fun g =>
    let (withId, g) := g.below 3
    let (ident, g) := if withId = 0 then let (i, g) := g.ident; (some i, g) else (none, g)
    let (positions, g) := g.many k fun g => g.word n
    ({ ident, positions }, g)
  ({ contest, positions := k, candidates, order, ballots }, g)

/-- Bytes that a mutation inserts or writes. -/
def mutationBytes : List UInt8 :=
  ascii "0123456789 ,|*\n-:aZ" ++ [0x0D, 0x00, 0x7F, 0x80, 0xFF, 0x09]

/-- A random change of `b`: a byte replaced, deleted, or inserted, a line duplicated or deleted, the
file cut short, or bytes appended. -/
def Rng.mutate (g : Rng) (b : List UInt8) : List UInt8 × Rng :=
  let (form, g) := g.below 7
  let (i, g) := g.below (b.length + 1)
  let (x, g) := g.pick mutationBytes
  match form with
  | 0 => (b.set i x, g)
  | 1 => (b.eraseIdx i, g)
  | 2 => (b.insertIdx i x, g)
  | 3 =>
    let ls := b.splitOn lf
    let (j, g) := g.below ls.length
    ([lf].intercalate (ls.take (j + 1) ++ ls.drop j), g)
  | 4 =>
    let ls := b.splitOn lf
    let (j, g) := g.below ls.length
    ([lf].intercalate (ls.eraseIdx j), g)
  | 5 => (b.take i, g)
  | _ => (b ++ [x, lf], g)

def t2Random (seed count : Nat) : IO UInt32 := do
  let mut g : Rng := ⟨UInt64.ofNat seed * 0x9E3779B97F4A7C15 + 1⟩
  let mut c : Counts := {}
  let mut roundTrips : Nat := 0
  for t in List.range count do
    let (f, g1) := g.contest
    g := g1
    if !decide f.WellFormed then
      IO.println s!"random structure {t} breaks a constraint"
      return 1
    if read (write f) != .ok f then
      IO.println s!"random structure {t}: read (write f) differs from f"
      c := { c with failed := c.failed + 1 }
    roundTrips := roundTrips + 1
    for m in List.range 10 do
      let (b, g2) := g.mutate (write f)
      g := g2
      c ← checkFile s!"structure {t}, mutation {m}" b c
  IO.println s!"{roundTrips} structures read back, {c.accepted + c.rejected} mutated files, {c.accepted} accepted, {c.rejected} rejected, {c.failed} failed"
  return if c.failed == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["report", path] =>
      writeBytes (reportFile (← readBytes path))
      return 0
    | "compare" :: paths => compare paths
    | "summary" :: paths => summary paths
    | "programs" :: paths => comparePrograms paths
    | "t2" :: paths => t2Files paths
    | ["t2-random", seed, count] => t2Random seed.toNat! count.toNat!
    | _ =>
      IO.eprintln ("usage: rcv-tabulate report FILE | rcv-tabulate compare FILE ... | " ++
        "rcv-tabulate t2 FILE ... | rcv-tabulate t2-random SEED COUNT")
      return 2
  catch e =>
    IO.eprintln s!"{e}"
    return 1

end Demos.Rcv.TabulateNative

def main (args : List String) : IO UInt32 := Demos.Rcv.TabulateNative.main args
