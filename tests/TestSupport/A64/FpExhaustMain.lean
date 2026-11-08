import TestSupport.A64.FpExhaust
import Std.Data.HashMap

/-!
The command `a64-fpexhaust` of the exhaustive test of the single-precision forms
(`tests/baremetal/a64-fpexhaust.sh`).  `a64-fpexhaust gen DIR SAMPLE CASE...` writes DIR/ex.img,
the arm64 Image of the cases, and DIR/ex.layout, a line for each segment with its case, first
chunk, and number of chunks: every chunk of each case when SAMPLE is 0, and otherwise SAMPLE
chunks spread over the words.  A CASE is a case's name, `unary`, `binary`, or `all`.
`a64-fpexhaust part DIR START COUNT CASE...` writes only DIR/ex.layout, with COUNT chunks from
START of each case, and `a64-fpexhaust stripes DIR LO HI CASE...` writes the layout of the blocks
of 16 chunks whose number modulo 100 lies from LO to below HI, for a share of the digests on
another host.  `a64-fpexhaust expect DIR TASKS`
writes DIR/ex.expect, the digests
of Talos's results for every chunk of the layout, computed in TASKS parallel tasks, and prints
each case's time, and `a64-fpexhaust expect DIR TASKS model` writes DIR/ex.model, the digests of
the model's runs of the cases' code.  `a64-fpexhaust join DIR PART...` writes DIR/ex.expect for
the layout of DIR from the layouts and digests of the directories PART, and fails when a chunk is
missing or when two parts give one chunk different digests.  `a64-fpexhaust check DIR SERIAL`
compares the digests of the UART output SERIAL with DIR/ex.expect, prints each segment's numbers of chunks and of chunks that differ and then every
chunk that differs, and exits with status 1 when a digest differs or the output cannot be checked.
-/

open TestSupport.A64.Fp TestSupport.A64.Exhaust

def hex16 (w : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 w.toNat)
  "0x" ++ String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- The chunks of a sample of `n` chunks: chunk `j (2^16 / n) + (37 j mod 2^16 / n)` for `j`
below `n`, one in each stretch of `2^16 / n` chunks. -/
def sampleChunks (n : Nat) : List Nat :=
  let w := 2 ^ (32 - chunkBits) / n
  (List.range n).map fun j => j * w + (37 * j) % w

def parseLayout (text : String) : Except String (List Segment) := do
  let lines := (text.splitOn "\n").filter (· ≠ "")
  lines.mapM fun l =>
    match l.splitOn " " with
    | [c, s, n] =>
        match caseOf c, s.toNat?, n.toNat? with
        | some case, some start, some count => pure { case, start, count }
        | _, _, _ => throw s!"the layout line {l}"
    | _ => throw s!"the layout line {l}"

/-- The cases that a name selects: one case, the unary ones, the binary ones, or all. -/
def pick (names : List String) : Option (List Case) :=
  (names.mapM fun
    | "all" => some cases
    | "unary" => some (cases.filter (!·.binary))
    | "binary" => some (cases.filter (·.binary))
    | n => (caseOf n).map ([·])).map List.flatten

/-- The chunks of each run of consecutive segments of one case, in order. -/
def runs (segs : List Segment) : List (Case × Array Nat) :=
  (segs.foldl (fun acc g =>
    let ks := (List.range g.count).toArray.map (g.start + ·)
    match acc with
    | (c, xs) :: rest => if c.name == g.case.name then (c, xs ++ ks) :: rest else (g.case, ks) :: acc
    | [] => [(g.case, ks)]) []).reverse

/-- The segments of `16`-chunk blocks of case `c` whose number modulo 100 lies from `lo` to below
`hi`, a share of the chunks that meets every part of the range. -/
def stripes (c : Case) (lo hi : Nat) : List Segment :=
  (List.range (2 ^ (32 - chunkBits) / 16)).filterMap fun b =>
    if lo ≤ b % 100 ∧ b % 100 < hi then some { case := c, start := 16 * b, count := 16 } else none

def readLayout (dir : String) : IO (List Segment) := do
  match parseLayout (← IO.FS.readFile s!"{dir}/ex.layout") with
  | .ok segs => return segs
  | .error e => throw (IO.userError e)

def main (args : List String) : IO UInt32 := do
  match args with
  | "gen" :: dir :: sample :: names =>
      match pick names, sample.toNat? with
      | some cs, some n =>
          if n ≠ 0 ∧ (2 ^ (32 - chunkBits)) % n ≠ 0 then
            IO.eprintln "a64-fpexhaust: SAMPLE must divide 65536"
            return 2
          let segs : List Segment :=
            if n = 0 then cs.map fun c => { case := c, start := 0, count := 2 ^ (32 - chunkBits) }
            else cs.flatMap fun c => (sampleChunks n).map fun k => { case := c, start := k, count := 1 }
          match image segs with
          | .error e =>
              IO.println s!"fail: the image: {e}"
              return 1
          | .ok img =>
              IO.FS.writeBinFile s!"{dir}/ex.img" img
              IO.FS.writeFile s!"{dir}/ex.layout" <| String.join <|
                segs.map fun g => s!"{g.case.name} {g.start} {g.count}\n"
              let chunks := segs.foldl (fun k g => k + g.count) 0
              IO.println s!"a64-fpexhaust: {segs.length} segments of {cs.length} cases, {chunks} chunks, an Image of {img.size} bytes"
              return 0
      | _, _ =>
          IO.eprintln "a64-fpexhaust: a CASE that does not exist, or a SAMPLE that is no number"
          return 2
  | "part" :: dir :: start :: count :: names =>
      match pick names, start.toNat?, count.toNat? with
      | some cs, some a, some n =>
          if n = 0 ∨ 2 ^ (32 - chunkBits) < a + n then
            IO.eprintln "a64-fpexhaust: the chunks lie beyond the 32-bit words"
            return 2
          IO.FS.writeFile s!"{dir}/ex.layout" <| String.join <|
            cs.map fun c => s!"{c.name} {a} {n}\n"
          return 0
      | _, _, _ =>
          IO.eprintln "a64-fpexhaust: a CASE that does not exist, or a START or COUNT that is no number"
          return 2
  | "stripes" :: dir :: lo :: hi :: names =>
      match pick names, lo.toNat?, hi.toNat? with
      | some cs, some a, some b =>
          let segs := cs.flatMap fun c => stripes c a b
          IO.FS.writeFile s!"{dir}/ex.layout" <| String.join <|
            segs.map fun g => s!"{g.case.name} {g.start} {g.count}\n"
          IO.println s!"a64-fpexhaust: {segs.length} blocks of 16 chunks"
          return 0
      | _, _, _ =>
          IO.eprintln "a64-fpexhaust: a CASE that does not exist, or a START or COUNT that is no number"
          return 2
  | "join" :: dir :: parts =>
      let segs ← readLayout dir
      let mut m : Std.HashMap (String × Nat) UInt64 := {}
      for p in parts do
        let ps ← readLayout p
        let bytes ← IO.FS.readBinFile s!"{p}/ex.expect"
        let n := ps.foldl (fun k g => k + g.count) 0
        if bytes.size ≠ 8 * n then
          IO.println s!"fail: {p}/ex.expect holds {bytes.size} bytes, not {8 * n}"
          return 1
        let mut k := 0
        for g in ps do
          for j in [0:g.count] do
            let d := digestAt bytes (k + j)
            match m.get? (g.case.name, g.start + j) with
            | some d' =>
                if d' ≠ d then
                  IO.println s!"fail: two parts disagree on {g.case.name} chunk {g.start + j}"
                  return 1
            | none => m := m.insert (g.case.name, g.start + j) d
          k := k + g.count
      let mut out := ByteArray.empty
      for g in segs do
        for j in [0:g.count] do
          match m.get? (g.case.name, g.start + j) with
          | some d =>
              for b in [0:8] do
                out := out.push (LeanExe.A64.byteOf d b)
          | none =>
              IO.println s!"fail: no part holds {g.case.name} chunk {g.start + j}"
              return 1
      IO.FS.writeBinFile s!"{dir}/ex.expect" out
      IO.println s!"a64-fpexhaust: joined {out.size / 8} digests from {m.size} in the parts"
      return 0
  | "expect" :: dir :: tasks :: rest =>
      let t := tasks.toNat?.getD 1
      let model := rest = ["model"]
      let segs ← readLayout dir
      let mut out := ByteArray.empty
      for (c, ks) in runs segs do
        let t0 ← IO.monoNanosNow
        match expected c ks model t with
        | .error e =>
            IO.println s!"fail: {e}"
            return 1
        | .ok ds =>
            for d in ds do
              for k in [0:8] do
                out := out.push (LeanExe.A64.byteOf d k)
            let t1 ← IO.monoNanosNow
            IO.println s!"expect {c.name}: {ks.size} chunks in {(t1 - t0) / 1000000} ms"
      IO.FS.writeBinFile s!"{dir}/{if model then "ex.model" else "ex.expect"}" out
      return 0
  | ["check", dir, serial] =>
      let segs ← readLayout dir
      let want ← IO.FS.readBinFile s!"{dir}/ex.expect"
      let out ← IO.FS.readBinFile serial
      let total := segs.foldl (fun k g => k + g.count) 0
      if want.size ≠ 8 * total then
        IO.println s!"fail: ex.expect holds {want.size} bytes, not {8 * total}"
        return 1
      if out.size ≠ 8 * total + 1 then
        IO.println s!"fail: the UART carries {out.size} bytes, not {8 * total + 1}"
        return 1
      if out[8 * total]! ≠ 0 then
        IO.println s!"fail: the status byte is {out[8 * total]!}, not 0"
        return 1
      let mut k := 0
      let mut bad := 0
      let mut diffs := #[]
      let mut byCase : List (String × Nat × Nat) := []
      for g in segs do
        let mut b := 0
        for j in [0:g.count] do
          if digestAt out (k + j) ≠ digestAt want (k + j) then
            b := b + 1
            diffs := diffs.push s!"differ: {g.case.name} chunk {g.start + j}: {hex16 (digestAt out (k + j))}, model {hex16 (digestAt want (k + j))}"
        k := k + g.count
        bad := bad + b
        byCase := match byCase with
          | (n, c, d) :: rest => if n == g.case.name then (n, c + g.count, d + b) :: rest
              else (g.case.name, g.count, b) :: byCase
          | [] => [(g.case.name, g.count, b)]
      for (n, c, d) in byCase.reverse do
        IO.println s!"case {n}: {c} chunks, {d} differ"
      for d in diffs do
        IO.println d
      IO.println s!"a64-fpexhaust: {total - bad} of {total} chunks agree with the model"
      return if bad = 0 then 0 else 1
  | _ =>
      IO.eprintln "usage: a64-fpexhaust gen DIR SAMPLE CASE... | part DIR START COUNT CASE... | stripes DIR LO HI CASE... | expect DIR TASKS [model] | join DIR PART... | check DIR SERIAL"
      return 2
