import Std.Data.HashMap
import TestSupport.M7.BoardCosim

/-!
The command `m7-cosim` of the co-simulation of the Cortex-M7 model.  `m7-cosim gen SEED PER_FORM
DIV OUT` writes to OUT the harness of PER_FORM cases of each of the model's forms and of the
division cases with DIV random pairs from the seed SEED.  `m7-cosim check SERIAL` checks every case
line and every division line of the harness's UART output SERIAL against the model, prints the
first differences, the number of agreeing cases of each form, the division cases and the range of
their instruction counts on each path of `udivmod64`, and a summary, and exits with status 1 when
a line differs or cannot be checked, or when no line of either kind is present.

`m7-cosim board SEED PER_FORM OUT [seeded]` writes to OUT the board's image of PER_FORM cases of
each form of `tests/TestSupport/M7/BoardCosim.lean` from the seed SEED, followed by the fixed cases
unless `seeded` is given, and prints its layout and a line `results ADDRESS BYTES` that names the
bytes of DTCM that hold the results.  `m7-cosim board-check SEED PER_FORM RESULTS [seeded]
[adc-carry]` checks the output records of the bytes RESULTS that `st-flash` read from that address
against the model, prints every difference with the case's inputs, the agreeing and differing cases
of each form and fixed case, the differences by field, and a summary, and exits with status 1 when
a case differs, when the header names another image, or when the board saved fewer cases than the
image holds.  With `adc-carry` the model's `ADC` ignores its carry in.
-/

open TestSupport.M7

/-- The check of the board's results. -/
def boardCheck (seed : UInt64) (per : Nat) (seeded : Bool) (path : String) (mutate : Bool) :
    IO UInt32 := do
  let res ← IO.FS.readBinFile path
  let cases ← IO.ofExcept (BoardCosim.boardCases seed per seeded)
  let n := cases.size
  let L := BoardCosim.layout n
  if res.size < BoardCosim.resultBytes n then
    IO.println s!"m7-cosim: {path} holds {res.size} bytes, not {BoardCosim.resultBytes n}"
    return 1
  let h (i : Nat) := BoardCosim.wordAt res ((BoardCosim.hdr - BoardCosim.win).toNat + 4 * i)
  if h 3 ≠ UInt32.ofNat n ∨ h 4 ≠ seed.toUInt32 ∨ h 5 ≠ (seed >>> 32).toUInt32 ∨
      h 6 ≠ UInt32.ofNat per then
    IO.println (s!"m7-cosim: the header names {(h 3).toNat} cases, seed " ++
      s!"{(h 5).toNat * 4294967296 + (h 4).toNat}, and {(h 6).toNat} of each form, not {n}, " ++
      s!"{seed.toNat}, and {per}")
    return 1
  let saved := min (h 1).toNat n
  let mut agree : Std.HashMap String Nat := {}
  let mut differ : Std.HashMap String Nat := {}
  let mut fields : Std.HashMap String Nat := {}
  for ((name, b), k) in cases.toList.zipIdx.take saved do
    match BoardCosim.checkCase mutate L res k b with
    | [] => agree := agree.insert name (agree.getD name 0 + 1)
    | diffs =>
        differ := differ.insert name (differ.getD name 0 + 1)
        for d in diffs do
          let f := if d.startsWith "the model stops" then "the model stops"
            else if d.startsWith "the model's" then "the model's device accesses"
            else (d.splitOn " ").headD d
          fields := fields.insert f (fields.getD f 0 + 1)
        IO.println s!"differ: case {k}, {asm b.c.instr}: {"; ".intercalate diffs}"
        IO.println s!"  inputs: {BoardCosim.inputs L k b}"
  let names := (cases.foldl (fun acc (nm, _) => if acc.contains nm then acc else acc.push nm)
    #[]).toList
  IO.println ("m7-cosim: agreeing cases by form: " ++
    ", ".intercalate (names.map fun f => s!"{f} {agree.getD f 0}"))
  let bad := differ.toList.foldl (fun a p => a + p.2) 0
  if bad > 0 then
    IO.println ("m7-cosim: differing cases by form: " ++
      ", ".intercalate (names.filterMap fun f => (differ.get? f).map fun c => s!"{f} {c}"))
    IO.println ("m7-cosim: differences by field: " ++ ", ".intercalate
      ((fields.toList.toArray.qsort (·.1 < ·.1)).toList.map fun (f, c) => s!"{f} {c}"))
  IO.println (s!"m7-cosim: {saved - bad} of {n} cases, {per} of each of {BoardCosim.kinds} " ++
    s!"forms and {n - per * BoardCosim.kinds} fixed, agree with the " ++
    s!"model{if mutate then " with ADC's carry in replaced by 0" else ""}; the board saved " ++
    s!"{(h 1).toNat} cases" ++
    (if h 0 = BoardCosim.doneWord then " and finished" else " and did not finish"))
  return if bad = 0 ∧ saved = n ∧ h 0 = BoardCosim.doneWord then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["gen", seed, perForm, div, out] =>
      match seed.toNat?, perForm.toNat?, div.toNat? with
      | some s, some n, some k =>
          IO.FS.writeFile out (harness (UInt64.ofNat s) n k)
          IO.println (s!"m7-cosim: {n * formCount} cases, {n} of each form, " ++
            s!"{boundaries.size * (boundaries.size - 1) + k} division cases, seed {s}")
          return 0
      | _, _, _ =>
          IO.eprintln "m7-cosim: SEED, PER_FORM, and DIV must be natural numbers"
          return 2
  | ["check", serial] =>
      let lines := (← IO.FS.lines serial).filter (·.startsWith "C ")
      let mut bad := 0
      let mut shown := 0
      let mut agree : Std.HashMap String Nat := {}
      for line in lines do
        match checkLine line with
        | .ok (form, []) => agree := agree.insert form (agree.getD form 0 + 1)
        | .ok (_, diffs) =>
            bad := bad + 1
            if shown < 20 then
              shown := shown + 1
              IO.println s!"differ: case {(line.splitOn " ")[1]!}: {"; ".intercalate diffs}"
        | .error e =>
            bad := bad + 1
            if shown < 20 then
              shown := shown + 1
              IO.println s!"unchecked: {e}"
      let forms := agree.toList.map (·.1) |>.toArray.qsort (· < ·)
      IO.println ("m7-cosim: agreeing cases by form: " ++
        ", ".intercalate (forms.toList.map fun f => s!"{f} {agree.getD f 0}"))
      IO.println (s!"m7-cosim: {lines.size - bad} of {lines.size} cases of {forms.size} forms " ++
        "agree with the model")
      let dlines := (← IO.FS.lines serial).filter (·.startsWith "D ")
      let mut dbad := 0
      let mut paths : Std.HashMap String (Nat × Nat × Nat × Nat × Nat) := {}
      for line in dlines do
        match checkDivLine line with
        | .ok (path, passes, steps, diffs) =>
            let (c, lo, hi, plo, phi) := paths.getD path (0, steps, steps, passes, passes)
            paths := paths.insert path
              (c + 1, min lo steps, max hi steps, min plo passes, max phi passes)
            if !diffs.isEmpty then
              dbad := dbad + 1
              if shown < 20 then
                shown := shown + 1
                IO.println s!"differ: division {(line.splitOn " ")[1]!}: {"; ".intercalate diffs}"
        | .error e =>
            dbad := dbad + 1
            if shown < 20 then
              shown := shown + 1
              IO.println s!"unchecked: {e}"
      for path in ["high", "low", "small", "loop"] do
        match paths.get? path with
        | some (c, lo, hi, plo, phi) =>
            IO.println (s!"m7-cosim: division path {path}: {c} cases, {lo} to {hi} instructions" ++
              (if path = "loop" then s!", {plo} to {phi} passes" else ""))
        | none => IO.println s!"m7-cosim: division path {path}: no case"
      IO.println (s!"m7-cosim: {dlines.size - dbad} of {dlines.size} division cases agree with " ++
        "the model, with UInt64 / and %, and with the paths' instruction counts")
      return if bad = 0 ∧ dbad = 0 ∧ lines.size > 0 ∧ dlines.size > 0 then 0 else 1
  | "board" :: seed :: perForm :: out :: rest =>
      match seed.toNat?, perForm.toNat?, rest with
      | some s, some n, [] | some s, some n, ["seeded"] =>
          match BoardCosim.image (UInt64.ofNat s) n (rest = ["seeded"]) with
          | .ok (bytes, L) =>
              IO.FS.writeBinFile out (ByteArray.mk bytes.toArray)
              IO.println (s!"m7-cosim: board image of {L.n} cases, {n} of each of " ++
                s!"{BoardCosim.kinds} forms and {L.n - n * BoardCosim.kinds} fixed, seed {s}: " ++
                s!"{bytes.length} bytes, cases from " ++
                s!"{hex L.cases.toNat}, landing code {hex L.land.toNat}, save " ++
                s!"{hex L.save.toNat}, setup {hex L.setup.toNat}, input records " ++
                s!"{hex L.data.toNat}")
              IO.println s!"results {hex BoardCosim.win.toNat} {BoardCosim.resultBytes L.n}"
              return 0
          | .error e =>
              IO.eprintln s!"m7-cosim: board: {e}"
              return 1
      | _, _, _ =>
          IO.eprintln "m7-cosim: board SEED PER_FORM OUT [seeded]"
          return 2
  | "board-check" :: seed :: perForm :: results :: rest =>
      let seeded := rest.contains "seeded"
      let mutate := rest.contains "adc-carry"
      match seed.toNat?, perForm.toNat? with
      | some s, some n =>
          if rest.all (fun a => a = "seeded" ∨ a = "adc-carry") then
            boardCheck (UInt64.ofNat s) n seeded results mutate
          else
            IO.eprintln "m7-cosim: board-check SEED PER_FORM RESULTS [seeded] [adc-carry]"
            return 2
      | _, _ =>
          IO.eprintln "m7-cosim: board-check SEED PER_FORM RESULTS [seeded] [adc-carry]"
          return 2
  | _ =>
      IO.eprintln ("usage: m7-cosim gen SEED PER_FORM DIV OUT | m7-cosim check SERIAL | " ++
        "m7-cosim board SEED PER_FORM OUT [seeded] | " ++
        "m7-cosim board-check SEED PER_FORM RESULTS [seeded] [adc-carry]")
      return 2
