import Std.Data.HashMap
import TestSupport.M7.Cosim

/-!
The command `m7-cosim` of the co-simulation of the Cortex-M7 model.  `m7-cosim gen SEED PER_FORM
DIV OUT` writes to OUT the harness of PER_FORM cases of each of the model's forms and of the
division cases with DIV random pairs from the seed SEED.  `m7-cosim check SERIAL` checks every case
line and every division line of the harness's UART output SERIAL against the model, prints the
first differences, the number of agreeing cases of each form, the division cases and the range of
their instruction counts on each path of `udivmod64`, and a summary, and exits with status 1 when
a line differs or cannot be checked, or when no line of either kind is present.
-/

open TestSupport.M7

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
  | _ =>
      IO.eprintln "usage: m7-cosim gen SEED PER_FORM DIV OUT | m7-cosim check SERIAL"
      return 2
