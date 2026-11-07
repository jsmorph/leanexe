import Std.Data.HashMap
import TestSupport.M7.Cosim

/-!
The command `m7-cosim` of the co-simulation of the Cortex-M7 model.  `m7-cosim gen SEED PER_FORM
OUT` writes to OUT the harness of PER_FORM cases of each of the model's forms from the seed SEED.
`m7-cosim check SERIAL` checks every case line of the harness's UART output SERIAL against the
model, prints the first differences, the number of agreeing cases of each form, and a summary, and
exits with status 1 when a line differs or cannot be checked, or when no line is present.
-/

open TestSupport.M7

def main (args : List String) : IO UInt32 := do
  match args with
  | ["gen", seed, perForm, out] =>
      match seed.toNat?, perForm.toNat? with
      | some s, some n =>
          IO.FS.writeFile out (harness (UInt64.ofNat s) n)
          IO.println s!"m7-cosim: {n * formCount} cases, {n} of each form, seed {s}"
          return 0
      | _, _ =>
          IO.eprintln "m7-cosim: SEED and PER_FORM must be natural numbers"
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
      return if bad = 0 ∧ lines.size > 0 then 0 else 1
  | _ =>
      IO.eprintln "usage: m7-cosim gen SEED PER_FORM OUT | m7-cosim check SERIAL"
      return 2
