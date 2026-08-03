import Project.Artifact.Binary.Validate

open Wasm.Binary

private def instructionAtPath : List Instr → List Nat → Option Instr
  | _, [] => none
  | instructions, index :: rest => do
      let instruction ← instructions[index]?
      match rest with
      | [] => some instruction
      | branch :: nested =>
          match instruction with
          | .block _ body => instructionAtPath body (branch :: nested)
          | .loop _ body => instructionAtPath body (branch :: nested)
          | .iff _ thenBody elseBody =>
              if branch = 0 then
                instructionAtPath thenBody nested
              else
                instructionAtPath (elseBody.getD []) nested
          | _ => none
  termination_by _ path => path.length
  decreasing_by all_goals simp_all <;> omega

private def checkFile (path : String) : IO Bool := do
  let bytes ← IO.FS.readBinFile path
  match decode bytes with
  | .error error =>
      IO.eprintln s!"{path}:{error.offset}: decode: {repr error.kind}"
      pure false
  | .ok raw =>
      match validate raw with
      | .error error =>
          IO.eprintln s!"{path}: validation: {repr error}"
          match error.functionIndex.bind (raw.codes[·]?) with
          | some code =>
              match instructionAtPath code.body error.instructionPath with
              | some instruction => IO.eprintln s!"instruction: {repr instruction}"
              | none => pure ()
          | none => pure ()
          pure false
      | .ok _ =>
          IO.println s!"validated {path}: {raw.codes.length} functions, {bytes.size} bytes"
          pure true

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: ValidateFile <program.wasm>..."
    pure 2
  else
    let results ← args.mapM checkFile
    pure (if results.all id then 0 else 1)
