import Examples.Gpt32.Driver

/-!
`lean --run Examples/Gpt32/Generate.lean HOST WEIGHTS WGSL SCORES NH F CHUNK VOCAB LAYERS N ID...`
generates `N` tokens after the prompt `ID...` with the weights of the directory `WEIGHTS`, writes
the kernels to the directory `WGSL`, appends the scores of each step to the file `SCORES` as
little-endian binary32 values, and prints the prompt and the generated tokens on one line.
-/

open Examples.Gpt32

def pushWord (b : ByteArray) (w : UInt32) : ByteArray :=
  (((b.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push (w >>> 24).toUInt8

def main (args : List String) : IO Unit := do
  match args with
  | host :: weights :: wgsl :: scores :: nh :: f :: chunk :: vocab :: layers :: n :: ids =>
    let num (t : String) : IO Nat := match t.toNat? with
      | some v => pure v
      | none => throw <| IO.userError s!"not a number: {t}"
    let s := shapeOf (← num nh) (← num f) (← num chunk) (← num vocab) (← num layers)
    let prompt ← ids.mapM num
    IO.FS.writeBinFile scores ByteArray.empty
    let out ← IO.FS.Handle.mk scores .append
    let ids ← generate host weights wgsl s!"{scores}.read" s prompt (← num n) fun zs => do
      for z in zs do
        out.write (z.foldl (fun b x => pushWord b x.toBits) ByteArray.empty)
    out.flush
    IO.println (" ".intercalate (ids.map toString))
  | _ =>
    throw <| IO.userError
      "usage: Generate.lean HOST WEIGHTS WGSL SCORES NH F CHUNK VOCAB LAYERS N ID..."
