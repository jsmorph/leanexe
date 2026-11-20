import Demos.RandomHistogram.CommandSpec

/-! The output and the status that the specification gives a run of the random-residue histogram's
command whose `random_get` calls take the bytes of a file in order, as they do in the Wasmtime host
with `--random-bytes FILE`: a call takes the file's next bytes, and a call that asks for more bytes
than remain returns errno 29 (`io`).  Writes take every byte that they offer.

`tests/random-histogram/run.sh` runs `lake env lean --run` on this file with a directory and the
names of its cases.  For each name, `NAME.args` holds the arguments, the program name first, one to
a line, and `NAME.bytes` the random bytes.  The script writes the output that the specification
gives to `NAME.expected` and the status in decimal to `NAME.status`.

The run follows `Meets` of `Demos/RandomHistogram/CommandSpec.lean`.  When `parseSpec` refuses the
argument buffer, the status is 2 and the run writes nothing.  Otherwise the calls of `Draws` draw
N words, each call for `8 · min r 512` bytes with `r` the words still to draw, and a call that
returns an errno ends the run with that errno as the status and no write.  When every call returns
errno 0, the output is `renderSpec (histogramSpec (words bytes))` and the status 0.  The script
fails when the words drawn or the sum of the counts differ from N, which `Meets` requires. -/

namespace RandomHistogramExpected

open LeanExe Demos.RandomHistogram

/-- The buffer that `args_get` fills for `args`: each argument's UTF-8 bytes followed by a zero
byte. -/
def argBuffer (args : List String) : Bytes :=
  ⟨⟨(args.flatMap fun a => a.toUTF8.toList ++ [0]).toArray⟩⟩

/-- The calls of `Draws r` that take their bytes from `file`: the bytes `drawn` followed by those
that the calls returned, and the errno of the last call, 0 when every call found its bytes and 29
when a call asked for more bytes than remain. -/
partial def draws (r : Nat) (file drawn : List UInt8) : List UInt8 × UInt64 :=
  if r = 0 then (drawn, 0)
  else
    let size := 8 * min r 512
    if file.length < size then (drawn, 29)
    else draws (r - min r 512) (file.drop size) (drawn ++ file.take size)

/-- The output and the status of a run with the arguments `args` and the random bytes `file`. -/
def expected (args : List String) (file : List UInt8) : Except String (List UInt8 × UInt64) := do
  let n := parseSpec (argBuffer args)
  if n = 0 then return ([], 2)
  let (bytes, errno) := draws n.toNat file []
  if errno ≠ 0 then return ([], errno)
  let counts := histogramSpec (words bytes).toArray
  unless (words bytes).length = n.toNat ∧ (counts.toList.map UInt64.toNat).sum = n.toNat do
    throw "the words drawn or the sum of the counts differ from N"
  return ((renderSpec counts).data.data.toList, 0)

end RandomHistogramExpected

open RandomHistogramExpected in
def main (args : List String) : IO UInt32 := do
  let dir :: names@(_ :: _) := args
    | throw (IO.userError "usage: lean --run tests/random-histogram/Expected.lean DIR NAME...")
  for name in names do
    let argv ← IO.FS.lines s!"{dir}/{name}.args"
    let file ← IO.FS.readBinFile s!"{dir}/{name}.bytes"
    match expected argv.toList file.toList with
    | .ok (out, status) =>
      IO.FS.writeBinFile s!"{dir}/{name}.expected" ⟨out.toArray⟩
      IO.FS.writeFile s!"{dir}/{name}.status" s!"{status}\n"
    | .error message => throw (IO.userError s!"{name}: {message}")
  return 0
