import LeanExe.Wasi.SysCalls
import LeanExe.Wasi.Interpreter

/-! Native runs of the typed functions with a record result through a scripted host.  The host
replies to each call with errno 0 and a record whose byte `i` is `i + 1`, so that every byte of the
record differs; each field must be the little-endian value of the bytes at its witx offset and
width, written below as constants.  A reply with an errno leaves every field 0, and a record one
byte short raises an `IO.Error`. -/

open LeanExe LeanExe.Wasi

namespace SysRecordsTest

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- The bytes `1, 2, …, size`. -/
private def counting (size : Nat) : Bytes :=
  ⟨⟨((List.range size).map fun index => (index + 1).toUInt8).toArray⟩⟩

/-- A host whose flat calls reply with `errno` and `record`, recording each call's name and
arguments. -/
private def scripted (calls : IO.Ref (Array (String × List Arg))) (errno : UInt64)
    (record : Bytes) : NativeHost where
  read _ := pure (.returned 0 Bytes.empty)
  write _ bytes := pure (.returned 0 bytes.size)
  exit _ := pure (.ok ())
  sys call args := do
    calls.modify (·.push (call.name, args))
    pure (.returned errno [record])

private def fields {α : Type} (action : Action α) (host : NativeHost) (project : α → List UInt64) :
    IO (List UInt64) := do
  match ← action.run host with
  | .returned result => pure (project result)
  | _ => throw (IO.userError "expected a return")

private def fdstat (result : FdstatResult) : List UInt64 :=
  [result.errno, result.fsFiletype, result.fsFlags, result.fsRightsBase, result.fsRightsInheriting]

private def filestat (result : FilestatResult) : List UInt64 :=
  [result.errno, result.dev, result.ino, result.filetype, result.nlink, result.size, result.atim,
    result.mtim, result.ctim]

private def prestat (result : PrestatResult) : List UInt64 :=
  [result.errno, result.tag, result.prNameLen]

/-- `$filestat` with byte `i` equal to `i + 1`: dev at 0, ino at 8, filetype at 16 (one byte),
nlink at 24, size at 32, and the times at 40, 48, and 56. -/
private def filestatFields : List UInt64 :=
  [0, 0x0807060504030201, 0x100f0e0d0c0b0a09, 0x11, 0x201f1e1d1c1b1a19, 0x2827262524232221,
    0x302f2e2d2c2b2a29, 0x3837363534333231, 0x403f3e3d3c3b3a39]

def main : IO Unit := do
  let calls ← IO.mkRef (#[] : Array (String × List Arg))
  let fdstatFields ← fields (fdFdstatGet 3) (scripted calls 0 (counting 24)) fdstat
  check (fdstatFields == [0, 0x01, 0x0403, 0x100f0e0d0c0b0a09, 0x1817161514131211])
    s!"fd_fdstat_get fields {fdstatFields}"
  let fdFilestatFields ← fields (fdFilestatGet 3) (scripted calls 0 (counting 64)) filestat
  check (fdFilestatFields == filestatFields) s!"fd_filestat_get fields {fdFilestatFields}"
  let pathFilestatFields ← fields (pathFilestatGet 3 1 bytes![102])
    (scripted calls 0 (counting 64)) filestat
  check (pathFilestatFields == filestatFields) s!"path_filestat_get fields {pathFilestatFields}"
  let prestatFields ← fields (fdPrestatGet 3) (scripted calls 0 (counting 8)) prestat
  check (prestatFields == [0, 0x01, 0x08070605]) s!"fd_prestat_get fields {prestatFields}"
  let recorded ← calls.get
  check (recorded.map (·.1) ==
      #["fd_fdstat_get", "fd_filestat_get", "path_filestat_get", "fd_prestat_get"])
    s!"calls {recorded.map (·.1)}"
  match recorded[2]? with
  | some (_, [Arg.word fd, Arg.word flags, Arg.bytes path]) =>
    check (fd == 3 && flags == 1 && path.data.data.toList == [102]) "path_filestat_get arguments"
  | _ => throw (IO.userError "path_filestat_get argument kinds")
  let failed ← fields (fdFilestatGet 3) (scripted calls 8 (counting 64)) filestat
  check (failed == [8, 0, 0, 0, 0, 0, 0, 0, 0]) s!"fd_filestat_get after an errno {failed}"
  let shortCaught ← try
    let _ ← (fdFdstatGet 3).run (scripted calls 0 (counting 23))
    pure false
  catch _ => pure true
  check shortCaught "a record one byte short was accepted"
  IO.println "record call native cases passed: 7"

end SysRecordsTest

def main : IO Unit := SysRecordsTest.main
