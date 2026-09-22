import LeanExe.Examples.TracePolicy

/-! Editable sample traces and a native Lean harness. No real filesystem
operations are performed: `open`, `read`, and `write` below construct data. -/
open LeanExe.Examples.TracePolicy

namespace TracePolicyHarness

structure Sample where
  name : String
  events : Array Event
  reason : Option Reason := none
  eventIndex : Nat := 0
  written : UInt64 := 0

def opened (path : String) (access : Access) (fd : UInt64)
    (create : Bool := false) (truncate : Bool := false) : Array Event :=
  #[.before (.open { path := path.toUTF8, access, create, truncate }), .after (.ok fd)]

def readBytes (fd count actual : UInt64) : Array Event :=
  #[.before (.read fd count), .after (.ok actual)]

def writeBytes (fd count actual : UInt64) : Array Event :=
  #[.before (.write fd count), .after (.ok actual)]

def closed (fd : UInt64) : Array Event :=
  #[.before (.close fd), .after (.ok 0)]

def output : Array Event := opened "output/b" .writeOnly 3 true true

def samples : Array Sample := #[
  { name := "copy", events :=
      opened "input/a" .readOnly 3 ++ readBytes 3 4096 12 ++
      opened "output/b" .writeOnly 4 true true ++ writeBytes 4 12 12 ++
      closed 3 ++ closed 4, written := 12 },
  { name := "partial-write", events := output ++
      writeBytes 3 100 40 ++ writeBytes 3 60 60, written := 100 },
  { name := "exact-budget", events := output ++ writeBytes 3 writeLimit writeLimit,
      written := writeLimit },
  { name := "budget-exceeded", events := output ++
      writeBytes 3 writeLimit writeLimit ++ #[.before (.write 3 1)],
      reason := some .writeBudget, eventIndex := 5, written := writeLimit },
  { name := "large-request", events := output ++
      #[.before (.write 3 18446744073709551615)],
      reason := some .writeBudget, eventIndex := 3 },
  { name := "partial-budget", events := output ++
      writeBytes 3 writeLimit 1 ++ writeBytes 3 (writeLimit - 1) (writeLimit - 1),
      written := writeLimit },
  { name := "zero-write-at-limit", events := output ++
      writeBytes 3 writeLimit writeLimit ++ writeBytes 3 0 0, written := writeLimit },
  { name := "standard-streams", events := readBytes 0 8 8 ++
      writeBytes 1 8 8 ++ writeBytes 2 1 1 },
  { name := "stdout-after-budget", events := output ++
      writeBytes 3 writeLimit writeLimit ++ writeBytes 1 5 5, written := writeLimit },
  { name := "descriptor-reuse", events := opened "input/a" .readOnly 3 ++ closed 3 ++
      output ++ writeBytes 3 5 5, written := 5 },
  { name := "stdout-number-reused", events := closed 1 ++
      opened "output/b" .writeOnly 1 true ++ writeBytes 1 writeLimit writeLimit ++
      #[.before (.write 1 1)], reason := some .writeBudget,
      eventIndex := 7, written := writeLimit },
  { name := "normalized-path", events := opened "/job//input/./a" .readOnly 3 },
  { name := "byte-filename", events :=
      #[.before (.open { path := "input/".toUTF8.push 255 }), .after (.ok 3)] },
  { name := "empty-trace", events := #[] },
  { name := "eof-read", events := readBytes 0 10 0 },
  { name := "outside-read", events := opened "/etc/passwd" .readOnly 3,
      reason := some .readOutsideInput, eventIndex := 1 },
  { name := "outside-write", events := opened "/job/input/a" .writeOnly 3,
      reason := some .writeOutsideOutput, eventIndex := 1 },
  { name := "prefix-confusion", events := opened "/job/output-extra/a" .writeOnly 3,
      reason := some .writeOutsideOutput, eventIndex := 1 },
  { name := "input-prefix-confusion", events := opened "/job/inputs/a" .readOnly 3,
      reason := some .readOutsideInput, eventIndex := 1 },
  { name := "root-is-not-a-file", events := opened "/job/output" .writeOnly 3,
      reason := some .writeOutsideOutput, eventIndex := 1 },
  { name := "parent-component", events := opened "output/../input/a" .writeOnly 3,
      reason := some .invalidPath, eventIndex := 1 },
  { name := "empty-path", events := opened "" .readOnly 3,
      reason := some .invalidPath, eventIndex := 1 },
  { name := "trailing-slash", events := opened "input/a/" .readOnly 3,
      reason := some .invalidPath, eventIndex := 1 },
  { name := "trailing-dot", events := opened "input/a/." .readOnly 3,
      reason := some .invalidPath, eventIndex := 1 },
  { name := "nul-path", events :=
      #[.before (.open { path := "input/a".toUTF8.push 0 })],
      reason := some .invalidPath, eventIndex := 1 },
  { name := "long-path", events :=
      #[.before (.open { path := ByteArray.mk (Array.replicate 4097 97) })],
      reason := some .invalidPath, eventIndex := 1 },
  { name := "truncate-input", events := opened "input/a" .writeOnly 3 false true,
      reason := some .writeOutsideOutput, eventIndex := 1 },
  { name := "readonly-truncate", events := opened "input/a" .readOnly 3 false true,
      reason := some .invalidOpen, eventIndex := 1 },
  { name := "readonly-create-input", events := opened "input/new" .readOnly 3 true,
      reason := some .writeOutsideOutput, eventIndex := 1 },
  { name := "readwrite-output", events := opened "output/b" .readWrite 3,
      reason := some .readOutsideInput, eventIndex := 1 },
  { name := "write-readonly", events := opened "input/a" .readOnly 3 ++
      #[.before (.write 3 1)], reason := some .wrongAccess, eventIndex := 3 },
  { name := "read-writeonly", events := output ++ #[.before (.read 3 1)],
      reason := some .wrongAccess, eventIndex := 3 },
  { name := "read-stdout", events := #[.before (.read 1 1)],
      reason := some .wrongAccess, eventIndex := 1 },
  { name := "write-stdin", events := #[.before (.write 0 1)],
      reason := some .wrongAccess, eventIndex := 1 },
  { name := "closed-descriptor", events := output ++ closed 3 ++
      #[.before (.write 3 1)], reason := some .unknownDescriptor, eventIndex := 5 },
  { name := "unknown-descriptor", events := #[.before (.read 99 1)],
      reason := some .unknownDescriptor, eventIndex := 1 },
  { name := "huge-descriptor", events := #[.before (.write 18446744073709551615 1)],
      reason := some .unknownDescriptor, eventIndex := 1 },
  { name := "result-without-request", events := #[.after (.ok 3)],
      reason := some .eventOrder, eventIndex := 1 },
  { name := "overlapping-requests", events :=
      #[.before (.read 0 1), .before (.write 1 1)],
      reason := some .eventOrder, eventIndex := 2 },
  { name := "unfinished-request", events := #[.before (.read 0 1)],
      reason := some .unfinishedRequest, eventIndex := 2 },
  { name := "duplicate-open-result", events := opened "input/a" .readOnly 1,
      reason := some .invalidResult, eventIndex := 2 },
  { name := "out-of-range-open-result", events := opened "input/a" .readOnly 256,
      reason := some .invalidResult, eventIndex := 2 },
  { name := "oversized-read-result", events := readBytes 0 1 2,
      reason := some .invalidResult, eventIndex := 2 },
  { name := "oversized-write-result", events := output ++ writeBytes 3 1 2,
      reason := some .invalidResult, eventIndex := 4 },
  { name := "bad-close-result", events := #[.before (.close 1), .after (.ok 1)],
      reason := some .invalidResult, eventIndex := 2 },
  { name := "syscall-error", events :=
      #[.before (.open { path := "input/missing".toUTF8 }), .after (.error 2)],
      reason := some .syscallError, eventIndex := 2 }
]

def reasonText : Reason → String
  | .invalidPath => "invalid or unsupported pathname"
  | .invalidOpen => "truncation requires write access"
  | .readOutsideInput => "read outside /job/input"
  | .writeOutsideOutput => "write/create/truncate outside /job/output"
  | .unknownDescriptor => "descriptor is not open"
  | .wrongAccess => "descriptor does not permit this operation"
  | .writeBudget => "requested write exceeds remaining file-write allowance"
  | .eventOrder => "request/result events are out of order"
  | .invalidResult => "result is inconsistent with the request or descriptor table"
  | .syscallError => "syscall failed; this example stops on errors"
  | .unfinishedRequest => "trace ended before the pending request completed"

def accessText : Access → String
  | .readOnly => "read"
  | .writeOnly => "write"
  | .readWrite => "read-write"

def requestText : Request → String
  | .open r =>
      let path := match String.fromUTF8? r.path with
        | some text => s!"{repr text}"
        | none => s!"bytes:{repr r.path.data.toList}"
      s!"open {path} access={accessText r.access} create={r.create} truncate={r.truncate}"
  | .read fd count => s!"read fd={fd} count={count}"
  | .write fd count => s!"write fd={fd} count={count}"
  | .close fd => s!"close fd={fd}"

def eventText : Event → String
  | .before r => s!"before {requestText r}"
  | .after (.ok value) => s!"after ok {value}"
  | .after (.error errno) => s!"after error {errno}"

def reportText (r : Report) : String :=
  match r.reason with
  | none => s!"ACCEPT; file bytes written={r.written}"
  | some reason =>
      s!"STOP at event {r.eventIndex}: {reasonText reason}; file bytes written={r.written}"

def checkSample (sample : Sample) (verbose : Bool) : IO Unit := do
  let actual := check sample.events
  unless actual.reason == sample.reason && actual.eventIndex == sample.eventIndex &&
      actual.written == sample.written do
    let expected : Report :=
      { reason := sample.reason, eventIndex := sample.eventIndex, written := sample.written }
    throw <| IO.userError s!"{sample.name}: expected {reportText expected}; got {reportText actual}"
  if verbose then
    for i in [:sample.events.size] do
      IO.println s!"  {i + 1}: {eventText sample.events[i]!}"
  IO.println s!"PASS {sample.name}: {reportText actual}"

def checkTransitions : IO Unit := do
  let awaiting := step initial (.before (.open {
    path := "output/a".toUTF8, access := .writeOnly, create := true }))
  unless (lookup awaiting 3).isNone && awaiting.written == 0 do
    throw <| IO.userError "authorization changed completed-operation state"
  let ready := step awaiting (.after (.ok 3))
  let pending := step ready (.before (.write 3 100))
  unless pending.written == 0 do
    throw <| IO.userError "write budget was charged before completion"
  let completed := step pending (.after (.ok 40))
  unless completed.written == 40 do
    throw <| IO.userError "write budget did not use actual transferred bytes"
  let denied := step completed (.before (.write 3 writeLimit))
  let later := step denied (.after (.ok writeLimit))
  unless denied.stopped == some .writeBudget && later.stopped == denied.stopped &&
      later.written == 40 do
    throw <| IO.userError "stop was not terminal"
  IO.println "PASS transitions: admission, completion, partial accounting, terminal stop"

def usage : String :=
  "usage: tools/trace-policy [--list | SAMPLE]\n" ++
  "With no arguments, checks all synthetic traces. SAMPLE shows every event.\n" ++
  "Edit test/TracePolicyHarness.lean to add a sample. No OS calls are intercepted."

def run (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      for sample in samples do checkSample sample false
      checkTransitions
      IO.println s!"Checked {samples.size} synthetic traces and transition invariants."
      return 0
  | ["--list"] =>
      for sample in samples do IO.println sample.name
      return 0
  | ["--help"] => IO.println usage; return 0
  | [name] =>
      match samples.find? (fun sample => sample.name == name) with
      | some sample => checkSample sample true; return 0
      | none => IO.eprintln s!"unknown sample: {name}\n{usage}"; return 2
  | _ => IO.eprintln usage; return 2

end TracePolicyHarness

def main (args : List String) : IO UInt32 := TracePolicyHarness.run args
