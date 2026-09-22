import Init.Data.ByteArray.Extra

/-!
A pure, single-process filesystem policy over synthetic requests and results.

The policy permits reads below /job/input, writes below /job/output, and at most
one MiB of successful file writes. Standard streams are explicit capabilities.
Paths have lexical directory-tree semantics; this module does not resolve real
files, symlinks, mounts, permissions, or concurrent changes.
-/
namespace LeanExe.Examples.TracePolicy

structure Path where
  components : Array ByteArray

inductive Access where
  | readOnly
  | writeOnly
  | readWrite
  deriving BEq, Inhabited

structure OpenRequest where
  path : ByteArray
  access : Access := .readOnly
  create : Bool := false
  truncate : Bool := false
  deriving Inhabited

inductive Request where
  | open (request : OpenRequest)
  | read (fd count : UInt64)
  | write (fd count : UInt64)
  | close (fd : UInt64)
  deriving Inhabited

/-- A normalized syscall result: a nonnegative result word or an error number. -/
inductive Outcome where
  | ok (value : UInt64)
  | error (errno : UInt64)
  deriving Inhabited

inductive Event where
  | before (request : Request)
  | after (outcome : Outcome)
  deriving Inhabited

inductive Reason where
  | invalidPath
  | invalidOpen
  | readOutsideInput
  | writeOutsideOutput
  | unknownDescriptor
  | wrongAccess
  | writeBudget
  | eventOrder
  | invalidResult
  | syscallError
  | unfinishedRequest
  deriving BEq, Inhabited

structure Handle where
  path : Path
  access : Access
  standardStream : Bool := false

structure State where
  handles : Array (Option Handle)
  pending : Option Request := none
  written : UInt64 := 0
  stopped : Option Reason := none

structure Report where
  reason : Option Reason
  /-- One-based failing event, or zero on acceptance. EOF is the next event. -/
  eventIndex : Nat
  written : UInt64

def writeLimit : UInt64 := 1048576
def descriptorLimit : Nat := 256
def inputRoot : Path := { components := #["job".toUTF8, "input".toUTF8] }
def outputRoot : Path := { components := #["job".toUTF8, "output".toUTF8] }

def canRead : Access → Bool
  | .readOnly => true
  | .writeOnly => false
  | .readWrite => true

def canWrite : Access → Bool
  | .readOnly => false
  | .writeOnly => true
  | .readWrite => true

/-- Parse a file pathname relative to the fixed cwd /job. Names are bytes.
    Empty paths, NUL, parent components, directory-only endings, and paths
    longer than 4096 bytes are outside this model. Repeated / and interior .
    are accepted. No filesystem lookup is performed. -/
def resolvePath (raw : ByteArray) : Option Path := Id.run do
  if raw.isEmpty || raw.size > 4096 then return none
  if raw[raw.size - 1]! == 47 then return none
  let mut parts : Array ByteArray := if raw[0]! == 47 then #[] else #["job".toUTF8]
  let mut component := ByteArray.empty
  for i in [:raw.size + 1] do
    if i == raw.size || raw[i]! == 47 then
      if component == "..".toUTF8 then return none
      if component == ".".toUTF8 then
        if i == raw.size then return none
      else if !component.isEmpty then
        parts := parts.push component
      component := ByteArray.empty
    else
      let byte := raw[i]!
      if byte == 0 then return none
      component := component.push byte
  return some { components := parts }

/-- Strict component ancestry; the directory itself is not an output file. -/
def isBelow (root path : Path) : Bool := Id.run do
  if path.components.size <= root.components.size then return false
  for i in [:root.components.size] do
    if root.components[i]! != path.components[i]! then return false
  return true

def initial : State :=
  let handles : Array (Option Handle) := Array.replicate descriptorLimit none
  let streamPath : Path := { components := #[] }
  let handles := handles.set! 0 (some { path := streamPath, access := .readOnly, standardStream := true })
  let handles := handles.set! 1 (some { path := streamPath, access := .writeOnly, standardStream := true })
  let handles := handles.set! 2 (some { path := streamPath, access := .writeOnly, standardStream := true })
  { handles := handles }

def lookup (state : State) (fd : UInt64) : Option Handle :=
  if fd.toNat < state.handles.size then state.handles[fd.toNat]! else none

def stop (state : State) (reason : Reason) : State :=
  { state with stopped := some reason }

/-- Admission uses subtraction under a guard, so large requests cannot wrap. -/
def fitsBudget (written count : UInt64) : Bool :=
  written <= writeLimit && count <= writeLimit - written

/-- This definition is the first example's policy, written directly in Lean.
    `none` means allow; `some reason` means stop before the operation. -/
def authorize (state : State) (request : Request) : Option Reason :=
  match request with
  | .open request =>
      match resolvePath request.path with
      | none => some .invalidPath
      | some path =>
          if request.truncate && !canWrite request.access then
            some .invalidOpen
          else if (canWrite request.access || request.create || request.truncate) &&
              !isBelow outputRoot path then
            some .writeOutsideOutput
          else if canRead request.access && !isBelow inputRoot path then
            some .readOutsideInput
          else none
  | .read fd _count =>
      match lookup state fd with
      | none => some .unknownDescriptor
      | some handle => if canRead handle.access then none else some .wrongAccess
  | .write fd count =>
      match lookup state fd with
      | none => some .unknownDescriptor
      | some handle =>
          if !canWrite handle.access then some .wrongAccess
          else if !handle.standardStream && !fitsBudget state.written count then
            some .writeBudget
          else none
  | .close fd =>
      match lookup state fd with
      | none => some .unknownDescriptor
      | some _handle => none

/-- Record a successful result; impossible results stop rather than corrupting
    the model. Errors are terminal in this first example. -/
def observe (state : State) (request : Request) (outcome : Outcome) : State :=
  match outcome with
  | .error _errno => stop state .syscallError
  | .ok value =>
      match request with
      | .open request =>
          if value.toNat >= state.handles.size then stop state .invalidResult
          else
            match lookup state value with
            | some _handle => stop state .invalidResult
            | none =>
                match resolvePath request.path with
                | none => stop state .invalidPath
                | some path =>
                    let handle : Handle := { path := path, access := request.access }
                    { state with handles := state.handles.set! value.toNat (some handle) }
      | .read _fd count =>
          if value <= count then state else stop state .invalidResult
      | .write fd count =>
          if value > count then stop state .invalidResult
          else
            match lookup state fd with
            | none => stop state .unknownDescriptor
            | some handle =>
                if handle.standardStream then state
                else if fitsBudget state.written value then
                  { state with written := state.written + value }
                else stop state .invalidResult
      | .close fd =>
          if value != 0 then stop state .invalidResult
          else { state with handles := state.handles.set! fd.toNat none }

/-- The only transition entry needed by a future supervisor. Stop is sticky. -/
def step (state : State) (event : Event) : State :=
  match state.stopped with
  | some _reason => state
  | none =>
      match event with
      | .before request =>
          match state.pending with
          | some _previous => stop state .eventOrder
          | none =>
              match authorize state request with
              | some reason => stop state reason
              | none => { state with pending := some request }
      | .after outcome =>
          match state.pending with
          | none => stop state .eventOrder
          | some request => observe { state with pending := none } request outcome

/-- Check a finite synthetic trace. Acceptance requires a complete final pair,
    but does not require that all descriptors were explicitly closed. -/
def check (events : Array Event) : Report := Id.run do
  let mut state := initial
  for i in [:events.size] do
    state := step state events[i]!
    match state.stopped with
    | some reason =>
        return { reason := some reason, eventIndex := i + 1, written := state.written }
    | none => pure ()
  match state.pending with
  | some _request =>
      return { reason := some .unfinishedRequest, eventIndex := events.size + 1,
               written := state.written }
  | none => return { reason := none, eventIndex := 0, written := state.written }

end LeanExe.Examples.TracePolicy
