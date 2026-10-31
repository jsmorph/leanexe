import Verified.Reflect.Command

/-! Matches on structures whose patterns fix fields to constructors of enumerations and bind the
other fields, as `{ value, steps, last := .add }` does.  The reflector reads such a match as a chain
of tests of the fixed fields' words, in the order of the alternatives, and the kernel checks the
chain's equation with the match by cases on the structure and on each fixed field.  The patterns
below fix one field or two, fix different fields in different alternatives, fix every field, bind
the value, or end without a wildcard.  The matches stand on a parameter, on a structure built in
place, on a call, in a loop's body, and on a record that holds an array.  A pattern that fixes a
`Bool` field stops the reflector, and so does a match on word literals, since the rule applies only
to structures with a `Flat` instance and Lean's `UInt64` has none. -/

namespace Verified.Examples.Patterns

open LeanExe.Pipeline

/-- A machine's mode, as the word of its constructor index. -/
inductive Mode where
  | idle | run | halt
  deriving Inhabited

instance : Flat Mode UInt64 := ⟨fun m => m.ctorIdx.toUInt64⟩

/-- A direction, as words other than the constructor indices. -/
inductive Dir where
  | up | down
  deriving Inhabited

instance : Flat Dir UInt64 := ⟨fun | .up => 7 | .down => 3⟩

/-- A machine, flattened with its count first. -/
structure Machine where
  mode : Mode
  dir : Dir
  count : UInt64
  deriving Inhabited

instance : Flat Machine (UInt64 × Mode × Dir) := ⟨fun m => (m.count, m.mode, m.dir)⟩

/-- One field fixed in each pattern, the others bound, and a final wildcard. -/
def tick (m : Machine) : Machine :=
  match m with
  | { mode := .run, dir, count } => { mode := .run, dir, count := count + 1 }
  | { mode := .halt, dir, count } => { mode := .idle, dir, count }
  | _ => m

/-- Patterns that cover every mode, without a wildcard. -/
def code (m : Machine) : UInt64 :=
  match m with
  | { mode := .idle, dir := _, count } => count
  | { mode := .run, dir := _, count } => count * 2
  | { mode := .halt, dir := _, count := _ } => 0

/-- Two fields fixed in one pattern, different fields fixed in different patterns, and a final
pattern that binds the value. -/
def steer (m : Machine) : UInt64 :=
  match m with
  | { mode := .run, dir := .up, count } => count + 1
  | { mode := .run, dir := .down, count } => count - 1
  | { mode := _, dir := .down, count } => count * 3
  | other => other.count + 100

/-- A structure of two enumerations, flattened in the other order. -/
structure Pair where
  mode : Mode
  dir : Dir
  deriving Inhabited

instance : Flat Pair (Dir × Mode) := ⟨fun p => (p.dir, p.mode)⟩

/-- Patterns that fix every field, so that the first two alternatives bind nothing. -/
def rank (p : Pair) : UInt64 :=
  match p with
  | { mode := .idle, dir := .up } => 1
  | { mode := .idle, dir := .down } => 2
  | { mode := .run, dir := _ } => 3
  | _ => 4

/-- A match on a structure built in place from the parameters. -/
def parts (md : Mode) (d : Dir) (k : UInt64) : UInt64 :=
  match ({ mode := md, dir := d, count := k } : Machine) with
  | { mode := .run, dir := .up, count } => count
  | { mode := .halt, dir := _, count := _ } => 1
  | _ => 2

/-- A match on a call. -/
def after (m : Machine) : UInt64 :=
  match tick m with
  | { mode := .run, dir := _, count } => count
  | _ => 0

/-- A match in a loop's body, on the loop's state. -/
def ticks (n : UInt64) (m : Machine) : Machine :=
  LeanExe.loop n m fun _ s =>
    match s with
    | { mode := .run, dir, count } => { mode := .run, dir, count := count + 2 }
    | { mode := .idle, dir, count } => { mode := .run, dir, count }
    | _ => s

/-- A log: a mode and the words that it holds. -/
structure Log where
  mode : Mode
  items : Array UInt64
  deriving Inhabited

instance : Flat Log (Mode × Array UInt64) := ⟨fun l => (l.mode, l.items)⟩

/-- A match on a record that holds an array, whose last pattern binds the value. -/
def record (l : Log) (x : UInt64) : Log :=
  match l with
  | { mode := .run, items } => { mode := .run, items := items.push x }
  | { mode := .halt, items } => { mode := .idle, items }
  | other => other

verified_compile compiled := [tick, code, steer, rank, parts, after, ticks, record]

/-- A flag and a word. -/
structure Flagged where
  flag : Bool
  value : UInt64

instance : Flat Flagged (Bool × UInt64) := ⟨fun f => (f.flag, f.value)⟩

/-- A pattern that fixes a `Bool` field, which the reflector rejects. -/
def flagged (f : Flagged) : UInt64 :=
  match f with
  | { flag := true, value } => value
  | _ => 0

/--
error: verified_compile: a pattern fixes the field `flag` to true, which is not a constructor of an enumeration with a `Flat` instance to words, in
  match f with
  | { flag := true, value := value } => value
  | x => 0
-/
#guard_msgs in
verified_compile rejected := [flagged]

/-- A match on word literals.  Lean's `UInt64` is a structure without a `Flat` instance, so the
reflector does not read the match as structure patterns and rejects it as an unsupported term. -/
def wordMatch (w : UInt64) : UInt64 :=
  match w with
  | 0 => 1
  | _ => 2

/--
error: verified_compile: unsupported term match w with
| 0 => 1
| x => 2
-/
#guard_msgs in
verified_compile wordRejected := [wordMatch]

#print axioms compiled.bytes

end Verified.Examples.Patterns
