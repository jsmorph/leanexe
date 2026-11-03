import LeanExe.WGSL.Events

/-!
Executions of a dispatch under the memory model that WGSL adopts.  WGSL 14.5 states that WGSL
follows the Vulkan memory model, and the definitions here transcribe the parts of that model's
appendix that the kernels of `Syntax.lean` use: memory operations, location order, data races,
visible-to, and acyclicity.  The kernels have no atomics and no barriers, so scoped modification
order, release sequences, and synchronizes-with do not occur.

The operations on a location fall into five phases: writes before the buffers receive the values
that the dispatch reads, the write of those values, the reads and writes of the invocations
(`Module.invokeE`, with an oracle for each invocation's reads), one read of each output word after
the dispatch, and writes after those reads.  The read after the dispatch represents the copy to
the readback buffer and the host's read of the mapped buffer, or a later dispatch's read.
WebGPU orders queue operations (WebGPU 3.4.1 and the queue-timeline steps of `writeBuffer()` and
`submit()`), and the implementation's memory dependencies between them make the location-order
edges between phases that `Dispatch.Consistent` requires (Vulkan memory model, "Location-Ordered",
the cases through the device and host domains).  Accesses of one invocation to one location are
location-ordered in program order, since they have the same agent and reference.

The Vulkan model's memory locations are bytes, so the location order and the value rule are stated
for each byte of a word.  A location here is a binding and a word.  Every access is an aligned
32-bit word, so the bytes of two accesses through one binding are equal or disjoint.  WebGPU 3.4.3
forbids a dispatch to use a buffer both as the read-write output and as a read-only input, so
output locations share no memory with input locations.  Read-only inputs may share memory, but
nothing writes them during the dispatch.

An execution chooses the oracles, the writes before and after the dispatch, the location order of
each byte, and the values of the reads after the dispatch.  `Dispatch.Consistent` requires the
edges above, no cycle in the location order, and the rule that a read returns the value of a write
visible-to it.  The Vulkan model's location order is one of the relations that meet these
requirements, so a statement about every consistent execution holds for the executions the model
allows.  The acyclicity axiom here omits reads-from and from-reads, which admits more executions.
-/

namespace LeanExe.WGSL

/-- A dispatch: a kernel, its read-only buffers, the output's initial words, and the number of
invocations, which is the number of workgroups times the workgroup size. -/
structure Dispatch where
  module : Module
  inputs : List (Array UInt32)
  output : Array UInt32
  count : Nat

/-- The buffers in binding order: the read-only inputs, then the output. -/
def Dispatch.buffers (d : Dispatch) : List (Array UInt32) := d.inputs ++ [d.output]

/-- A memory location: a binding and a word. -/
abbrev Loc := Nat × Nat

/-- Byte `k` of a word: bits `8k` to `8k + 7`. -/
def byteOf (k : Fin 4) (v : UInt32) : Nat := v.toNat / 256 ^ k.val % 256

/-- A memory operation on the dispatch's locations: write `n` before the initial values, the write
of a location's initial value, event `p` of invocation `g`, the read of output word `i` after the
dispatch, and write `n` after those reads. -/
inductive Op where
  | before (n : Nat)
  | init (loc : Loc)
  | inv (g p : Nat)
  | obs (i : Nat)
  | after (n : Nat)
  deriving DecidableEq

/-- The phase of an operation. -/
def Op.phase : Op → Nat
  | .before _ => 0
  | .init _ => 1
  | .inv .. => 2
  | .obs _ => 3
  | .after _ => 4

/-- An operation's location, the value it wrote or read, and whether it is a write. -/
structure Access where
  loc : Loc
  value : UInt32
  write : Bool

/-- The access of an invocation's event; `output` is the output's binding. -/
def Event.access (output : Nat) : Event → Access
  | .read b i v => ⟨(b, i), v, false⟩
  | .write i v => ⟨(output, i), v, true⟩

/-- A candidate execution: the oracle of each invocation, the location and value of each write
before and after the dispatch, the location order of each byte, and the values of the reads after
the dispatch. -/
structure Execution where
  oracle : Nat → Oracle
  before : Nat → Option (Loc × UInt32)
  after : Nat → Option (Loc × UInt32)
  lo : Fin 4 → Op → Op → Prop
  observed : Nat → UInt32

/-- The events of invocation `g` with oracle `o`, and whether it ended. -/
def Dispatch.events (d : Dispatch) (o : Oracle) (g : Nat) : List Event × Bool :=
  d.module.invokeE (d.inputs.map (·.size)) d.output.size o (UInt32.ofNat g)

/-- The access of an operation, or `none` for an operation that the execution does not
perform. -/
def Dispatch.access (d : Dispatch) (E : Execution) : Op → Option Access
  | .before n => (E.before n).map fun w => ⟨w.1, w.2, true⟩
  | .init (b, i) => (d.buffers[b]?.bind (·[i]?)).map fun v => ⟨(b, i), v, true⟩
  | .inv g p =>
      if g < d.count then
        ((d.events (E.oracle g) g).1[p]?).map (Event.access d.inputs.length)
      else none
  | .obs i => if i < d.output.size then some ⟨(d.inputs.length, i), E.observed i, false⟩ else none
  | .after n => (E.after n).map fun w => ⟨w.1, w.2, true⟩

/-- Write `x` is visible-to read `y` for byte `k`: they access one location, `x` is
location-ordered before `y`, and no other write to that location is location-ordered between them
(Vulkan memory model, "Visible-To"). -/
def Dispatch.VisibleTo (d : Dispatch) (E : Execution) (k : Fin 4) (x y : Op) : Prop :=
  ∃ ax ay, d.access E x = some ax ∧ d.access E y = some ay ∧ ax.write = true ∧ ay.write = false ∧
    ax.loc = ay.loc ∧ E.lo k x y ∧
    ∀ z az, z ≠ x → d.access E z = some az → az.write = true → az.loc = ax.loc →
      ¬(E.lo k x z ∧ E.lo k z y)

/-- A consistent execution of a dispatch. -/
structure Dispatch.Consistent (d : Dispatch) (E : Execution) : Prop where
  /-- Accesses to one location in different phases, at least one of them a write, are
  location-ordered by phase. -/
  phase : ∀ k x y ax ay, d.access E x = some ax → d.access E y = some ay → ax.loc = ay.loc →
    x.phase < y.phase → (ax.write = true ∨ ay.write = true) → E.lo k x y
  /-- An invocation's accesses to one location are location-ordered in program order. -/
  program : ∀ k g p q a b, d.access E (.inv g p) = some a → d.access E (.inv g q) = some b →
    a.loc = b.loc → p < q → E.lo k (.inv g p) (.inv g q)
  /-- The location order has no cycle (Vulkan memory model, "Acyclicity"). -/
  acyclic : ∀ k x, ¬Relation.TransGen (E.lo k) x x
  /-- A read returns the value of a write visible-to it (Vulkan memory model, "Visible-To"). -/
  value : ∀ k x y ax ay, d.VisibleTo E k x y → d.access E x = some ax →
    d.access E y = some ay → byteOf k ay.value = byteOf k ax.value

/-- The dispatch has no data race: an access of an invocation and another access to the same
location, at least one of them a write, are location-ordered in one direction (Vulkan memory
model, "Data Race"). -/
def Dispatch.NoDataRace (d : Dispatch) (E : Execution) : Prop :=
  ∀ k x y ax ay, x ≠ y → (x.phase = 2 ∨ y.phase = 2) → d.access E x = some ax →
    d.access E y = some ay → ax.loc = ay.loc → (ax.write = true ∨ ay.write = true) →
      E.lo k x y ∨ E.lo k y x

end LeanExe.WGSL
