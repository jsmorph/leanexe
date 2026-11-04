import LeanExe.PTX.Det

/-!
Executions of a launch under the PTX memory consistency model (PTX ISA chapter 8).

The operations on a location fall into five phases:
- writes before the buffers receive the values that the kernel reads;
- the writes of those values by copies to the device, memsets, or the threads of earlier launches;
- the threads' loads and stores (`Module.invoke`, with an oracle for each thread's loads);
- one read of each output word by the copy back to the host or by a later launch;
- writes after that read.

The memory model's storage unit is a byte, and a memory location is the range of bytes that an
access covers (8.2).  A location here is a buffer and a 64-bit word.  Every access of a thread
covers one aligned word, and the buffers are allocations aligned to 8 bytes, so two accesses of
threads overlap completely or not at all.  Two input buffers may share one allocation, which the
kernel's threads only read.  The relations are stated for each byte of a word, and a write before or
after the kernel covers one byte, so writes of any size before and after the kernel are covered.

Causality order is defined here, not chosen.  An operation precedes another on the same location
when its phase is earlier, or when both are accesses of one thread in program order.  The phase
edges follow from API synchronization (8.9.4): the host queues the writes of the buffers, the
launch, and the later reads on one stream, where the completion of a task synchronizes with the
start of the next; the start of a kernel synchronizes with the start of its threads; and the end of
the threads synchronizes with the end of the kernel.  A write of a buffer is a copy from the host, a
memset, or a store of an earlier launch's thread, and a later read is a copy to the host or a load
of a later launch's thread.  These synchronizations also take part in proxy-preserved base causality
order.  Program order is part of base causality order (8.9.1, 8.9.5).  The ISA's causality order
contains these edges.  A smaller causality order weakens the coherence and causality axioms and
leaves more pairs of accesses unrelated, so a statement that holds in every consistent execution,
including that no access of a thread is in a data race, holds for the ISA's order.

An execution chooses the oracle of each thread, the writes before and after the kernel, a coherence
order and a reads-from map for each byte, and the values that the copy back reads.  A read takes
each byte from a write to its location (8.9.7).  The axioms kept are coherence (8.10.1) and the two
rules of causality (8.10.6).  No Thin Air, Fence-SC, atomicity, and sequential consistency per
location are omitted, which admits more executions.  Loads and stores without a qualifier are
`.weak` (9.7.10.8, 9.7.10.11), so two accesses are morally strong only when one thread performs
both, and a data race is a pair of conflicting accesses of different threads unrelated in
causality order (8.7.1).
-/

namespace LeanExe.PTX

/-- A launch: a kernel, its input buffers, the output's initial words, the number of blocks, and
the number of threads in a block. -/
structure Launch where
  module : Module
  inputs : List (Array UInt64)
  output : Array UInt64
  blocks : Nat
  block : Nat

/-- The number of threads of a launch. -/
def Launch.threads (L : Launch) : Nat := L.blocks * L.block

/-- The buffers in parameter order: the inputs, then the output. -/
def Launch.buffers (L : Launch) : List (Array UInt64) := L.inputs ++ [L.output]

/-- A memory location: a buffer and a word. -/
abbrev Loc := Nat × Nat

/-- Byte `k` of a word: bits `8k` to `8k + 7`. -/
def byteOf (k : Fin 8) (v : UInt64) : Nat := v.toNat / 256 ^ k.val % 256

/-- A memory operation on the launch's locations: write `n` before the kernel, the write of a
location's initial value, event `p` of thread `g`, the read of output word `i` by the copy back, and
write `n` after that read. -/
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

/-- An operation's location, whether it writes, and the value of each byte of the word that it
accesses. -/
structure Access where
  loc : Loc
  write : Bool
  bytes : Fin 8 → Option Nat

/-- An access of a whole word with value `v`. -/
def Access.word (loc : Loc) (write : Bool) (v : UInt64) : Access :=
  ⟨loc, write, fun k => some (byteOf k v)⟩

/-- A write of byte `k` of a location with value `v`. -/
def Access.byte (w : Loc × Fin 8 × UInt8) : Access :=
  ⟨w.1, true, fun k => if k = w.2.1 then some w.2.2.toNat else none⟩

/-- The access of a thread's event; `output` is the output's parameter. -/
def Event.access (output : Nat) : Event → Access
  | .read b i v => .word (b, i) false v
  | .write i v => .word (output, i) true v

/-- A candidate execution: the oracle of each thread, the byte writes before and after the kernel,
the coherence order and the reads-from map of each byte, and the values that the copy back
reads. -/
structure Execution where
  oracle : Nat → Oracle
  before : Nat → Option (Loc × Fin 8 × UInt8)
  after : Nat → Option (Loc × Fin 8 × UInt8)
  co : Fin 8 → Op → Op → Prop
  rf : Fin 8 → Op → Op
  observed : Nat → UInt64

/-- The events of thread `g` with oracle `o`, and whether it ended. -/
def Launch.events (L : Launch) (o : Oracle) (g : Nat) : List Event × Bool :=
  L.module.invoke (L.inputs.map (·.size)) L.output.size L.block o g

/-- The access of an operation, or `none` for an operation that the execution does not
perform. -/
def Launch.access (L : Launch) (E : Execution) : Op → Option Access
  | .before n => (E.before n).map Access.byte
  | .init (b, i) => (L.buffers[b]?.bind (·[i]?)).map (Access.word (b, i) true)
  | .inv g p =>
      if g < L.threads then
        ((L.events (E.oracle g) g).1[p]?).map (Event.access L.inputs.length)
      else none
  | .obs i =>
      if i < L.output.size then some (.word (L.inputs.length, i) false (E.observed i)) else none
  | .after n => (E.after n).map Access.byte

/-- Causality order: `x` precedes `y` on the same location by phase, or as accesses of one thread
in program order. -/
def Launch.Cause (L : Launch) (E : Execution) (x y : Op) : Prop :=
  ∃ ax ay, L.access E x = some ax ∧ L.access E y = some ay ∧ ax.loc = ay.loc ∧
    (x.phase < y.phase ∨ ∃ g p q, x = .inv g p ∧ y = .inv g q ∧ p < q)

/-- A consistent execution of a launch. -/
structure Launch.Consistent (L : Launch) (E : Execution) : Prop where
  /-- A read takes each byte it accesses from a write to its location, and returns that byte. -/
  reads : ∀ k y ay, L.access E y = some ay → ay.write = false → (ay.bytes k).isSome →
    ∃ ax, L.access E (E.rf k y) = some ax ∧ ax.write = true ∧ ax.loc = ay.loc ∧
      ax.bytes k = ay.bytes k
  /-- Coherence order is a partial order (8.9.6). -/
  co_irrefl : ∀ k x, ¬E.co k x x
  co_trans : ∀ k x y z, E.co k x y → E.co k y z → E.co k x z
  /-- A write that precedes another write in causality order precedes it in coherence order
  (8.10.1). -/
  coherence : ∀ k w w' aw aw', L.access E w = some aw → L.access E w' = some aw' →
    aw.write = true → aw'.write = true → (aw.bytes k).isSome → (aw'.bytes k).isSome →
    L.Cause E w w' → E.co k w w'
  /-- A read does not read from a write that it precedes in causality order (8.10.6). -/
  causality_read : ∀ k r ar, L.access E r = some ar → ar.write = false → (ar.bytes k).isSome →
    ∀ w, L.Cause E r w → E.rf k r ≠ w
  /-- If a write precedes a read in causality order, the read does not read, at a byte both
  access, from a write that precedes that write in coherence order (8.10.6). -/
  causality_write : ∀ k w r aw ar, L.access E w = some aw → L.access E r = some ar →
    aw.write = true → ar.write = false → (aw.bytes k).isSome → (ar.bytes k).isSome →
    L.Cause E w r → ¬E.co k (E.rf k r) w

/-- No access of a thread is in a data race: it and every other access to its location, at least
one of them a write, are related in causality order (8.7.1). -/
def Launch.NoDataRace (L : Launch) (E : Execution) : Prop :=
  ∀ x y ax ay, x ≠ y → (x.phase = 2 ∨ y.phase = 2) → L.access E x = some ax →
    L.access E y = some ay → ax.loc = ay.loc → (ax.write = true ∨ ay.write = true) →
      L.Cause E x y ∨ L.Cause E y x

/-- The oracle whose loads return the input buffers' words. -/
def inputOracle (inputs : List (Array UInt64)) : Oracle :=
  fun _ b i => (inputs[b]?.bind (·[i]?)).getD 0

/-- The output after threads `0` to `threads - 1`, each run with the input oracle and its stores
applied in order, or `none` when a thread stops. -/
def Launch.seq (L : Launch) : Option (Array UInt64) :=
  (List.range L.threads).foldlM (fun out g =>
    let r := L.events (inputOracle L.inputs) g
    if r.2 then some (setAll out (writesOf r.1)) else none) L.output

/-- Distinct threads, run with the input oracle, store to distinct words. -/
def Launch.RaceFree (L : Launch) : Prop :=
  ∀ g h, g < L.threads → h < L.threads → g ≠ h → ∀ i v w,
    Event.write i v ∈ (L.events (inputOracle L.inputs) g).1 →
    Event.write i w ∉ (L.events (inputOracle L.inputs) h).1

end LeanExe.PTX
