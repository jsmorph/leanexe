import LeanExe.PTX.Syntax

/-!
The meaning of one thread of a kernel.  A load of a global word takes its value from an oracle and
records a read event, and a store records a write event; the memory model of `MemoryModel.lean`
constrains the values of the reads.  A result keeps the events produced before the thread stops,
so the memory model also constrains the reads of a thread that stops.  A thread stops at an
operand of the wrong class, a register read before it is written, a division by zero, an access
outside a buffer or not aligned to 8 bytes, a load of the output, a store to an input, or a loop
past `loopBound` tests.

A `.b64` register holds a word or a pointer.  A pointer is a buffer and a byte offset: `ld.param`
of parameter `j` gives buffer `j` at offset 0, `cvta.to.global.u64` keeps a pointer, and
`add.u64` of a pointer and a word adds the word to the offset.  `mov.b64` and `selp.b64` copy a
pointer, and every other use of a pointer stops the thread, as does a store of a pointer.
`ld.param` records no event: the launch writes each parameter before the kernel starts, and
nothing writes the parameters during the kernel.  Only loads of the input buffers and stores to
the output are events.
-/

namespace LeanExe.PTX

/-- The value of a `.b64` register: a word, or a pointer at byte `offset` of buffer `buffer`. -/
inductive Val64 where
  | word (value : UInt64)
  | ptr (buffer : Nat) (offset : UInt64)
  deriving Repr, DecidableEq

/-- A memory operation of a thread: a read of word `word` of buffer `buffer` that returned
`value`, or a write of `value` to word `word` of the output. -/
inductive Event where
  | read (buffer word : Nat) (value : UInt64)
  | write (word : Nat) (value : UInt64)
  deriving Repr, DecidableEq

/-- The value of a load, given the number of the thread's earlier events, the buffer, and the
word.  Since the first argument differs for every load of a run, an oracle can give the loads of a
run any values. -/
abbrev Oracle := Nat → Nat → Nat → UInt64

/-- What a thread uses besides the buffers' contents: its special registers, the sizes in words
of the input buffers, and the size of the output in words. -/
structure Shape where
  tid : UInt32
  ntid : UInt32
  ctaid : UInt32
  sizes : List Nat
  outputSize : Nat

/-- A thread's registers and whether it has returned.  A register that has not been written
holds `none`. -/
structure Local where
  r32 : Nat → Option UInt32
  r64 : Nat → Option Val64
  rp : Nat → Option Bool
  returned : Bool

/-- The registers at the start of a thread. -/
def Local.initial : Local := ⟨fun _ => none, fun _ => none, fun _ => none, false⟩

def Local.set32 (l : Local) (d : Nat) (v : UInt32) : Local :=
  { l with r32 := fun i => if i = d then some v else l.r32 i }

def Local.set64 (l : Local) (d : Nat) (v : Val64) : Local :=
  { l with r64 := fun i => if i = d then some v else l.r64 i }

def Local.setp (l : Local) (d : Nat) (v : Bool) : Local :=
  { l with rp := fun i => if i = d then some v else l.rp i }

/-- The value of an operand of a 64-bit instruction. -/
def Src64.get (l : Local) : Src64 → Option Val64
  | .reg i => l.r64 i
  | .imm v => some (.word v)

/-- The word of an operand of a 64-bit instruction; a pointer has none. -/
def Src64.word (l : Local) (a : Src64) : Option UInt64 :=
  match a.get l with
  | some (.word v) => some v
  | _ => none

/-- The value of an operand of a 32-bit instruction. -/
def Src32.get (l : Local) : Src32 → Option UInt32
  | .reg i => l.r32 i
  | .imm v => some v

/-- The word in a `.b64` register; a pointer has none. -/
def Local.word (l : Local) (i : Nat) : Option UInt64 :=
  match l.r64 i with
  | some (.word v) => some v
  | _ => none

def Bin64.apply : Bin64 → Val64 → Val64 → Option Val64
  | .add, .word x, .word y => some (.word (x + y))
  | .add, .ptr j o, .word y => some (.ptr j (o + y))
  | .sub, .word x, .word y => some (.word (x - y))
  | .mulLo, .word x, .word y => some (.word (x * y))
  | .div, .word x, .word y => if y = 0 then none else some (.word (x / y))
  | .rem, .word x, .word y => if y = 0 then none else some (.word (x % y))
  | .and, .word x, .word y => some (.word (x &&& y))
  | .or, .word x, .word y => some (.word (x ||| y))
  | .xor, .word x, .word y => some (.word (x ^^^ y))
  | _, _, _ => none

/-- A shift by 64 or more gives 0 (PTX ISA 9.7.9.8 and 9.7.9.9). -/
def Shift.apply : Shift → UInt64 → UInt32 → UInt64
  | .shl, x, n => if n.toNat < 64 then x <<< n.toUInt64 else 0
  | .shr, x, n => if n.toNat < 64 then x >>> n.toUInt64 else 0

def Cmp.apply : Cmp → UInt64 → UInt64 → Bool
  | .eq, x, y => x == y
  | .ne, x, y => x != y
  | .lt, x, y => decide (x < y)
  | .le, x, y => decide (x ≤ y)

/-- A result: the events so far, and a value, or `none` when the thread stops. -/
abbrev Res (α : Type) := List Event × Option α

/-- Continue with `k` after a result that has a value. -/
def Res.andThen (r : Res α) (k : List Event → α → Res β) : Res β :=
  match r with
  | (evs, some x) => k evs x
  | (evs, none) => (evs, none)

/-- The word index of byte `offset + imm` of a buffer of `size` words, when that byte is aligned
to 8 and inside the buffer.  The address offset of `ld` and `st` is a signed 32-bit constant (PTX
ISA 6.4.1), so an immediate of `2^31` or more stops the thread. -/
def wordAt (size : Nat) (offset imm : UInt64) : Option Nat :=
  let addr := offset.toNat + imm.toNat
  if imm.toNat < 2 ^ 31 ∧ addr % 8 = 0 ∧ addr / 8 < size then some (addr / 8) else none

/-- One instruction, after the events `evs`. -/
def Instr.exec (s : Shape) (o : Oracle) (l : Local) (evs : List Event) : Instr → Res Local
  | .special d sp => (evs, some (l.set32 d (match sp with
      | .tidX => s.tid
      | .ntidX => s.ntid
      | .ctaidX => s.ctaid)))
  | .mov32 d a => (evs, (a.get l).map (l.set32 d))
  | .mov64 d a => (evs, (a.get l).map (l.set64 d))
  | .bin64 op d a b => (evs, match l.r64 a, b.get l with
      | some x, some y => (op.apply x y).map (l.set64 d)
      | _, _ => none)
  | .shift op d a b => (evs, match l.word a, b.get l with
      | some x, some n => some (l.set64 d (.word (op.apply x n)))
      | _, _ => none)
  | .setp c p a b => (evs, match l.word a, b.word l with
      | some x, some y => some (l.setp p (c.apply x y))
      | _, _ => none)
  | .selp d t f p => (evs, match l.rp p with
      | some c => ((if c then t else f).get l).map (l.set64 d)
      | none => none)
  | .notPred d a => (evs, (l.rp a).map fun v => l.setp d !v)
  | .widen d a => (evs, (l.r32 a).map fun v => l.set64 d (.word v.toUInt64))
  | .narrow d a => (evs, (l.word a).map fun v => l.set32 d v.toUInt32)
  | .madWide d a b c => (evs, match l.r32 a, l.r32 b, l.word c with
      | some x, some y, some z => some (l.set64 d (.word (x.toUInt64 * y.toUInt64 + z)))
      | _, _, _ => none)
  | .ldParam d j => (evs, if j ≤ s.sizes.length then some (l.set64 d (.ptr j 0)) else none)
  | .cvtaGlobal d a => (evs, match l.r64 a with
      | some (.ptr j off) => some (l.set64 d (.ptr j off))
      | _ => none)
  | .ld d a imm => match l.r64 a with
      | some (.ptr j off) => match s.sizes[j]? with
        | some size => match wordAt size off imm with
          | some k =>
              let v := o evs.length j k
              (evs ++ [.read j k v], some (l.set64 d (.word v)))
          | none => (evs, none)
        | none => (evs, none)
      | _ => (evs, none)
  | .st a imm v => match l.r64 a, l.word v with
      | some (.ptr j off), some x =>
          if j = s.sizes.length then
            match wordAt s.outputSize off imm with
            | some k => (evs ++ [.write k x], some l)
            | none => (evs, none)
          else (evs, none)
      | _, _ => (evs, none)

/-- Whether a guard holds; `none` when its predicate has not been written. -/
def Guard.holds (l : Local) (g : Guard) : Option Bool :=
  (l.rp g.pred).map fun v => v != g.negated

/-- The bound on the tests of a loop's condition. -/
def loopBound : Nat := 2 ^ 64

/-- At most `fuel` runs of a loop's condition, each followed, while predicate `p` holds, by a run
of the body; a `ret` ends the loop. -/
def loopRuns (cond body : Local → List Event → Res Local) (p : Nat) :
    Nat → Local → List Event → Res Local
  | 0, _, evs => (evs, none)
  | fuel + 1, l, evs =>
      if l.returned then (evs, some l)
      else (cond l evs).andThen fun evs l =>
        if l.returned then (evs, some l)
        else match l.rp p with
          | some true => (body l evs).andThen fun evs l => loopRuns cond body p fuel l evs
          | some false => (evs, some l)
          | none => (evs, none)

mutual
  /-- One statement. -/
  def Stmt.exec (s : Shape) (o : Oracle) (l : Local) (evs : List Event) : Stmt → Res Local
    | .instr none i => i.exec s o l evs
    | .instr (some g) i => match g.holds l with
      | some true => i.exec s o l evs
      | some false => (evs, some l)
      | none => (evs, none)
    | .ite p ts es => match l.rp p with
      | some true => Stmt.execList s o l evs ts
      | some false => Stmt.execList s o l evs es
      | none => (evs, none)
    | .while_ cond p body =>
        loopRuns (fun l evs => Stmt.execList s o l evs cond)
          (fun l evs => Stmt.execList s o l evs body) p loopBound l evs
    | .ret => (evs, some { l with returned := true })

  /-- Statements in order; those after a `ret` do nothing. -/
  def Stmt.execList (s : Shape) (o : Oracle) (l : Local) (evs : List Event) :
      List Stmt → Res Local
    | [] => (evs, some l)
    | st :: rest =>
        if l.returned then (evs, some l)
        else (Stmt.exec s o l evs st).andThen fun evs l => Stmt.execList s o l evs rest
end

/-- The shape of thread `g` of a launch with blocks of `block` threads, for input buffers of
`sizes` words and an output of `outputSize` words. -/
def threadShape (sizes : List Nat) (outputSize block g : Nat) : Shape :=
  ⟨UInt32.ofNat (g % block), UInt32.ofNat block, UInt32.ofNat (g / block), sizes, outputSize⟩

/-- The events of thread `g` in program order, up to its end or to the point where it stops, and
whether it ended. -/
def Module.invoke (m : Module) (sizes : List Nat) (outputSize block : Nat) (o : Oracle)
    (g : Nat) : List Event × Bool :=
  if sizes.length = m.inputs then
    let r := Stmt.execList (threadShape sizes outputSize block g) o Local.initial [] m.body
    (r.1, r.2.isSome)
  else ([], false)

end LeanExe.PTX
