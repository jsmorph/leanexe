module

public import LeanExe.Base

@[expose] public section

/-!
The Linux call layer, which depends on no architecture.  A described call has a name, its numbers
on arm64 and on x86-64, the kinds of its parameters in argument order, whether it returns a
descriptor, and whether it ends the process.  `tools/linux-calls.py` generates the descriptions
of `LeanExe/Linux/CallTable.lean` from the syzlang files of syzkaller commit
`a3e64cfc0d091fba81397847a5ab9790a4a944ca` in `tests/linux/syzlang/`.

A request is a call and its argument words.  The layer reads and writes a process's memory
through `Memory`, an interface of byte reads, byte writes, and a test that every byte of a region
is accessible, with addresses as 64-bit words.  A reply is the call's result and the bytes of its
output region after the call.  `step` is the frame rule: when every region of the request is
accessible, the memory after the call differs from the memory before only in the output region,
which holds the reply's bytes, and the event records the request, the bytes of its input regions,
the bytes of its output region before and after the call, and the result.  `step_frame` proves
the frame for every memory that meets `Memory.Lawful`.  The rule says nothing else about the
reply; `LeanExe/Linux/Replies.lean` names properties of replies that a theorem may assume.
-/

namespace LeanExe.Linux

/-- The kind of an argument: a word; a descriptor; a directory descriptor or `AT_FDCWD`; the
address of a file name that the kernel reads through its first zero byte; an address and a length
in two arguments of bytes that the kernel reads or may write; or the address of `size` bytes
that the kernel may write. -/
inductive Param where
  | value
  | fd
  | dirfd
  | path
  | input
  | output
  | record (size : Nat)
  deriving DecidableEq, Repr

/-- A described call: its name, its numbers on arm64 and on x86-64, its parameters, whether it
returns a descriptor, and whether it ends the process. -/
structure Call where
  name : String
  arm64 : UInt64
  amd64 : UInt64
  params : List Param
  opens : Bool
  terminal : Bool
  deriving DecidableEq, Repr

/-- The number of argument words of a parameter. -/
def Param.words : Param → Nat
  | .input | .output => 2
  | _ => 1

/-- The number of argument words of a call. -/
def Call.words (c : Call) : Nat := (c.params.map Param.words).sum

/-- A process's memory as the layer sees it: the byte at an address, the memory with one byte
written, and whether every one of `n` bytes from an address is accessible. -/
structure Memory (M : Type) where
  read : M → UInt64 → UInt8
  write : M → UInt64 → UInt8 → M
  mapped : M → UInt64 → Nat → Bool

/-- The laws of a memory that the frame lemma uses, stated for accessible bytes: a read of the
byte just written, a read of any other byte, each byte of a region that `mapped` accepts
accessible, and a write at an accessible byte keeping every answer of `mapped`. -/
structure Memory.Lawful {M : Type} (I : Memory M) : Prop where
  read_write_same : ∀ m a v, I.mapped m a 1 = true → I.read (I.write m a v) a = v
  read_write_other : ∀ m a b v, I.mapped m a 1 = true → b ≠ a →
    I.read (I.write m a v) b = I.read m b
  mapped_bytes : ∀ m a n, I.mapped m a n = true → ∀ i < n,
    I.mapped m (a + UInt64.ofNat i) 1 = true
  mapped_write : ∀ m a v b k, I.mapped m a 1 = true →
    I.mapped (I.write m a v) b k = I.mapped m b k

namespace Memory

variable {M : Type} (I : Memory M)

/-- The `n` bytes from `a`. -/
def readBytes (m : M) (a : UInt64) : Nat → List UInt8
  | 0 => []
  | n + 1 => I.read m a :: readBytes m (a + 1) n

/-- The memory with the bytes `bs` written from `a`. -/
def writeBytes (m : M) (a : UInt64) : List UInt8 → M
  | [] => m
  | b :: bs => writeBytes (I.write m a b) (a + 1) bs

/-- The number of bytes of the file name at `a` that the kernel reads: through its first zero
byte among the first 4096, or 4096 when they hold none. -/
def pathLength (m : M) (a : UInt64) : Nat :=
  match (List.range 4096).find? (fun i => I.read m (a + UInt64.ofNat i) = 0) with
  | some i => i + 1
  | none => 4096

end Memory

/-- Argument `r` of `args`, and 0 past their end. -/
def arg (args : List UInt64) (r : Nat) : UInt64 := args.getD r 0

/-- The address and size of each region that the parameters `ps`, from argument `r`, give the
kernel to read. -/
def inputRegions {M : Type} (I : Memory M) (m : M) (args : List UInt64) :
    Nat → List Param → List (UInt64 × Nat)
  | _, [] => []
  | r, .path :: ps => (arg args r, I.pathLength m (arg args r)) :: inputRegions I m args (r + 1) ps
  | r, .input :: ps => (arg args r, (arg args (r + 1)).toNat) :: inputRegions I m args (r + 2) ps
  | r, p :: ps => inputRegions I m args (r + p.words) ps

/-- The address and size of each region that the parameters `ps`, from argument `r`, let the
kernel write. -/
def outputRegions (args : List UInt64) : Nat → List Param → List (UInt64 × Nat)
  | _, [] => []
  | r, .output :: ps => (arg args r, (arg args (r + 1)).toNat) :: outputRegions args (r + 2) ps
  | r, .record n :: ps => (arg args r, n) :: outputRegions args (r + 1) ps
  | r, p :: ps => outputRegions args (r + p.words) ps

/-- A request: a described call and its argument words in order. -/
structure Request where
  call : Call
  args : List UInt64

/-- A reply: the call's result, and byte `i` of its output region after the call. -/
structure Reply where
  ret : UInt64
  bytes : Nat → UInt8

/-- The replies of a kernel to a process's calls: the reply to call `k`, the call made after `k`
events. -/
abbrev Replies := Nat → Reply

/-- An event: the request, the bytes of its input regions before the call, the bytes of its
output region before the call, the result, and the bytes of its output region after the call. -/
structure Event where
  call : Call
  args : List UInt64
  inputs : List (List UInt8)
  prior : List UInt8
  ret : UInt64
  output : List UInt8

/-- The frame rule: the memory after the request `q` with the reply `r` and the event, or `none`
when a region of the request is not accessible.  The output region, the first of
`outputRegions`, holds the reply's bytes; every other byte keeps its value. -/
def step {M : Type} (I : Memory M) (m : M) (q : Request) (r : Reply) : Option (M × Event) :=
  let ins := inputRegions I m q.args 0 q.call.params
  let outs := outputRegions q.args 0 q.call.params
  if ins.all (fun g => I.mapped m g.1 g.2) && outs.all (fun g => I.mapped m g.1 g.2) then
    let w := match outs with
      | [] => []
      | g :: _ => (List.range g.2).map r.bytes
    let before := match outs with
      | [] => []
      | g :: _ => I.readBytes m g.1 g.2
    let m' := match outs with
      | [] => m
      | g :: _ => I.writeBytes m g.1 w
    some (m', ⟨q.call, q.args, ins.map fun g => I.readBytes m g.1 g.2, before, r.ret, w⟩)
  else none

theorem succ_ofNat (a : UInt64) (i : Nat) :
    a + 1 + UInt64.ofNat i = a + UInt64.ofNat (i + 1) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat, Nat.reducePow]
  omega

theorem Memory.writeBytes_other {M : Type} {I : Memory M} (hI : I.Lawful) :
    ∀ (bs : List UInt8) (m : M) (a b : UInt64),
      (∀ i < bs.length, I.mapped m (a + UInt64.ofNat i) 1 = true) →
      ¬ (b - a).toNat < bs.length → I.read (I.writeBytes m a bs) b = I.read m b
  | [], _, _, _, _, _ => rfl
  | v :: bs, m, a, b, hm, h => by
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    have hm0 : I.mapped m a 1 = true := by
      have := hm 0 (by simp)
      simpa using this
    have e : (b - a).toNat = ((b - (a + 1)).toNat + 1) % 2 ^ 64 := by
      simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow] at *
      omega
    rw [Memory.writeBytes, writeBytes_other hI bs (I.write m a v) (a + 1) b (fun i hi => by
        rw [hI.mapped_write _ _ _ _ _ hm0, succ_ofNat]
        exact hm (i + 1) (by simp only [List.length_cons]; omega)) (by
      simp only [List.length_cons] at h
      intro h'
      apply h
      rw [e]
      simp only [Nat.reducePow] at *
      omega)]
    refine hI.read_write_other _ _ _ _ hm0 fun e => h ?_
    rw [e, UInt64.sub_self]
    simp

/-- The frame: a step changes no byte outside the output region. -/
theorem step_frame {M : Type} {I : Memory M} (hI : I.Lawful) {m m' : M} {q : Request}
    {r : Reply} {e : Event} (h : step I m q r = some (m', e)) (b : UInt64)
    (hb : ∀ g ∈ outputRegions q.args 0 q.call.params, ¬ (b - g.1).toNat < g.2) :
    I.read m' b = I.read m b := by
  unfold step at h
  dsimp only at h
  split at h
  · rename_i hall
    cases hg : outputRegions q.args 0 q.call.params with
    | nil =>
      simp only [hg] at h
      cases h
      rfl
    | cons g gs =>
      simp only [hg] at h
      cases h
      have := hb g (by rw [hg]; exact List.mem_cons_self ..)
      have hmap : I.mapped m g.1 g.2 = true := by
        simp only [Bool.and_eq_true, List.all_eq_true] at hall
        exact hall.2 g (by rw [hg]; exact List.mem_cons_self ..)
      exact Memory.writeBytes_other hI _ m g.1 b
        (fun i hi => hI.mapped_bytes _ _ _ hmap i (by simpa using hi)) (by simpa using this)
  · cases h

/-- `pathLength` of a name whose first `n` bytes are not zero and whose byte `n` is zero, for
`n` below 4096: `n + 1`. -/
theorem Memory.pathLength_eq {M : Type} (I : Memory M) (m : M) (a : UInt64) {n : Nat}
    (hn : n < 4096) (hz : I.read m (a + UInt64.ofNat n) = 0)
    (hnz : ∀ i < n, I.read m (a + UInt64.ofNat i) ≠ 0) : I.pathLength m a = n + 1 := by
  unfold Memory.pathLength
  have : (List.range 4096).find? (fun i => I.read m (a + UInt64.ofNat i) = 0) = some n := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simpa using hz, n, by simpa using hn, by simp, fun j hj => ?_⟩
    simpa using hnz j (by simpa using hj)
  rw [this]

/-- `pathLength` of 4096 bytes none of which is zero: 4096. -/
theorem Memory.pathLength_none {M : Type} (I : Memory M) (m : M) (a : UInt64)
    (hnz : ∀ i < 4096, I.read m (a + UInt64.ofNat i) ≠ 0) : I.pathLength m a = 4096 := by
  unfold Memory.pathLength
  have : (List.range 4096).find? (fun i => I.read m (a + UInt64.ofNat i) = 0) = none := by
    rw [List.find?_eq_none]
    intro i hi
    simpa using hnz i (List.mem_range.mp hi)
  rw [this]

end LeanExe.Linux
