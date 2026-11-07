import LeanExe.Native.Requests

/-!
The windows of a program with requests, whatever its back end.  `main` runs a step function
forever, and each window calls the step on its state and the value that the last request read and
performs the one register access that the step requests.  The step returns the new state and the
request `q`: bit 63 set requests a write of the low 32 bits of `q` to register `reqReg q`, of 16
bits, and bit 63 clear a read of that register, whose value is the `k`-th read's `σ k`.
`ReqState` is the state before a window: the step's state, the last value read, and the number of
reads so far.  `reqNext` gives the state after a window, and `reqRun` the state before window
`n`.

Each back end records a register access in a trace of its own type `α`: the C path as CompCert's
volatile events of `lx_reg`, and the Cortex-M7 path as the model's device accesses at the
addresses of the device window.  `Bus α` gives the access of each kind to each register and the
value of an access of each kind to a given register, with the laws that the theorems about
records use.  `reqTrace B tick s0 σ n` is the trace of window `n`, its one access, and
`windows W n` the trace of the first `n` windows.  `reqTrace_map` states that a map of states that
commutes with the steps leaves the window traces unchanged.
-/

namespace LeanExe.Requests

open LeanExe.Native (readReq writeReq)

/-- The register of the request `q`, `(q >> 32) & 65535`. -/
def reqReg (q : UInt64) : UInt64 := (q >>> UInt64.ofNat 32) &&& UInt64.ofNat 65535

/-- Whether the request `q` is a write, bit 63. -/
def reqWrite (q : UInt64) : Bool := q >>> UInt64.ofNat 63 != UInt64.ofNat 0

/-- The state before a window: the step's state, the last value read, and the number of reads
so far. -/
structure ReqState (G : Type) where
  state : G
  last : UInt64
  reads : Nat

variable {G : Type}

/-- The state after a window. -/
def reqNext (tick : G → UInt64 → G × UInt64) (σ : Nat → UInt32) (r : ReqState G) :
    ReqState G :=
  if reqWrite (tick r.state r.last).2 then ⟨(tick r.state r.last).1, 0, r.reads⟩
  else ⟨(tick r.state r.last).1, UInt64.ofNat (σ r.reads).toNat, r.reads + 1⟩

/-- The state before window `n`. -/
def reqRun (tick : G → UInt64 → G × UInt64) (s0 : G) (σ : Nat → UInt32) : Nat → ReqState G
  | 0 => ⟨s0, 0, 0⟩
  | n + 1 => reqNext tick σ (reqRun tick s0 σ n)

/-- How a trace of type `α` records the register accesses of requests: `read r v` is a read of
register `r` that returned `v`, and `write r v` a write of `v` to register `r`.  `readOf r e` is
the value of the event `e` when it is a read of register `r`, and `writeOf r e` the value when it
is a write of register `r`.  The laws hold for the registers of 16 bits that requests name. -/
structure Bus (α : Type) where
  read : UInt64 → UInt32 → α
  write : UInt64 → UInt32 → α
  readOf : UInt64 → α → Option UInt32
  writeOf : UInt64 → α → Option UInt32
  readOf_read : ∀ r v, readOf r (read r v) = some v
  readOf_read_ne : ∀ r r' v, r.toNat < 65536 → r'.toNat < 65536 → r ≠ r' →
    readOf r (read r' v) = none
  readOf_write : ∀ r r' v, readOf r (write r' v) = none
  writeOf_write : ∀ r v, writeOf r (write r v) = some v
  writeOf_read : ∀ r r' v, writeOf r (read r' v) = none

variable {α : Type}

/-- The access of the window from the state `r`. -/
def reqEvent (B : Bus α) (tick : G → UInt64 → G × UInt64) (σ : Nat → UInt32) (r : ReqState G) :
    α :=
  if reqWrite (tick r.state r.last).2 then
    B.write (reqReg (tick r.state r.last).2)
      (UInt32.ofNat ((tick r.state r.last).2.toNat % 2 ^ 32))
  else B.read (reqReg (tick r.state r.last).2) (σ r.reads)

/-- The trace of window `n`: its one register access. -/
def reqTrace (B : Bus α) (tick : G → UInt64 → G × UInt64) (s0 : G) (σ : Nat → UInt32)
    (n : Nat) : List α :=
  [reqEvent B tick σ (reqRun tick s0 σ n)]

theorem reqTrace_ne (B : Bus α) (tick : G → UInt64 → G × UInt64) (s0 : G) (σ : Nat → UInt32)
    (n : Nat) : reqTrace B tick s0 σ n ≠ [] := by
  simp [reqTrace]

/-- The trace of the first `n` windows, `W 0 ++ ... ++ W (n - 1)`: `windows` of
`rocq/Clight2Asm.v`. -/
def windows (W : Nat → List α) : Nat → List α
  | 0 => []
  | n + 1 => windows W n ++ W n

theorem reqNext_of {B : Bus α} {tick : G → UInt64 → G × UInt64} {σ : Nat → UInt32}
    {r : ReqState G} {g : G} {q : UInt64} (h : tick r.state r.last = (g, q)) :
    (reqNext tick σ r).state = g ∧
      (reqNext tick σ r).last = (if reqWrite q then 0 else UInt64.ofNat (σ r.reads).toNat) ∧
      (reqNext tick σ r).reads = (if reqWrite q then r.reads else r.reads + 1) ∧
      reqEvent B tick σ r = (if reqWrite q then B.write (reqReg q) (UInt32.ofNat (q.toNat % 2 ^ 32))
        else B.read (reqReg q) (σ r.reads)) := by
  simp only [reqNext, reqEvent, h]
  split <;> simp

theorem next_read {B : Bus α} {tick : G → UInt64 → G × UInt64} {σ : Nat → UInt32}
    {r : ReqState G} {g : G} {q : UInt64} (ht : tick r.state r.last = (g, q))
    (hw : reqWrite q = false) :
    (reqNext tick σ r).state = g ∧ (reqNext tick σ r).last = UInt64.ofNat (σ r.reads).toNat ∧
      reqEvent B tick σ r = B.read (reqReg q) (σ r.reads) := by
  obtain ⟨h1, h2, -, h3⟩ := reqNext_of (B := B) (σ := σ) ht
  simp only [hw, Bool.false_eq_true, ite_false] at h2 h3
  exact ⟨h1, h2, h3⟩

theorem next_write {B : Bus α} {tick : G → UInt64 → G × UInt64} {σ : Nat → UInt32}
    {r : ReqState G} {g : G} {q : UInt64} (ht : tick r.state r.last = (g, q))
    (hw : reqWrite q = true) :
    (reqNext tick σ r).state = g ∧ (reqNext tick σ r).last = 0 ∧
      reqEvent B tick σ r = B.write (reqReg q) (UInt32.ofNat (q.toNat % 2 ^ 32)) := by
  obtain ⟨h1, h2, -, h3⟩ := reqNext_of (B := B) (σ := σ) ht
  simp only [hw, ite_true] at h2 h3
  exact ⟨h1, h2, h3⟩

/-- A map `abs` of states that commutes with the steps carries the run. -/
theorem reqRun_map {G' : Type} {tick : G → UInt64 → G × UInt64}
    {tick' : G' → UInt64 → G' × UInt64} (abs : G → G')
    (h : ∀ s v, tick' (abs s) v = (abs (tick s v).1, (tick s v).2)) (s0 : G) (σ : Nat → UInt32) :
    ∀ n, (reqRun tick' (abs s0) σ n).state = abs (reqRun tick s0 σ n).state ∧
      (reqRun tick' (abs s0) σ n).last = (reqRun tick s0 σ n).last ∧
      (reqRun tick' (abs s0) σ n).reads = (reqRun tick s0 σ n).reads
  | 0 => ⟨rfl, rfl, rfl⟩
  | n + 1 => by
      obtain ⟨h1, h2, h3⟩ := reqRun_map abs h s0 σ n
      simp only [reqRun, reqNext, h1, h2, h3, h]
      split <;> exact ⟨rfl, rfl, rfl⟩

/-- A map `abs` of states that commutes with the steps leaves the window traces unchanged. -/
theorem reqTrace_map {B : Bus α} {G' : Type} {tick : G → UInt64 → G × UInt64}
    {tick' : G' → UInt64 → G' × UInt64} (abs : G → G')
    (h : ∀ s v, tick' (abs s) v = (abs (tick s v).1, (tick s v).2)) (s0 : G) (σ : Nat → UInt32) :
    reqTrace B tick' (abs s0) σ = reqTrace B tick s0 σ := by
  funext n
  obtain ⟨h1, h2, h3⟩ := reqRun_map abs h s0 σ n
  simp only [reqTrace, reqEvent, h1, h2, h3, h]

/-! ## Requests -/

theorem reqReg_lt (q : UInt64) : (reqReg q).toNat < 65536 := by
  simp only [reqReg, UInt64.toNat_and]
  have := Nat.and_le_right (n := (q >>> UInt64.ofNat 32).toNat) (m := (UInt64.ofNat 65535).toNat)
  have h255 : (UInt64.ofNat 65535).toNat = 65535 := rfl
  omega

theorem readReq_toNat {r : UInt64} (hr : r.toNat < 65536) :
    (readReq r).toNat = r.toNat * 4294967296 := by
  have h2 : (4294967296 : UInt64).toNat = 4294967296 := rfl
  simp only [readReq, UInt64.toNat_mul, h2]
  omega

theorem writeReq_toNat {r : UInt64} (v : UInt64) (hr : r.toNat < 65536) :
    (writeReq r v).toNat = 9223372036854775808 + r.toNat * 4294967296 + v.toNat % 4294967296 := by
  have h1 : (9223372036854775808 : UInt64).toNat = 9223372036854775808 := rfl
  have h2 : (4294967296 : UInt64).toNat = 4294967296 := rfl
  simp only [writeReq, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mod, h1, h2]
  omega

theorem reqWrite_iff (q : UInt64) : reqWrite q = true ↔ 9223372036854775808 ≤ q.toNat := by
  have h : (q >>> UInt64.ofNat 63).toNat = q.toNat / 9223372036854775808 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  unfold reqWrite
  rw [bne_iff_ne, ne_eq, ← UInt64.toNat_inj, h]
  show ¬q.toNat / 9223372036854775808 = 0 ↔ _
  omega

theorem reqReg_toNat (q : UInt64) : (reqReg q).toNat = q.toNat / 4294967296 % 65536 := by
  unfold reqReg
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight,
    show (UInt64.ofNat 65535).toNat = 2 ^ 16 - 1 from rfl,
    show (UInt64.ofNat 32).toNat % 64 = 32 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]

theorem reqWrite_readReq {r : UInt64} (hr : r.toNat < 65536) : reqWrite (readReq r) = false := by
  cases h : reqWrite (readReq r)
  · rfl
  · rw [reqWrite_iff, readReq_toNat hr] at h
    omega

theorem reqWrite_writeReq {r : UInt64} (v : UInt64) (hr : r.toNat < 65536) :
    reqWrite (writeReq r v) = true := by
  rw [reqWrite_iff, writeReq_toNat v hr]
  omega

theorem reqReg_readReq {r : UInt64} (hr : r.toNat < 65536) : reqReg (readReq r) = r := by
  apply UInt64.toNat_inj.mp
  rw [reqReg_toNat, readReq_toNat hr]
  omega

theorem reqReg_writeReq {r : UInt64} (v : UInt64) (hr : r.toNat < 65536) :
    reqReg (writeReq r v) = r := by
  apply UInt64.toNat_inj.mp
  rw [reqReg_toNat, writeReq_toNat v hr]
  omega

end LeanExe.Requests
