import Project.ByteIO.Memory
import Interpreter.Wasm.Wp.Call

/-!
Executable models and independent relational contracts for the WASI subset.
The oracle chooses syscall errors and partial-transfer sizes; it represents
the external device, not a trusted theorem about the native C implementation.
All memory checks and transfer effects are performed by the model itself.
-/
namespace Project.ByteIO
open Wasm

def errno (e : UInt32) : UInt32 := if e = 0 then 29 else e

theorem errno_ne_zero (e : UInt32) : errno e ≠ 0 := by
  unfold errno; split <;> simp_all

abbrev TransferOracle := World → Nat → Except UInt32 Nat

def returnErr (st : Store World) (e : UInt32) : HostResult World :=
  .Return [.i32 e] st

def fdRead (choose : TransferOracle) (st : Store World)
    (fd iov count out : UInt32) : HostResult World :=
  if fd ≠ 0 then returnErr st 8 else
  if count ≠ 1 then returnErr st 28 else
  if ¬ (inBounds st.mem iov.toNat 8 ∧ inBounds st.mem out.toNat 4) then
    returnErr st 21 else
  let ptr := st.mem.read32 iov
  let cap := (st.mem.read32 (iov + 4)).toNat
  if ¬ inBounds st.mem ptr.toNat cap then returnErr st 21 else
  match choose st.host cap with
  | .error e => returnErr st (errno e)
  | .ok proposed =>
      let n := min cap (min st.host.input.length (max 1 proposed))
      .Return [.i32 0] (commitRead st ptr out n)

def fdWrite (choose : TransferOracle) (st : Store World)
    (fd iov count out : UInt32) : HostResult World :=
  if fd ≠ 1 then returnErr st 8 else
  if count ≠ 1 then returnErr st 28 else
  if ¬ (inBounds st.mem iov.toNat 8 ∧ inBounds st.mem out.toNat 4) then
    returnErr st 21 else
  let ptr := st.mem.read32 iov
  let cap := (st.mem.read32 (iov + 4)).toNat
  if ¬ inBounds st.mem ptr.toNat cap then returnErr st 21 else
  match choose st.host cap with
  | .error e => returnErr st (errno e)
  | .ok proposed =>
      let n := min cap proposed
      .Return [.i32 0] (commitWrite st ptr out n)

def ReadOutcome (st : Store World) (fd iov count out : UInt32)
    (result : HostResult World) : Prop :=
  (∃ e : UInt32, e ≠ 0 ∧ result = .Return [.i32 e] st) ∨
  (fd = 0 ∧ count = 1 ∧ inBounds st.mem iov.toNat 8 ∧ inBounds st.mem out.toNat 4 ∧
    let ptr := st.mem.read32 iov
    let cap := (st.mem.read32 (iov + 4)).toNat
    inBounds st.mem ptr.toNat cap ∧
    ∃ n, n ≤ cap ∧ n ≤ st.host.input.length ∧
      (n = 0 → cap = 0 ∨ st.host.input = []) ∧
      result = .Return [.i32 0] (commitRead st ptr out n))

def WriteOutcome (st : Store World) (fd iov count out : UInt32)
    (result : HostResult World) : Prop :=
  (∃ e : UInt32, e ≠ 0 ∧ result = .Return [.i32 e] st) ∨
  (fd = 1 ∧ count = 1 ∧ inBounds st.mem iov.toNat 8 ∧ inBounds st.mem out.toNat 4 ∧
    let ptr := st.mem.read32 iov
    let cap := (st.mem.read32 (iov + 4)).toNat
    inBounds st.mem ptr.toNat cap ∧
    ∃ n, n ≤ cap ∧ result = .Return [.i32 0] (commitWrite st ptr out n))

theorem fdRead_contract (choose : TransferOracle) (st : Store World)
    (fd iov count out : UInt32) :
    ReadOutcome st fd iov count out (fdRead choose st fd iov count out) := by
  unfold fdRead
  split
  · exact Or.inl ⟨8, by decide, rfl⟩
  · split
    · exact Or.inl ⟨28, by decide, rfl⟩
    · split
      · exact Or.inl ⟨21, by decide, rfl⟩
      · dsimp only
        split
        · exact Or.inl ⟨21, by decide, rfl⟩
        · split
          · exact Or.inl ⟨_, errno_ne_zero _, rfl⟩
          · right
            simp only [not_not] at *
            refine ⟨‹fd = 0›, ‹count = 1›, ‹_ ∧ _›.1, ‹_ ∧ _›.2, ‹_›,
              _, Nat.min_le_left _ _, ?_, ?_, rfl⟩
            · omega
            · intro hz
              have : st.host.input.length = 0 ∨ (st.mem.read32 (iov + 4)).toNat = 0 := by omega
              simpa [List.length_eq_zero_iff] using this.symm

theorem fdWrite_contract (choose : TransferOracle) (st : Store World)
    (fd iov count out : UInt32) :
    WriteOutcome st fd iov count out (fdWrite choose st fd iov count out) := by
  unfold fdWrite
  split
  · exact Or.inl ⟨8, by decide, rfl⟩
  · split
    · exact Or.inl ⟨28, by decide, rfl⟩
    · split
      · exact Or.inl ⟨21, by decide, rfl⟩
      · dsimp only
        split
        · exact Or.inl ⟨21, by decide, rfl⟩
        · split
          · exact Or.inl ⟨_, errno_ne_zero _, rfl⟩
          · right
            simp only [not_not] at *
            exact ⟨‹fd = 1›, ‹count = 1›, ‹_ ∧ _›.1, ‹_ ∧ _›.2, ‹_›,
              _, Nat.min_le_left _ _, rfl⟩

def readHost (choose : TransferOracle) : HostFn World where
  params := [.i32, .i32, .i32, .i32]
  results := [.i32]
  invoke st args := match args with
    | [.i32 fd, .i32 iov, .i32 count, .i32 out] => fdRead choose st fd iov count out
    | _ => .Trap st "fd_read: invalid arguments"

def writeHost (choose : TransferOracle) : HostFn World where
  params := [.i32, .i32, .i32, .i32]
  results := [.i32]
  invoke st args := match args with
    | [.i32 fd, .i32 iov, .i32 count, .i32 out] => fdWrite choose st fd iov count out
    | _ => .Trap st "fd_write: invalid arguments"

def readContract : HostContract World := fun st args result =>
  match args with
  | [.i32 fd, .i32 iov, .i32 count, .i32 out] => ReadOutcome st fd iov count out result
  | _ => result = .Trap st "fd_read: invalid arguments"

def writeContract : HostContract World := fun st args result =>
  match args with
  | [.i32 fd, .i32 iov, .i32 count, .i32 out] => WriteOutcome st fd iov count out result
  | _ => result = .Trap st "fd_write: invalid arguments"

theorem readHost_contract (choose : TransferOracle) (st : Store World) (args : List Value) :
    readContract st args ((readHost choose).invoke st args) := by
  unfold readContract readHost
  dsimp only
  split
  · exact fdRead_contract choose st _ _ _ _
  · split <;> simp_all
    rename_i fd iov count out h
    exact (h fd iov count out rfl rfl rfl rfl).elim

theorem writeHost_contract (choose : TransferOracle) (st : Store World) (args : List Value) :
    writeContract st args ((writeHost choose).invoke st args) := by
  unfold writeContract writeHost
  dsimp only
  split
  · exact fdWrite_contract choose st _ _ _ _
  · split <;> simp_all
    rename_i fd iov count out h
    exact (h fd iov count out rfl rfl rfl rfl).elim

#print axioms fdRead_contract
#print axioms fdWrite_contract
#print axioms readHost_contract
#print axioms writeHost_contract

end Project.ByteIO
