import Demos.OrderBook.ProcessFuture
import Demos.OrderBook.ProcessProof
import Demos.OrderBook.ProgramCounts
import Verified.ChargeFacts

/-! The sizes that the charges of the compiled process need.  `run_batch_out_size` bounds the event
words of `Program.run` on a batch of at most 74 records from any book, by the count of
[the program's counts](ProgramCounts.lean).  `Sized` states the sizes of a reached state: the
arrays of `Inv`, a carry below 56 bytes, and an output of at most `outputLimit` bytes, and
`copyLimit` bounds the copy of such a state.  `step_sized` states that a step from a state with the
invariant `Future` returns a state with these sizes. -/

namespace Demos.OrderBook.Process

open LeanExe LeanExe.Wasi Verified Refinement
open Demos.StreamFold (StreamPosition StreamHost)

/-- The event words of `run` on a batch of at most 518 words, which holds at most 74 records. -/
theorem run_batch_out_size (b : Program.Book) (ws : Array UInt64) (small : ws.size ≤ 518) :
    (Program.run b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count ws).2.size ≤
      7 * 5122 * 74 := by
  have bound := Program.run_out_size b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId
    b.count ws
  have fits : ws.size + 6 < UInt64.size := Nat.lt_of_le_of_lt (Nat.add_le_add_right small 6)
    (by decide)
  have sizeNat : ws.size.toUInt64.toNat = ws.size := UInt64.toNat_ofNat_of_lt' (by omega)
  have records : ((ws.size.toUInt64 + 6) / 7).toNat = (ws.size + 6) / 7 := by
    rw [UInt64.toNat_div, UInt64.toNat_add, sizeNat]
    simp only [UInt64.reduceToNat]
    rw [Nat.mod_eq_of_lt (show ws.size + 6 < 2 ^ 64 from fits)]
  rw [records] at bound
  omega

/-- The bytes of a copy of a state. -/
def copyBytes (s : State) : Nat :=
  blockCost s.oid.size + blockCost s.acct.size + blockCost s.qty.size + blockCost s.lvl.size +
    blockCost s.nxt.size + blockCost s.head.size + blockCost s.tail.size +
    Bytes.allocationCost s.carry.data.size + Bytes.allocationCost s.output.data.size

theorem state_copyCost (s : State) : stateTy.copyCost (sourceState s) = copyBytes s := by
  simp only [stateTy, sourceState, Ty.copyCost, Elem.width, copyBytes, blockCost, allocCost]
  omega

/-- The sizes of a reached state: the arrays of `Inv`, a carry below 56 bytes, and an output of at
most `outputLimit` bytes. -/
structure Sized (s : State) : Prop where
  oid : s.oid.size = 4097
  acct : s.acct.size = 4097
  qty : s.qty.size = 4097
  lvl : s.lvl.size = 4097
  nxt : s.nxt.size = 4097
  head : s.head.size = 2048
  tail : s.tail.size = 2048
  carry : s.carry.data.size < 56
  output : s.output.data.size ≤ outputLimit

/-- A bound on the copy of a state with the sizes of `Sized`: the book's arrays, 197,040 bytes, a
carry block of at most 110 bytes, and an output block of at most `outputLimit + 55` bytes. -/
def copyLimit : Nat := 197205 + outputLimit

theorem Sized.copyCost {s : State} (sized : Sized s) :
    stateTy.copyCost (sourceState s) ≤ copyLimit := by
  rw [state_copyCost]
  have carry := allocationCost_le s.carry.data.size
  have output := allocationCost_le s.output.data.size
  have := sized.carry
  have := sized.output
  simp only [copyBytes, copyLimit, blockCost_eq, sized.oid, sized.acct, sized.qty, sized.lvl,
    sized.nxt, sized.head, sized.tail]
  omega

theorem Future.sized {input : List UInt64} {s : State} {position : StreamPosition}
    {processed : List UInt64} (future : Future input s position processed) : Sized s := by
  have inv := future.inv
  have carry : s.carry.data.size < 56 := by
    cases eof : s.eof with
    | false => exact (future.reading eof).2
    | true => have := (future.ended eof).2; omega
  exact ⟨inv.oidSize, inv.acctSize, inv.qtySize, inv.lvlSize, inv.nxtSize, inv.headSize,
    inv.tailSize, carry, future.outputSize⟩

/-- A step under `StreamProgress` that stops returns the state it started from. -/
theorem step_stopped_state {host : Host World} {rep : Ghost → World → Prop}
    {unread zeroWrites : Ghost → Nat}
    (progress : Demos.StreamFold.StreamProgress host rep unread zeroWrites)
    {s : State} {ghost : Ghost} {world final : World} {trace : List Event}
    {next : ProcessStep State} (ready : rep ghost world) (safe : Safe s)
    (execution : LeanExe.Wasi.Exec host (step s) world trace (.returned next) final)
    (stopped : next.running = false) : next.state = s := by
  by_cases pending : s.written < s.output.size
  · rw [step_write pending] at execution
    change LeanExe.Wasi.Exec host
      (.write .stdout (remainingOutput s) fun reply => .pure (afterWrite s reply))
      world trace (.returned next) final at execution
    cases execution with
    | write_return operation continuation =>
        cases continuation
        obtain ⟨count, _, replyEq, _, _, _⟩ :=
          progress.write_reply ready (remainingOutput_nonempty safe pending) operation
        cases replyEq
        simp only [writeResult, ↓reduceIte] at stopped
        rw [(afterWrite_running s _).1] at stopped
        cases stopped
  · cases eof : s.eof with
    | false =>
        rw [step_read pending eof] at execution
        change LeanExe.Wasi.Exec host (.read 4096 fun reply => .pure (afterRead s reply))
          world trace (.returned next) final at execution
        cases execution with
        | read_reject capacity continuation =>
            exact False.elim ((by decide : ¬ 2 ^ 32 ≤ (4096 : UInt64).toNat) capacity)
        | read_return capacity operation continuation =>
            cases continuation
            obtain ⟨bytes, _, replyEq, _, _, _⟩ := progress.read_reply ready operation
            cases replyEq
            simp only [readResult, ↓reduceIte] at stopped
            rw [(afterRead_running s _).1] at stopped
            cases stopped
    | true =>
        rw [step_stop pending eof] at execution
        cases execution
        rfl

/-- Every state that a step from a state with the invariant returns, running or stopped, has the
sizes of `Sized`. -/
theorem step_sized {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {input : List UInt64}
    (ids : (Spec.records (leWords input)).length < 2 ^ 64 - 1)
    {s : State} {position : StreamPosition} {processed : List UInt64}
    {world final : World} {trace : List Event} {next : ProcessStep State}
    (represented : rep position world) (future : Future input s position processed)
    (execution : LeanExe.Wasi.Exec host (step s) world trace (.returned next) final) :
    Sized next.state := by
  cases running : next.running with
  | true =>
      obtain ⟨_, _, continued, _⟩ := future_step streams ids represented future execution
      obtain ⟨_, nextFuture⟩ := continued running
      exact nextFuture.sized
  | false =>
      rw [step_stopped_state streams.progress represented future.safe execution running]
      exact future.sized

end Demos.OrderBook.Process
