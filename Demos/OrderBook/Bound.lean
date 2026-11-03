import Demos.OrderBook.Verified
import Demos.OrderBook.ProcessBatch
import Demos.OrderBook.ProgramCounts

/-! The allocation bound of the order book's `run`.  `verified_compile` defines `run.bound`, the
number of bytes by which the module's `run` can raise the allocator's `top`, and states it through
the equations `bound_eq` and `cost_eq` of `run` and of the functions whose costs its cost includes:
`emit`, `fillArrays`, `submitArrays`, and `stepArrays`.  `Equations` states those equations for
any functions, so that `run_bound_le` applies to every compilation of the program that generates
them, and `compiled_run_bound` applies it to `Verified.compiled`.

`run_bound_le` bounds the bound on a book that satisfies `Refinement.Inv` and a stream of at most
`k` records by `runBoundOf k`.  The bound charges the credits of the book's seven arrays, 393,408
bytes, once before the loop and once at each record, and the credit of the event array at each
record.  Each word that a step pushes costs 80 bytes, and a cancelled remainder charges the event
array's credit once more.  A step on a book that satisfies the invariant gives at most 4,098 events
of seven words (`Spec.step_events_length`), so the event array holds at most `28,686 i` words
before record `i`.  `runBoundOf 74` is 2,712,680,536.

`run_bound_le_sized` bounds the bound on any book whose seven arrays have the program's sizes, and
any stream of at most `k` records, by `runBoundSized k`, without the invariant and without room for
the next ids.  It counts at most 5,122 events of seven words for each record from the program
(`Program.step_out_size`), where `run_bound_le` counts the specification's 4,098, and it keeps the
arrays' sizes through every step (`Program.step_sizes`).  The WASI process charges its read step
with it, because that charge holds for every reply that the host may give, so for a batch that
need not lie in the input and for a book whose next ids may leave no room for the batch.
`runBoundSized 74` is 3,383,146,584. -/

namespace Demos.OrderBook.Bound

open _root_.Verified (creditCost blockCost blockCost_eq loopCost paidGrowCost sumBelow
  sumBelow_succ')
open Refinement (Inv)

local notation "MovedArray" => LeanExe.Pipeline.Moved (Array UInt64)

/-- The equations that `verified_compile` generates for the bound of `run`, `runBound`, and the
costs of `run`, `stepArrays`, `submitArrays`, `fillArrays`, and `emit`. -/
structure Equations
    (emitCost : MovedArray × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 → Nat)
    (fillCost : MovedArray × MovedArray × MovedArray × MovedArray × MovedArray × MovedArray ×
      MovedArray × UInt64 × UInt64 × MovedArray × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 → Nat)
    (submitCost : MovedArray × MovedArray × MovedArray × MovedArray × MovedArray × MovedArray ×
      MovedArray × UInt64 × UInt64 × MovedArray × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
      UInt64 → Nat)
    (stepCost : MovedArray × MovedArray × MovedArray × MovedArray × MovedArray × MovedArray ×
      MovedArray × UInt64 × UInt64 × MovedArray × Array UInt64 × UInt64 → Nat)
    (runCost runBound : MovedArray × MovedArray × MovedArray × MovedArray × MovedArray ×
      MovedArray × MovedArray × UInt64 × UInt64 × Array UInt64 → Nat) : Prop where
  emit_cost : ∀ (out : Array UInt64) (w0 w1 w2 w3 w4 w5 w6 : UInt64),
    emitCost (⟨out⟩, w0, w1, w2, w3, w4, w5, w6) =
      paidGrowCost 1 + paidGrowCost 1 + paidGrowCost 1 + paidGrowCost 1 + paidGrowCost 1 +
        paidGrowCost 1 + paidGrowCost 1
  fill_cost : ∀ (oid acct qty lvl nxt head tail : Array UInt64) (nextId count : UInt64)
      (out : Array UInt64) (taker account side limit q : UInt64),
    fillCost (⟨oid⟩, ⟨acct⟩, ⟨qty⟩, ⟨lvl⟩, ⟨nxt⟩, ⟨head⟩, ⟨tail⟩, nextId, count, ⟨out⟩, taker,
        account, side, limit, q) =
      min
        (0 + 0 + 0 +
          loopCost (fun _ => 0)
            (fun (m : Program.Matching) =>
              m.rem != 0 && !m.selfTrade && Program.acceptable side limit m.price)
            (fun _ (b : Program.Matching) =>
              if (b.book.head[(Program.level (1 - side) b.price).toNat]! == 0) = true then 0
              else
                if (b.book.acct[b.book.head[(Program.level (1 - side) b.price).toNat]!.toNat]! ==
                    account) = true then 0
                else
                  creditCost b.out.size +
                    emitCost (⟨b.out⟩, 3,
                      b.book.oid[b.book.head[(Program.level (1 - side) b.price).toNat]!.toNat]!,
                      taker, b.price,
                      min b.rem
                        b.book.qty[b.book.head[(Program.level (1 - side) b.price).toNat]!.toNat]!,
                      b.book.acct[b.book.head[(Program.level (1 - side) b.price).toNat]!.toNat]!,
                      b.book.qty[b.book.head[(Program.level (1 - side) b.price).toNat]!.toNat]! -
                        min b.rem
                          b.book.qty[b.book.head[(Program.level (1 - side) b.price).toNat]!.toNat]!))
            (fun _ s => Program.matchStep taker account side s) Program.matchFuel.toNat 0
            ({ book :=
                { oid := oid, acct := acct, qty := qty, lvl := lvl, nxt := nxt, head := head,
                  tail := tail, nextId := nextId, count := count },
               out := out, price := if (side == 0) = true then 1 else Program.maxPrice, rem := q,
               selfTrade := false } : Program.Matching))
        (0 + 0 + 0 + 0 +
          loopCost (fun _ => 0)
            (fun (m : Program.Matching) =>
              m.rem != 0 && !m.selfTrade && Program.acceptable side limit m.price)
            (fun _ (b : Program.Matching) =>
              if (b.book.head[(Program.level (1 - side) b.price).toNat]! == 0) = true then 0
              else
                if (b.book.acct[b.book.head[(Program.level (1 - side) b.price).toNat]!.toNat]! ==
                    account) = true then 0
                else
                  emitCost (⟨b.out⟩, 3,
                    b.book.oid[b.book.head[(Program.level (1 - side) b.price).toNat]!.toNat]!,
                    taker, b.price,
                    min b.rem
                      b.book.qty[b.book.head[(Program.level (1 - side) b.price).toNat]!.toNat]!,
                    b.book.acct[b.book.head[(Program.level (1 - side) b.price).toNat]!.toNat]!,
                    b.book.qty[b.book.head[(Program.level (1 - side) b.price).toNat]!.toNat]! -
                      min b.rem
                        b.book.qty[b.book.head[(Program.level (1 - side) b.price).toNat]!.toNat]!))
            (fun _ s => Program.matchStep taker account side s) Program.matchFuel.toNat 0
            ({ book :=
                { oid := oid, acct := acct, qty := qty, lvl := lvl, nxt := nxt, head := head,
                  tail := tail, nextId := nextId, count := count },
               out := out, price := if (side == 0) = true then 1 else Program.maxPrice, rem := q,
               selfTrade := false } : Program.Matching))
  submit_cost : ∀ (oid acct qty lvl nxt head tail : Array UInt64) (nextId count : UInt64)
      (out : Array UInt64) (side limit q account tag tif : UInt64),
    submitCost (⟨oid⟩, ⟨acct⟩, ⟨qty⟩, ⟨lvl⟩, ⟨nxt⟩, ⟨head⟩, ⟨tail⟩, nextId, count, ⟨out⟩, side,
        limit, q, account, tag, tif) =
      emitCost (⟨out⟩, 1, nextId, tag, 0, 0, 0, 0) +
          fillCost (⟨oid⟩, ⟨acct⟩, ⟨qty⟩, ⟨lvl⟩, ⟨nxt⟩, ⟨head⟩, ⟨tail⟩, nextId + 1, count,
            ⟨Program.emit out 1 nextId tag 0 0 0 0⟩, nextId, account, side, limit, q) +
        if (((Program.fillArrays oid acct qty lvl nxt head tail (nextId + 1) count
              (Program.emit out 1 nextId tag 0 0 0 0) nextId account side limit q).rem == 0) =
            true) then 0
        else
          if (Program.fillArrays oid acct qty lvl nxt head tail (nextId + 1) count
              (Program.emit out 1 nextId tag 0 0 0 0) nextId account side limit q).selfTrade =
              true then
            creditCost (Program.fillArrays oid acct qty lvl nxt head tail (nextId + 1) count
                (Program.emit out 1 nextId tag 0 0 0 0) nextId account side limit q).out.size +
              emitCost (⟨(Program.fillArrays oid acct qty lvl nxt head tail (nextId + 1) count
                  (Program.emit out 1 nextId tag 0 0 0 0) nextId account side limit q).out⟩, 4,
                nextId, (Program.fillArrays oid acct qty lvl nxt head tail (nextId + 1) count
                  (Program.emit out 1 nextId tag 0 0 0 0) nextId account side limit q).rem, 3, 0,
                0, 0)
          else
            if (tif == 1) = true then
              creditCost (Program.fillArrays oid acct qty lvl nxt head tail (nextId + 1) count
                  (Program.emit out 1 nextId tag 0 0 0 0) nextId account side limit q).out.size +
                emitCost (⟨(Program.fillArrays oid acct qty lvl nxt head tail (nextId + 1) count
                    (Program.emit out 1 nextId tag 0 0 0 0) nextId account side limit q).out⟩, 4,
                  nextId, (Program.fillArrays oid acct qty lvl nxt head tail (nextId + 1) count
                    (Program.emit out 1 nextId tag 0 0 0 0) nextId account side limit q).rem, 2, 0,
                  0, 0)
            else
              if (Program.fillArrays oid acct qty lvl nxt head tail (nextId + 1) count
                  (Program.emit out 1 nextId tag 0 0 0 0) nextId account side limit q).book.count <
                  Program.capacity then 0
              else
                creditCost (Program.fillArrays oid acct qty lvl nxt head tail (nextId + 1) count
                    (Program.emit out 1 nextId tag 0 0 0 0) nextId account side limit q).out.size +
                  emitCost (⟨(Program.fillArrays oid acct qty lvl nxt head tail (nextId + 1) count
                      (Program.emit out 1 nextId tag 0 0 0 0) nextId account side limit q).out⟩, 4,
                    nextId, (Program.fillArrays oid acct qty lvl nxt head tail (nextId + 1) count
                      (Program.emit out 1 nextId tag 0 0 0 0) nextId account side limit q).rem, 4,
                    0, 0, 0)
  step_cost : ∀ (oid acct qty lvl nxt head tail : Array UInt64) (nextId count : UInt64)
      (out ws : Array UInt64) (o : UInt64),
    stepCost (⟨oid⟩, ⟨acct⟩, ⟨qty⟩, ⟨lvl⟩, ⟨nxt⟩, ⟨head⟩, ⟨tail⟩, nextId, count, ⟨out⟩, ws, o) =
      if ws.size.toUInt64 - o < 7 then emitCost (⟨out⟩, 2, 0, 0, 1, 0, 0, 0)
      else
        if (Program.word ws o 0 == 1) = true then
          if 1 < Program.word ws o 1 then
            emitCost (⟨out⟩, 2, Program.word ws o 0, Program.word ws o 5, 3, 0, 0, 0)
          else
            if 2 < Program.word ws o 6 then
              emitCost (⟨out⟩, 2, Program.word ws o 0, Program.word ws o 5, 4, 0, 0, 0)
            else
              if (!Program.inRange 1 Program.maxPrice (Program.word ws o 2)) = true then
                emitCost (⟨out⟩, 2, Program.word ws o 0, Program.word ws o 5, 5, 0, 0, 0)
              else
                if (!Program.inRange 1 Program.maxQty (Program.word ws o 3)) = true then
                  emitCost (⟨out⟩, 2, Program.word ws o 0, Program.word ws o 5, 6, 0, 0, 0)
                else
                  if (Program.word ws o 6 == 2 &&
                      Program.crosses head (Program.word ws o 1) (Program.word ws o 2)) = true then
                    emitCost (⟨out⟩, 2, Program.word ws o 0, Program.word ws o 5, 9, 0, 0, 0)
                  else
                    submitCost (⟨oid⟩, ⟨acct⟩, ⟨qty⟩, ⟨lvl⟩, ⟨nxt⟩, ⟨head⟩, ⟨tail⟩, nextId, count,
                      ⟨out⟩, Program.word ws o 1, Program.word ws o 2, Program.word ws o 3,
                      Program.word ws o 4, Program.word ws o 5, Program.word ws o 6)
        else
          if (Program.word ws o 0 == 2) = true then
            if 1 < Program.word ws o 1 then
              emitCost (⟨out⟩, 2, Program.word ws o 0, Program.word ws o 4, 3, 0, 0, 0)
            else
              if (!Program.inRange 1 Program.maxQty (Program.word ws o 2)) = true then
                emitCost (⟨out⟩, 2, Program.word ws o 0, Program.word ws o 4, 6, 0, 0, 0)
              else
                submitCost (⟨oid⟩, ⟨acct⟩, ⟨qty⟩, ⟨lvl⟩, ⟨nxt⟩, ⟨head⟩, ⟨tail⟩, nextId, count,
                  ⟨out⟩, Program.word ws o 1,
                  if (Program.word ws o 1 == 0) = true then Program.maxPrice else 1,
                  Program.word ws o 2, Program.word ws o 3, Program.word ws o 4, 1)
          else
            if (Program.word ws o 0 == 3) = true then
              if (Program.findSlot oid (Program.word ws o 1) == 0) = true then
                emitCost (⟨out⟩, 2, Program.word ws o 0, Program.word ws o 1, 7, 0, 0, 0)
              else
                if (acct[(Program.findSlot oid (Program.word ws o 1)).toNat]! !=
                    Program.word ws o 2) = true then
                  emitCost (⟨out⟩, 2, Program.word ws o 0, Program.word ws o 1, 8, 0, 0, 0)
                else
                  emitCost (⟨out⟩, 4, Program.word ws o 1,
                    qty[(Program.findSlot oid (Program.word ws o 1)).toNat]!, 1, 0, 0, 0)
            else
              if (Program.word ws o 0 == 4) = true then
                if (Program.findSlot oid (Program.word ws o 1) == 0) = true then
                  emitCost (⟨out⟩, 2, Program.word ws o 0, Program.word ws o 1, 7, 0, 0, 0)
                else
                  if (acct[(Program.findSlot oid (Program.word ws o 1)).toNat]! !=
                      Program.word ws o 2) = true then
                    emitCost (⟨out⟩, 2, Program.word ws o 0, Program.word ws o 1, 8, 0, 0, 0)
                  else
                    if (!Program.inRange 1 Program.maxQty (Program.word ws o 3)) = true then
                      emitCost (⟨out⟩, 2, Program.word ws o 0, Program.word ws o 1, 6, 0, 0, 0)
                    else
                      if qty[(Program.findSlot oid (Program.word ws o 1)).toNat]! ≤
                          Program.word ws o 3 then
                        emitCost (⟨out⟩, 2, Program.word ws o 0, Program.word ws o 1, 10, 0, 0, 0)
                      else emitCost (⟨out⟩, 5, Program.word ws o 1, Program.word ws o 3, 0, 0, 0, 0)
              else emitCost (⟨out⟩, 2, Program.word ws o 0, 0, 2, 0, 0, 0)
  run_cost : ∀ (oid acct qty lvl nxt head tail : Array UInt64) (nextId count : UInt64)
      (ws : Array UInt64),
    runCost (⟨oid⟩, ⟨acct⟩, ⟨qty⟩, ⟨lvl⟩, ⟨nxt⟩, ⟨head⟩, ⟨tail⟩, nextId, count, ws) =
      blockCost (UInt64.toNat 0) +
        loopCost (fun _ => 0) (fun _ => true)
          (fun a (b : Program.Book × Array UInt64) =>
            creditCost b.1.oid.size +
                (creditCost b.1.acct.size +
                  (creditCost b.1.qty.size +
                    (creditCost b.1.lvl.size +
                      (creditCost b.1.nxt.size +
                        (creditCost b.1.head.size +
                          (creditCost b.1.tail.size + creditCost b.2.size)))))) +
              stepCost (⟨b.1.oid⟩, ⟨b.1.acct⟩, ⟨b.1.qty⟩, ⟨b.1.lvl⟩, ⟨b.1.nxt⟩, ⟨b.1.head⟩,
                ⟨b.1.tail⟩, b.1.nextId, b.1.count, ⟨b.2⟩, ws, 7 * a))
          (fun i (x : Program.Book × Array UInt64) =>
            match x with
            | (b, out) =>
              Program.stepArrays b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count out
                ws (7 * i))
          ((ws.size.toUInt64 + 6) / 7).toNat 0
          (({ oid := oid, acct := acct, qty := qty, lvl := lvl, nxt := nxt, head := head,
              tail := tail, nextId := nextId, count := count } : Program.Book), #[])
  run_bound : ∀ (oid acct qty lvl nxt head tail : Array UInt64) (nextId count : UInt64)
      (ws : Array UInt64),
    runBound (⟨oid⟩, ⟨acct⟩, ⟨qty⟩, ⟨lvl⟩, ⟨nxt⟩, ⟨head⟩, ⟨tail⟩, nextId, count, ws) =
      creditCost oid.size +
          (creditCost acct.size +
            (creditCost qty.size +
              (creditCost lvl.size + (creditCost nxt.size + (creditCost head.size +
                creditCost tail.size))))) +
        runCost (⟨oid⟩, ⟨acct⟩, ⟨qty⟩, ⟨lvl⟩, ⟨nxt⟩, ⟨head⟩, ⟨tail⟩, nextId, count, ws)

/-! ## The closed form -/

/-- The most event words of one record: `Spec.capacity + 2` events of seven words, the `accepted`
event, a trade with each resting order, and a cancellation. -/
def recordWords : Nat := 7 * (Spec.capacity + 2)

/-- The credits of the book's arrays: five arrays of 4,097 words and two of 2,048. -/
def bookCredit : Nat := 5 * creditCost 4097 + 2 * creditCost 2048

/-- The most that the pass of `run`'s loop for record `i`, counted from 0, charges: the book's
credits, the credit of an event array of at most `recordWords * i` words, 80 bytes for each word
that the step pushes, and the credit of the event array after the step, which a cancelled remainder
charges. -/
def recordBound (i : Nat) : Nat :=
  bookCredit + creditCost (recordWords * i) + 80 * recordWords + 16 * (recordWords * (i + 1))

/-- The bound of `run` on a stream of at most `k` records: the book's credits, the block of the
empty event array, and the sum of `recordBound i` for `i` below `k`, which is
`3,147,280 k + 458,976 k (k - 1)`. -/
def runBoundOf (k : Nat) : Nat := 393464 + 3147280 * k + 458976 * (k * (k - 1))

theorem sumBelow_recordBound : ∀ k, sumBelow recordBound k = 3147280 * k + 458976 * (k * (k - 1))
  | 0 => rfl
  | k + 1 => by
    rw [sumBelow, sumBelow_recordBound k]
    simp only [recordBound, recordWords, bookCredit, creditCost, Spec.capacity,
      Nat.add_sub_cancel]
    have h1 : (k + 1) * k = k * k + k := Nat.succ_mul k k
    have h2 : k * (k - 1) + k = k * k := by
      cases k with
      | zero => rfl
      | succ j => simp only [Nat.add_sub_cancel, Nat.mul_add_one]
    omega

theorem sumBelow_mono (f : Nat → Nat) {n : Nat} : ∀ {k : Nat}, n ≤ k → sumBelow f n ≤ sumBelow f k
  | 0, h => by
    have : n = 0 := Nat.le_zero.mp h
    subst this
    exact Nat.le_refl _
  | k + 1, h => by
    rcases Nat.lt_or_eq_of_le h with h | h
    · have : sumBelow f n ≤ sumBelow f k := sumBelow_mono f (by omega)
      simp only [sumBelow]
      omega
    · subst h
      exact Nat.le_refl _

/-- `runBoundOf 74`, for the largest batch of the process: a read of 4,096 bytes and a carry of
fewer than 56 bytes. -/
theorem runBoundOf_74 : runBoundOf 74 = 2712680536 := by decide

/-! ## Loops -/

/-- `loopCost_le` for an invariant that need hold only at the indices below the loop's count. -/
theorem loopCost_le_below {α : Type} {CA : α → Nat} {C : α → Bool} {BA : UInt64 → α → Nat}
    {F : UInt64 → α → α} (P : Nat → α → Prop) (cost : Nat → Nat) {n : Nat}
    (hcost : ∀ k s, k < n → P k s → CA s + (if C s then BA (UInt64.ofNat k) s else 0) ≤ cost k)
    (hstep : ∀ k s, k + 1 < n → P k s → C s = true → P (k + 1) (F (UInt64.ofNat k) s))
    {I : α} (hI : P 0 I) : loopCost CA C BA F n 0 I ≤ sumBelow cost n := by
  suffices h : ∀ m k s, k + m = n → P k s →
      loopCost CA C BA F m (UInt64.ofNat k) s ≤ sumBelow (fun j => cost (k + j)) m by
    simpa using h n 0 I (Nat.zero_add n) hI
  intro m
  induction m with
  | zero => intro _ _ _ _; simp [loopCost, sumBelow]
  | succ m ih =>
    intro k s hkm hP
    have hc := hcost k s (by omega) hP
    have hk : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
      omega
    rw [sumBelow_succ']
    cases hC : C s
    · simp only [loopCost, hC, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc ⊢
      omega
    · simp only [loopCost, hC, ↓reduceIte, Nat.add_zero] at hc ⊢
      have hrest : loopCost CA C BA F m (UInt64.ofNat k + 1) (F (UInt64.ofNat k) s) ≤
          sumBelow (fun j => cost (k + (j + 1))) m := by
        cases m with
        | zero => simp [loopCost, sumBelow]
        | succ m =>
          have hn := ih (k + 1) _ (by omega) (hstep k s (by omega) hP hC)
          rw [← hk] at hn
          have hsum : sumBelow (fun j => cost (k + 1 + j)) (m + 1) =
              sumBelow (fun j => cost (k + (j + 1))) (m + 1) := by
            congr 1; funext j; congr 1; omega
          omega
      omega

/-- A loop whose condition costs nothing, and whose body at each state that passes the condition
costs at most `c` times the growth of `g` along the step, costs at most `c` times the growth of `g`
along the loop. -/
theorem loopCost_go {α : Type} {C : α → Bool} {BA : UInt64 → α → Nat} {F : α → α}
    (g : α → Nat) (c : Nat) (h : ∀ i s, C s = true → BA i s + c * g s ≤ c * g (F s)) :
    ∀ (n : Nat) (i : UInt64) (s : α),
      loopCost (fun _ => 0) C BA (fun _ s => F s) n i s + c * g s ≤
        c * g (LeanExe.repeatWhile.go C F n s)
  | 0, _, _ => by simp [loopCost, LeanExe.repeatWhile.go]
  | n + 1, i, s => by
    have ih := loopCost_go g c h n (i + 1) (F s)
    cases hC : C s
    · simp only [loopCost, LeanExe.repeatWhile.go, hC, Bool.false_eq_true, ↓reduceIte,
        Nat.zero_add, Nat.le_refl]
    · have hs := h i s hC
      simp only [loopCost, LeanExe.repeatWhile.go, hC, ↓reduceIte, Nat.zero_add]
      omega

/-! ## Steps -/

theorem emit_size (out : Array UInt64) (w0 w1 w2 w3 w4 w5 w6 : UInt64) :
    (Program.emit out w0 w1 w2 w3 w4 w5 w6).size = out.size + 7 := by
  simp only [Program.emit, Array.size_push]

/-- A bound on an `if` of costs by an `if` of step results on the same condition, with any two
instances of its decidability. -/
theorem ite_bound {c : Prop} {d₁ d₂ : Decidable c} {A A' k : Nat}
    {B B' : Program.Book × Array UInt64} (h₁ : c → A + k ≤ 96 * B.2.size)
    (h₂ : ¬c → A' + k ≤ 96 * B'.2.size) :
    @ite Nat c d₁ A A' + k ≤ 96 * (@ite _ c d₂ B B').2.size := by
  by_cases hc : c
  · rw [@ite_eq_left c d₁ hc, @ite_eq_left c d₂ hc]
    exact h₁ hc
  · rw [@ite_eq_right c d₁ hc, @ite_eq_right c d₂ hc]
    exact h₂ hc

section

variable
  {emitCost : MovedArray × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 → Nat}
  {fillCost : MovedArray × MovedArray × MovedArray × MovedArray × MovedArray × MovedArray ×
    MovedArray × UInt64 × UInt64 × MovedArray × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 → Nat}
  {submitCost : MovedArray × MovedArray × MovedArray × MovedArray × MovedArray × MovedArray ×
    MovedArray × UInt64 × UInt64 × MovedArray × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
    UInt64 → Nat}
  {stepCost : MovedArray × MovedArray × MovedArray × MovedArray × MovedArray × MovedArray ×
    MovedArray × UInt64 × UInt64 × MovedArray × Array UInt64 × UInt64 → Nat}
  {runCost runBound : MovedArray × MovedArray × MovedArray × MovedArray × MovedArray ×
    MovedArray × MovedArray × UInt64 × UInt64 × Array UInt64 → Nat}
  (E : Equations emitCost fillCost submitCost stepCost runCost runBound)
include E

/-- An event costs seven words at 80 bytes each. -/
theorem emit_cost_eq (out : Array UInt64) (w0 w1 w2 w3 w4 w5 w6 : UInt64) :
    emitCost (⟨out⟩, w0, w1, w2, w3, w4, w5, w6) = 560 :=
  (E.emit_cost out w0 w1 w2 w3 w4 w5 w6).trans (by decide)

/-- Matching costs at most 80 bytes for each word that it pushes, by the loop that counts the
potential of the event array. -/
theorem fill_le (oid acct qty lvl nxt head tail : Array UInt64) (nextId count : UInt64)
    (out : Array UInt64) (taker account side limit q : UInt64) :
    fillCost (⟨oid⟩, ⟨acct⟩, ⟨qty⟩, ⟨lvl⟩, ⟨nxt⟩, ⟨head⟩, ⟨tail⟩, nextId, count, ⟨out⟩, taker,
        account, side, limit, q) + 80 * out.size ≤
      80 * (Program.fillArrays oid acct qty lvl nxt head tail nextId count out taker account side
        limit q).out.size := by
  rw [E.fill_cost]
  refine Nat.le_trans (Nat.add_le_add_right (Nat.min_le_right _ _) _) ?_
  simp only [Nat.zero_add]
  refine loopCost_go (fun m : Program.Matching => m.out.size) 80 ?_ _ _ _
  intro i m _
  simp only [Program.matchStep]
  repeat' split
  all_goals first
    | omega
    | (simp only [emit_cost_eq E, emit_size]; omega)

/-- An accepted order costs at most 80 bytes for each word that it pushes, and the credit of its
event words. -/
theorem submit_le (oid acct qty lvl nxt head tail : Array UInt64) (nextId count : UInt64)
    (out : Array UInt64) (side limit q account tag tif : UInt64) :
    submitCost (⟨oid⟩, ⟨acct⟩, ⟨qty⟩, ⟨lvl⟩, ⟨nxt⟩, ⟨head⟩, ⟨tail⟩, nextId, count, ⟨out⟩, side,
        limit, q, account, tag, tif) + 80 * out.size ≤
      96 * (Program.submitArrays oid acct qty lvl nxt head tail nextId count out side limit q
        account tag tif).2.size := by
  have hf := fill_le E oid acct qty lvl nxt head tail (nextId + 1) count
    (Program.emit out 1 nextId tag 0 0 0 0) nextId account side limit q
  rw [emit_size] at hf
  rw [E.submit_cost]
  simp only [Program.submitArrays, Program.submit, emit_cost_eq E]
  generalize Program.fillArrays oid acct qty lvl nxt head tail (nextId + 1) count
    (Program.emit out 1 nextId tag 0 0 0 0) nextId account side limit q = m at hf ⊢
  repeat' split
  all_goals first
    | omega
    | (simp only [emit_size, creditCost]; omega)

/-- A step costs at most 80 bytes for each word that it pushes, and the credit of its event
words. -/
theorem step_le (oid acct qty lvl nxt head tail : Array UInt64) (nextId count : UInt64)
    (out ws : Array UInt64) (o : UInt64) :
    stepCost (⟨oid⟩, ⟨acct⟩, ⟨qty⟩, ⟨lvl⟩, ⟨nxt⟩, ⟨head⟩, ⟨tail⟩, nextId, count, ⟨out⟩, ws, o) +
        80 * out.size ≤
      96 * (Program.stepArrays oid acct qty lvl nxt head tail nextId count out ws o).2.size := by
  rw [E.step_cost]
  simp only [Program.stepArrays, Program.step, Program.reject, Program.cancel, Program.reduce]
  repeat' first
    | exact submit_le E ..
    | (simp only [emit_cost_eq E, emit_size]; omega)
    | (refine ite_bound ?_ ?_ <;> intro _)

end

/-- A step at an offset inside the stream, on a book that satisfies the invariant while the next
id lies below 2^64 - 1, keeps the invariant, raises the next id by at most 1, and pushes at most
`recordWords` words. -/
theorem step_events {B : Program.Book} (h : Inv B) (hn : B.nextId.toNat < 2 ^ 64 - 1)
    (out ws : Array UInt64) (o : UInt64) (ho : o.toNat < ws.size) (hs : ws.size < 2 ^ 64) :
    Inv (Program.stepArrays B.oid B.acct B.qty B.lvl B.nxt B.head B.tail B.nextId B.count out ws
        o).1 ∧
      (Program.stepArrays B.oid B.acct B.qty B.lvl B.nxt B.head B.tail B.nextId B.count out ws
        o).1.nextId.toNat ≤ B.nextId.toNat + 1 ∧
      (Program.stepArrays B.oid B.acct B.qty B.lvl B.nxt B.head B.tail B.nextId B.count out ws
        o).2.size ≤ out.size + recordWords := by
  obtain ⟨i1, i2, i3⟩ := Refinement.step_eq h hn out ws o ho hs
  have e : Program.stepArrays B.oid B.acct B.qty B.lvl B.nxt B.head B.tail B.nextId B.count out
      ws o = Program.step B out ws o := rfl
  rw [e]
  refine ⟨i1, ?_, ?_⟩
  · have hid := Spec.step_nextId (Abstract.toSpec B) (Refinement.recordAt ws o.toNat)
    rw [← i2, Refinement.StreamLemmas.toSpec_nextId, Refinement.StreamLemmas.toSpec_nextId] at hid
    split at hid
    · rw [hid, UInt64.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]
      simp
    · rw [hid]
      omega
  · rw [i3, Array.size_append, Spec.encodeAll_size]
    have := Spec.step_events_length h.valid (Refinement.recordAt ws o.toNat)
    simp only [recordWords, Spec.capacity] at this ⊢
    omega

/-! ## The bound -/

/-- **The allocation bound of `run`.**  For any functions with the equations that
`verified_compile` generates, on a book that satisfies the invariant, and a stream of at most `k`
records whose next ids stay below 2^64 - 1, the bound of `run` is at most `runBoundOf k`. -/
theorem run_bound_le
    {emitCost : MovedArray × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 → Nat}
    {fillCost : MovedArray × MovedArray × MovedArray × MovedArray × MovedArray × MovedArray ×
      MovedArray × UInt64 × UInt64 × MovedArray × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 → Nat}
    {submitCost : MovedArray × MovedArray × MovedArray × MovedArray × MovedArray × MovedArray ×
      MovedArray × UInt64 × UInt64 × MovedArray × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
      UInt64 → Nat}
    {stepCost : MovedArray × MovedArray × MovedArray × MovedArray × MovedArray × MovedArray ×
      MovedArray × UInt64 × UInt64 × MovedArray × Array UInt64 × UInt64 → Nat}
    {runCost runBound : MovedArray × MovedArray × MovedArray × MovedArray × MovedArray ×
      MovedArray × MovedArray × UInt64 × UInt64 × Array UInt64 → Nat}
    (E : Equations emitCost fillCost submitCost stepCost runCost runBound)
    {b : Program.Book} (inv : Inv b) (ws : Array UInt64) (hs : ws.size + 6 < 2 ^ 64)
    (hn : b.nextId.toNat + (ws.size + 6) / 7 ≤ 2 ^ 64 - 1) {k : Nat}
    (hk : (ws.size + 6) / 7 ≤ k) :
    runBound (⟨b.oid⟩, ⟨b.acct⟩, ⟨b.qty⟩, ⟨b.lvl⟩, ⟨b.nxt⟩, ⟨b.head⟩, ⟨b.tail⟩, b.nextId, b.count,
      ws) ≤ runBoundOf k := by
  rw [E.run_bound, E.run_cost, Refinement.StreamLemmas.count_toNat ws hs]
  refine Nat.le_trans (Nat.add_le_add_left (Nat.add_le_add_left (loopCost_le_below
    (fun j (s : Program.Book × Array UInt64) =>
      Inv s.1 ∧ s.1.nextId.toNat ≤ b.nextId.toNat + j ∧ s.2.size ≤ recordWords * j)
    recordBound ?hcost ?hstep ?hI) _) _) ?_
  case hcost =>
    intro j s hj hP
    obtain ⟨B, out⟩ := s
    obtain ⟨hinv, hid, hsize⟩ := hP
    dsimp only at hinv hid hsize ⊢
    have ho : (7 * UInt64.ofNat j).toNat = 7 * j :=
      Refinement.StreamLemmas.toNat_seven_mul j (by omega)
    have hst := step_le E B.oid B.acct B.qty B.lvl B.nxt B.head B.tail B.nextId B.count out ws
      (7 * UInt64.ofNat j)
    have hev := (step_events hinv (by omega) out ws (7 * UInt64.ofNat j) (by omega)
      (by omega)).2.2
    simp only [↓reduceIte, Nat.zero_add, hinv.oidSize, hinv.acctSize, hinv.qtySize,
      hinv.lvlSize, hinv.nxtSize, hinv.headSize, hinv.tailSize, creditCost, recordBound,
      recordWords, bookCredit, Spec.capacity] at hev hsize ⊢
    omega
  case hstep =>
    intro j s hj hP _
    obtain ⟨B, out⟩ := s
    obtain ⟨hinv, hid, hsize⟩ := hP
    dsimp only at hinv hid hsize ⊢
    have ho : (7 * UInt64.ofNat j).toNat = 7 * j :=
      Refinement.StreamLemmas.toNat_seven_mul j (by omega)
    obtain ⟨i1, i2, i3⟩ :=
      step_events hinv (by omega) out ws (7 * UInt64.ofNat j) (by omega) (by omega)
    refine ⟨i1, by omega, ?_⟩
    simp only [recordWords, Spec.capacity] at i3 hsize ⊢
    omega
  case hI => exact ⟨inv, by simp, by simp⟩
  have hm := sumBelow_mono recordBound hk
  rw [sumBelow_recordBound k] at hm
  simp only [inv.oidSize, inv.acctSize, inv.qtySize, inv.lvlSize, inv.nxtSize, inv.headSize,
    inv.tailSize, creditCost, blockCost_eq, UInt64.toNat_zero, runBoundOf]
  omega

/-! ## The bound on any book of the program's sizes -/

/-- The most event words of one record on any book: 5,122 events of seven words, the `accepted`
event, a trade at each of matching's 5,120 iterations, and a final event
(`Program.step_out_size`). -/
def anyRecordWords : Nat := 7 * 5122

/-- The most that the pass of `run`'s loop for record `i`, counted from 0, charges on a book whose
arrays have the program's sizes: the book's credits, the credit of an event array of at most
`anyRecordWords * i` words, and the step's cost, which `step_le` bounds by 96 bytes for each word
after the step less 80 bytes for each word before it. -/
def sizedRecordBound (i : Nat) : Nat :=
  bookCredit + creditCost (anyRecordWords * i) + 96 * anyRecordWords + 16 * (anyRecordWords * i)

/-- The bound of `run` on a stream of at most `k` records from a book whose arrays have the
program's sizes: the book's credits, the block of the empty event array, and the sum of
`sizedRecordBound i` for `i` below `k`, which is `3,835,408 k + 573,664 k (k - 1)`. -/
def runBoundSized (k : Nat) : Nat := 393464 + 3835408 * k + 573664 * (k * (k - 1))

theorem sumBelow_sizedRecordBound :
    ∀ k, sumBelow sizedRecordBound k = 3835408 * k + 573664 * (k * (k - 1))
  | 0 => rfl
  | k + 1 => by
    rw [sumBelow, sumBelow_sizedRecordBound k]
    simp only [sizedRecordBound, anyRecordWords, bookCredit, creditCost, Nat.add_sub_cancel]
    have h1 : (k + 1) * k = k * k + k := Nat.succ_mul k k
    have h2 : k * (k - 1) + k = k * k := by
      cases k with
      | zero => rfl
      | succ j => simp only [Nat.add_sub_cancel, Nat.mul_add_one]
    omega

/-- `runBoundSized 74`, for the largest batch of the process: a read of 4,096 bytes and a carry of
fewer than 56 bytes. -/
theorem runBoundSized_74 : runBoundSized 74 = 3383146584 := by decide

/-- **The allocation bound of `run` on any book of the program's sizes.**  For any functions with
the equations that `verified_compile` generates, on a book whose seven arrays have the sizes of the
program, and a stream of at most `k` records, the bound of `run` is at most `runBoundSized k`.  The
theorem needs neither the invariant nor room for the next ids, since it counts the events of a
record from the program, and every step keeps the arrays' sizes (`Program.step_sizes`). -/
theorem run_bound_le_sized
    {emitCost : MovedArray × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 → Nat}
    {fillCost : MovedArray × MovedArray × MovedArray × MovedArray × MovedArray × MovedArray ×
      MovedArray × UInt64 × UInt64 × MovedArray × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 → Nat}
    {submitCost : MovedArray × MovedArray × MovedArray × MovedArray × MovedArray × MovedArray ×
      MovedArray × UInt64 × UInt64 × MovedArray × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
      UInt64 → Nat}
    {stepCost : MovedArray × MovedArray × MovedArray × MovedArray × MovedArray × MovedArray ×
      MovedArray × UInt64 × UInt64 × MovedArray × Array UInt64 × UInt64 → Nat}
    {runCost runBound : MovedArray × MovedArray × MovedArray × MovedArray × MovedArray ×
      MovedArray × MovedArray × UInt64 × UInt64 × Array UInt64 → Nat}
    (E : Equations emitCost fillCost submitCost stepCost runCost runBound)
    {b : Program.Book}
    (hsizes : Program.sizes b = (4097, 4097, 4097, 4097, 4097, 2048, 2048))
    (ws : Array UInt64) (hs : ws.size + 6 < 2 ^ 64) {k : Nat} (hk : (ws.size + 6) / 7 ≤ k) :
    runBound (⟨b.oid⟩, ⟨b.acct⟩, ⟨b.qty⟩, ⟨b.lvl⟩, ⟨b.nxt⟩, ⟨b.head⟩, ⟨b.tail⟩, b.nextId, b.count,
      ws) ≤ runBoundSized k := by
  rw [E.run_bound, E.run_cost, Refinement.StreamLemmas.count_toNat ws hs]
  refine Nat.le_trans (Nat.add_le_add_left (Nat.add_le_add_left (loopCost_le_below
    (fun j (s : Program.Book × Array UInt64) =>
      Program.sizes s.1 = (4097, 4097, 4097, 4097, 4097, 2048, 2048) ∧
        s.2.size ≤ anyRecordWords * j)
    sizedRecordBound ?hcost ?hstep ?hI) _) _) ?_
  case hcost =>
    intro j s _ hP
    obtain ⟨B, out⟩ := s
    obtain ⟨hsz, hsize⟩ := hP
    dsimp only at hsz hsize ⊢
    have hst := step_le E B.oid B.acct B.qty B.lvl B.nxt B.head B.tail B.nextId B.count out ws
      (7 * UInt64.ofNat j)
    have hev : (Program.stepArrays B.oid B.acct B.qty B.lvl B.nxt B.head B.tail B.nextId B.count
        out ws (7 * UInt64.ofNat j)).2.size ≤ out.size + 7 * 5122 :=
      Program.step_out_size B out ws (7 * UInt64.ofNat j)
    simp only [Program.sizes, Prod.mk.injEq] at hsz
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hsz
    simp only [↓reduceIte, Nat.zero_add, h1, h2, h3, h4, h5, h6, h7, creditCost, sizedRecordBound,
      anyRecordWords, bookCredit] at hsize ⊢
    omega
  case hstep =>
    intro j s _ hP _
    obtain ⟨B, out⟩ := s
    obtain ⟨hsz, hsize⟩ := hP
    dsimp only at hsz hsize ⊢
    have hev : (Program.stepArrays B.oid B.acct B.qty B.lvl B.nxt B.head B.tail B.nextId B.count
        out ws (7 * UInt64.ofNat j)).2.size ≤ out.size + 7 * 5122 :=
      Program.step_out_size B out ws (7 * UInt64.ofNat j)
    refine ⟨(Program.step_sizes B out ws (7 * UInt64.ofNat j)).trans hsz, ?_⟩
    simp only [anyRecordWords] at hsize ⊢
    omega
  case hI => exact ⟨hsizes, by simp⟩
  have hm := sumBelow_mono sizedRecordBound hk
  rw [sumBelow_sizedRecordBound k] at hm
  simp only [Program.sizes, Prod.mk.injEq] at hsizes
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hsizes
  simp only [h1, h2, h3, h4, h5, h6, h7, creditCost, blockCost_eq, UInt64.toNat_zero,
    runBoundSized]
  omega

/-! ## The compiled program -/

/-- The equations of `Verified.compiled`. -/
theorem compiled_equations : Equations Verified.compiled.emit.cost
    Verified.compiled.fillArrays.cost Verified.compiled.submitArrays.cost
    Verified.compiled.stepArrays.cost Verified.compiled.run.cost Verified.compiled.run.bound :=
  ⟨Verified.compiled.emit.cost_eq, Verified.compiled.fillArrays.cost_eq,
    Verified.compiled.submitArrays.cost_eq, Verified.compiled.stepArrays.cost_eq,
    Verified.compiled.run.cost_eq, Verified.compiled.run.bound_eq⟩

/-- The bound of `Verified.compiled`'s `run` on a book that satisfies the invariant and a stream of
at most `k` records is at most `runBoundOf k`. -/
theorem compiled_run_bound {b : Program.Book} (inv : Inv b) (ws : Array UInt64)
    (hs : ws.size + 6 < 2 ^ 64) (hn : b.nextId.toNat + (ws.size + 6) / 7 ≤ 2 ^ 64 - 1) {k : Nat}
    (hk : (ws.size + 6) / 7 ≤ k) :
    Verified.compiled.run.bound (⟨b.oid⟩, ⟨b.acct⟩, ⟨b.qty⟩, ⟨b.lvl⟩, ⟨b.nxt⟩, ⟨b.head⟩,
      ⟨b.tail⟩, b.nextId, b.count, ws) ≤ runBoundOf k :=
  run_bound_le compiled_equations inv ws hs hn hk

/-- The bound of `Verified.compiled`'s `run` on a book whose arrays have the program's sizes and a
stream of at most `k` records is at most `runBoundSized k`. -/
theorem compiled_run_bound_sized {b : Program.Book}
    (hsizes : Program.sizes b = (4097, 4097, 4097, 4097, 4097, 2048, 2048)) (ws : Array UInt64)
    (hs : ws.size + 6 < 2 ^ 64) {k : Nat} (hk : (ws.size + 6) / 7 ≤ k) :
    Verified.compiled.run.bound (⟨b.oid⟩, ⟨b.acct⟩, ⟨b.qty⟩, ⟨b.lvl⟩, ⟨b.nxt⟩, ⟨b.head⟩,
      ⟨b.tail⟩, b.nextId, b.count, ws) ≤ runBoundSized k :=
  run_bound_le_sized compiled_equations hsizes ws hs hk

#print axioms run_bound_le
#print axioms compiled_run_bound
#print axioms runBoundOf_74
#print axioms run_bound_le_sized
#print axioms compiled_run_bound_sized
#print axioms runBoundSized_74

end Demos.OrderBook.Bound
