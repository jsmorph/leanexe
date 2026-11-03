import Demos.OrderBook.Program

/-! Counts over [the program](Program.lean) that hold on every book, without the representation
invariant.  A record adds at most 5,122 events of seven words to the event words of `run`: the
accepted event, at most one trade for each of the 5,120 iterations of matching, and a final event.
Every step keeps the sizes of the book's seven arrays, since the program changes them only with
`set!`.  The process's charges and the closed form of `run`'s bound that they use depend on these
counts, because the charge of a read step holds for every reply, so for a batch that need not lie
in the input and for a book whose next ids may leave no room for it. -/

namespace Demos.OrderBook.Program

/-- An iteration of matching adds at most one event. -/
theorem matchStep_out_size (taker account side : UInt64) (m : Matching) :
    (matchStep taker account side m).out.size ≤ m.out.size + 7 := by
  unfold matchStep
  dsimp only
  split
  · simp
  · split
    · simp
    · simp only [emit, Array.size_push]
      omega

theorem repeatWhile_out_size (fuel : UInt64) (init : Matching) (cond : Matching → Bool)
    (f : Matching → Matching) (grows : ∀ m, (f m).out.size ≤ m.out.size + 7) :
    (LeanExe.repeatWhile fuel init cond f).out.size ≤ init.out.size + 7 * fuel.toNat := by
  unfold LeanExe.repeatWhile
  generalize fuel.toNat = steps
  induction steps generalizing init with
  | zero => simp [LeanExe.repeatWhile.go]
  | succ steps ih =>
      simp only [LeanExe.repeatWhile.go]
      split
      · have rest := ih (f init)
        have once := grows init
        omega
      · omega

/-- Matching adds at most 5,120 events. -/
theorem fillArrays_out_size (oid acct qty lvl nxt head tail : Array UInt64) (nextId count : UInt64)
    (out : Array UInt64) (taker account side limit q : UInt64) :
    (fillArrays oid acct qty lvl nxt head tail nextId count out taker account side limit
      q).out.size ≤ out.size + 7 * 5120 := by
  unfold fillArrays fill
  exact repeatWhile_out_size matchFuel _ _ _ (matchStep_out_size taker account side)

/-- An accepted order adds at most 5,122 events: its `accepted` event, its trades, and a final
cancellation. -/
theorem submitArrays_out_size (oid acct qty lvl nxt head tail : Array UInt64)
    (nextId count : UInt64) (out : Array UInt64) (side limit q account tag tif : UInt64) :
    (submitArrays oid acct qty lvl nxt head tail nextId count out side limit q account tag
      tif).2.size ≤ out.size + 7 * 5122 := by
  have fill := fillArrays_out_size oid acct qty lvl nxt head tail (nextId + 1) count
    (emit out 1 nextId tag 0 0 0 0) nextId account side limit q
  have emitted : (emit out 1 nextId tag 0 0 0 0).size = out.size + 7 := by
    simp only [emit, Array.size_push]
  unfold submitArrays submit
  dsimp only
  generalize fillArrays oid acct qty lvl nxt head tail (nextId + 1) count
    (emit out 1 nextId tag 0 0 0 0) nextId account side limit q = m at fill ⊢
  repeat' split
  all_goals (try simp only [emit, Array.size_push]); omega

set_option maxHeartbeats 1000000 in
/-- A record adds at most 5,122 events. -/
theorem step_out_size (b : Book) (out ws : Array UInt64) (o : UInt64) :
    (step b out ws o).2.size ≤ out.size + 7 * 5122 := by
  unfold step
  dsimp only [reject, cancel, reduce]
  repeat' split
  all_goals first
    | (simp only [emit, Array.size_push]; omega)
    | exact submitArrays_out_size _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem fold_out_size {β : Type} (F : UInt64 → β × Array UInt64 → β × Array UInt64) (c : Nat)
    (grows : ∀ i state, (F i state).2.size ≤ state.2.size + c) (init : β × Array UInt64) :
    ∀ count : Nat,
      (Nat.fold count (fun i _ state => F (UInt64.ofNat i) state) init).2.size ≤
        init.2.size + c * count
  | 0 => by simp
  | count + 1 => by
      have rest := fold_out_size F c grows init count
      have once := grows (UInt64.ofNat count)
        (Nat.fold count (fun i _ state => F (UInt64.ofNat i) state) init)
      rw [Nat.fold_succ, Nat.mul_succ]
      omega

theorem loop_out_size {β : Type} (count : UInt64) (init : β × Array UInt64)
    (F : UInt64 → β × Array UInt64 → β × Array UInt64) (c : Nat)
    (grows : ∀ i state, (F i state).2.size ≤ state.2.size + c) :
    (LeanExe.loop count init F).2.size ≤ init.2.size + c * count.toNat :=
  fold_out_size F c grows init count.toNat

/-- `run` gives at most 5,122 events for each record, from any book. -/
theorem run_out_size (oid acct qty lvl nxt head tail : Array UInt64) (nextId count : UInt64)
    (ws : Array UInt64) :
    (run oid acct qty lvl nxt head tail nextId count ws).2.size ≤
      7 * 5122 * ((ws.size.toUInt64 + 6) / 7).toNat := by
  unfold run
  refine Nat.le_trans (loop_out_size _ _ _ (7 * 5122) ?_) ?_
  · intro i state
    obtain ⟨b, out⟩ := state
    exact step_out_size _ _ _ _
  · simp

/-! ## Array sizes -/

/-- The sizes of a book's seven arrays. -/
def sizes (b : Book) : Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (b.oid.size, b.acct.size, b.qty.size, b.lvl.size, b.nxt.size, b.head.size, b.tail.size)

theorem unlink_sizes (b : Book) (lv pr s : UInt64) : sizes (unlink b lv pr s) = sizes b := by
  unfold unlink sizes
  dsimp only
  repeat' split
  all_goals simp only [Array.size_set!]

theorem place_sizes (b : Book) (side price id account q : UInt64) :
    sizes (place b side price id account q) = sizes b := by
  unfold place sizes
  dsimp only
  repeat' split
  all_goals simp only [Array.size_set!]

theorem matchStep_sizes (taker account side : UInt64) (m : Matching) :
    sizes (matchStep taker account side m).book = sizes m.book := by
  unfold matchStep
  dsimp only
  split
  · rfl
  · split
    · rfl
    · dsimp only
      split
      · exact unlink_sizes _ _ _ _
      · simp only [sizes, Array.size_set!]

theorem repeatWhile_sizes (fuel : UInt64) (init : Matching) (cond : Matching → Bool)
    (f : Matching → Matching) (keeps : ∀ m, sizes (f m).book = sizes m.book) :
    sizes (LeanExe.repeatWhile fuel init cond f).book = sizes init.book := by
  unfold LeanExe.repeatWhile
  generalize fuel.toNat = steps
  induction steps generalizing init with
  | zero => rfl
  | succ steps ih =>
      simp only [LeanExe.repeatWhile.go]
      split
      · rw [ih (f init), keeps init]
      · rfl

theorem fillArrays_sizes (oid acct qty lvl nxt head tail : Array UInt64) (nextId count : UInt64)
    (out : Array UInt64) (taker account side limit q : UInt64) :
    sizes (fillArrays oid acct qty lvl nxt head tail nextId count out taker account side limit
      q).book = sizes ⟨oid, acct, qty, lvl, nxt, head, tail, nextId, count⟩ := by
  unfold fillArrays fill
  exact repeatWhile_sizes matchFuel _ _ _ (matchStep_sizes taker account side)

theorem submitArrays_sizes (oid acct qty lvl nxt head tail : Array UInt64) (nextId count : UInt64)
    (out : Array UInt64) (side limit q account tag tif : UInt64) :
    sizes (submitArrays oid acct qty lvl nxt head tail nextId count out side limit q account tag
      tif).1 = sizes ⟨oid, acct, qty, lvl, nxt, head, tail, nextId, count⟩ := by
  have fill := fillArrays_sizes oid acct qty lvl nxt head tail (nextId + 1) count
    (emit out 1 nextId tag 0 0 0 0) nextId account side limit q
  unfold submitArrays submit
  dsimp only
  generalize fillArrays oid acct qty lvl nxt head tail (nextId + 1) count
    (emit out 1 nextId tag 0 0 0 0) nextId account side limit q = m at fill ⊢
  repeat' split
  all_goals first
    | exact fill
    | exact (place_sizes _ _ _ _ _ _).trans fill
    | exact fill.trans rfl

set_option maxHeartbeats 1000000 in
/-- A record keeps the sizes of the book's seven arrays. -/
theorem step_sizes (b : Book) (out ws : Array UInt64) (o : UInt64) :
    sizes (step b out ws o).1 = sizes b := by
  unfold step
  dsimp only [reject, cancel, reduce]
  repeat' split
  all_goals first
    | (simp only [sizes, Array.size_set!]; done)
    | exact unlink_sizes _ _ _ _
    | exact submitArrays_sizes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end Demos.OrderBook.Program
