import Demos.OrderBook.Process
import Demos.OrderBook.Refinement

/-! The batch lemma of [the process](Process.lean).  `batch_refines` states that one call of
`Program.run` on a batch of words, from a book that represents the specification's book after a
whole number of records, keeps the invariant, represents the specification's book after the batch,
and appends the event words of the batch.  It applies `Refinement.run_eq` and joins the batch to
the earlier words with `Spec.run_append`, and `Spec.run_nextId_le` supplies the next-id premise of
`run_eq` from a bound on the number of records. -/

namespace Demos.OrderBook.Spec

/-- Each record of a fold of `runStep` advances the next id by at most 1. -/
theorem foldl_nextId_le (rs : List (Array UInt64)) (b : Book) (es : List Event)
    (hn : b.nextId.toNat + rs.length ≤ 2 ^ 64 - 1) :
    (rs.foldl runStep (b, es)).1.nextId.toNat ≤ b.nextId.toNat + rs.length := by
  induction rs generalizing b es with
  | nil => simp
  | cons r rs ih =>
    simp only [List.foldl_cons, runStep]
    simp only [List.length_cons] at hn ⊢
    have once : (step b r).1.nextId.toNat ≤ b.nextId.toNat + 1 := by
      have := step_nextId b r
      split at this <;> rw [this]
      · rw [UInt64.toNat_add]
        exact Nat.le_trans (Nat.mod_le _ _) (by simp)
      · omega
    have rest := ih (step b r).1 (es ++ (step b r).2) (by omega)
    omega

/-- The next id after a run is at most the next id before it plus the number of records. -/
theorem run_nextId_le (b : Book) (ws : List UInt64)
    (hn : b.nextId.toNat + (records ws).length ≤ 2 ^ 64 - 1) :
    (run b ws).1.nextId.toNat ≤ b.nextId.toNat + (records ws).length := by
  rw [run_eq]
  exact foldl_nextId_le _ _ _ hn

/-- Each record of a fold of `runStep` on a valid book adds at most `capacity + 2` events. -/
theorem foldl_events_length (rs : List (Array UInt64)) (b : Book) (es : List Event)
    (h : Valid b) (hn : b.nextId.toNat + rs.length ≤ 2 ^ 64 - 1) :
    (rs.foldl runStep (b, es)).2.length ≤ es.length + rs.length * (capacity + 2) := by
  induction rs generalizing b es with
  | nil => simp
  | cons r rs ih =>
    simp only [List.foldl_cons, runStep]
    simp only [List.length_cons] at hn ⊢
    have hn' : b.nextId.toNat < 2 ^ 64 - 1 := by omega
    have once : (step b r).1.nextId.toNat ≤ b.nextId.toNat + 1 := by
      have := step_nextId b r
      split at this <;> rw [this]
      · rw [UInt64.toNat_add]
        exact Nat.le_trans (Nat.mod_le _ _) (by simp)
      · omega
    have rest := ih (step b r).1 (es ++ (step b r).2) (step_valid h hn' r) (by omega)
    have here := step_events_length h r
    simp only [List.length_append, capacity] at rest here ⊢
    omega

/-- A run on a valid book gives at most `capacity + 2` events for each record. -/
theorem run_events_length {b : Book} (h : Valid b) (ws : List UInt64)
    (hn : b.nextId.toNat + (records ws).length ≤ 2 ^ 64 - 1) :
    (run b ws).2.length ≤ (records ws).length * (capacity + 2) := by
  rw [run_eq]
  simpa using foldl_events_length _ _ [] h hn

/-- Each event has seven words. -/
theorem encodeAll_size (es : List Event) : (encodeAll es).size = 7 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have single : (encodeAll [e]).size = 7 := by simp [encodeAll, encode_size]
    rw [show e :: es = [e] ++ es from rfl, Refinement.StreamLemmas.encodeAll_append,
      Array.size_append, ih, single, List.length_append, List.length_singleton]
    omega

end Demos.OrderBook.Spec

namespace Demos.OrderBook.Process

open Refinement Abstract

/-- The book of the process's state. -/
def book (s : State) : Program.Book :=
  ⟨s.oid, s.acct, s.qty, s.lvl, s.nxt, s.head, s.tail, s.nextId, s.count⟩

theorem book_mk (b : Program.Book) (carry output : LeanExe.Bytes) (written : UInt64) (eof : Bool) :
    book ⟨b.oid, b.acct, b.qty, b.lvl, b.nxt, b.head, b.tail, b.nextId, b.count, carry, output,
      written, eof⟩ = b := rfl

theorem book_initial : book initial = Program.init () := by
  simp only [book, initial, Program.init]

/-- One call of `run` on the words `ws`, from a book that represents the specification's book after
the words `p`, a whole number of records, keeps the invariant, represents the specification's book
after `p` followed by `ws`, appends the event words of the batch, and gives at most
`capacity + 2` events for each record of the batch. -/
theorem batch_refines {B : Program.Book} (inv : Inv B) {p : List UInt64}
    (bookEq : toSpec B = (Spec.run Spec.empty p).1) (whole : p.length % 7 = 0)
    (ws : Array UInt64) (small : ws.size + 6 < 2 ^ 64)
    (ids : (Spec.records (p ++ ws.toList)).length < 2 ^ 64 - 1) :
    let r := Program.run B.oid B.acct B.qty B.lvl B.nxt B.head B.tail B.nextId B.count ws
    Inv r.1 ∧ toSpec r.1 = (Spec.run Spec.empty (p ++ ws.toList)).1 ∧
      Spec.encodeAll (Spec.run Spec.empty p).2 ++ r.2 =
        Spec.encodeAll (Spec.run Spec.empty (p ++ ws.toList)).2 ∧
      r.2.size ≤ 7 * ((ws.size + 6) / 7 * (Spec.capacity + 2)) := by
  have records : (Spec.records (p ++ ws.toList)).length =
      (Spec.records p).length + (ws.size + 6) / 7 := by
    rw [Spec.records_append _ _ whole, List.length_append, Spec.records_length ws.toList,
      Array.length_toList (xs := ws)]
  have nextId : B.nextId = (Spec.run Spec.empty p).1.nextId := by
    rw [← StreamLemmas.toSpec_nextId, bookEq]
  have nextLe := Spec.run_nextId_le Spec.empty p (by
    change (1 : UInt64).toNat + _ ≤ _
    simp only [UInt64.toNat_one]
    omega)
  change _ ≤ (1 : UInt64).toNat + _ at nextLe
  simp only [UInt64.toNat_one] at nextLe
  have hn : B.nextId.toNat + (ws.size + 6) / 7 ≤ 2 ^ 64 - 1 := by
    rw [nextId]
    omega
  have valid : Spec.Valid (toSpec B) := inv.valid
  have events := Spec.run_events_length valid ws.toList (by
    rw [StreamLemmas.toSpec_nextId, Spec.records_length, Array.length_toList (xs := ws)]
    exact hn)
  rw [Spec.records_length, Array.length_toList (xs := ws)] at events
  obtain ⟨i1, i2, i3⟩ := run_eq inv ws small hn
  dsimp only
  generalize Program.run B.oid B.acct B.qty B.lvl B.nxt B.head B.tail B.nextId B.count ws = r
    at i1 i2 i3 ⊢
  rw [bookEq] at i2 i3 events
  refine ⟨i1, ?_, ?_, ?_⟩
  · rw [i2, Spec.run_append _ _ _ whole]
  · rw [i3, Spec.run_append _ _ _ whole, StreamLemmas.encodeAll_append]
  · rw [i3, Spec.encodeAll_size]
    exact Nat.mul_le_mul_left 7 events

end Demos.OrderBook.Process
