import Demos.OrderBook.Verified
import Demos.OrderBook.Refinement
import Verified.Call

/-! The calls of the verified order book's exports `run` and `top` from a ready store, the state
that `Verified.Ready` describes.  `run` consumes the book's seven arrays, so `run_call` starts from
`compiled.run.trapFree` rather than from `Verified.Call`, whose arguments move no object, and
composes it with `Refinement.run_eq`: called with the book's arrays moved in, a borrowed stream,
and room for `compiled.run.bound`, the export returns without a trap a book that satisfies `Inv`,
whose `toSpec` is the book of `Spec.run`, and the words `Spec.encodeAll` of its events.
`top_call` composes `compiled.top.trapFree`, through `Verified.Call.spec`, with
`Refinement.top_eq`: the export returns the four words of `Spec.top`.

Both theorems take room for the bounds that `verified_compile` generates, so they hold for any
bound that the compiler states.  The generated bound of `run` charges, at each record, the credits
of the seven book arrays and of the event array, 393,424 bytes and 16 bytes for each event word so
far, and, at each trade and each cancelled remainder, the credit of the event array again, besides
80 bytes for each pushed word, so it grows with the records times the event words and with the
square of the event words.  `Demos/OrderBook/README.md` gives its values on sample and edge
streams. -/

namespace Demos.OrderBook.Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime
open Program (Book)
open Abstract (toSpec)
open Refinement (Inv)

/-- From a ready store that holds the book's seven arrays as owned arrays at `po` to `pt`, whose
blocks are disjoint and lie apart from the stream's words at `pw`, under `Inv` and the size and
next-id bounds of `run_eq`, and with room for the generated bound, entry 13 consumes the book's
arrays and returns without a trap a book `b'` and event words `out`.  `b'` satisfies `Inv`, its
`toSpec` is the book of `Spec.run` on the stream, and `out` encodes the events of `Spec.run`.  The
call leaves a ready store in which the stream stays borrowed, every region of the heap apart from
the book's blocks keeps its bytes, stays a region, and lies apart from the result, and `top` lies
at most the bound above its value before the call. -/
theorem run_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) {b : Book} (h : Inv b)
    (ws : Array UInt64) (hs : ws.size + 6 < 2 ^ 64)
    (hn : b.nextId.toNat + (ws.size + 6) / 7 ≤ 2 ^ 64 - 1) (po pa pq pl pn ph pt pw : UInt64)
    (hR : _root_.Verified.Ready compiled.module compiled.tables heap store)
    (hoid : heap.Owned store po b.oid) (hacct : heap.Owned store pa b.acct)
    (hqty : heap.Owned store pq b.qty) (hlvl : heap.Owned store pl b.lvl)
    (hnxt : heap.Owned store pn b.nxt) (hhead : heap.Owned store ph b.head)
    (htail : heap.Owned store pt b.tail) (hws : heap.Borrowed store pw ws)
    (hsep : Separate store [po, pa, pq, pl, pn, ph, pt] [(pw.toNat, 8 * (ws.size + 1))])
    (hroom : heap.Within store compiled.module (compiled.run.bound (⟨b.oid⟩, ⟨b.acct⟩, ⟨b.qty⟩,
      ⟨b.lvl⟩, ⟨b.nxt⟩, ⟨b.head⟩, ⟨b.tail⟩, b.nextId, b.count, ws))) :
    Runs false env compiled.module 13 store
      [.i64 po, .i64 pa, .i64 pq, .i64 pl, .i64 pn, .i64 ph, .i64 pt, .i64 b.nextId, .i64 b.count,
        .i64 pw].reverse
      fun final values => ∃ (heap' : Heap) (b' : Book) (out : Array UInt64),
        Represent.owned heap' final values.reverse (b', out) ∧
        _root_.Verified.Ready compiled.module compiled.tables heap' final ∧
        Inv b' ∧ toSpec b' = (Spec.run (toSpec b) ws.toList).1 ∧
        out = Spec.encodeAll (Spec.run (toSpec b) ws.toList).2 ∧
        heap'.Borrowed final pw ws ∧
        (∀ r, heap.Region r → 0 < r.2 → Apart store [po, pa, pq, pl, pn, ph, pt] r →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r ∧ Represent.outside final values.reverse (b', out) r) ∧
        heap'.top.toNat ≤ heap.top.toNat + compiled.run.bound (⟨b.oid⟩, ⟨b.acct⟩, ⟨b.qty⟩,
          ⟨b.lvl⟩, ⟨b.nxt⟩, ⟨b.head⟩, ⟨b.tail⟩, b.nextId, b.count, ws) := by
  obtain ⟨hAt, hCap, -⟩ := hR
  obtain ⟨hr1, hr2, hr3⟩ := Refinement.run_eq h ws hs hn
  refine (compiled.run.trapFree env store heap
    [.i64 po, .i64 pa, .i64 pq, .i64 pl, .i64 pn, .i64 ph, .i64 pt, .i64 b.nextId, .i64 b.count,
      .i64 pw]
    (⟨b.oid⟩, ⟨b.acct⟩, ⟨b.qty⟩, ⟨b.lvl⟩, ⟨b.nxt⟩, ⟨b.head⟩, ⟨b.tail⟩, b.nextId, b.count, ws)
    hAt hroom
    ⟨[.i64 po], _, rfl, ⟨po, rfl, hoid⟩, [.i64 pa], _, rfl, ⟨pa, rfl, hacct⟩, [.i64 pq], _, rfl,
      ⟨pq, rfl, hqty⟩, [.i64 pl], _, rfl, ⟨pl, rfl, hlvl⟩, [.i64 pn], _, rfl, ⟨pn, rfl, hnxt⟩,
      [.i64 ph], _, rfl, ⟨ph, rfl, hhead⟩, [.i64 pt], _, rfl, ⟨pt, rfl, htail⟩, [.i64 b.nextId],
      _, rfl, rfl, [.i64 b.count], [.i64 pw], rfl, rfl, ⟨pw, rfl, hws⟩⟩
    hsep hCap).mono ?_
  rintro final values ⟨heap', hAt', howned, hcaps, hframe, htop⟩
  obtain ⟨hBytes, hReg, -⟩ := hframe _ hws.region (by show 0 < 8 * (ws.size + 1); omega)
    (hsep.2 _ (List.mem_singleton_self _))
  exact ⟨heap', (Program.run b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count ws).1,
    (Program.run b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count ws).2, howned,
    ⟨hAt', memoryCap_le_of_caps hcaps hCap, fun k hk => absurd hk (Nat.not_lt_zero k)⟩, hr1, hr2,
    hr3, hws.keepIn hAt' hBytes hReg, hframe, htop⟩

/-- Entry 8 computes `Program.top` from every ready store in which `top` can rise by the generated
bound within the memory cap, and `top` rises by at most that much. -/
theorem top_callSpec :
    _root_.Verified.CallSpec compiled.module compiled.tables 8 Program.top compiled.top.bound :=
  (_root_.Verified.ImplementsTables.call
    (_root_.Verified.ImplementsTables.ofA compiled.top.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- From a ready store that holds the book's seven arrays as borrowed arrays at `po` to `pt`,
under `Inv` and with room for the generated bound, entry 8 returns without a trap the four words
of `Spec.top` of the book: the best bid and its total quantity, and the best ask and its total
quantity.  The call leaves a ready store in which every borrowed array stays borrowed and `top`
lies at most the bound above its value before the call. -/
theorem top_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) {b : Book} (h : Inv b)
    (po pa pq pl pn ph pt : UInt64)
    (hR : _root_.Verified.Ready compiled.module compiled.tables heap store)
    (hoid : heap.Borrowed store po b.oid) (hacct : heap.Borrowed store pa b.acct)
    (hqty : heap.Borrowed store pq b.qty) (hlvl : heap.Borrowed store pl b.lvl)
    (hnxt : heap.Borrowed store pn b.nxt) (hhead : heap.Borrowed store ph b.head)
    (htail : heap.Borrowed store pt b.tail)
    (hroom : heap.Within store compiled.module (compiled.top.bound b)) :
    Runs false env compiled.module 8 store
      [.i64 po, .i64 pa, .i64 pq, .i64 pl, .i64 pn, .i64 ph, .i64 pt, .i64 b.nextId,
        .i64 b.count].reverse
      fun final values => ∃ (bp bq ap aq : UInt64) (heap' : Heap),
        values.reverse = [.i64 bp, .i64 bq, .i64 ap, .i64 aq] ∧
        (bp.toNat, bq.toNat, ap.toNat, aq.toNat) = Spec.top (toSpec b) ∧
        _root_.Verified.Ready compiled.module compiled.tables heap' final ∧
        (∀ p xs, heap.Borrowed store p xs → heap'.Borrowed final p xs) ∧
        heap'.top.toNat ≤ heap.top.toNat + compiled.top.bound b := by
  refine (top_callSpec env heap store
    [.i64 po, .i64 pa, .i64 pq, .i64 pl, .i64 pn, .i64 ph, .i64 pt, .i64 b.nextId, .i64 b.count] b
    hR
    ⟨[.i64 po], _, rfl, ⟨po, rfl, hoid⟩, [.i64 pa], _, rfl, ⟨pa, rfl, hacct⟩, [.i64 pq], _, rfl,
      ⟨pq, rfl, hqty⟩, [.i64 pl], _, rfl, ⟨pl, rfl, hlvl⟩, [.i64 pn], _, rfl, ⟨pn, rfl, hnxt⟩,
      [.i64 ph], _, rfl, ⟨ph, rfl, hhead⟩, [.i64 pt], _, rfl, ⟨pt, rfl, htail⟩, rfl⟩
    rfl hroom).mono ?_
  rintro final values ⟨heap', howned, hR', hkept, -, -, htop⟩
  exact ⟨(Program.top b).1, (Program.top b).2.1, (Program.top b).2.2.1, (Program.top b).2.2.2,
    heap', howned, Refinement.top_eq h, hR', hkept, htop⟩

theorem run_export :
    ({ name := "run", funcIdx := 13 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem top_export :
    ({ name := "top", funcIdx := 8 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The bytes of `compiled.module` decode to the module, whose exports `run` and `top` are
entries 13 and 8, the entries of `run_call` and `top_call`. -/
theorem orderbook_module :
    (∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok compiled.module) ∧
    ({ name := "run", funcIdx := 13 } : Wasm.Export) ∈ compiled.module.exports ∧
    ({ name := "top", funcIdx := 8 } : Wasm.Export) ∈ compiled.module.exports := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  exact ⟨⟨bytes, henc, hdec⟩, run_export, top_export⟩

#print axioms run_call
#print axioms top_callSpec
#print axioms top_call
#print axioms run_export
#print axioms top_export
#print axioms orderbook_module

end Demos.OrderBook.Verified
