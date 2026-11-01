import Demos.OrderBook.RefineStep
import Demos.OrderBook.RefineStream

/-! The refinement of [the specification](Spec.lean) by [the program](Program.lean), under the
invariant of [the representation](Invariant.lean).  `step_eq` of [the step's
proof](RefineStep.lean) states that a step at an offset inside a stream keeps `Inv` and gives the
book and the event words of `Spec.step` on the record there, and `top_eq`, `init_inv`, and
`toSpec_init` state that `top` gives `Spec.top` and that the empty book satisfies `Inv` and reads
as `Spec.empty`.  `run_append` of [the stream theorems](RefineStream.lean) states that a stream run
in two parts gives the book and the event words of one run on any book, and `run_eq` here states
that, under `Inv`, `run` keeps `Inv` and gives the book and the event words of `Spec.run`. -/

namespace Demos.OrderBook.Refinement

open Program (Book)
open Abstract

/-- Under the invariant, and while the next id stays below 2^64 - 1, `run` keeps the invariant and
gives the book and the event words of `Spec.run` on the book that `toSpec` reads. -/
theorem run_eq {b : Book} (h : Inv b) (ws : Array UInt64) (hs : ws.size + 6 < 2 ^ 64)
    (hn : b.nextId.toNat + (ws.size + 6) / 7 ≤ 2 ^ 64 - 1) :
    Inv (Program.run b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count ws).1 ∧
      toSpec (Program.run b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count ws).1 =
        (Spec.run (toSpec b) ws.toList).1 ∧
      (Program.run b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count ws).2 =
        Spec.encodeAll (Spec.run (toSpec b) ws.toList).2 :=
  run_eq_of_step (fun _ _ _ _ hb hn ho hs => step_eq hb hn _ _ _ ho hs) h ws hs hn

#print axioms step_eq
#print axioms init_inv
#print axioms toSpec_init
#print axioms top_eq
#print axioms run_eq

end Demos.OrderBook.Refinement
