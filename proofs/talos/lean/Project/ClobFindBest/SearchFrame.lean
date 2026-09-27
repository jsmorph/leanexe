import Project.ClobFindBest.SearchProgram
import Project.ClobFindBest.Helpers

namespace Project.ClobFindBest.SearchFrame
open Wasm Project.Common Project.Clob Project.ClobFindBest.Model

def params (fuel owner ptr : UInt64) (taker : OrderL) (k : Nat) (best : Option Nat) : List Value :=
  [.i64 fuel, .i64 owner, .i64 ptr, .i64 taker.oid, .i64 taker.otrader,
    .i64 taker.oside, .i64 taker.oprice, .i64 taker.oqty, .i64 (UInt64.ofNat k),
    .i64 (optionTag best), .i64 (optionPayload best)]

structure Candidate (s : Locals) (maker : OrderL) : Prop where
  oid : s.locals[4]? = some (.i64 maker.oid)
  trader : s.locals[5]? = some (.i64 maker.otrader)
  side : s.locals[6]? = some (.i64 maker.oside)
  price : s.locals[7]? = some (.i64 maker.oprice)
  qty : s.locals[8]? = some (.i64 maker.oqty)

structure DecisionFrame (before after : Locals) (word : UInt64) : Prop where
  params : after.params = before.params
  locals : after.locals.length = 56
  values : after.values = [.i64 word]
  kept : ∀ i, i < 9 ∨ i = 30 → after.locals[i]? = before.locals[i]?

theorem Candidate.frame {before after : Locals} {maker : OrderL} {word : UInt64}
    (h : Candidate before maker) (hf : DecisionFrame before after word) : Candidate after maker := by
  constructor
  · rw [hf.kept 4 (by omega)]; exact h.oid
  · rw [hf.kept 5 (by omega)]; exact h.trader
  · rw [hf.kept 6 (by omega)]; exact h.side
  · rw [hf.kept 7 (by omega)]; exact h.price
  · rw [hf.kept 8 (by omega)]; exact h.qty

structure ReadFrame (before after : Locals) (maker : OrderL) : Prop where
  params : after.params = before.params
  locals : after.locals.length = 56
  values : after.values = []
  candidate : Candidate after maker
  kept : ∀ i, i < 4 → after.locals[i]? = before.locals[i]?

end Project.ClobFindBest.SearchFrame
