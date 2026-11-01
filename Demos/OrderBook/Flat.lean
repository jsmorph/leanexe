import Demos.OrderBook.Program
import LeanExe.Pipeline.Implements

/-! Representations for the verified compiler: a book is the tuple of its seven arrays, its next
id, and its count, and the state of matching is the tuple of its fields. -/

namespace Demos.OrderBook.Program

open LeanExe.Pipeline

instance : Flat Book (Array UInt64 × Array UInt64 × Array UInt64 × Array UInt64 ×
    Array UInt64 × Array UInt64 × Array UInt64 × UInt64 × UInt64) :=
  ⟨fun b => (b.oid, b.acct, b.qty, b.lvl, b.nxt, b.head, b.tail, b.nextId, b.count)⟩

instance : Flat Matching (Book × Array UInt64 × UInt64 × UInt64 × Bool) :=
  ⟨fun m => (m.book, m.out, m.price, m.rem, m.selfTrade)⟩

end Demos.OrderBook.Program
