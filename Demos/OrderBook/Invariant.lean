import Demos.OrderBook.Abstract
import Demos.OrderBook.Theorems

/-! The representation invariant of [the program's](Program.lean) book and the refinement of one
step.  `Inv` states what the program's book must satisfy: arrays of the program's sizes, the chain
of each level of the band a list of distinct slots from 1 to 4,096 that hold orders of that level
and end at the level's tail, every slot in use on the chain of its level, a count equal to the
number of resting orders, and a specification's book, as `toSpec` reads it, that `Spec.Valid`
describes.  `StepRefines` states that the step at an offset of a stream keeps the invariant and
gives the book and the event words of `Spec.step` on the record at that offset. -/

namespace Demos.OrderBook.Refinement

open Program (Book)
open Abstract

/-- The slots of the chain from slot `s`, read for at most `fuel` slots. -/
def slotsFrom (b : Book) : Nat → UInt64 → List UInt64
  | 0, _ => []
  | fuel + 1, s => if s = 0 then [] else s :: slotsFrom b fuel b.nxt[s.toNat]!

/-- The slots of the chain of level `l`, read for at most 4,097 slots, as `levelOrders` reads its
orders. -/
def levelSlots (b : Book) (l : Nat) : List UInt64 := slotsFrom b 4097 b.head[l]!

/-- Whether `l` is the level of a price from 1 to 1,023 on either side. -/
def BandLevel (l : Nat) : Prop := l < 2048 ∧ l % 1024 ≠ 0

/-- The representation invariant of the program's book. -/
structure Inv (b : Book) : Prop where
  oidSize : b.oid.size = 4097
  acctSize : b.acct.size = 4097
  qtySize : b.qty.size = 4097
  lvlSize : b.lvl.size = 4097
  nxtSize : b.nxt.size = 4097
  headSize : b.head.size = 2048
  tailSize : b.tail.size = 2048
  chainNodup : ∀ l, BandLevel l → (levelSlots b l).Nodup
  chainSlots : ∀ l, BandLevel l → ∀ s ∈ levelSlots b l,
    1 ≤ s.toNat ∧ s.toNat ≤ 4096 ∧ b.lvl[s.toNat]!.toNat = l
  chainTail : ∀ l, BandLevel l → b.tail[l]! = (levelSlots b l).getLast?.getD 0
  used : ∀ s, 1 ≤ s → s ≤ 4096 → b.oid[s]! ≠ 0 →
    BandLevel b.lvl[s]!.toNat ∧ s.toUInt64 ∈ levelSlots b b.lvl[s]!.toNat
  count : b.count.toNat = Spec.size (toSpec b)
  valid : Spec.Valid (toSpec b)

/-- The record of the stream `ws` at offset `o`: its words from `o` to `o + 7`, fewer at the end of
the stream. -/
def recordAt (ws : Array UInt64) (o : Nat) : Array UInt64 := ws.extract o (o + 7)

/-- The step at offset `o` of the stream `ws`, with the event words `out` before it, keeps the
invariant and gives the book of `Spec.step` on the record at `o`, and `out` followed by the words of
its events. -/
def StepRefines (b : Book) (out ws : Array UInt64) (o : UInt64) : Prop :=
  Inv (Program.step b out ws o).1 ∧
    toSpec (Program.step b out ws o).1 = (Spec.step (toSpec b) (recordAt ws o.toNat)).1 ∧
    (Program.step b out ws o).2 =
      out ++ Spec.encodeAll (Spec.step (toSpec b) (recordAt ws o.toNat)).2

end Demos.OrderBook.Refinement
