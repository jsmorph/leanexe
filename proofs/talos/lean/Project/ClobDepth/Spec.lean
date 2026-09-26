import Project.ClobDepth.Func7

/-! The exported theorem covers every represented order book under a valid
runtime heap and sufficient existing memory.  Returned pointers follow the
actual reusable allocator; the result proves unique ownership, disjointness,
exact source aggregation, preservation of the input and all protected live
regions, valid final allocator globals and free list, unchanged page count,
and a worst-case heap-top bound. -/
namespace Project.ClobDepth.Spec
open Wasm Project.Clob Project.Runtime Project.ClobDepth Project.ClobDepth.Model
  Project.ClobDepth.Properties Project.ClobDepth.Representation Project.EulerRiemann.Execution

theorem result_bids {initial heap : Heap} {st0 st : Store Unit} {os : List OrderL}
    {orders : UInt64} {bids asks : FreeNode}
    (h : Func7.Result initial st0 st os orders heap bids asks) :
    OwnedLevelArrayAt st bids.root bids.capacity (depthL os).bids :=
  h.bidsOwned.buffer.contents

theorem result_asks {initial heap : Heap} {st0 st : Store Unit} {os : List OrderL}
    {orders : UInt64} {bids asks : FreeNode}
    (h : Func7.Result initial st0 st os orders heap bids asks) :
    OwnedLevelArrayAt st asks.root asks.capacity (depthL os).asks :=
  h.asksOwned.buffer.contents

theorem result_qtyAt (os : List OrderL) (side price : UInt64) :
    levelQtyAt (depthSideL os side) price = orderQtyAt os side price :=
  depthSideL_qtyAt os side price

theorem result_qtyAt_nat (os : List OrderL) (side price : UInt64)
    (hBound : orderQtyAtNat os side price < UInt64.size) :
    (levelQtyAt (depthSideL os side) price).toNat = orderQtyAtNat os side price :=
  depthSideL_qtyAt_nat os side price hBound

end Project.ClobDepth.Spec
