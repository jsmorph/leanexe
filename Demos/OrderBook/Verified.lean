import Verified.Reflect.Command
import Demos.OrderBook.Flat

/-! The order book of `Demos/OrderBook/Program.lean`, compiled by the verified compiler.  The export
`run` takes the book's seven arrays, which it consumes, its next id, its count, and a command
stream, and returns the new book and the event words, and the export `top` reads a book.  `init`
is absent because the reflector rejects its parameter of type `Unit`, so a host passes arrays of
zeros, next id 1, and count 0 for the empty book.  The reflection of `fillArrays` takes about
270,000 heartbeats, above the default limit. -/

namespace Demos.OrderBook.Verified

open _root_.Demos.OrderBook.Program

set_option maxHeartbeats 1000000 in
verified_compile compiled := [emit, findSlot, freeSlot, predecessor, bestPrice, levelQty, top,
  crosses, fillArrays, submitArrays, stepArrays, run]

#print axioms compiled.run.trapFree
#print axioms compiled.top.trapFree
#print axioms compiled.bytes

end Demos.OrderBook.Verified
