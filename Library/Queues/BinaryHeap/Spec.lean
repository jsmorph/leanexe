/-! The specification of the priority queue: the operations run on a list that holds the queue's
words in any order.  An insertion adds its value to the list.  A removal outputs the largest word of
the list and deletes one copy of it, and a removal from an empty list outputs nothing.  The input
holds the operations as pairs `xs[2i], xs[2i + 1]` of a code and a value.  Code 0 inserts the
value, every other code removes and ignores the value, and a last word without a partner is no
operation.  The specification fixes the outputs and not how the queue stores its
words. -/

namespace Library.Queues.BinaryHeap

/-- The largest word of a list, or 0 for the empty list. -/
def largest (bag : List UInt64) : UInt64 := bag.foldl max 0

/-- The outputs of the operations `ops` on the queue `bag`, after the outputs `out`. -/
def runOps : List (UInt64 × UInt64) → List UInt64 → List UInt64 → List UInt64
  | [], _, out => out
  | (op, v) :: rest, bag, out =>
    if op = 0 then runOps rest (v :: bag) out
    else if bag = [] then runOps rest bag out
    else runOps rest (bag.erase (largest bag)) (out ++ [largest bag])

/-- The operations of the input, as pairs of a code and a value. -/
def operations (xs : Array UInt64) : List (UInt64 × UInt64) :=
  (List.range (xs.size / 2)).map fun i => (xs[2 * i]!, xs[2 * i + 1]!)

def expected (xs : Array UInt64) : Array UInt64 := (runOps (operations xs) [] []).toArray

end Library.Queues.BinaryHeap
