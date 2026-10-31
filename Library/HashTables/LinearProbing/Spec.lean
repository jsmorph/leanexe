/-! The specification of the hash table: the operations run on a list of distinct keys, the keys
that the table holds, in any order.  Code 0 inserts, code 1 looks up, and every other code deletes.
An insertion adds an absent key while the list holds fewer than `M - 1` keys, a lookup tests
membership, and a deletion removes a present key.  Each operation
outputs 1 when it adds, finds, or removes its key, and 0 otherwise.  For `M = 0` and `M = 1` the
table holds no key, so every operation outputs 0.  The input holds `M = xs[0]` and then the
operations as pairs `xs[2i + 1], xs[2i + 2]` of a code and a key, and a last word without a partner
is no operation.  The empty input has no operations.  The specification fixes the outputs and not
the hash function or the arrangement of the slots.  It defines the outputs for every `M`, and the
module's theorem covers `M < 2^63`. -/

namespace Library.HashTables.LinearProbing

/-- The number of slots `M`. -/
def slots (xs : Array UInt64) : Nat := xs[0]!.toNat

/-- The operations of the input, as pairs of a code and a key. -/
def operations (xs : Array UInt64) : List (UInt64 × UInt64) :=
  (List.range ((xs.size - 1) / 2)).map fun i => (xs[2 * i + 1]!, xs[2 * i + 2]!)

/-- The outputs of the operations `ops` on a table of `m` slots that holds `keys`, after the
outputs `out`. -/
def runOps (m : Nat) : List (UInt64 × UInt64) → List UInt64 → List UInt64 → List UInt64
  | [], _, out => out
  | (op, k) :: rest, keys, out =>
    if op = 0 then
      if k ∈ keys ∨ m ≤ keys.length + 1 then runOps m rest keys (out ++ [0])
      else runOps m rest (k :: keys) (out ++ [1])
    else if op = 1 then runOps m rest keys (out ++ [if k ∈ keys then 1 else 0])
    else if k ∈ keys then runOps m rest (keys.erase k) (out ++ [1])
    else runOps m rest keys (out ++ [0])

def expected (xs : Array UInt64) : Array UInt64 :=
  (runOps (slots xs) (operations xs) [] []).toArray

end Library.HashTables.LinearProbing
