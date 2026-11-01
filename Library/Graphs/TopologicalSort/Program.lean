import LeanExe.Dialect.Build
import LeanExe.Dialect.Loop

/-! Topological sorting, Algorithm T of TAOCP §2.2.3.  The input `xs` holds the vertex count
`n = xs[0]` and then the relations, relation `e` stating that vertex `xs[2e + 1]` comes before
vertex `xs[2e + 2]`, for vertices below `n`, where Knuth numbers the objects from 1 to `n`.  The
program keeps Knuth's count of predecessors for each vertex in an array of `n` words and his queue
of vertices whose count is 0 in an array that grows at its end, and the queue is also the output.
A scan of the relations replaces Knuth's successor lists, so that the loop's state holds only these
two arrays: when the vertex at the front of the queue leaves it, the program scans every relation
for those that start at that vertex.  Each scan makes one pass for each of the `m` relations, and
at most `n` vertices leave the queue, so the scans make at most `n·m` passes. -/

namespace Library.Graphs.TopologicalSort

/-- Steps T1 to T3 without the successor lists: for the vertex count `n` and the relation count
`m`, the array of `n` words whose word `k` is the number of relations `e < m` whose second vertex
`xs[2e + 2]` is `k`. -/
def countPredecessors (xs : Array UInt64) (n m : UInt64) : Array UInt64 :=
  LeanExe.loop m (LeanExe.build n fun _ => 0) fun e cnt =>
    cnt.set! (xs[(e + e + 2).toNat]!).toNat (cnt[(xs[(e + e + 2).toNat]!).toNat]! + 1)

/-- Step T4: the vertices `v < n` whose count `cnt[v]` is 0, in increasing order. -/
def initialQueue (cnt : Array UInt64) (n : UInt64) : Array UInt64 :=
  LeanExe.loop n #[] fun v q => if cnt[v.toNat]! == 0 then q.push v else q

/-- Steps T5 to T7.  The state is the pair of the counts and the queue, and step `f` takes the
vertex at position `f` of the queue.  It scans the `m` relations for those that start at that
vertex, decreases the count of each such relation's second vertex, and appends that vertex to the
queue when its count reaches 0.  At most `n` vertices enter the queue, so `n` steps suffice.  A step
whose `f` lies past the queue scans no relation, because its scan has length 0.  The test lies in
the scan's length because the compiler does not accept a loop body that ends in an `if` between
the scan and the unchanged state. -/
def process (xs : Array UInt64) (n m : UInt64) (cnt q : Array UInt64) :
    Array UInt64 × Array UInt64 :=
  LeanExe.loop n (cnt, q) fun f s =>
    LeanExe.loop (if f < s.2.size.toUInt64 then m else 0) s fun e t =>
      if xs[(e + e + 1).toNat]! == t.2[f.toNat]! then
        if t.1[(xs[(e + e + 2).toNat]!).toNat]! == 1 then
          (t.1.set! (xs[(e + e + 2).toNat]!).toNat 0, t.2.push xs[(e + e + 2).toNat]!)
        else
          (t.1.set! (xs[(e + e + 2).toNat]!).toNat (t.1[(xs[(e + e + 2).toNat]!).toNat]! - 1),
            t.2)
      else t

/-- The vertices in a topological order, or the empty array when the relations contain a cycle or
`xs` is empty: step T8 compares the length of the queue with the vertex count. -/
def topoSort (xs : Array UInt64) : Array UInt64 :=
  if xs.size.toUInt64 = 0 then #[]
  else
    let n := xs[(0 : UInt64).toNat]!
    let m := (xs.size.toUInt64 - 1) / 2
    let cnt := countPredecessors xs n m
    let q := initialQueue cnt n
    let st := process xs n m cnt q
    if st.2.size.toUInt64 = n then st.2 else #[]

end Library.Graphs.TopologicalSort
