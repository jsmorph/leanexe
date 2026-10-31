import LeanExe.Dialect.Build
import LeanExe.Dialect.Loop

/-! Topological sorting, Algorithm T of TAOCP §2.2.3.  The program keeps Knuth's count of
predecessors for each vertex and his queue of vertices whose count is 0, and the queue is also the
output.  Knuth's successor lists are replaced by a scan of the relations: when the vertex at the
front of the queue leaves it, the program scans every relation for those that start at that vertex.
Each scan takes time proportional to the number of relations, so the whole sort takes time
proportional to the number of vertices times the number of relations. -/

namespace Library.Graphs.TopologicalSort

/-- Steps T1 to T3: for each vertex `k` below `n`, the number of relations whose second vertex is
`k`. -/
def countPredecessors (xs : Array UInt64) (n m : UInt64) : Array UInt64 :=
  LeanExe.loop m (LeanExe.build n fun _ => 0) fun e cnt =>
    cnt.set! (xs[(e + e + 2).toNat]!).toNat (cnt[(xs[(e + e + 2).toNat]!).toNat]! + 1)

/-- Step T4: the vertices without predecessors, in increasing order. -/
def initialQueue (cnt : Array UInt64) (n : UInt64) : Array UInt64 :=
  LeanExe.loop n #[] fun v q => if cnt[v.toNat]! == 0 then q.push v else q

/-- Steps T5 to T7: for `f` from 0, while the queue has an element at `f`, scan the relations that
start at that vertex, decrease the count of each relation's second vertex, and append that vertex
to the queue when its count reaches 0.  At most `n` vertices enter the queue, so `n` steps suffice.
A step whose `f` lies past the queue scans no relation: its scan has length 0. -/
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

/-- The vertices in a topological order, or the empty array when the relations contain a cycle:
step T8 compares the length of the queue with the vertex count. -/
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
