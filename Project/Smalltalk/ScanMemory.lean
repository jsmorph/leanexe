import Project.Smalltalk.MarkInvariant

namespace Project.Smalltalk.ScanMemory
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Graph
open Project.Smalltalk.Worklist

/-- The concrete scan removes exactly the represented top handle, then marks
exactly the pointer fields of that cell in their specified order. -/
theorem scanCell_eq {s : Array UInt64} {cap : Nat} {queue : List UInt64} {h : UInt64}
    (hs : Shape s cap) (q : Represents s cap (queue ++ [h])) (hh : Handle cap h)
    (tag : ValidTag (field s h 0)) :
    scanCell s = (pointers s h).foldl mark (write s 18 (read s 18 - 1)) := by
  rcases tag with t | t | t | t | t | t | t <;>
    simp [scanCell, top_word hs q, kind_eq_field hs hh, t, pointers, List.foldl]

end Project.Smalltalk.ScanMemory
