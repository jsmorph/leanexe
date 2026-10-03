/-!
Array updates for execution tests of the compiler's update templates: chains of updates on an
owned array, each applied to the result of the one inside it, and a `push` on a borrowed array,
which copies.
-/

namespace LeanExe.Examples.Updates

/-- `xs` with `a` and then `b` pushed. -/
def pushTwo (xs : Array UInt64) (a b : UInt64) : Array UInt64 := (xs.push a).push b

/-- `xs` with element `i` set to `a`, then element `j` set to the old element `i`. -/
def setTwice (xs : Array UInt64) (i j a : UInt64) : Array UInt64 :=
  (xs.set! i.toNat a).set! j.toNat xs[i.toNat]!

/-- `xs` with `a` inserted at `i`, then the element at `j` removed. -/
def insertErase (xs : Array UInt64) (i j a : UInt64) : Array UInt64 :=
  (xs.insertIdx! i.toNat a).eraseIdxIfInBounds j.toNat

/-- `xs` with `v` pushed, and `xs`: the `let` value borrows `xs`, so its push copies. -/
def pushCopy (xs : Array UInt64) (v : UInt64) : Array UInt64 × Array UInt64 :=
  let ys := xs.push v
  (ys, xs)

end LeanExe.Examples.Updates
