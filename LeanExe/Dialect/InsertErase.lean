namespace LeanExe

/-- `xs` with `v` inserted at position `i`, before the element there, or appended when `i` is
the size, and `xs` itself when `i` is past the size. -/
def insertAt (xs : Array α) (i : UInt64) (v : α) : Array α :=
  xs.insertIdxIfInBounds i.toNat v

/-- `xs` without the element at position `i`, and `xs` itself when `i` is not below the size. -/
def eraseAt (xs : Array α) (i : UInt64) : Array α :=
  xs.eraseIdxIfInBounds i.toNat

end LeanExe
