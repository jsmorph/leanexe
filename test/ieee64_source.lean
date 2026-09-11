import Project.IEEE64Source.Source

open Project.IEEE64Source

def cases : List (String × UInt64 × UInt64) := [
  ("addBits", 0x3FF0000000000000, 0x3CA0000000000000),
  ("addBits", 0x3FF0000000000001, 0x3CA0000000000000),
  ("addBits", 0x8000000000000000, 0x8000000000000000),
  ("addBits", 0x000FFFFFFFFFFFFF, 1),
  ("addBits", 0x7FEFFFFFFFFFFFFF, 0x7FEFFFFFFFFFFFFF),
  ("subBits", 0x3FF0000000000000, 0x3FEFFFFFFFFFFFFF),
  ("subBits", 0x8000000000000000, 0),
  ("subBits", 0x0010000000000000, 0x000FFFFFFFFFFFFF),
  ("subBits", 0x7FF0000000000000, 0x7FF0000000000000),
  ("mulBits", 0x3FF8000000000000, 0x4000000000000000),
  ("mulBits", 0x0010000000000000, 0x3FE0000000000000),
  ("mulBits", 0x8000000000000000, 0x3FF0000000000000),
  ("mulBits", 0, 0x7FF0000000000000),
  ("divBits", 0x3FF0000000000000, 0x4008000000000000),
  ("divBits", 3, 0x4000000000000000),
  ("divBits", 0x3FF0000000000000, 0x8000000000000000),
  ("divBits", 0, 0),
  ("sqrtBits", 0x4000000000000000, 0),
  ("sqrtBits", 1, 0),
  ("sqrtBits", 0x8000000000000000, 0),
  ("sqrtBits", 0xBFF0000000000000, 0),
  ("sqrtBits", 0x7FF8000000000001, 0),
  ("sqrtDivBits", 0x4022000000000000, 0x4010000000000000),
  ("sqrtDivBits", 0x8000000000000000, 0x3FF0000000000000)]

def main : IO Unit := do
  for (name, a, b) in cases do
    let result ← match name with
      | "addBits" => pure (addBits a b)
      | "subBits" => pure (subBits a b)
      | "mulBits" => pure (mulBits a b)
      | "divBits" => pure (divBits a b)
      | "sqrtBits" => pure (sqrtBits a)
      | "sqrtDivBits" => pure (sqrtDivBits a b)
      | _ => throw (IO.userError s!"unknown operation {name}")
    IO.println s!"{name} {a.toNat} {b.toNat} {result.toNat}"
