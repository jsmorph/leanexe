namespace LeanExe.Examples.Beck

def maxJobs : Nat := 6
def maxCategories : Nat := 8

structure Fraction where
  negative : Bool
  numerator : UInt64
  denominator : UInt64
  deriving Inhabited, DecidableEq, Repr

def invalid : Fraction := ⟨false, 0, 0⟩
def zero : Fraction := ⟨false, 0, 1⟩
def one : Fraction := ⟨false, 1, 1⟩

def gcdFuel : Nat → UInt64 → UInt64 → UInt64
  | 0, _, _ => 0
  | fuel + 1, a, b => if b == 0 then a else gcdFuel fuel b (a % b)

def fraction (negative : Bool) (numerator denominator : UInt64) : Fraction :=
  if denominator == 0 then invalid
  else if numerator == 0 then zero
  else
    let g := gcdFuel 129 numerator denominator
    if g == 0 then invalid else ⟨negative, numerator / g, denominator / g⟩

def productFits (a b : UInt64) : Bool :=
  a == 0 || b ≤ 18446744073709551615 / a

def negate (a : Fraction) : Fraction :=
  if a.numerator == 0 then a else ⟨!a.negative, a.numerator, a.denominator⟩

def add (a b : Fraction) : Fraction :=
  if a.denominator == 0 || b.denominator == 0 then invalid
  else if !productFits a.numerator b.denominator ||
      !productFits b.numerator a.denominator ||
      !productFits a.denominator b.denominator then invalid
  else
    let x := a.numerator * b.denominator
    let y := b.numerator * a.denominator
    let d := a.denominator * b.denominator
    if a.negative == b.negative then
      if x > 18446744073709551615 - y then invalid
      else fraction a.negative (x + y) d
    else if x ≥ y then fraction a.negative (x - y) d
    else fraction b.negative (y - x) d

def subtract (a b : Fraction) : Fraction := add a (negate b)

def multiply (a b : Fraction) : Fraction :=
  if a.denominator == 0 || b.denominator == 0 then invalid
  else if !productFits a.numerator b.numerator ||
      !productFits a.denominator b.denominator then invalid
  else fraction (a.negative != b.negative)
    (a.numerator * b.numerator) (a.denominator * b.denominator)

def divide (a b : Fraction) : Fraction :=
  if b.denominator == 0 then invalid
  else multiply a ⟨b.negative, b.denominator, b.numerator⟩

def positiveLt (a b : Fraction) : Bool :=
  a.numerator * b.denominator < b.numerator * a.denominator

def frozen (x : Fraction) : Bool := x.numerator == x.denominator

structure Input where
  status : UInt64
  jobs : Nat
  categories : Nat
  overlap : Nat
  incidence : Array UInt64
  deriving Inhabited, Repr

def reject (status : UInt64) : Input := ⟨status, 0, 0, 0, #[]⟩

def readInput (words : Array UInt64) : Input := Id.run do
  if words.size < 2 then return reject 1
  if words[0]! > 6 || words[1]! > 8 then return reject 2
  let n := words[0]!.toNat
  let m := words[1]!.toNat
  let mut incidence := Array.replicate (n * m) (0 : UInt64)
  let mut pos := 2
  let mut overlap := 0
  for job in [:n] do
    if pos ≥ words.size then return reject 1
    let count := words[pos]!
    pos := pos + 1
    if count > m.toUInt64 then return reject 1
    let count := count.toNat
    if pos + count > words.size then return reject 1
    overlap := max overlap count
    for k in [:count] do
      let category := words[pos + k]!
      if category ≥ m.toUInt64 then return reject 1
      let index := job * m + category.toNat
      if incidence[index]! != 0 then return reject 1
      incidence := incidence.set! index 1
    pos := pos + count
  if pos != words.size then return reject 1
  return ⟨0, n, m, overlap, incidence⟩

def protectedMatrix (input : Input) (x : Array Fraction) : Array Fraction := Id.run do
  let mut matrix := #[]
  for category in [:input.categories] do
    let mut live := 0
    for job in [:input.jobs] do
      if !frozen x[job]! && input.incidence[job * input.categories + category]! == 1 then
        live := live + 1
    if live > input.overlap then
      for job in [:input.jobs] do
        matrix := matrix.push
          (if !frozen x[job]! && input.incidence[job * input.categories + category]! == 1
           then one else zero)
  return matrix

structure Reduction where
  matrix : Array Fraction
  pivots : Array UInt64
  deriving Inhabited, Repr

def eliminate (n : Nat) (matrix : Array Fraction) : Reduction := Id.run do
  let rows := matrix.size / n
  let mut matrix := matrix
  let mut pivots := #[]
  for col in [:n] do
    let rank := pivots.size
    let mut selected := rows
    for row in [rank:rows] do
      if selected == rows && matrix[row * n + col]!.numerator != 0 then
        selected := row
    if selected < rows then
      for j in [:n] do
        let a := matrix[rank * n + j]!
        let b := matrix[selected * n + j]!
        matrix := (matrix.set! (rank * n + j) b).set! (selected * n + j) a
      let pivot := matrix[rank * n + col]!
      for j in [:n] do
        matrix := matrix.set! (rank * n + j) (divide matrix[rank * n + j]! pivot)
      for row in [:rows] do
        if row != rank then
          let coefficient := matrix[row * n + col]!
          for j in [:n] do
            matrix := matrix.set! (row * n + j)
              (subtract matrix[row * n + j]!
                (multiply coefficient matrix[rank * n + j]!))
      pivots := pivots.push col.toUInt64
  return ⟨matrix, pivots⟩

def direction (input : Input) (x : Array Fraction) : Array Fraction := Id.run do
  let reduced := eliminate input.jobs (protectedMatrix input x)
  for i in [:reduced.matrix.size] do
    if reduced.matrix[i]!.denominator == 0 then return #[]
  let mut free := input.jobs
  for col in [:input.jobs] do
    if free == input.jobs && !frozen x[col]! then
      let mut pivot := false
      for row in [:reduced.pivots.size] do
        if reduced.pivots[row]! == col.toUInt64 then pivot := true
      if !pivot then free := col
  if free == input.jobs then return #[]
  let mut d := (Array.replicate input.jobs zero).set! free one
  for row in [:reduced.pivots.size] do
    d := d.set! reduced.pivots[row]!.toNat
      (negate reduced.matrix[row * input.jobs + free]!)
  return d

def boundary (x d : Fraction) : Fraction :=
  divide (subtract (if d.negative then negate one else one) x) d

def round (input : Input) (x : Array Fraction) : Array Fraction := Id.run do
  let d := direction input x
  if d.size != input.jobs then return #[]
  let mut step := invalid
  for job in [:input.jobs] do
    if d[job]!.denominator == 0 then return #[]
    if d[job]!.numerator != 0 then
      let candidate := boundary x[job]! d[job]!
      if candidate.denominator == 0 || candidate.negative || candidate.numerator == 0 then
        return #[]
      if step.denominator == 0 then step := candidate
      else
        if !productFits candidate.numerator step.denominator ||
            !productFits step.numerator candidate.denominator then return #[]
        if positiveLt candidate step then step := candidate
  if step.denominator == 0 then return #[]
  let mut result := #[]
  for job in [:input.jobs] do
    let next := add x[job]! (multiply step d[job]!)
    if next.denominator == 0 || next.numerator > next.denominator then return #[]
    result := result.push next
  return result

def allFrozen (x : Array Fraction) : Bool := Id.run do
  for job in [:x.size] do
    if !frozen x[job]! then return false
  return true

def rounds : Nat → Input → Array Fraction → Array Fraction
  | 0, _, x => if allFrozen x then x else #[]
  | fuel + 1, input, x =>
    if allFrozen x then x
    else
      let next := round input x
      if next.size != input.jobs then #[] else rounds fuel input next

def compute (words : Array UInt64) : Array UInt64 := Id.run do
  let input := readInput words
  if input.status != 0 then return #[input.status]
  let x := rounds input.jobs input (Array.replicate input.jobs zero)
  if x.size != input.jobs then return #[3]
  let mut result := #[0, input.overlap.toUInt64]
  for job in [:input.jobs] do
    result := result.push (if x[job]!.negative then 0 else 1)
  return result

end LeanExe.Examples.Beck
