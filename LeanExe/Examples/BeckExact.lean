import LeanExe.Examples.Beck
import LeanExe.Examples.BeckExact.Integer

namespace LeanExe.Examples.BeckExact

open Beck (Input)

structure Point where
  denominator : Integer
  numerators : Array Integer
  deriving Inhabited, Repr

def frozen (point : Point) (job : Nat) : Bool :=
  Integer.equal (Integer.abs point.numerators[job]!) point.denominator

def readInput (words : Array UInt64) : Input :=
  if words.size < 2 then Beck.reject 1
  else
    let jobs := words[0]!.toNat
    let categories := words[1]!.toNat
    if jobs > words.size - 2 then Beck.reject 1
    else if jobs != 0 && categories > ((4294967296 - 4096) / 8) / jobs then Beck.reject 2
    else
      match Beck.readJobs jobs words categories ⟨2, 0, #[]⟩ with
      | none => Beck.reject 1
      | some parsed =>
        if parsed.position != words.size then Beck.reject 1
        else ⟨0, jobs, categories, parsed.overlap, parsed.incidence⟩

def liveCount (input : Input) (point : Point) (category : Nat) : Nat := Id.run do
  let mut count := 0
  for job in [:input.jobs] do
    if !frozen point job && input.incidence[job * input.categories + category]! == 1 then
      count := count + 1
  return count

def protectedMatrix (input : Input) (point : Point) : Array Integer := Id.run do
  let mut matrix := #[]
  for category in [:input.categories] do
    if liveCount input point category > input.overlap then
      for job in [:input.jobs] do
        matrix := matrix.push (if frozen point job then Integer.zero
          else Integer.ofWord input.incidence[job * input.categories + category]!)
  return matrix

def pivotRow (width rows rank column : Nat) (matrix : Array Integer) : Nat := Id.run do
  for row in [rank:rows] do
    if !Integer.isZero matrix[row * width + column]! then return row
  return rows

def swapRows (width first second : Nat) (matrix : Array Integer) : Array Integer := Id.run do
  if first == second then return matrix
  let mut result := matrix
  for column in [:width] do
    result := result.set! (first * width + column) matrix[second * width + column]!
    result := result.set! (second * width + column) matrix[first * width + column]!
  return result

def eliminate (width rows rank column : Nat) (matrix : Array Integer)
    (previous : Integer) : Option (Array Integer) := do
  let pivot := matrix[rank * width + column]!
  let mut result := matrix
  for row in [rank + 1:rows] do
    let factor := matrix[row * width + column]!
    for col in [column + 1:width] do
      let numerator := Integer.sub (Integer.mul pivot matrix[row * width + col]!)
        (Integer.mul factor matrix[rank * width + col]!)
      let value ← Integer.divideExact numerator previous
      result := result.set! (row * width + col) value
    result := result.set! (row * width + column) Integer.zero
  return result

structure Echelon where
  matrix : Array Integer
  columns : Array UInt64
  determinant : Integer
  deriving Inhabited, Repr

def echelon (width : Nat) (matrix : Array Integer) : Option Echelon := do
  let rows := matrix.size / width
  let mut state := Echelon.mk matrix #[] (Integer.ofWord 1)
  for column in [:width] do
    let rank := state.columns.size
    let row := pivotRow width rows rank column state.matrix
    if row < rows then
      let swapped := swapRows width rank row state.matrix
      let pivot := swapped[rank * width + column]!
      let reduced ← eliminate width rows rank column swapped state.determinant
      state := ⟨reduced, state.columns.push column.toUInt64, pivot⟩
  return state

def freeColumn (input : Input) (point : Point) (columns : Array UInt64) : Nat := Id.run do
  for job in [:input.jobs] do
    if !frozen point job && !Beck.contains columns job.toUInt64 then return job
  return input.jobs

def direction (input : Input) (point : Point) : Option (Array Integer) := do
  let basis ← echelon input.jobs (protectedMatrix input point)
  let free := freeColumn input point basis.columns
  if free == input.jobs then none
  else
    let mut result := (Array.replicate input.jobs Integer.zero).set! free basis.determinant
    for offset in [:basis.columns.size] do
      let row := basis.columns.size - 1 - offset
      let column := basis.columns[row]!.toNat
      let mut total := Integer.zero
      for job in [column + 1:input.jobs] do
        total := Integer.add total (Integer.mul basis.matrix[row * input.jobs + job]! result[job]!)
      let value ← Integer.divideExact (Integer.neg total) basis.matrix[row * input.jobs + column]!
      result := result.set! column value
    return result

def boundaryStep (point : Point) (direction : Array Integer) : Integer × Integer := Id.run do
  let mut distance := Integer.zero
  let mut speed := Integer.zero
  for job in [:direction.size] do
    let magnitude := Integer.abs direction[job]!
    if !Integer.isZero magnitude then
      let gap := if direction[job]!.negative then Integer.add point.denominator point.numerators[job]!
        else Integer.sub point.denominator point.numerators[job]!
      if Integer.isZero speed || Integer.less (Integer.mul gap speed) (Integer.mul distance magnitude) then
        distance := gap
        speed := magnitude
  return (distance, speed)

def round (input : Input) (point : Point) : Option Point := do
  let vector ← direction input point
  let (distance, speed) := boundaryStep point vector
  if Integer.isZero speed then none
  else
    let mut values := #[]
    for job in [:input.jobs] do
      values := values.push (Integer.add (Integer.mul point.numerators[job]! speed)
        (Integer.mul distance vector[job]!))
    return ⟨Integer.mul point.denominator speed, values⟩

def allFrozen (point : Point) : Bool := Id.run do
  for job in [:point.numerators.size] do
    if !frozen point job then return false
  return true

def rounds : Nat → Input → Point → Option Point
  | 0, _, point => if allFrozen point then some point else none
  | fuel + 1, input, point =>
    if allFrozen point then some point
    else do
      let next ← round input point
      rounds fuel input next

def compute (words : Array UInt64) : Array UInt64 := Id.run do
  let input := readInput words
  if input.status != 0 then return #[input.status]
  match rounds input.jobs input ⟨Integer.ofWord 1, Array.replicate input.jobs Integer.zero⟩ with
  | none => return #[3]
  | some result =>
    let mut output := #[0, input.overlap.toUInt64]
    for job in [:input.jobs] do
      output := output.push (if result.numerators[job]!.negative then 0 else 1)
    return output

end LeanExe.Examples.BeckExact
