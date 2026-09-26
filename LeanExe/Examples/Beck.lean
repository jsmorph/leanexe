namespace LeanExe.Examples.Beck

def maxJobs : Nat := 6
def maxCategories : Nat := 8

def negative (x : UInt64) : Bool := x ≥ 9223372036854775808

def magnitude (x : UInt64) : UInt64 := if negative x then 0 - x else x

structure Point where
  denominator : UInt64
  numerators : Array UInt64
  deriving Inhabited, Repr

def frozen (x : Point) (job : Nat) : Bool :=
  magnitude x.numerators[job]! == x.denominator

structure Input where
  status : UInt64
  jobs : Nat
  categories : Nat
  overlap : Nat
  incidence : Array UInt64
  deriving Inhabited, Repr

def reject (status : UInt64) : Input := ⟨status, 0, 0, 0, #[]⟩

def readMemberships : Nat → Array UInt64 → Nat → Nat → Array UInt64 → Option (Array UInt64)
  | 0, _, _, _, row => some row
  | count + 1, words, pos, categories, row =>
    let category := words[pos]!.toNat
    if category ≥ categories then none
    else if row[category]! != 0 then none
    else readMemberships count words (pos + 1) categories (row.set! category 1)

structure ParseState where
  position : Nat
  overlap : Nat
  incidence : Array UInt64
  deriving Inhabited, Repr

def readJobs : Nat → Array UInt64 → Nat → ParseState → Option ParseState
  | 0, _, _, state => some state
  | jobs + 1, words, categories, state =>
    if state.position ≥ words.size then none
    else
      let count := words[state.position]!.toNat
      let pos := state.position + 1
      if count > categories || pos + count > words.size then none
      else
        match readMemberships count words pos categories (Array.replicate categories 0) with
        | none => none
        | some row =>
          let next := ParseState.mk (pos + count) (max state.overlap count) (state.incidence ++ row)
          readJobs jobs words categories next

def readInput (words : Array UInt64) : Input :=
  if words.size < 2 then reject 1
  else if words[0]! > 6 || words[1]! > 8 then reject 2
  else
    let n := words[0]!.toNat
    let m := words[1]!.toNat
    match readJobs n words m ⟨2, 0, #[]⟩ with
    | none => reject 1
    | some result =>
      if result.position != words.size then reject 1
      else ⟨0, n, m, result.overlap, result.incidence⟩

def liveCount (input : Input) (x : Point) (category : Nat) : Nat := Id.run do
  let mut live := 0
  for job in [:input.jobs] do
    if !frozen x job && input.incidence[job * input.categories + category]! == 1 then
      live := live + 1
  return live

def protectedMatrix (input : Input) (x : Point) : Array UInt64 := Id.run do
  let mut matrix := #[]
  for category in [:input.categories] do
    if liveCount input x category > input.overlap then
      for job in [:input.jobs] do
        matrix := matrix.push
          (if !frozen x job then input.incidence[job * input.categories + category]! else 0)
  return matrix

def omitIndex (xs : Array UInt64) (index : Nat) : Array UInt64 :=
  xs.eraseIdxIfInBounds index

def contains (xs : Array UInt64) (value : UInt64) : Bool := Id.run do
  for i in [:xs.size] do
    if xs[i]! == value then return true
  return false

def determinant : Nat → Nat → Array UInt64 → Array UInt64 → Array UInt64 → UInt64
  | 0, _, _, _, _ => 1
  | fuel + 1, width, matrix, rows, columns => Id.run do
    let mut result : UInt64 := 0
    let tail := omitIndex rows 0
    for j in [:columns.size] do
      let entry := matrix[rows[0]!.toNat * width + columns[j]!.toNat]!
      if entry != 0 then
        let remaining := omitIndex columns j
        let term := entry * determinant fuel width matrix tail remaining
        result := if j % 2 == 0 then result + term else result - term
    return result

structure Basis where
  rows : Array UInt64
  columns : Array UInt64
  determinant : UInt64
  deriving Inhabited, Repr

def borderCandidate (width : Nat) (matrix : Array UInt64) (basis : Basis)
    (row col : Nat) : Option Basis :=
  if contains basis.rows row.toUInt64 || contains basis.columns col.toUInt64 then none
  else
    let rows := basis.rows.push row.toUInt64
    let columns := basis.columns.push col.toUInt64
    let value := determinant rows.size width matrix rows columns
    if value == 0 then none else some ⟨rows, columns, value⟩

def extend (width : Nat) (matrix : Array UInt64) (basis : Basis) : Basis := Id.run do
  for row in [:matrix.size / width] do
    for col in [:width] do
      match borderCandidate width matrix basis row col with
      | some next => return next
      | none => pure ()
  return basis

def findBasis : Nat → Nat → Array UInt64 → Basis → Basis
  | 0, _, _, basis => basis
  | fuel + 1, width, matrix, basis =>
    let next := extend width matrix basis
    if next.rows.size == basis.rows.size then basis
    else findBasis fuel width matrix next

def freeColumn (input : Input) (x : Point) (columns : Array UInt64) : Nat := Id.run do
  for col in [:input.jobs] do
    if !frozen x col && !contains columns col.toUInt64 then return col
  return input.jobs

def direction (input : Input) (x : Point) : Array UInt64 := Id.run do
  let matrix := protectedMatrix input x
  let basis := findBasis input.jobs input.jobs matrix ⟨#[], #[], 1⟩
  let free := freeColumn input x basis.columns
  if free == input.jobs then return #[]
  let mut d := (Array.replicate input.jobs (0 : UInt64)).set! free basis.determinant
  for j in [:basis.columns.size] do
    let columns := basis.columns.set! j free.toUInt64
    let value := determinant basis.rows.size input.jobs matrix basis.rows
      columns
    d := d.set! basis.columns[j]!.toNat (0 - value)
  return d

def gap (denominator numerator direction : UInt64) : UInt64 :=
  if negative direction then denominator + numerator else denominator - numerator

def boundaryStep (input : Input) (x : Point) (d : Array UInt64) : UInt64 × UInt64 := Id.run do
  let mut stepNumerator := 0
  let mut stepDenominator := 0
  for job in [:input.jobs] do
    let speed := magnitude d[job]!
    if speed != 0 then
      let distance := gap x.denominator x.numerators[job]! d[job]!
      if stepDenominator == 0 || distance * stepDenominator < stepNumerator * speed then
        stepNumerator := distance
        stepDenominator := speed
  return (stepNumerator, stepDenominator)

def round (input : Input) (x : Point) : Point := Id.run do
  let d := direction input x
  if d.size != input.jobs then return ⟨0, #[]⟩
  let step := boundaryStep input x d
  let stepNumerator := step.1
  let stepDenominator := step.2
  if stepDenominator == 0 then return ⟨0, #[]⟩
  let denominator := x.denominator * stepDenominator
  let mut numerators := #[]
  for job in [:input.jobs] do
    numerators := numerators.push
      (x.numerators[job]! * stepDenominator + stepNumerator * d[job]!)
  return ⟨denominator, numerators⟩

def allFrozen (x : Point) : Bool := Id.run do
  for job in [:x.numerators.size] do
    if !frozen x job then return false
  return true

def rounds : Nat → Input → Point → Point
  | 0, _, x => if allFrozen x then x else ⟨0, #[]⟩
  | fuel + 1, input, x =>
    if allFrozen x then x
    else
      let next := round input x
      if next.denominator == 0 then ⟨0, #[]⟩ else rounds fuel input next

def compute (words : Array UInt64) : Array UInt64 := Id.run do
  let input := readInput words
  if input.status != 0 then return #[input.status]
  let x := rounds input.jobs input ⟨1, Array.replicate input.jobs 0⟩
  if x.denominator == 0 then return #[3]
  let mut result := #[0, input.overlap.toUInt64]
  for job in [:input.jobs] do
    result := result.push (if negative x.numerators[job]! then 0 else 1)
  return result

end LeanExe.Examples.Beck
