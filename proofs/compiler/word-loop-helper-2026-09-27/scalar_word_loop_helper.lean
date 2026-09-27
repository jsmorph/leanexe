import LeanExe.Extract.ScalarFunc

namespace WordLoopHelperTest

def rangeWordChooseHelperWord (count seed : UInt64) : UInt64 :=
  let bump : UInt64 → UInt64 := fun x => x + seed % 7
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := bump seed
        for i in [:(bump count % 17).toNat] do
          a := a + bump i.toUInt64 + 1
        return a
      value % 7 == seed % 7
    if flag then bump count else bump seed * 3
  else seed * 13 + count

def rangeWordChooseHelperBoolean (count seed : UInt64) : UInt64 :=
  let select : Bool → UInt64 := fun b => if b then seed + 7 else seed * 3
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := select (seed % 2 == 0)
        for i in [:count.toNat] do
          if i.toUInt64 % 2 == 0 then continue
          a := a + select (i.toUInt64 % 3 == 0)
        return a
      value % 7 == seed % 7
    select flag + count
  else seed * 13 + count

def rangeWordChooseHelperPredicate (count seed : UInt64) : UInt64 :=
  let pred : UInt64 → Bool := fun x => x % 7 == seed % 7
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          a := a + i.toUInt64 + 1
          if pred a then break
        return a
      pred value
    if flag then seed + count else seed * 3
  else seed * 13 + count

def rangeWordChooseHelperBooleanPredicate (count seed : UInt64) : UInt64 :=
  let selected := seed % 3 == 0
  let flip : Bool → Bool := fun b => b != selected
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          if flip (i.toUInt64 % 2 == 0) then a := a + i.toUInt64 + 1
        return a
      flip (value % 7 == seed % 7)
    if flag then seed + count else seed * 3
  else seed * 13 + count

def rangeWordChooseHelperBinary (count seed : UInt64) : UInt64 :=
  let combine : UInt64 → UInt64 → UInt64 := fun x y => x * 3 + y + seed
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := combine seed 1
        for i in [:(combine count 2 % 17).toNat] do
          a := combine a i.toUInt64
        return a
      value % 7 == seed % 7
    if flag then combine count seed else combine seed count
  else seed * 13 + count

def rangeWordChooseHelperMany (count seed : UInt64) : UInt64 :=
  let combine : UInt64 → UInt64 → UInt64 → UInt64 := fun x y z => x * 3 + y * 5 + z + seed
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := combine seed 1 2
        for i in [:(combine count 2 3 % 17).toNat] do
          a := combine a i.toUInt64 7
        return a
      value % 7 == seed % 7
    if flag then combine count seed 11 else combine seed count 13
  else seed * 13 + count

def rangeWordChooseHelperManyFive (count seed : UInt64) : Id UInt64 := do
  let combine : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 :=
    fun a b c d e => a * 3 + b * 5 + c * 7 + d * 11 + e + seed
  if seed % 2 == 0 then
    let flag ← (do
      let value ← (do
        let mut a := combine seed 1 2 3 4
        for i in [:(combine count 2 3 4 5 % 17).toNat] do
          a := combine a i.toUInt64 7 11 13
        return a)
      pure (value % 7 == seed % 7))
    pure (if flag then combine count seed 11 13 17 else combine seed count 13 17 19)
  else pure (seed * 13 + count)

def rangeWordChooseHelperUnit (count seed : UInt64) : UInt64 :=
  let bump : Unit → UInt64 → UInt64 := fun _ x => x + seed % 7
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := bump () seed
        for i in [:(bump () count % 17).toNat] do
          a := a + bump () i.toUInt64 + 1
        return a
      value % 7 == seed % 7
    if flag then bump () count else bump () seed * 3
  else seed * 13 + count

def rangeWordChooseHelperPunit (count seed : UInt64) : UInt64 :=
  let bump : PUnit.{1} → UInt64 → UInt64 := fun _ x => x + seed % 7
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := bump PUnit.unit seed
        for i in [:count.toNat:2] do
          a := a + bump PUnit.unit i.toUInt64 + 1
        return a
      value % 7 == seed % 7
    if flag then bump PUnit.unit count else bump PUnit.unit seed * 3
  else seed * 13 + count

def rangeWordChooseHelperId (count seed : UInt64) : Id UInt64 := do
  let bump : Id (Id UInt64) → Id UInt64 := fun x => Id.run (Id.run x) + seed % 7
  let flip : Id (Id Bool) → Id Bool := fun b => !(Id.run (Id.run b))
  if seed % 2 == 0 then
    let flag ← (do
      let value ← (do
        let mut a := Id.run (bump seed)
        for i in [:count.toNat] do
          a := a + Id.run (bump i.toUInt64) + 1
        return a)
      pure (Id.run (flip (value % 7 == seed % 7))))
    pure (if flag then Id.run (bump count) else Id.run (bump seed) * 3)
  else pure (seed * 13 + count)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end WordLoopHelperTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`WordLoopHelperTest.rangeWordChooseHelperWord, (fun (x y : UInt64) => WordLoopHelperTest.rangeWordChooseHelperWord x y), true),
    (`WordLoopHelperTest.rangeWordChooseHelperBoolean, (fun (x y : UInt64) => WordLoopHelperTest.rangeWordChooseHelperBoolean x y), true),
    (`WordLoopHelperTest.rangeWordChooseHelperPredicate, (fun (x y : UInt64) => WordLoopHelperTest.rangeWordChooseHelperPredicate x y), true),
    (`WordLoopHelperTest.rangeWordChooseHelperBooleanPredicate, (fun (x y : UInt64) => WordLoopHelperTest.rangeWordChooseHelperBooleanPredicate x y), true),
    (`WordLoopHelperTest.rangeWordChooseHelperBinary, (fun (x y : UInt64) => WordLoopHelperTest.rangeWordChooseHelperBinary x y), true),
    (`WordLoopHelperTest.rangeWordChooseHelperMany, (fun (x y : UInt64) => WordLoopHelperTest.rangeWordChooseHelperMany x y), true),
    (`WordLoopHelperTest.rangeWordChooseHelperManyFive, (fun (x y : UInt64) => WordLoopHelperTest.rangeWordChooseHelperManyFive x y), true),
    (`WordLoopHelperTest.rangeWordChooseHelperUnit, (fun (x y : UInt64) => WordLoopHelperTest.rangeWordChooseHelperUnit x y), true),
    (`WordLoopHelperTest.rangeWordChooseHelperPunit, (fun (x y : UInt64) => WordLoopHelperTest.rangeWordChooseHelperPunit x y), true),
    (`WordLoopHelperTest.rangeWordChooseHelperId, (fun (x y : UInt64) => WordLoopHelperTest.rangeWordChooseHelperId x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: word-loop helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else WordLoopHelperTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/word-loop helper IR comparisons passed"
