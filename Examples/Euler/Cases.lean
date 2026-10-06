import Examples.Euler.ReconstructedProgram
import Examples.Host

/-! The module cases of `euler`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Euler

open Examples.Host

def eulerCases : IO Unit := do
  let cellWords (c : Cell) : List UInt64 :=
    [c.state.density.toBits, c.state.mx.toBits, c.state.my.toBits, c.state.energy.toBits,
     c.pressure.toBits, c.status]
  let gridArg (g : Array Cell) : String := arrU (g.toList.flatMap cellWords)
  let gridWords (g : Array Cell) : String := words (g.toList.flatMap cellWords)
  let sp := specialFloats.toArray
  -- A physical state for most indices, and special values in one component for the others.
  let state (i : Nat) : Float × Float × Float × Float :=
    let rho := 0.1 + (small i).abs / 10
    let m := small (i + 1) / 20
    let t := small (i + 2) / 20
    let e := rho + 0.5 + (small (i + 3)).abs / 5
    match i % 7 with
    | 0 => (sp[i % sp.size]!, m, t, e)
    | 1 => (rho, sp[i % sp.size]!, t, e)
    | 2 => (rho, m, t, sp[i % sp.size]!)
    | 3 => (rho, 2 * rho, t, e)
    | _ => (rho, m, t, e)
  for i in [:120] do
    let (rho, m, t, e) := state i
    let q := side rho m t e
    line "euler" "side" "list:i64,f64,f64,f64,f64,f64,f64,f64" [fl rho, fl m, fl t, fl e]
      (words [q.status, q.velocity.toBits, q.pressure.toBits, q.speed.toBits, q.massFlux.toBits,
        q.momentumFlux.toBits, q.transverseFlux.toBits, q.energyFlux.toBits])
    let alpha := if i % 5 == 0 then sp[i % sp.size]! else (small (i + 4)).abs
    let c := component alpha m t rho e
    line "euler" "component" "list:i64,f64" [fl alpha, fl m, fl t, fl rho, fl e]
      (words [c.status, c.value.toBits])
    let u := update (alpha / 10) rho m t
    line "euler" "update" "list:i64,f64" [fl (alpha / 10), fl rho, fl m, fl t]
      (words [u.status, u.value.toBits])
    let (rho2, m2, t2, e2) := state (i + 3)
    let f := flux rho m t e rho2 m2 t2 e2
    line "euler" "flux" "list:i64,f64,f64,f64,f64,f64"
      [fl rho, fl m, fl t, fl e, fl rho2, fl m2, fl t2, fl e2]
      (words [f.status, f.mass.toBits, f.momentum.toBits, f.transverse.toBits, f.energy.toBits,
        f.alpha.toBits])
    let (rho3, m3, t3, e3) := state (i + 5)
    let ratio := if i % 6 == 0 then sp[i % sp.size]! else (small (i + 6)).abs / 50
    let a := advanceCell ratio rho m t e rho2 m2 t2 e2 rho3 m3 t3 e3
    line "euler" "advanceCell" "list:i64,f64,f64,f64,f64,f64,f64,f64"
      [fl ratio, fl rho, fl m, fl t, fl e, fl rho2, fl m2, fl t2, fl e2, fl rho3, fl m3, fl t3,
        fl e3]
      (words [a.status, a.density.toBits, a.momentum.toBits, a.transverse.toBits,
        a.energy.toBits, a.pressure.toBits, a.alpha.toBits, a.courant.toBits])
  for n in [2, 3, 5, 8] do
    let n : UInt64 := n
    let g := initialCells n
    line "euler" "initialCells" "array-u64" [u n] (gridWords g)
    line "euler" "accepted" "i64" [gridArg g] (if accepted g then "1" else "0")
    let sc := scan g
    line "euler" "scan" "list:i64,f64" [gridArg g] (words [sc.1, sc.2.toBits])
    for ratio in [0.05, 0.3, 2.0, 0.0, -0.1, nan] do
      for axisY in [false, true] do
        line "euler" "sweep" "array-u64" [u n, u (if axisY then 1 else 0), fl ratio, gridArg g]
          (gridWords (sweep n axisY ratio g))
      line "euler" "step" "array-u64" [u n, fl ratio, gridArg g] (gridWords (step n ratio g))
    for (time, dt) in [(0.0, 0.01), (0.0, 0.9), (0.7, 0.2), (0.0, -0.01), (0.0, 1e-30)] do
      let r := advanceWith n time dt g
      line "euler" "advanceWith" "list:i64,f64,array-u64" [u n, fl time, fl dt, gridArg g]
        (words ([r.1, r.2.1.toBits] ++ r.2.2.toList.flatMap cellWords))
    let r := advanceStep n 0 0 g
    line "euler" "advanceStep" "list:i64,f64,array-u64" [u n, u 0, fl 0, gridArg g]
      (words ([r.1, r.2.1.toBits] ++ r.2.2.toList.flatMap cellWords))
  for n in [0, 1, 2, 3, 4, 7, 16, 801] do
    let n : UInt64 := n
    line "euler" "solve" "array-u64" [u n] (words (solve n).toList)

def reconstructedCases : IO Unit := do
  let cellWords (c : Cell) : List UInt64 :=
    [c.state.density.toBits, c.state.mx.toBits, c.state.my.toBits, c.state.energy.toBits,
     c.pressure.toBits, c.status]
  let gridArg (g : Array Cell) : String := arrU (g.toList.flatMap cellWords)
  let gridWords (g : Array Cell) : String := words (g.toList.flatMap cellWords)
  let checked (c : Checked) : String := words [c.status, c.value.toBits]
  let stateArgs (q : Conserved) : List String := [fl q.density, fl q.mx, fl q.my, fl q.energy]
  let stateWords (q : Conserved) : List UInt64 :=
    [q.density.toBits, q.mx.toBits, q.my.toBits, q.energy.toBits]
  let facesWords (f : Faces) : String :=
    words ([f.status] ++ stateWords f.left ++ stateWords f.right ++ [f.factor.toBits])
  let updatedWords (a : Updated) : String :=
    words [a.status, a.density.toBits, a.momentum.toBits, a.transverse.toBits, a.energy.toBits,
      a.pressure.toBits, a.alpha.toBits, a.courant.toBits]
  let sp := specialFloats.toArray
  let state (i : Nat) : Conserved :=
    let rho := 0.1 + (small i).abs / 10
    let m := small (i + 1) / 20
    let t := small (i + 2) / 20
    let e := rho + 0.5 + (small (i + 3)).abs / 5
    match i % 7 with
    | 0 => ⟨sp[i % sp.size]!, m, t, e⟩
    | 1 => ⟨rho, sp[i % sp.size]!, t, e⟩
    | 2 => ⟨rho, m, t, sp[i % sp.size]!⟩
    | 3 => ⟨rho, 2 * rho, t, e⟩
    | _ => ⟨rho, m, t, e⟩
  for a in specialFloats do
    for b in [1.0, -2.5, 0.0, 3e-310, 1e308] do
      for up in [false, true] do
        let w := u (if up then 1 else 0)
        line "euler" "endpoint" "list:i64,f64" [w, fl a] (checked (endpoint up a))
        line "euler" "outAdd" "list:i64,f64" [w, fl a, fl b] (checked (outAdd up a b))
        line "euler" "outSub" "list:i64,f64" [w, fl a, fl b] (checked (outSub up a b))
        line "euler" "outMul" "list:i64,f64" [w, fl a, fl b] (checked (outMul up a b))
        line "euler" "outDiv" "list:i64,f64" [w, fl a, fl b] (checked (outDiv up a b))
        line "euler" "outSqrt" "list:i64,f64" [w, fl a] (checked (outSqrt up a))
  for i in [:80] do
    let q := state i
    line "euler" "speedUpper" "list:i64,f64" (stateArgs q)
      (checked (speedUpper q.density q.mx q.my q.energy))
    line "euler" "cellUpper" "list:i64,f64" (stateArgs q)
      (checked (cellUpper q.density q.mx q.my q.energy))
    let s := outwardSide q.density q.mx q.my q.energy
    line "euler" "outwardSide" "list:i64,f64,f64,f64,f64,f64,f64,f64" (stateArgs q)
      (words [s.status, s.velocity.toBits, s.pressure.toBits, s.speed.toBits, s.massFlux.toBits,
        s.momentumFlux.toBits, s.transverseFlux.toBits, s.energyFlux.toBits])
    let q2 := state (i + 3)
    let q3 := state (i + 5)
    let q4 := state (i + 8)
    let q5 := state (i + 11)
    let f := outwardFlux q.density q.mx q.my q.energy q2.density q2.mx q2.my q2.energy
    line "euler" "outwardFlux" "list:i64,f64,f64,f64,f64,f64" (stateArgs q ++ stateArgs q2)
      (words [f.status, f.mass.toBits, f.momentum.toBits, f.transverse.toBits, f.energy.toBits,
        f.alpha.toBits])
    let ratio := if i % 6 == 0 then sp[i % sp.size]! else (small (i + 6)).abs / 50
    line "euler" "faceStep" "list:i64,f64,f64,f64,f64,f64,f64,f64"
      ([fl ratio] ++ stateArgs q ++ stateArgs q2 ++ stateArgs q3 ++ stateArgs q4 ++ stateArgs q5)
      (updatedWords (faceStep ratio q.density q.mx q.my q.energy q2.density q2.mx q2.my
        q2.energy q3.density q3.mx q3.my q3.energy q4.density q4.mx q4.my q4.energy q5.density
        q5.mx q5.my q5.energy))
    let d := slope q2 q q3
    line "euler" "slope" "list:i64,f64,f64,f64,f64" (stateArgs q2 ++ stateArgs q ++ stateArgs q3)
      (words ([d.status] ++ stateWords d.state))
    let factor := if i % 5 == 0 then sp[i % sp.size]! else 0.5
    line "euler" "candidate" "list:i64,f64,f64,f64,f64,f64,f64,f64,f64,f64"
      (stateArgs q ++ stateArgs d.state ++ [fl factor]) (facesWords (candidate q d.state factor))
    for trials in [0, 1, 8] do
      let trials : UInt64 := trials
      line "euler" "limit" "list:i64,f64,f64,f64,f64,f64,f64,f64,f64,f64"
        ([u trials] ++ stateArgs q ++ stateArgs d.state) (facesWords (limit trials q d.state))
      line "euler" "reconstruct" "list:i64,f64,f64,f64,f64,f64,f64,f64,f64,f64"
        ([u trials] ++ stateArgs q2 ++ stateArgs q ++ stateArgs q3)
        (facesWords (reconstruct trials q2 q q3))
      line "euler" "reconstructedStep" "list:i64,f64,f64,f64,f64,f64,f64,f64"
        ([u trials, fl ratio] ++ stateArgs q4 ++ stateArgs q2 ++ stateArgs q ++ stateArgs q3 ++
          stateArgs q5)
        (updatedWords (reconstructedStep trials ratio q4 q2 q q3 q5))
  for n in [2, 3, 5, 8] do
    let n : UInt64 := n
    let g := initialCells n
    line "euler" "gridUpper" "list:i64,f64" [gridArg g] (checked (gridUpper g))
    for (dt, alpha) in [(0.01, 2.0), (0.5, 2.0), (0.0, 1.0), (0.01, nan)] do
      line "euler" "gridRatio" "list:i64,f64" [u n, fl dt, fl alpha]
        (checked (gridRatio n dt alpha))
    for ratio in [0.05, 0.3, 2.0, 0.0, -0.1, nan] do
      for axisY in [false, true] do
        line "euler" "reconstructedSweep" "array-u64"
          [u n, u (if axisY then 1 else 0), u 8, fl ratio, gridArg g]
          (gridWords (reconstructedSweep n axisY 8 ratio g))
      line "euler" "reconstructedStepGrid" "array-u64" [u n, u 8, fl ratio, gridArg g]
        (gridWords (reconstructedStepGrid n 8 ratio g))
    for (time, dt) in [(0.0, 0.01), (0.0, 0.9), (0.7, 0.2), (0.0, -0.01), (0.0, 1e-30)] do
      let r := reconstructedAdvanceWith n 8 time dt 2.0 g
      line "euler" "reconstructedAdvanceWith" "list:i64,f64,array-u64"
        [u n, u 8, fl time, fl dt, fl 2.0, gridArg g]
        (words ([r.1, r.2.1.toBits] ++ r.2.2.toList.flatMap cellWords))
    let r := reconstructedAdvanceStep n 8 0 g
    line "euler" "reconstructedAdvanceStep" "list:i64,f64,array-u64" [u n, u 8, fl 0, gridArg g]
      (words ([r.1, r.2.1.toBits] ++ r.2.2.toList.flatMap cellWords))
  for n in [0, 1, 2, 3, 4, 7, 16, 801] do
    for trials in [0, 1, 8] do
      let n : UInt64 := n
      let trials : UInt64 := trials
      line "euler" "reconstructedSolve" "array-u64" [u n, u trials]
        (words (reconstructedSolve n trials).toList)

def cases : IO Unit := do
  eulerCases
  reconstructedCases

end Examples.Euler
