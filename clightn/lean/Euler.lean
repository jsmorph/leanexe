import TestSupport.Bare.Theorems
import LeanExe.ProofKit.F64Bits
import LeanExe.Native.ClightN.Instance
import LeanExe.Native.ClightN.Read
import ClightNEuler.EulerSpec

/-!
The statement `euler_terminates` of the instance that `clightn/check.sh` writes for the
bare-metal program of the Euler solver on a grid of 16 cells, `solve 4` of
`Demos/Euler/Verified.lean`: N's program judgment holds of the definitions and `main` of
`clightgen`'s file either with one volatile store to `lx_out` of each byte of the solver's packed
result and the result 0, or with no event and the code of `unreachable`, since the entry may
abort.  `bare_n` carries the copy's theorem `compiled.solve.program` to the statement, and the
kernel computes the bytes after `solve_four` gives the result of `Demos.Euler.Buffered.solve 4`.

The kernel computes the solver's run one step at a time.  A single evaluation of the whole run
holds the terms of every step at once and exceeds 40 GB.  The command `euler_steps` runs the
solver's steps natively and adds, for each step `k`, the state `w<k>` after it as words and the
theorem `step<k>`, which the kernel checks by evaluation, that the step takes the state `w<k>` to
the state `w<k+1>`, each in a declaration of its own, checked before the next one.  The theorems
state the loop's initial state, condition, and step as the equation of `runFromInto 4` gives them,
and `solve_four` rewrites the run by them.  The native run only proposes the states: the
kernel checks every step and every condition of the solver's loop.
-/

namespace ClightN.Proof.Euler

open Demos.Euler Demos.Euler.Buffered

/-- The state of the solver's loop: the status, the time, the grid, and the two grids into which
the sweeps write. -/
abbrev EState := UInt64 × Float × Array Cell × Array Cell × Array Cell

/-- The words of a cell: the bits of its four conserved quantities and its pressure, and its
status. -/
abbrev W6 := UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64

/-- The words of a state. -/
abbrev WState := UInt64 × UInt64 × List W6 × List W6 × List W6

instance : DecidableEq W6 := inferInstance
instance : DecidableEq (List W6) := inferInstance
instance : DecidableEq WState := inferInstance

def encCell (c : Cell) : W6 :=
  (c.state.density.toBits, c.state.mx.toBits, c.state.my.toBits, c.state.energy.toBits,
    c.pressure.toBits, c.status)

def decCell (w : W6) : Cell :=
  ⟨⟨Float.ofBits w.1, Float.ofBits w.2.1, Float.ofBits w.2.2.1, Float.ofBits w.2.2.2.1⟩,
    Float.ofBits w.2.2.2.2.1, w.2.2.2.2.2⟩

def enc (s : EState) : WState :=
  (s.1, s.2.1.toBits, s.2.2.1.toList.map encCell, s.2.2.2.1.toList.map encCell,
    s.2.2.2.2.toList.map encCell)

def dec (w : WState) : EState :=
  (w.1, Float.ofBits w.2.1, (w.2.2.1.map decCell).toArray, (w.2.2.2.1.map decCell).toArray,
    (w.2.2.2.2.map decCell).toArray)

theorem decCell_encCell (c : Cell) : decCell (encCell c) = c := by
  obtain ⟨⟨d, x, y, e⟩, p, s⟩ := c
  simp [decCell, encCell, LeanExe.ProofKit.F64Bits.ofBits_toBits]

theorem dec_enc (s : EState) : dec (enc s) = s := by
  obtain ⟨st, t, g, a, b⟩ := s
  have h : ∀ xs : Array Cell, ((xs.toList.map encCell).map decCell).toArray = xs := by
    intro xs
    rw [List.map_map]
    simp [Function.comp_def, decCell_encCell]
  simp only [dec, enc, h, LeanExe.ProofKit.F64Bits.ofBits_toBits]

/-- A state whose words the kernel computes. -/
theorem eq_of_enc {s : EState} {w : WState} (h : enc s = w) : s = dec w := by
  rw [← h, dec_enc]

/-- The solver's loop in `runFromInto 4`, run natively by `euler_steps`. -/
def condFn (s : EState) : Bool := s.1 == 0 && s.2.1.toBits != endTime.toBits

def stepFn (s : EState) : EState := stepInto 4 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2

def start : EState := (0, 0, initialCells 4, initialCells 4, initialCells 4)

theorem go_step {c : EState → Bool} {f : EState → EState} {k : Nat} {w w' : WState}
    (hc : c (dec w) = true) (hf : enc (f (dec w)) = w') :
    LeanExe.repeatWhile.go c f (k + 1) (dec w) = LeanExe.repeatWhile.go c f k (dec w') := by
  rw [← hf, dec_enc]
  simp [LeanExe.repeatWhile.go, hc]

theorem go_stop {c : EState → Bool} {f : EState → EState} {k : Nat} {w : WState}
    (hc : c (dec w) = false) : LeanExe.repeatWhile.go c f (k + 1) (dec w) = dec w := by
  simp [LeanExe.repeatWhile.go, hc]

open Lean Meta in
/-- Adds the theorem `name : prop`, proved by the kernel's evaluation of `decide prop`, as
`decide +kernel` proves it. -/
def addByKernel (name : Name) (prop : Expr) : MetaM Unit := do
  let inst ← synthInstance (mkApp (mkConst ``Decidable) prop)
  let pf := mkApp3 (mkConst ``of_decide_eq_true) prop inst
    (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
  addDecl (.thmDecl { name, levelParams := [], type := prop, value := pf })

open Lean Elab Command Meta in
/-- Runs the solver's loop natively from `start` and adds the words `w<k>` of the state after
`k` steps.  The theorems that it adds name the initial state, the condition, and the step of the
loop as the equation of `runFromInto 4` gives them: `start_eq` that the initial state has the
words `w0`, `cond<k>` the condition's value at `w<k>`, and `step<k>` that step `k` takes `w<k>`
to `w<k+1>`, each checked by the kernel's evaluation in a declaration of its own.  `run<k>` and
`stop` apply `go_step` and `go_stop` to them with every argument given, so that no unification
reduces an application of the loop's step, and state the loop's fuel as a numeral.  Last, the
command states and proves `solve_four`.  The proof rewrites under the match of `runFromInto` and
the match of `solve`, and the kernel compares two applications of a matcher by unfolding them,
which runs the loop unless their discriminants are the same term.  The proof therefore rewrites
by the definitions' equations, where `unfold` would leave the kernel to compare the match on
`repeatWhile …` with the match on `repeatWhile.go …`, and the theorems state the fuel as the
numeral in the goal. -/
elab "euler_steps" : command => do
  let mut s := start
  let mut ws : Array WState := #[enc start]
  while condFn s do
    s := stepFn s
    ws := ws.push (enc s)
  let ns := `ClightN.Proof.Euler
  let w (k : Nat) : Name := ns.str s!"w{k}"
  for h : k in [0:ws.size] do
    liftCoreM <| addDecl (.defnDecl {
      name := w k, levelParams := [], type := mkConst ``WState,
      value := toExpr ws[k], hints := .abbrev, safety := .safe })
  let n := ws.size - 1
  liftTermElabM do
    let run ← Term.elabTerm (← `(Demos.Euler.Buffered.runFromInto 4)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let some body ← unfoldDefinition? (← instantiateMVars run)
      | throwError "euler_steps: runFromInto"
    let some loop := body.find? (·.isAppOfArity ``LeanExe.repeatWhile 5)
      | throwError "euler_steps: the loop of runFromInto"
    let init := loop.getArg! 2
    let cond := loop.getArg! 3
    let step := loop.getArg! 4
    let dec (k : Nat) : Expr := mkApp (mkConst ``dec) (mkConst (w k))
    addByKernel (ns.str "start_eq") (← mkEq (mkApp (mkConst ``enc) init) (mkConst (w 0)))
    for k in [0:n] do
      addByKernel (ns.str s!"cond{k}") (← mkEq (mkApp cond (dec k)) (mkConst ``Bool.true))
      addByKernel (ns.str s!"step{k}")
        (← mkEq (mkApp (mkConst ``enc) (mkApp step (dec k))) (mkConst (w (k + 1))))
    addByKernel (ns.str s!"cond{n}") (← mkEq (mkApp cond (dec n)) (mkConst ``Bool.false))
    let fuel : Nat := 4294967296
    let go (k : Nat) (s : Expr) : MetaM Expr :=
      mkAppM ``LeanExe.repeatWhile.go #[cond, step, mkNatLit k, s]
    for k in [0:n] do
      let type ← mkEq (← go (fuel - k) (dec k)) (← go (fuel - k - 1) (dec (k + 1)))
      let value := mkAppN (mkConst ``go_step) #[cond, step, mkNatLit (fuel - k - 1),
        mkConst (w k), mkConst (w (k + 1)), mkConst (ns.str s!"cond{k}"),
        mkConst (ns.str s!"step{k}")]
      addDecl (.thmDecl { name := ns.str s!"run{k}", levelParams := [], type, value })
    let type ← mkEq (← go (fuel - n) (dec n)) (dec n)
    let value := mkAppN (mkConst ``go_stop) #[cond, step, mkNatLit (fuel - n - 1), mkConst (w n),
      mkConst (ns.str s!"cond{n}")]
    addDecl (.thmDecl { name := ns.str "stop", levelParams := [], type, value })
  let mut proof := "theorem solve_four :\n" ++
    "    Demos.Euler.Buffered.solve 4 =\n" ++
    s!"      pack 4 (dec w{n}).1 (dec w{n}).2.1 (dec w{n}).2.2.1 := by\n" ++
    s!"  have hrun : runFromInto 4 = dec w{n} := by\n" ++
    "    rw [runFromInto, LeanExe.repeatWhile]\n" ++
    "    rw [show (4294967296 : UInt64).toNat = 4294967296 from rfl, eq_of_enc start_eq]\n"
  for k in [0:n] do
    proof := proof ++ s!"    rw [run{k}]\n"
  proof := proof ++ "    rw [stop]\n" ++
    "    exact eq_of_enc (by decide +kernel)\n" ++
    "  rw [Demos.Euler.Buffered.solve, runInto, hrun]\n  decide +kernel"
  match Parser.runParserCategory (← getEnv) `command proof with
  | .error e => throwError "euler_steps: {e}"
  | .ok stx => elabCommand stx

set_option maxHeartbeats 0 in
set_option Elab.async false in
euler_steps

end ClightN.Proof.Euler

namespace ClightN.Proof

open LClight LeanExe.Native ClightN.Spec

set_option maxHeartbeats 0 in
theorem euler_terminates : stmt_euler_terminates := by
  refine (bare_n ?_ (Demos.Euler.Verified.compiled.solve.program _ _) ?_).imp_right And.right
  · inst_ok
  · rw [Euler.solve_four]
    decide +kernel

end ClightN.Proof

run_cmd ClightN.Read.dump
