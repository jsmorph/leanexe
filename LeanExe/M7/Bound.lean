import LeanExe.M7.Cost

/-!
A bound on the instructions of every run of a function whose reached functions have no loop,
computed over the WebAssembly code in the pattern of `stackNeedOf` of `LeanExe/CallGraph.lean`,
so that the kernel evaluates it.  `costI` charges a straight-line form its units from
`instrSize`, a division its units and `divBound`, an `if` its test and the larger of the
then-branch with the branch over the else-branch and the else-branch, a block its body, and a call
its copies, `BL`, and the callee's bound; a loop has no bound.  `costL` adds the bounds of a list's
instructions.  `costOf m d k` bounds function `k` of `m` through calls `d` deep, and
`staticCost m k` through as many calls as `m` has functions, which bounds every chain of calls when
the calls form no cycle.  `costRun_le_staticCost` of `LeanExe/M7/Proof/Bound.lean` states that it
bounds `costRun` at every fuel.

`pathCost m k dec` bounds the runs of function `k` whose tests have the outcomes that the table
`dec` lists.  A test is the code from the start of a list of instructions to an `if` in it, when
each of its forms has a key of `pureKey`: `local.get`, `i64.const`, and the `i64` operations
other than the divisions.  `pathL` charges such an `if` only the branch that the table's outcome
for its test selects, and it charges every other `if`, and every instruction after the first
`if` or the first form without a key, as `costL` does.  A step whose state selects a phase
through such tests, as a step that the reflector compiles from `if`s on its fields does, has a
bound for each phase's windows.  `costRun_le_pathCost` of `LeanExe/M7/Proof/Bound.lean` states
the bound for the arguments from which each test of the table has its outcome.
-/

namespace LeanExe.M7

open Wasm

mutual

/-- A bound on `costOne` of `inst` under constructs whose branches carry `ar` values, with the
bounds `callee` of the called functions, which `fs` names. -/
def costI (callee : Nat → Option Nat) (fs : Nat → Option Function) (ar : List Nat) :
    Instruction → Option Nat
  | .block _ ra body _ _ => costL callee fs (ra :: ar) body
  | .loop .. => none
  | .iff _ ra thn els _ _ =>
      match costL callee fs (ra :: ar) thn, costL callee fs (ra :: ar) els with
      | some t, some e => some (3 + max (t + 1) e)
      | _, _ => none
  | .call k =>
      match fs k, callee k with
      | some f, some c => some (4 * f.params.length + 1 + c + 4 * f.results.length)
      | _, _ => none
  | .divUI64 => some (9 + divBound)
  | .remUI64 => some (9 + divBound)
  | i => some (instrSize (fun _ => none) ar 0 i).1

/-- A bound on `costExec` of `p`: the sum of its instructions' bounds. -/
def costL (callee : Nat → Option Nat) (fs : Nat → Option Function) (ar : List Nat) :
    List Instruction → Option Nat
  | [] => some 0
  | i :: rest =>
      match costI callee fs ar i, costL callee fs ar rest with
      | some c, some d => some (c + d)
      | _, _ => none

end

/-- A bound on `costRun` of the function `f`. -/
def costF (callee : Nat → Option Nat) (fs : Nat → Option Function) (f : Function) :
    Option Nat :=
  (costL callee fs [f.results.length] f.body).map (frameCost f + ·)

/-- A bound on `costRun` of function `k` of `m` through calls `d` deep, `none` when the calls
reach deeper, a loop, or a missing function. -/
def costOf (m : Module) : Nat → Nat → Option Nat
  | 0, _ => none
  | d + 1, k =>
      match m.funcs[k]? with
      | some f => costF (costOf m d) (fun j => m.funcs[j]?) f
      | none => none

/-- A bound on `costRun` of function `k` of `m`, through as many calls as `m` has functions. -/
def staticCost (m : Module) (k : Nat) : Option Nat := costOf m (m.funcs.length + 1) k

/-- A key for each form that the simulation covers and that computes on the operand stack
without other effects: `local.get`, `i64.const`, and the `i64` operations other than the
divisions. -/
inductive PureKey where
  | get (i : Nat)
  | const (c : UInt64)
  | op (n : Nat)
  deriving DecidableEq

/-- The key of a form without effects, and `none` for every other form. -/
def pureKey : Instruction → Option PureKey
  | .localGet i => some (.get i)
  | .constI64 c => some (.const c)
  | .andI64 => some (.op 0)
  | .orI64 => some (.op 1)
  | .xorI64 => some (.op 2)
  | .addI64 => some (.op 3)
  | .subI64 => some (.op 4)
  | .mulI64 => some (.op 5)
  | .eqI64 => some (.op 6)
  | .neI64 => some (.op 7)
  | .ltUI64 => some (.op 8)
  | .leUI64 => some (.op 9)
  | .geUI64 => some (.op 10)
  | .ltSI64 => some (.op 11)
  | .leSI64 => some (.op 12)
  | .eqzI64 => some (.op 13)
  | .extendUI32 => some (.op 14)
  | .wrapI64 => some (.op 15)
  | .shlI64 => some (.op 16)
  | .shrUI64 => some (.op 17)
  | .shrSI64 => some (.op 18)
  | _ => none

/-- The form of a key. -/
def keyForm : PureKey → Instruction
  | .get i => .localGet i
  | .const c => .constI64 c
  | .op 0 => .andI64
  | .op 1 => .orI64
  | .op 2 => .xorI64
  | .op 3 => .addI64
  | .op 4 => .subI64
  | .op 5 => .mulI64
  | .op 6 => .eqI64
  | .op 7 => .neI64
  | .op 8 => .ltUI64
  | .op 9 => .leUI64
  | .op 10 => .geUI64
  | .op 11 => .ltSI64
  | .op 12 => .leSI64
  | .op 13 => .eqzI64
  | .op 14 => .extendUI32
  | .op 15 => .wrapI64
  | .op 16 => .shlI64
  | .op 17 => .shrUI64
  | .op _ => .shrSI64

/-- The outcome that the table `dec` gives the test whose code is `pre`: that of the first entry
whose code has the keys of `pre`, and `none` when a form of `pre` has no key or no entry
matches. -/
def testOutcome (dec : List (Program × Bool)) (pre : Program) : Option Bool :=
  match pre.mapM pureKey with
  | none => none
  | some ks => (dec.find? fun e => e.1.mapM pureKey == some ks).map Prod.snd

mutual

/-- A bound on `costOne` of `inst`, an `if` whose test has the outcome `o`: 3 and the bound of
the branch that `o` selects, with the branch over the else-branch after the then-branch, and
`costI` when `o` is `none`. -/
def pathI (callee : Nat → Option Nat) (fs : Nat → Option Function) (dec : List (Program × Bool))
    (ar : List Nat) (o : Option Bool) : Instruction → Option Nat
  | .iff pa ra thn els pt rt =>
      match o with
      | some true => (pathL callee fs dec (ra :: ar) [] thn).map (3 + · + 1)
      | some false => (pathL callee fs dec (ra :: ar) [] els).map (3 + ·)
      | none => costI callee fs ar (.iff pa ra thn els pt rt)
  | inst => costI callee fs ar inst

/-- A bound on `costExec` of `p` for a run that starts the list that holds `p` with the locals of
the function's entry and an empty stack and has run the code `pre` before `p`.  While the
instructions have keys, the bound charges each its `costI` and adds it to `pre`.  At an `if`
whose test `pre` is, it charges the branch that `testOutcome dec pre` selects and the rest by
`costL`, and from any other instruction on it charges `costL`. -/
def pathL (callee : Nat → Option Nat) (fs : Nat → Option Function) (dec : List (Program × Bool))
    (ar : List Nat) (pre : Program) : Program → Option Nat
  | [] => some 0
  | inst :: rest =>
      match inst with
      | .iff .. =>
          match pathI callee fs dec ar (testOutcome dec pre) inst, costL callee fs ar rest with
          | some c, some d => some (c + d)
          | _, _ => none
      | _ =>
          match pureKey inst with
          | some _ =>
              match costI callee fs ar inst, pathL callee fs dec ar (pre ++ [inst]) rest with
              | some c, some d => some (c + d)
              | _, _ => none
          | none => costL callee fs ar (inst :: rest)

end

/-- A bound on `costRun` of function `k` of `m` for the runs whose tests have the outcomes of
`dec`: `staticCost` with the body's bound from `pathL`. -/
def pathCost (m : Module) (k : Nat) (dec : List (Program × Bool)) : Option Nat :=
  match m.funcs[k]? with
  | some f =>
      (pathL (costOf m m.funcs.length) (fun j => m.funcs[j]?) dec [f.results.length] []
        f.body).map (frameCost f + ·)
  | none => none

end LeanExe.M7
