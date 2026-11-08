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

end LeanExe.M7
