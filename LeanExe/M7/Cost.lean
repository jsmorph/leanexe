import LeanExe.M7.Gen
import LeanExe.M7.Div
import Interpreter.Wasm.Semantics

/-!
The instructions that the generated code executes for a run of Talos.  `costOne fuel m st s ar
inst env` follows the recursion of Talos's `execOne`, as `AlignedOne` of
`LeanExe/ProofKit/AlignedDefs.lean` does, and takes every intermediate state from Talos's
`execOne` and `exec`.  It bounds the instructions that the code of `inst`, which `genInstr` emits
under constructs whose branches carry `ar` values, executes from a state that the simulation
relates to Talos's `st` and `s`, until the code falls through, branches, or returns.  A straight-line
form costs its units from `instrSize`, a division its 9 units and `udivmod64`'s `divBound`, an
`if` its test, the taken branch, and for the then-branch the branch over the else-branch, a block
its body, a loop its body and, after a branch back to its head, the loop again, and a call the
copies of its arguments and results, `BL`, and the callee's run.  `costRun` adds a function's
prologue, clearing, and epilogue to its body's cost.
-/

namespace LeanExe.M7

open Wasm

variable {α : Type}

/-- The instructions of a call of function `id` of `m` besides the callee's: the copies of the
arguments and of the results and `BL`. -/
def callCost (m : Module) (id : Nat) : Nat :=
  match m.funcs[id - m.imports.length]? with
  | some f => 4 * f.params.length + 1 + 4 * f.results.length
  | none => 0

/-- The instructions of the prologue, the clearing of the named locals, and the epilogue of `f`,
whose return `BX LR` the epilogue's count includes. -/
def frameCost (f : Function) : Nat :=
  prologueSize + clearSize (frameOf (fun _ => none) f) + 4 * f.results.length + 3

mutual

/-- The instructions that the code of `inst` executes for `execOne fuel m st s inst env`. -/
def costOne (fuel : Nat) (m : Module) (st : Store α) (s : Locals) (ar : List Nat)
    (inst : Instruction) (env : HostEnv α) : Nat :=
  match fuel, inst with
  | 0, _ => 0
  | f + 1, .block _ ra body _ _ => costExec f m st s (ra :: ar) body env
  | f + 1, .loop pa ra body pt rt =>
    costExec f m st s (0 :: ar) body env +
      match Wasm.exec f m st s body env with
      | .Break 0 r' s' =>
        costOne f m r' { s' with values := s'.values.take pa ++ s.values.drop pa } ar
          (.loop pa ra body pt rt) env
      | _ => 0
  | f + 1, .iff _ ra thn els _ _ => match s.values with
    | .i32 c :: vs =>
      3 + if c ≠ 0 then costExec f m st { s with values := vs } (ra :: ar) thn env + 1
        else costExec f m st { s with values := vs } (ra :: ar) els env
    | _ => 0
  | f + 1, .call id => callCost m id + costRun f m id st s.values env
  | _ + 1, .divUI64 => 9 + divBound
  | _ + 1, .remUI64 => 9 + divBound
  | _ + 1, i => (instrSize (fun _ => none) ar 0 i).1
termination_by (fuel, 0, sizeOf inst)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; omega)

/-- The instructions that the code of `p` executes for `exec fuel m st s p env`. -/
def costExec (fuel : Nat) (m : Module) (st : Store α) (s : Locals) (ar : List Nat) (p : Program)
    (env : HostEnv α) : Nat :=
  match p with
  | [] => 0
  | inst :: rest =>
    costOne fuel m st s ar inst env +
      match Wasm.execOne fuel m st s inst env with
      | .Fallthrough st' s' => costExec fuel m st' s' ar rest env
      | _ => 0
termination_by (fuel, 0, sizeOf p)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.right; apply Prod.Lex.right; omega)

/-- The instructions that the code of function `id` of `m` executes for
`run fuel m id st params env`, from its entry to its return. -/
def costRun (fuel : Nat) (m : Module) (id : Nat) (st : Store α) (params : List Value)
    (env : HostEnv α) : Nat :=
  match m.imports[id]? with
  | some _ => 0
  | none =>
    match m.funcs[id - m.imports.length]? with
    | some f => frameCost f +
        costExec fuel m st (f.toLocals (params.take f.numParams).reverse) [f.results.length]
          f.body env
    | none => 0
termination_by (fuel, 2, 0)
decreasing_by
  all_goals (apply Prod.Lex.right; apply Prod.Lex.left; omega)

end

/-- The forms that `costOne` charges their units from `instrSize`: every form but a construct, a
call, and a division. -/
def plainForm : Instruction → Bool
  | .block .. | .loop .. | .iff .. | .call _ | .divUI64 | .remUI64 => false
  | _ => true

theorem costOne_plain {f : Nat} {m : Module} {st : Store α} {s : Locals} {ar : List Nat}
    {inst : Instruction} {env : HostEnv α} (h : plainForm inst = true) :
    costOne (f + 1) m st s ar inst env = (instrSize (fun _ => none) ar 0 inst).1 := by
  rw [costOne.eq_def]
  split <;> simp_all [plainForm]

theorem costExec_nil {fuel : Nat} {m : Module} {st : Store α} {s : Locals} {ar : List Nat}
    {env : HostEnv α} : costExec fuel m st s ar [] env = 0 := by
  rw [costExec.eq_def]

theorem costExec_cons {fuel : Nat} {m : Module} {st : Store α} {s : Locals} {ar : List Nat}
    {i : Instruction} {rest : Program} {env : HostEnv α} :
    costExec fuel m st s ar (i :: rest) env = costOne fuel m st s ar i env +
      match Wasm.execOne fuel m st s i env with
      | .Fallthrough st' s' => costExec fuel m st' s' ar rest env
      | _ => 0 := by
  rw [costExec.eq_def]

theorem costOne_block {f pa ra : Nat} {m : Module} {st : Store α} {s : Locals} {ar : List Nat}
    {body : Program} {pt rt : List ValueType} {env : HostEnv α} :
    costOne (f + 1) m st s ar (.block pa ra body pt rt) env = costExec f m st s (ra :: ar) body env := by
  rw [costOne.eq_def]

theorem costOne_loop {f pa ra : Nat} {m : Module} {st : Store α} {s : Locals} {ar : List Nat}
    {body : Program} {pt rt : List ValueType} {env : HostEnv α} :
    costOne (f + 1) m st s ar (.loop pa ra body pt rt) env = costExec f m st s (0 :: ar) body env +
      match Wasm.exec f m st s body env with
      | .Break 0 r' s' =>
        costOne f m r' { s' with values := s'.values.take pa ++ s.values.drop pa } ar
          (.loop pa ra body pt rt) env
      | _ => 0 := by
  rw [costOne.eq_def]

theorem costOne_iff {f pa ra : Nat} {m : Module} {st : Store α} {s : Locals} {ar : List Nat}
    {thn els : Program} {pt rt : List ValueType} {env : HostEnv α} {c : UInt32}
    {vs : List Value} (hv : s.values = .i32 c :: vs) :
    costOne (f + 1) m st s ar (.iff pa ra thn els pt rt) env =
      3 + if c ≠ 0 then costExec f m st { s with values := vs } (ra :: ar) thn env + 1
        else costExec f m st { s with values := vs } (ra :: ar) els env := by
  rw [costOne.eq_def]
  simp only [hv]

theorem costOne_call {f id : Nat} {m : Module} {st : Store α} {s : Locals} {ar : List Nat}
    {env : HostEnv α} :
    costOne (f + 1) m st s ar (.call id) env = callCost m id + costRun f m id st s.values env := by
  rw [costOne.eq_def]

theorem costRun_some {fuel id : Nat} {m : Module} {st : Store α} {params : List Value}
    {env : HostEnv α} {f : Function} (hi : m.imports[id]? = none)
    (hf : m.funcs[id - m.imports.length]? = some f) :
    costRun fuel m id st params env = frameCost f +
      costExec fuel m st (f.toLocals (params.take f.numParams).reverse) [f.results.length] f.body
        env := by
  rw [costRun.eq_def]
  simp only [hi, hf]

theorem costOne_divUI64 {f : Nat} {m : Module} {st : Store α} {s : Locals} {ar : List Nat}
    {env : HostEnv α} : costOne (f + 1) m st s ar .divUI64 env = 9 + divBound := by
  rw [costOne.eq_def]

theorem costOne_remUI64 {f : Nat} {m : Module} {st : Store α} {s : Locals} {ar : List Nat}
    {env : HostEnv α} : costOne (f + 1) m st s ar .remUI64 env = 9 + divBound := by
  rw [costOne.eq_def]

theorem le_costOne_plain {n f : Nat} {m : Module} {st : Store α} {s : Locals} {ar : List Nat}
    {inst : Instruction} {env : HostEnv α} (h : plainForm inst = true)
    (hn : n = (instrSize (fun _ => none) ar 0 inst).1) : n ≤ costOne (f + 1) m st s ar inst env := by
  rw [costOne_plain h, hn]
  exact Nat.le_refl _

end LeanExe.M7
