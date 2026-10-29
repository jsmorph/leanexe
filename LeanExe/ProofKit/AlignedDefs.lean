import Interpreter.Wasm.Semantics

/-!
The aligned runs.  `AlignedExec fuel m st s p env` states that every 64-bit load and store that
`exec fuel m st s p env` performs inside memory has an address that is a multiple of 8.  The
predicates follow the recursion of Talos's `execOne`, `exec`, `run`, and `runTail` and take every
intermediate state from those functions, so that no instruction's semantics is restated.  An
access out of bounds traps before it reads or writes, so only an access inside memory must be
aligned.  The module imports only Talos's semantics, so that the proofs of the translator to C
can state the premise without the rules of `wp` and their imports.
-/

namespace LeanExe.ProofKit

open Wasm

variable {α : Type}

mutual

/-- The 64-bit accesses of `execOne fuel m st s inst env` inside memory are aligned. -/
def AlignedOne (fuel : Nat) (m : Module) (st : Store α) (s : Locals) (inst : Instruction)
    (env : HostEnv α) : Prop :=
  match fuel, inst with
  | 0, _ => True
  | _ + 1, .load64 off => match s.values with
    | .i32 a :: _ => a.toNat + off.toNat + 8 ≤ st.mem.pages * 65536 →
        (a.toNat + off.toNat) % 8 = 0
    | .i64 a :: _ => a.toNat + off.toNat + 8 ≤ st.mem.pages * 65536 →
        (a.toUInt32.toNat + off.toNat) % 8 = 0
    | _ => True
  | _ + 1, .store64 off => match s.values with
    | .i64 _ :: .i32 a :: _ => a.toNat + off.toNat + 8 ≤ st.mem.pages * 65536 →
        (a.toNat + off.toNat) % 8 = 0
    | .i64 _ :: .i64 a :: _ => a.toNat + off.toNat + 8 ≤ st.mem.pages * 65536 →
        (a.toUInt32.toNat + off.toNat) % 8 = 0
    | _ => True
  | f + 1, .block _ _ body _ _ => AlignedExec f m st s body env
  | f + 1, .loop pa ra body pt rt =>
    AlignedExec f m st s body env ∧
      match exec f m st s body env with
      | .Break 0 r' s' =>
        AlignedOne f m r' { s' with values := s'.values.take pa ++ s.values.drop pa }
          (.loop pa ra body pt rt) env
      | _ => True
  | f + 1, .iff _ _ thn els _ _ => match s.values with
    | .i32 c :: vs => AlignedExec f m st { s with values := vs } (if c ≠ 0 then thn else els) env
    | _ => True
  | f + 1, .call id => AlignedRun f m id st s.values env
  | _ + 1, _ => True
termination_by (fuel, 0, sizeOf inst)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; omega)

/-- The 64-bit accesses of `exec fuel m st s p env` inside memory are aligned. -/
def AlignedExec (fuel : Nat) (m : Module) (st : Store α) (s : Locals) (p : Program)
    (env : HostEnv α) : Prop :=
  match p with
  | [] => True
  | inst :: rest =>
    AlignedOne fuel m st s inst env ∧
      match execOne fuel m st s inst env with
      | .Fallthrough st' s' => AlignedExec fuel m st' s' rest env
      | _ => True
termination_by (fuel, 0, sizeOf p)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.right; apply Prod.Lex.right; omega)

/-- The 64-bit accesses of `run fuel m id st params env` inside memory are aligned. -/
def AlignedRun (fuel : Nat) (m : Module) (id : Nat) (st : Store α) (params : List Value)
    (env : HostEnv α) : Prop :=
  match m.imports[id]? with
  | some _ => True
  | none =>
    match m.funcs[id - m.imports.length]? with
    | some f =>
      AlignedExec fuel m st (f.toLocals (params.take f.numParams).reverse) f.body env ∧
        match exec fuel m st (f.toLocals (params.take f.numParams).reverse) f.body env with
        | .ReturnCall id' st' vs => AlignedRunTail fuel m id' st' vs env
        | _ => True
    | none => True
termination_by (fuel, 2, 0)
decreasing_by
  all_goals (apply Prod.Lex.right; apply Prod.Lex.left; omega)

/-- The 64-bit accesses of `runTail fuel m id st vs env` inside memory are aligned. -/
def AlignedRunTail (fuel : Nat) (m : Module) (id : Nat) (st : Store α) (vs : List Value)
    (env : HostEnv α) : Prop :=
  match fuel with
  | 0 => True
  | f + 1 => AlignedRun f m id st vs env
termination_by (fuel, 1, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; omega)

end

end LeanExe.ProofKit
