import Project.Core.Compile
import Project.Core.Loop

namespace Project.Core

open LeanExe.Core
open Project.ProofKit.ScalarTransition (State)
open Project.Compiler.ScalarLowering (Agrees capacity)

/-- Primitive implementations carry their native-to-Talos proof. The compiler
composes these proofs with control flow and recursive function calls. -/
structure Context (σ α : Type) where
  source : LeanExe.Core.Module
  effects : Effects σ
  target : Wasm.Module
  host : Wasm.HostEnv α
  effectCode : Nat → Wasm.Program
  represents : σ → Wasm.Store α → Prop
  functions : ∀ (index : Nat) (function : LeanExe.Core.Function), source[index]? = some function →
    target.funcs[index]? = some (compileFunction target.imports.length effectCode function)
  effectCorrect : ∀ (operation : Nat) (args : List UInt64) (initial : σ) (value : UInt64) (final : σ),
    effects operation args initial value final →
    ∀ (store : Wasm.Store α) (state : State), represents initial store →
    ∀ (rest : Wasm.Program) (Q : Wasm.Assertion α),
      (∀ nextStore, represents final nextStore →
        Wasm.wp target rest Q nextStore (state.toLocals [.i64 value]) host) →
      Wasm.wp target (effectCode operation ++ rest) Q store
        (state.toLocals (args.map Wasm.Value.i64).reverse) host

def StatementSpec (context : Context σ α) (source : Stmt)
    (initial : σ) (locals : LeanExe.Core.Locals) (final : σ) (result : LeanExe.Core.Locals) : Prop :=
  ∀ (scratch : Nat) (store : Wasm.Store α) (state : State),
    context.represents initial store → Agrees locals state →
    locals.length ≤ scratch → locals.length ≤ capacity state →
    scratch + width source ≤ capacity state →
    ∀ (rest : Wasm.Program) (Q : Wasm.Assertion α),
      (∀ nextStore nextState,
        context.represents final nextStore → Agrees result nextState →
        capacity nextState = capacity state →
        Wasm.wp context.target rest Q nextStore (nextState.toLocals []) context.host) →
      Wasm.wp context.target
        (statement context.target.imports.length context.effectCode scratch source ++ rest)
        Q store (state.toLocals []) context.host

def LoopSpec (context : Context σ α) (source : Stmt)
    (initial : σ) (locals : LeanExe.Core.Locals) (final : σ) (result : LeanExe.Core.Locals) : Prop :=
  match source with
  | .loop condition body =>
      ∃ count, WhileTrace
        (fun (source : σ × LeanExe.Core.Locals) flag => condition.eval source.2 = some flag)
        (fun before after : σ × LeanExe.Core.Locals =>
          after.2.length = before.2.length ∧
          StatementSpec context body before.1 before.2 after.1 after.2)
        (initial, locals) (final, result) count
  | _ => True

end Project.Core
