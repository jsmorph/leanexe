import Interpreter.Wasm.Host.Registry
import Interpreter.Wasm.Semantics.Lemmas

namespace Verified.Wasi.PureTransport

open Wasm

def erase (store : Store World) : Store Unit :=
  store.mapHost fun _ => ()

def restore (world : World) (store : Store Unit) : Store World :=
  store.mapHost fun _ => world

@[simp] theorem erase_restore (world : World) (store : Store Unit) :
    erase (restore world store) = store := by
  change { store with host := () } = store
  rw [Subsingleton.elim () store.host]

@[simp] theorem restore_erase (store : Store World) :
    restore store.host (erase store) = store := rfl

@[simp] theorem restore_host (world : World) (store : Store Unit) :
    (restore world store).host = world := rfl

@[simp] theorem erase_mem (store : Store World) : (erase store).mem = store.mem := rfl

@[simp] theorem erase_globals (store : Store World) :
    (erase store).globals = store.globals := rfl

@[simp] theorem erase_memoryCaps (store : Store World) :
    (erase store).memoryCaps = store.memoryCaps := rfl

def liftContinuation (world : World) : Continuation Unit → Continuation World
  | .Fallthrough store locals => .Fallthrough (restore world store) locals
  | .Break label store locals => .Break label (restore world store) locals
  | .Return store values => .Return (restore world store) values
  | .Trap store message => .Trap (restore world store) message
  | .Invalid message => .Invalid message
  | .OutOfFuel => .OutOfFuel
  | .ReturnCall entry store values => .ReturnCall entry (restore world store) values
  | .Throwing tag values store locals => .Throwing tag values (restore world store) locals

def liftResult (world : World) : Result Unit → Result World
  | .Success values store => .Success values (restore world store)
  | .Trap store message => .Trap (restore world store) message
  | .Invalid message => .Invalid message
  | .OutOfFuel => .OutOfFuel
  | .Thrown tag values store => .Thrown tag values (restore world store)

def NoReturnCall : Continuation World → Prop
  | .ReturnCall _ _ _ => False
  | _ => True

def NoReturnCalls (m : Module) (code : Program) : Prop :=
  ∀ (fuel : Nat) (store : Store Unit) (locals : Locals) (host : HostEnv Unit),
    NoReturnCall (exec fuel m store locals code host)

/-- This premise requires an instruction-execution proof.  The remaining pure-code theorem
must establish it for closed direct calls, nested control flow, and the emitted atomic
instructions, including allocator memory growth. -/
def CodeTransport (World : Type) (source target : Module)
    (sourceCode targetCode : Program) : Prop :=
  ∀ (fuel : Nat) (initial : Store Unit) (world : World) (locals : Locals)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World),
    exec fuel target (restore world initial) locals targetCode targetHost =
      liftContinuation world (exec fuel source initial locals sourceCode sourceHost)

structure FunctionShape (source target : Function) : Prop where
  params : target.params = source.params
  locals : target.locals = source.locals
  results : target.results = source.results

theorem FunctionShape.frame {source target : Function} (h : FunctionShape source target)
    (args : List Value) :
    target.toLocals (args.take target.numParams).reverse =
      source.toLocals (args.take source.numParams).reverse := by
  simp only [Function.toLocals, Function.numParams, h.params, h.locals]

theorem nil_transport (World : Type) (source target : Module) :
    CodeTransport World source target [] [] := by
  intro fuel initial world locals sourceHost targetHost
  simp only [exec, liftContinuation]

theorem noReturnCalls_nil (m : Module) : NoReturnCalls m [] := by
  intro fuel store locals host
  simp only [exec, NoReturnCall]

theorem execOne_unreachable {World : Type} (source target : Module) (fuel : Nat)
    (initial : Store Unit) (world : World) (locals : Locals)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    execOne fuel target (restore world initial) locals .unreachable targetHost =
      liftContinuation world (execOne fuel source initial locals .unreachable sourceHost) := by
  cases fuel <;> simp only [execOne.eq_def, liftContinuation]

theorem run_frame_at {World : Type} {source target : Module} {index : Nat}
    {sourceFunction targetFunction : Function}
    (hSourceImports : source.imports = []) (hTargetImports : target.imports.length = 3)
    (hSourceFunction : source.funcs[index]? = some sourceFunction)
    (hTargetFunction : target.funcs[index]? = some targetFunction)
    (hShape : FunctionShape sourceFunction targetFunction)
    (fuel : Nat) (initial : Store Unit) (world : World) (args : List Value)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World)
    (hBody : ∀ locals,
      exec fuel target (restore world initial) locals targetFunction.body targetHost =
        liftContinuation world (exec fuel source initial locals sourceFunction.body sourceHost))
    (hNoTail : ∀ locals,
      NoReturnCall (exec fuel source initial locals sourceFunction.body sourceHost)) :
    run fuel target (3 + index) (restore world initial) args targetHost =
      liftResult world (run fuel source index initial args sourceHost) := by
  have hSourceNoImport : source.imports[index]? = none := by simp [hSourceImports]
  have hTargetNoImport : target.imports[3 + index]? = none :=
    List.getElem?_eq_none (by omega)
  have hSourcePosition : index - source.imports.length = index := by simp [hSourceImports]
  have hTargetPosition : 3 + index - target.imports.length = index := by omega
  rw [run_eq hTargetNoImport, run_eq hSourceNoImport]
  simp only [hSourcePosition, hTargetPosition, hSourceFunction, hTargetFunction]
  rw [hShape.frame args]
  simp only [Function.numParams, hShape.params, hShape.results]
  rw [hBody (sourceFunction.toLocals (args.take sourceFunction.params.length).reverse)]
  have hNo := hNoTail (sourceFunction.toLocals (args.take sourceFunction.params.length).reverse)
  cases hExec : exec fuel source initial
      (sourceFunction.toLocals (args.take sourceFunction.params.length).reverse)
      sourceFunction.body sourceHost with
  | Fallthrough store locals => rfl
  | Break label store locals => cases label <;> rfl
  | Return store values => rfl
  | Trap store message => rfl
  | Invalid message => rfl
  | OutOfFuel => rfl
  | ReturnCall entry store values =>
      simp only [hExec, NoReturnCall] at hNo
  | Throwing tag values store locals => rfl

theorem run_frame {World : Type} {source target : Module} {index : Nat}
    {sourceFunction targetFunction : Function}
    (hSourceImports : source.imports = []) (hTargetImports : target.imports.length = 3)
    (hSourceFunction : source.funcs[index]? = some sourceFunction)
    (hTargetFunction : target.funcs[index]? = some targetFunction)
    (hShape : FunctionShape sourceFunction targetFunction)
    (hBody : CodeTransport World source target sourceFunction.body targetFunction.body)
    (hNoTail : NoReturnCalls source sourceFunction.body)
    (fuel : Nat) (initial : Store Unit) (world : World) (args : List Value)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    run fuel target (3 + index) (restore world initial) args targetHost =
      liftResult world (run fuel source index initial args sourceHost) :=
  run_frame_at hSourceImports hTargetImports hSourceFunction hTargetFunction hShape
    fuel initial world args sourceHost targetHost
    (fun locals => hBody fuel initial world locals sourceHost targetHost)
    (fun locals => hNoTail fuel initial locals sourceHost)

theorem exec_call_cons_of_run {World : Type} {source target : Module}
    {sourceEntry targetEntry fuel : Nat} {initial : Store Unit} {world : World}
    {locals : Locals} {sourceRest targetRest : Program}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    (hRun : run fuel target targetEntry (restore world initial) locals.values targetHost =
      liftResult world (run fuel source sourceEntry initial locals.values sourceHost))
    (hRest : CodeTransport World source target sourceRest targetRest) :
    exec (fuel + 1) target (restore world initial) locals
        (.call targetEntry :: targetRest) targetHost =
      liftContinuation world (exec (fuel + 1) source initial locals
        (.call sourceEntry :: sourceRest) sourceHost) := by
  rw [exec_call_cons, exec_call_cons, hRun]
  cases hSourceRun : run fuel source sourceEntry initial locals.values sourceHost with
  | Success values store =>
      exact hRest (fuel + 1) store world { locals with values := values } sourceHost targetHost
  | Trap store message => rfl
  | Invalid message => rfl
  | OutOfFuel => rfl
  | Thrown tag values store => rfl

end Verified.Wasi.PureTransport
