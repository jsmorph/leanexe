import Project.ClobMatchFuel.Program
import Project.ProofKit.FuelGuard
import Project.ProofKit.Annotation

namespace Project.ClobMatchFuel.LoopControl
open Wasm Project.ClobMatchFuel

def loopGuardProg : Wasm.Program :=
  [
  .localGet 0,
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 1 [
    .localGet 24,
    .constI64 0,
    .eqI64
  ] [
    .const 0
  ] [] [.i32],
  .eqz,
  .br_if 1
  ]

theorem loopGuard_region :
    Project.ProofKit.Annotation.region func14
      [{ instructionIndex := 26, field := .block }, { instructionIndex := 0, field := .loop }]
      0 7 = some loopGuardProg := rfl

set_option Elab.async false in
theorem loopGuard_done_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals) (fuel : UInt64)
    (_hParams : base.params.length = 9)
    (_hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hFuel : base.get 0 = some (.i64 fuel))
    (hDone : base.get 24 = some (.i64 1))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hBreak : Q (.Break 1 st base)) :
    wp «module» (loopGuardProg ++ rest) Q st base env := by
  exact Project.ProofKit.FuelGuard.program_spec 0 24 «module» env st base fuel 1
    hValues hFuel hDone Q rest (by simpa using hBreak)

set_option Elab.async false in
theorem loopGuard_zero_fuel_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (_hParams : base.params.length = 9)
    (_hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hFuel : base.get 0 = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hBreak : Q (.Break 1 st base)) :
    wp «module» (loopGuardProg ++ rest) Q st base env := by
  exact Project.ProofKit.FuelGuard.zeroFuel_spec 0 24 «module» env st base
    hValues hFuel Q rest hBreak

set_option Elab.async false in
theorem loopGuard_running_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals) (fuel : UInt64)
    (_hParams : base.params.length = 9)
    (_hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hFuel : base.get 0 = some (.i64 fuel))
    (hFuelNonzero : fuel ≠ 0)
    (hDone : base.get 24 = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hRest : wp «module» rest Q st base env) :
    wp «module» (loopGuardProg ++ rest) Q st base env := by
  exact Project.ProofKit.FuelGuard.program_spec 0 24 «module» env st base fuel 0
    hValues hFuel hDone Q rest (by simpa [hFuelNonzero] using hRest)

#print axioms loopGuard_done_spec
#print axioms loopGuard_region
#print axioms loopGuard_zero_fuel_spec
#print axioms loopGuard_running_spec

end Project.ClobMatchFuel.LoopControl
