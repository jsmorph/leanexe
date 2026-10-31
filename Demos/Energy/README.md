# Energy: authorization of battery power limits

[The program](Program.lean) decides whether a gateway may send proposed battery power limits to the inverter of a behind-the-meter solar-and-battery site for one window of time.  The inverter's own self-consumption mode follows the load within the limits, and a held setpoint `s` is the limits `[s, s]`.  An optimizer without proofs proposes the limits, and the authorizer accepts them only when every trajectory that the model admits keeps the site's energy and grid limits, or stays no further outside a limit than an immediate return to the inverter's fallback mode would.  `verified_compile` compiles the authorizer, with the test site's profile table, into a module of 6,316 bytes, and the theorems carry the authorizer's soundness to the module's bytes.  [The plan](../../energy-controller-plan.md) gives the design, the assumptions, and the stages of the work, and [the replay study](Replay.md) measures the authorizer's margins and the bills of dispatch policies on two years of a test house's data.

## The authorization problem

Signed powers are in watts and positive for charging, energies are in joules, and times are in seconds.  A profile, compiled into the module as a table, holds the site's limits and device parameters: the energy floor `E_floor` and ceiling `E_max`, the largest charge `C` and discharge `D`, the import cap `I` and export cap `X`, a lower bound `η` of the charge and discharge efficiencies, a largest auxiliary loss rate `ℓ⁺`, a tolerance `e` of battery power about a command's limits, a fallback power interval `F = [f⁻, f⁺]` that contains 0, a transition time `τ`, a window length `W`, and the gateway's send deadline `a`.  A snapshot, taken at time `t_m`, holds the interval `[E⁻, E⁺]` of stored energy, the state in force, the intervals `[L⁻, L⁺]` of load and `[S⁻, S⁺]` of PV output over the window, and the proposed limits `[c⁻, c⁺]`.  The state in force is a command with limits `[h⁻, h⁺]`, whose power interval `P` is `[h⁻ - e, h⁺ + e]`, or fallback, whose power interval `P` is `F`.

The window's power interval `B` is the smallest interval that contains `P`, `[c⁻ - e, c⁺ + e]`, and `F`, so `B⁻ = min(P⁻, c⁻ - e, f⁻)` and `B⁺ = max(P⁺, c⁺ + e, f⁺)`.  Because `F` contains 0, `B⁻ ≤ 0 ≤ B⁺`.  A side of `B` that equals the same side of `F` admits only what an immediate return to fallback admits, and the authorizer accepts it without a test.  On a side where `B` extends beyond `F`, the authorizer tests that side's grid cap and energy limit:

| Side | Grid test | Energy test |
|---|---|---|
| Lower, `B⁻ < f⁻` | Export: `L⁻ + B⁻ + X ≥ S⁺` | Floor: `E_floor + ⌈\|B⁻\| · W · 10^6 / η⌉ + ℓ⁺ · W ≤ E⁻`, with `η` in ppm |
| Upper, `B⁺ > f⁺` | Import: `L⁺ + B⁺ ≤ I + S⁻` | Ceiling: `E⁺ + B⁺ · W ≤ E_max` |

The floor test drains stored energy at efficiency `η` and the largest loss, rounded up, and the ceiling test gains it at efficiency 1 with no loss.  Each energy test bounds the end of the window, and because the drain and the gain are at least 0, it also bounds the start.  An accepted result carries the limits and the command's expiry `t_m + W - τ`, after which the device reaches fallback within `τ`, by the end of the window.  The profile requires `a + 2τ < W`, so that a command sent at the deadline `a` settles within `τ`, and the gateway's next snapshot follows, before the command expires.

## Interface

```text
profile  word   field                                          unit
         0      layout version, 1
         1, 2   energy floor and ceiling                       J
         3, 4   largest charge C and discharge D               W
         5, 6   import cap I and export cap X                  W
         7      efficiency bound η                             ppm
         8      largest auxiliary loss rate ℓ⁺                 W
         9      tolerance e about the limits                   W
         10, 11 fallback interval, as p + 2^32                 W
         12     transition time τ                              s
         13     window length W                                s
         14     send deadline a, which only the gateway uses   s

input    word   field                                          unit
         0      layout version, 1
         1      snapshot time t_m                              s
         2, 3   energy interval E⁻, E⁺                         J
         4      state in force: mode (0 command, 1 fallback)
         5, 6   limits in force h⁻, h⁺, as p + 2^32            W
         7, 8   load interval L⁻, L⁺                           W
         9, 10  PV interval S⁻, S⁺                             W
         11, 12 proposed limits c⁻, c⁺, as p + 2^32            W

result          status, lower limit, upper limit, expiry
status   0 accepted, 1 length, 2 version, 3 range, 4 order, 5 power, 6 exportCap, 7 floor,
         8 importCap, 9 ceiling: acceptance, or the first condition that fails
```

The profile's validity condition, `ProfileValid` in [the word layer](Words.lean), requires 15 words, version 1, `E_floor ≤ E_max ≤ 2^42`, every power at most `2^20` W, `η` from 500,000 to 1,000,000 ppm, `f⁻ ≤ 0 ≤ f⁺`, `W ≤ 3,600` s, and `a + 2τ < W`.  The authorizer rejects an input with status `length` unless it has 13 words, `version` unless word 0 is 1, `range` unless `t_m < 2^40`, both energies are at most `2^42`, the mode is 0 or 1, load and PV are at most `2^20`, and the four limit words lie within `2^20` of `2^32`, `order` unless every interval and both pairs of limits are ordered, and `power` unless `-D ≤ c⁻` and `c⁺ ≤ C`.  The words of the limits in force are checked in fallback mode too, so the gateway fills them, for example with `2^32`, the word of 0.  A rejection returns 0 for the limits and the expiry.

The test site's table, in [the site module](Site.lean), has an energy floor of 10,800,000 J, a ceiling of 34,200,000 J, `C`, `D`, and `I` of 5,000 W, `X` of 2,000 W, `η` of 900,000 ppm, `ℓ⁺` of 20 W, `e` of 50 W, `F = [-50, 50]` W, `τ` of 30 s, `W` of 900 s, and `a` of 60 s.  The authorizer reads the input as a borrowed array, uses no loop and no recursion, and allocates nothing, so the compiler's theorem for its export excludes traps without a premise on free memory.

## Theorems

[The specification](Spec.lean) defines the model in integers and reals, independently of the program and its word layout.  `ModelUntil` states assumptions A1 and A3 to A5 of [the plan](../../energy-controller-plan.md) from `t_m` to a time `t`: stored energy at `t_m` in `[E⁻, E⁺]`, efficiencies between `η` and 1, a loss rate between 0 and `ℓ⁺`, load and PV in their intervals, measurable power, efficiencies, and loss rate, and stored energy equal to its value at `t_m` plus the integral of its rate.  `AdmittedUntil` adds assumption A2, battery power in `B`.  `WithinOrFallback` states each site limit at `t`, or the model's worst case for an immediate return to fallback, whichever lies further out.  `tests/verified/run.sh` runs [the axiom audit](../../tests/energy/Axioms.lean) and fails unless every audited theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`, and the kernel-evaluated examples depend only on `propext`.

| Theorem | File | Hypotheses | Conclusion |
|---|---|---|---|
| `compiled.authorize.implements` | [The compilation](Verified.lean) | A heap with the allocator invariant, a memory cap of at most 65,535 pages, the profile table at its address, and argument words that represent the borrowed input | Function 17, the `authorize` export, returns the words of `authorize xs` without a trap. |
| `compiled.authorize.native` | [The compilation](Verified.lean) | A C global environment that holds the translation's globals, memory, and functions, and the premises of `compiled.authorize.implements` | The C translation's `authorize` computes `authorize xs` as `compiled.authorize.implements` states. |
| `window_sound` | [The window lemma](Window.lean) | A positive efficiency bound, a fallback interval that contains 0, the integer conditions of the tests, `t` in the window, and a trajectory admitted until `t` | `WithinOrFallback` at `t`. |
| `authorizeWith_iff` | [The authorizer's theorems](Authorize.lean) | A valid profile table | The authorizer accepts exactly when the input is valid and the integer conditions of the tests hold. |
| `site_valid` | [The site's theorems](Theorems.lean) | None | The test site's table meets the profile's validity condition. |
| `authorize_sound` | [The site's theorems](Theorems.lean) | An accepted input, `t` in the window, and a trajectory admitted until `t` | `WithinOrFallback` at `t`. |
| `authorize_accepted` | [The site's theorems](Theorems.lean) | An accepted input | The result holds the proposed limits and the expiry `t_m + W - τ`. |
| `admitted_exists`, `authorize_admits` | [The window lemma](Window.lean), [the site's theorems](Theorems.lean) | An efficiency bound of at most 1,000,000 ppm, a fallback interval that contains 0, and ordered intervals, or an accepted input | For every time `t`, some trajectory is admitted until `t`, so `authorize_sound` is not vacuous. |
| `fallback_keeps_floor`, `_ceiling`, `_export`, `_import`, `within_of_fallback` | [The specification](Spec.lean) | Fallback's worst case within one site limit, or all four, at `t`, and `WithinOrFallback` at `t` | That limit, or `Within`, at `t`. |
| `operation_sound`, `authorize_operation` | [Consecutive windows](Compose.lean), [the site's theorems](Theorems.lean) | Accepted inputs whose snapshots lie at most `W` apart, and `t` from the first snapshot to the end of the last window | `t` lies in the window of the latest accepted snapshot at or before `t`, whose bounds hold at `t` for a trajectory that meets that window's `ModelUntil` and `OperatesIn` until `t`. |
| `operates_exists` | [Consecutive windows](Compose.lean) | An efficiency bound of at most 1,000,000 ppm, ordered intervals, and a nonempty interval of the state in force | Some trajectory and applied states meet a window's `ModelUntil` and `OperatesIn`, so the composition is not vacuous. |
| `energy_authorize` | [The site's theorems](Theorems.lean) | None | The module's bytes decode to the module, whose export `authorize` is function 17, whose start store is ready, and whose entry returns `authorize xs` without a trap from every ready store, and every accepted result meets `authorize_sound`. |
| `example_accept`, `example_export`, `example_floor`, `example_relative`, `example_renewal`, `example_limits`, `example_limits_import` | [The examples](Examples.lean) | None | The decisions of the plan's worked example, by kernel evaluation. |
| `energy_file`, `energy_file_decode` | [The file theorems](File.lean) | The file `build/verified/energy.wasm` as written | The file holds `encode compiled.module` and decodes to `compiled.module`. |

`authorize_sound` would also hold of an authorizer that rejected every input, and `authorizeWith_iff` excludes that authorizer by stating the acceptance condition exactly.  `example_accept` and `example_relative` accept a discharge of 1,000 W and a charge of 3,000 W.  `example_renewal` rejects the renewal of a 1,000 W discharge whose lower energy bound would cross the floor, because the discharge in force and its renewal extend `B` below `F`, so the authorizer tests the floor.  `example_relative` accepts a charge while PV output with the battery in idle fallback could exceed the export cap, with an export bound relative to fallback's worst case of -4,550 W.  `example_limits` accepts the limits `[-1,000, 500]` W, which the authorizer tests on both sides, and `example_limits_import` rejects `[-1,000, 1,000]` W, whose charge of 1,050 W, the upper limit and the tolerance, with the load at 4,000 W and no PV could import 5,050 W.

## Consecutive windows

[The operation's specification](Operation.lean) describes a gateway that sends one accepted command after another.  A `Run` lists the accepted authorizations in order of time, each with its snapshot and limits, and `Run.Spaced` requires each accepted snapshot to follow the previous one within `W`, which is the plan's rule 5 together with the acceptance of a snapshot in each window.  For one window, `OperatesIn` states the gateway's rules and the device's response from the window's snapshot to a time `t`, with `state w` the state that the device has applied at time `w`:

| Field | Requirement | Plan's source |
|---|---|---|
| `settled` | At the snapshot, battery power lies in the interval of the state that the snapshot records | Rule 1 |
| `states` | From the snapshot to the next accepted snapshot, the applied state is the recorded one, the command authorized from this snapshot, or fallback | Rules 2 to 4 and assumption A7 |
| `low`, `high` | From the snapshot on, battery power stays within the smallest interval that contains its value at the snapshot, 0, and the intervals of the states that the device applies | The device's transitions, protective trips and deratings toward 0, and return to fallback |

`power_in_window` derives assumption A2 from `OperatesIn`, because every allowed state's interval and 0 lie in `B`.  `run_sound` gives an accepted window's bounds at each time from its snapshot to the next, and `run_covered` shows that when the run is spaced, every time from the first snapshot to the end of the last window lies in the window of the latest accepted snapshot at or before it.  `operation_sound` combines them, and `authorize_operation` states the result for the test site's module.  Its premises at `t` concern only the window that contains `t`, so a fault in one window leaves the theorems of later windows intact, and nothing is claimed after the end of the last window.

## Limits of the theorems

The theorems concern the model.  Stored energy changes only by battery power through the efficiencies and by the auxiliary loss, the grid limits are limits on instantaneous power, and load and PV output are nonnegative, so a PV inverter's standby draw counts as load.  No theorem proves the device's response or the gateway's rules, which equipment qualification and tests support, and none states anything about a time after a premise fails, or after the last window, when the fallback mode's own protections apply.  A different site needs its own profile table, its own `site_valid`, and its own module and file theorems, because the table is part of the module's bytes.

The module statements describe execution in Talos's semantics, and the agreement of Wasmtime with Talos, the decoder's reading of the bytes, Wasmtime's instantiation, and the host's placement of the input are assumptions of [the trusted base](../../docs/trusted-base.md).  The tests compare Wasmtime with native Lean on every case, which is evidence for these assumptions without proving them.  For the C translation, `compiled.authorize.native` replaces these assumptions with those that the trusted base lists for C files, among them CompCert and the Lean copy of Clight.  The replay tool implements the acceptance rule a second time and agrees with the module on every case, which is evidence that the program states the plan's rule.

## Building, running, and testing

```sh
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
tools/leanrun --timeout 60m lake build Demos.Energy.Theorems Demos.Energy.Examples
tests/verified/run.sh --cases energy
build/tools/leanexe-wasmtime-host call build/verified/energy.wasm authorize list:i64,i64,i64,i64 \
  array-u64:1,0,14400000,15120000,0,4294967296,4294967296,3000,4000,0,3000,4294966296,4294967796
lake exe verified-cases-energy > cases.txt
uv run tests/energy/replay.py check cases.txt
CCOMP=ccomp CLIGHTGEN=clightgen tests/native/verified.sh --module energy
```

The run writes `build/verified/energy.wasm`, checks its file theorems, runs the axiom audit, and compares 2,056 cases between Wasmtime and native Lean from [the case generator](../../tests/TestSupport/Energy/Cases.lean).  The cases are the worked example, invalid inputs with each word one past its range, inputs on both sides of each test's boundary and at the ends of each range, and 2,000 inputs that SplitMix64 draws from a fixed seed.  The call passes the worked example's limits `[-1,000, 500]` W and prints `0`, `4294966296`, `4294967796`, and `870` on four lines: acceptance, the two limits, and the expiry.  `lake exe verified-cases-energy --summary` prints the count of each status in each class of cases, and `replay.py check` compares every case with the replay tool's rule.  The native driver translates the module to C, compares the Clight that `clightgen` reads back from the printed C with the translation, compiles the C with CompCert 3.18's `ccomp`, and runs the same 2,056 cases.

## References

- [Verified Energy Controller: Plan and Design](../../energy-controller-plan.md)
- [Energy: replay study](Replay.md)
- [Trusted base](../../docs/trusted-base.md)
- [Verified Compiler Manual](../../docs/verified-manual.md)
- [Talos](https://github.com/jsmorph/talos)
- [Wasmtime documentation](https://docs.wasmtime.dev/)
- [WebAssembly Core Specification](https://webassembly.github.io/spec/core/)
- [Mathlib: Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.html)
- [Steele, Lea, and Flood, Fast Splittable Pseudorandom Number Generators, OOPSLA 2014](https://doi.org/10.1145/2660193.2660195)
