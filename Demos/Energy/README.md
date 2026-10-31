# Energy: authorization of battery setpoints

[The program](Program.lean) decides whether a gateway may send a proposed battery setpoint to the inverter of a behind-the-meter solar-and-battery site for one window of time.  An optimizer without proofs proposes the setpoint, and the authorizer accepts it only when every trajectory that the model admits keeps the site's energy and grid limits, or stays no further outside a limit than an immediate return to the inverter's fallback mode would.  `verified_compile` compiles the authorizer, with the test site's profile table, into a module of 5,922 bytes, and the theorems carry the authorizer's soundness to the module's bytes.  [The plan](../../energy-controller-plan.md) gives the design, the assumptions, and the stages of the work beyond this module, and [the replay study](Replay.md) measures the authorizer's margins and the bills of dispatch policies on two years of a test house's data.

## The authorization problem

A profile, compiled into the module as a table, holds the site's limits and device parameters: an energy floor and ceiling in joules, setpoint limits, grid import and export caps in watts, a lower bound `η` of the charge and discharge efficiencies, a largest auxiliary loss rate `ℓ⁺`, a tracking tolerance `e`, a fallback power interval `F` that contains 0, a transition time `τ`, and a window length `W`.  A snapshot, taken at time `t_m`, holds the interval of stored energy, the state in force (a command with its setpoint, or fallback), the intervals of load and PV output over the window, and the proposed setpoint `s`.  Signed powers are positive for charging.

The window's power interval `B` is the smallest interval that contains the interval of the state in force, `[s - e, s + e]`, and `F`.  When `B` extends below `F`, the authorizer tests the export cap, `L⁻ + B⁻ + X ≥ S⁺`, and the energy floor at both ends of the window, with the lower energy bound discharging at efficiency `η` and losing `ℓ⁺`, rounded up.  When `B` extends above `F`, it tests the import cap, `L⁺ + B⁺ ≤ I + S⁻`, and the energy ceiling, with the upper energy bound charging at efficiency 1 with no loss.  A side of `B` that equals the same side of `F` admits only what an immediate return to fallback admits, and the authorizer accepts it without a test.  An accepted result carries the setpoint and the command's expiry `t_m + W - τ`.

## Interface

```text
profile  word   field                                          unit
         0      layout version, 1
         1, 2   energy floor and ceiling                       J
         3, 4   largest charge and discharge setpoints         W
         5, 6   import and export caps                         W
         7      efficiency bound η                             ppm
         8      largest auxiliary loss rate ℓ⁺                 W
         9      tracking tolerance e                           W
         10, 11 fallback interval, as p + 2^32                 W
         12     transition time τ                              s
         13     window length W                                s
         14     send deadline, which only the gateway uses     s

input    word   field                                          unit
         0      layout version, 1
         1      snapshot time t_m                              s
         2, 3   energy interval                                J
         4, 5   state in force: mode (0 command, 1 fallback)
                and setpoint, as p + 2^32                      W
         6, 7   load interval                                  W
         8, 9   PV interval                                    W
         10     proposed setpoint, as p + 2^32                 W

result          status, setpoint, expiry
status   0 accepted, 1 length, 2 version, 3 range, 4 order, 5 power, 6 exportCap, 7 floor,
         8 importCap, 9 ceiling: acceptance, or the first condition that fails
```

The test site's table, in [the site module](Site.lean), has an energy floor of 10,800,000 J, a ceiling of 34,200,000 J, setpoint limits and an import cap of 5,000 W, an export cap of 2,000 W, `η` of 900,000 ppm, `ℓ⁺` of 20 W, `e` of 50 W, `F = [-50, 50]` W, `τ` of 30 s, `W` of 900 s, and a send deadline of 60 s.  The authorizer reads the input as a borrowed array, uses no loop and no recursion, and allocates nothing, so the compiler's theorem for its export excludes traps without a premise on memory.  A rejection returns 0 for the setpoint and the expiry.

## Theorems

Every theorem in the table depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`, which [the axiom audit](../../tests/energy/Axioms.lean) confirms, and the kernel-evaluated examples depend only on `propext`.  [The specification](Spec.lean) defines the model in integers and reals, independently of the program and its word layout.  `AdmittedUntil` states the assumptions from `t_m` to a time `t`: stored energy at `t_m` in the snapshot's interval, battery power in `B`, efficiencies between `η` and 1, loss rate between 0 and `ℓ⁺`, load and PV in their intervals, measurable power, efficiencies, and loss rate, and stored energy equal to its value at `t_m` plus the integral of the rate.  `WithinOrFallback` states each limit at `t`, or the model's worst case for an immediate return to fallback, whichever lies further out.

| Theorem | File | Hypotheses | Conclusion |
|---|---|---|---|
| `compiled.authorize.implements` | [The compilation](Verified.lean) | A heap with the allocator invariant, a memory cap of at most 65,535 pages, the profile table at its address, and argument words that represent the borrowed input | Function 17, the `authorize` export, returns the words of `authorize xs` without a trap. |
| `window_sound` | [The window lemma](Window.lean) | A positive efficiency bound, a fallback interval that contains 0, the integer conditions of the tests, `t` in the window, and a trajectory admitted until `t` | `WithinOrFallback` at `t`. |
| `authorizeWith_iff` | [The authorizer's theorems](Authorize.lean) | A valid profile table | The authorizer accepts exactly when the input is valid and the integer conditions of the tests hold. |
| `site_valid` | [The site's theorems](Theorems.lean) | None | The test site's table meets the profile's validity condition. |
| `authorize_sound` | [The site's theorems](Theorems.lean) | An accepted input, `t` in the window, and a trajectory admitted until `t` | `WithinOrFallback` at `t`. |
| `authorize_accepted` | [The site's theorems](Theorems.lean) | An accepted input | The result holds the proposed setpoint and the expiry `t_m + W - τ`. |
| `fallback_keeps_floor`, `_ceiling`, `_export`, `_import` | [The specification](Spec.lean) | Fallback's worst case within one limit at `t`, and `WithinOrFallback` at `t` | That limit at `t`. |
| `energy_authorize` | [The site's theorems](Theorems.lean) | None | The module's bytes decode to the module, whose export `authorize` is function 17, whose start store is ready, and whose entry returns `authorize xs` without a trap from every ready store, and every accepted result meets `authorize_sound`. |
| `example_accept`, `example_export`, `example_floor`, `example_relative`, `example_renewal` | [The examples](Examples.lean) | None | The decisions of the plan's worked example, by kernel evaluation. |
| `energy_file`, `energy_file_decode` | [The file theorems](File.lean) | The file `build/verified/energy.wasm` as written | The file holds `encode compiled.module` and decodes to `compiled.module`. |

`authorizeWith_iff` states the acceptance condition exactly, so the theorems hold of an authorizer that accepts inputs: `example_accept` and `example_relative` accept a discharge of 1,000 W and a charge of 3,000 W.  `example_renewal` rejects the renewal of a 1,000 W discharge in force whose lower energy bound would cross the floor, because the state in force extends `B` below `F` and the authorizer then tests the floor.  `example_relative` accepts a charge while the PV output of idle fallback could exceed the export cap, with an export bound relative to fallback's worst case of -4,550 W.

## Limits of the theorems

The theorems concern the model.  Stored energy changes only by battery power through the efficiencies and by the auxiliary loss, the grid limits are limits on instantaneous power, and load and PV output are nonnegative, so a PV inverter's standby draw counts as load.  The device properties that give battery power in `B` (tracking within `e`, transitions between the old and new states that end within `τ`, protective reductions toward 0, and the return to fallback at expiry) and the gateway's rules for snapshots and sends are assumptions that qualification and tests support, and no theorem proves them.  The theorems state nothing about a time after a premise fails, and nothing after the window, when the fallback mode's own protections apply.

The module statements describe execution in Talos's semantics, and the agreement of Wasmtime with Talos, the decoder's reading of the bytes, Wasmtime's instantiation, and the host's placement of the input are assumptions of [the trusted base](../../docs/trusted-base.md).  The tests compare Wasmtime with native Lean on every case, which is evidence for these assumptions without proving them.  A different site needs its own profile table, its own `site_valid`, and its own module and file theorems, because the table is part of the module's bytes.

## Building, running, and testing

```sh
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
tools/leanrun --timeout 60m lake build Demos.Energy.Theorems Demos.Energy.Examples
tests/verified/run.sh --cases energy
build/tools/leanexe-wasmtime-host call build/verified/energy.wasm authorize list:i64,i64,i64 \
  array-u64:1,0,14400000,15120000,0,4294967296,3000,4000,0,3000,4294966296
```

The run writes `build/verified/energy.wasm`, checks its file theorems and the axiom audit, and compares 2,038 cases between Wasmtime and native Lean from [the case generator](../../tests/TestSupport/Energy/Cases.lean): the worked example, invalid inputs, inputs on both sides of each test's boundary, and 2,000 inputs drawn from SplitMix64.  The call is the worked example's discharge of 1,000 W, and it prints `0`, `4294966296`, and `870` on three lines: acceptance, the setpoint, and the expiry.  `lake exe verified-cases-energy --summary` prints the count of each status in each class of cases.
