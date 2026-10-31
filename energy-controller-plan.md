# Verified Energy Controller: Plan and Design

The energy controller schedules the battery of a behind-the-meter solar-and-battery site to lower the electricity bill while it keeps the battery's stored energy and the site's grid import and export within configured limits.  An optimizer without proofs proposes a battery setpoint, and an authorizer compiled with `verified_compile` decides whether a gateway may send it to the battery inverter for the next window of time.  The authorizer's theorem states that an accepted setpoint keeps each modeled limit, or leaves the site no further outside a limit than an immediate return to fallback would, for every load, solar output, efficiency, loss, and device response that the stated assumptions admit.  The compiler's generated theorems and a file theorem connect that statement to the bytes of the WebAssembly module that the gateway runs.  This document gives the scope, the model, the interfaces, the theorems, the tests, and the stages of the work.

## Scope

The first release covers one site with an AC-coupled battery inverter and its battery management system (BMS), a photovoltaic (PV) inverter, the site's loads, and one grid meter.  The controller sets the battery's AC power and nothing else.  The inverters and the BMS keep their own electrical, thermal, state-of-charge, interconnection, and export protections, and the controller never changes their settings.

| Subject | Choice | Reason |
|---|---|---|
| Site | One battery, PV, site load, one grid meter | Small enough for a precise model |
| Electrical architecture | AC-coupled and grid-connected, with no islanding | Islanding and grid-forming behavior remain functions of the inverter |
| Control variable | Battery AC power setpoint, signed, positive for charging | The inverter's own control loop tracks it |
| Verified component | One authorizer that accepts or rejects one setpoint for a window of `W` seconds | The window covers the setpoint, its expiry, and the return to fallback |
| Limits | Energy floor and ceiling, and instantaneous grid import and export caps | An instantaneous cap also bounds every average |
| Profile | Installer's and owner's limits and device parameters, compiled into the module | The theorem names the limits, and the file theorem fixes them in the released bytes |
| Arithmetic | `UInt64` words in fixed units with validated ranges | Every operation on an accepted input equals the integer operation |
| Specification | Real numbers and Mathlib's interval integral | The physical model is defined apart from the authorizer |
| Optimizer | A short rule without proofs | The theorem holds for every proposal |
| Tariffs and costs | Outside the authorizer | The evaluation measures savings against baselines |

The first release excludes schedules longer than one window, time-varying reserves, EV charging, grid-forming control, islanding, protection relays, thermal management, cell balancing, breaker control, frequency and voltage regulation, per-phase limits, demand charges, tiered rates, and negative prices.  It makes no claim about the accuracy of forecasts or of the BMS's energy estimate, and the theorem takes both as premises in the form of intervals.  It makes no claim about the WebAssembly engine, the operating system, the gateway, or the device firmware beyond the assumptions that the next two sections list.

## Guarantees and their limits

The model, module, and file levels of the guarantee are theorems.  The installation level consists of the qualification, commissioning, and operating evidence that Stages 4 to 7 collect.  A claim about the running system needs every level, and each level adds its own assumptions.

| Level | Claim | Evidence | Depends on |
|---|---|---|---|
| Model | An accepted setpoint keeps every admitted trajectory of its window within each limit, or no further outside it than an immediate return to fallback | Theorems about Lean functions and the real-valued model | Assumptions A1 to A5 |
| Module | The module's export computes the authorizer and returns without a trap | `p.f.implements` and `p.bytes`, which `verified_compile` generates | Talos's semantics, the binary decoder, the initial store, and the host's placement of arguments |
| File | The released file holds the module's encoding | `energy_file` and `energy_file_decode` | The file as it was when Lean checked the theorem, and the gateway's digest check when it loads the file |
| Installation | The site behaves as the model states | Equipment qualification, commissioning, read-only operation, and fault-injection tests | Measurements, device firmware, the gateway, communication, and wiring |

A window's theorem covers the interval from one measurement to the end of the window, including the command's expiry and the device's return to fallback.  The gateway authorizes a new setpoint from a new measurement before the current command expires, so consecutive windows overlap and each has its own theorem.  Each theorem takes its premises only up to the time of its conclusion, so a window's theorem covers the site until power leaves that window's interval, which the next command can cause only after the next measurement has started the next window.  When no new authorization arrives, the device runs in its fallback mode after the window, and the safety of that mode then depends on the device's own protections (A8).

## Site, equipment, and assumptions

The equipment must accept a battery power setpoint with an expiry, after which the inverter returns to a fallback mode without help from the controller.  The vendor must document the fallback mode, its power interval, and the time the inverter takes to reach it, and qualification measures each of them.  The equipment must report battery power, site import and export, PV output, and the BMS's usable-energy estimate with a stated error.  A site whose equipment lacks command expiry or a qualified fallback mode runs only in read-only operation.

| ID | Assumption | Role in the theorem | Evidence |
|---|---|---|---|
| A1 | At the snapshot time `t_m`, usable stored energy lies in `[E⁻, E⁺]` | Premise | Characterization of the BMS estimate against metered charge and discharge |
| A2 | From `t_m` to `t`, battery AC power lies in the window's power interval `B` | Premise | Qualification of tracking tolerance, transitions, expiry, and fallback, and the gateway's rules |
| A3 | From `t_m` to `t`, the charge and discharge efficiencies lie between `η` and 1, and the auxiliary loss rate between 0 and `ℓ⁺` | Premise | Characterization over the permitted power and temperature range |
| A4 | From `t_m` to `t`, instantaneous load and PV output lie within the snapshot's intervals | Premise | Statistics of high-resolution measurements, which a proof cannot supply |
| A5 | Stored energy changes only through battery power, the efficiencies, and the auxiliary loss, as the energy equation states, with measurable power, efficiencies, and loss rate | Premise, as the model | Comparison of the model with measured energy |
| A6 | The profile matches the installed equipment, the approved interconnection, and the owner's policy | Outside | Installer and owner sign-off |
| A7 | The snapshot time and the gateway's record of the state in force are correct, and every change of state, including an expiry, takes effect within the transition time `τ` of its time on the gateway's clock | Outside | Clock synchronization checks and device qualification |
| A8 | The BMS and inverters enforce their protections, and the fallback mode keeps the equipment within its limits without the controller | Outside | Vendor documentation and commissioning tests |

The theorem takes each premise on the interval from `t_m` to a time `t` and concludes the bounds at `t`, because `E(t)` and `G(t)` depend only on the trajectory up to `t`, and it states nothing about a trajectory after the time at which the trajectory violates a premise.  The gateway compares live measurements with the snapshot's intervals during the window and returns the device to fallback when a measurement falls outside them or when telemetry stops, and assumption A2 already includes that return.  Coverage statistics for A4 from historical data are evidence about future load and PV, and no theorem can supply that evidence.

The controller performs supervisory economic dispatch, and the site's protection consists of the BMS, the inverters, and the installation's protective devices.  The installation remains subject to the local adoption of the electrical code (NFPA 70), the energy-storage installation standard (NFPA 855), equipment listing (UL 9540), and the interconnection standard (IEEE 1547), and to the utility's interconnection approval.  Writes to devices start only after the installer and the equipment vendor approve the fallback mode, the limits, and the monitoring, and the theorem certifies no part of the installation.

## Plant model

### Units and ranges

The authorizer and the specification work in joules, watts, seconds, and parts per million.  The profile's validity condition bounds every quantity, and under those bounds every product that the authorizer computes stays below `2^53`, which is less than `2^64`, so each `UInt64` operation on an accepted input equals the corresponding operation on natural numbers.  The proofs establish this equality operation by operation, and the authorizer subtracts only where a validated range or a preceding comparison keeps the result nonnegative, so no operation wraps.

| Quantity | Unit | Representation | Range that validity requires |
|---|---|---|---|
| Power, including the tracking tolerance | W | `UInt64`; a signed power `p` as the word `p + 2^32` | `\|p\| ≤ 2^20` W |
| Energy | J | `UInt64` | At most `2^42` J, about 1.2 GWh |
| Time | s, UTC | `UInt64` | Window at most 3,600 s; times below `2^40` |
| Efficiency | ppm | `UInt64` | 500,000 to 1,000,000 |
| Auxiliary loss rate | W | `UInt64` | At most `2^20` W |

### Battery power in a window

A snapshot taken at time `t_m` records the state in force, a command with setpoint `p` or fallback.  A command's interval is `[p - e, p + e]`, where `e` is the profile's tracking tolerance, and fallback's interval is the profile's fallback interval `F = [f⁻, f⁺]`.  The gateway takes a snapshot only after the last change of state has completed, so battery power at `t_m` lies in the interval `P` of the state in force.  The fallback interval contains 0, because a protective trip or derating by the BMS or an inverter moves power toward 0.  For a proposed setpoint `s`, the window's power interval `B` is the smallest interval that contains `P`, `[s - e, s + e]`, and `F`:

```text
B⁻ = min(P⁻, s - e, f⁻)
B⁺ = max(P⁺, s + e, f⁺)
```

Qualification of the equipment establishes the device properties from which assumption A2 follows.  When the device's state changes, by a new setpoint, by the command's expiry, or by a request to return to fallback, its power stays between its value at the change and the new state's interval, and it enters that interval within `τ` seconds of the change's time on the gateway's clock, including the delivery delay, the application delay, the ramp, and the difference between the clocks.  Once settled, power stays in the state's interval, except that a protective trip or derating moves it toward 0 and keeps it between its value and 0.  `B` is an interval that contains `P`, `[s - e, s + e]`, `F`, and 0, so every sequence of these changes inside the window keeps power in `B`, whatever the delays.

The window starts at `t_m` and ends at `t_m + W`.  The authorizer returns the command's expiry `t_x = t_m + W - τ`, and the device reaches fallback by the end of the window unless a later authorization replaced the command.  Assumption A2 also requires the gateway to follow these rules, which Stage 6 tests:

1. Take a snapshot only after the last change of state has completed, `τ` seconds after it, and only when measured battery power lies in the state's interval.
2. Send at most one command for each authorization, only from the authorization of the most recent snapshot, with the expiry `t_x` that the authorizer returned, and only before `t_m + a`, where the profile's send deadline `a` meets `W > a + 2τ`, so that a command sent at the deadline settles, and the next snapshot follows, before the command expires.
3. Send exactly the returned setpoint, and nothing on a rejection.
4. Return the device to fallback when a measurement leaves the snapshot's intervals or telemetry stops, and send nothing more from the current authorization.
5. Take the next snapshot after the new command has settled and before `t_x`, to continue control without a gap.

### Stored energy

Let `E(t)` be usable stored energy, `b(t)` battery AC power, `η_c(t)` and `η_d(t)` the charge and discharge efficiencies, and `ℓ(t)` the auxiliary loss rate, with `b`, `η_c`, `η_d`, and `ℓ` measurable, so that the bounds of A2 and A3 make the integrand `ρ` below bounded and integrable.  In the model, charging stores the AC power times the charge efficiency, and discharging removes the AC power divided by the discharge efficiency.  For fixed efficiencies `ρ` is nondecreasing in `b`, so the bounds of A2 and A3 bound the rate as the second part of the block states.

```text
E(t) = E(t_m) + ∫_{t_m}^{t} ρ(u) du
ρ(u) = η_c(u) · max(b(u), 0) - max(-b(u), 0) / η_d(u) - ℓ(u)

r⁻ = g(B⁻) - ℓ⁺      g(b) = η · b if b ≥ 0,  b / η if b < 0
r⁺ = B⁺
```

Integrating the rate bounds with Mathlib's `intervalIntegral.integral_mono_on` gives `E⁻ + r⁻ (t - t_m) ≤ E(t) ≤ E⁺ + r⁺ (t - t_m)` on the window.  Both bounds are affine in `t`, so their extremes on the window occur at its ends.  The energy stays at or above the floor `E_floor` throughout the window when `E⁻ ≥ E_floor` and `E⁻ + r⁻ W ≥ E_floor`, and at or below the ceiling `E_max` when `E⁺ ≤ E_max` and `E⁺ + r⁺ W ≤ E_max`.

The model bounds rates instead of totals over an interval because a bound on the total gain or loss says nothing about the energy inside the interval.  Starting at 9.95 kWh under a 10 kWh ceiling, a constant charge that adds 0.20 kWh over 15 minutes and losses of 0.20 kWh confined to the second half reach 10.05 kWh at the midpoint and return to 9.95 kWh at the end, so a check of totals at the ends accepts the interval.  The rate bounds reject it, because the upper bound rises at the full charging rate.

The fallback interval contains 0, so `B⁻ ≤ 0 ≤ B⁺`: the lower bound only drains and the upper bound only gains.  The upper bound takes efficiency 1 and no loss, which overstates the gain by the losses and makes its term exact.  The lower bound rounds its drain up, so the integer bound lies below the real one, with `W` in seconds, powers in watts, and `η` in ppm:

```text
drain⁻ = ⌈|B⁻| · W · 10^6 / η⌉ + ℓ⁺ · W
gain⁺  = B⁺ · W
```

The floor conditions become `E⁻ ≥ E_floor` and `E_floor + drain⁻ ≤ E⁻`, and the ceiling conditions `E⁺ ≤ E_max` and `E⁺ + gain⁺ ≤ E_max`, all comparisons of sums of nonnegative words.  The authorizer evaluates only the term of a side on which `B` extends beyond `F`, as the acceptance rule below states.  The largest product, `|B| · W · 10^6`, is below `2^21 · 2^12 · 2^20 = 2^53`, since each endpoint of `B` has magnitude at most `2^20 + e` with `e ≤ 2^20`.

### Grid power

Grid power, positive for import, is `G(t) = L(t) + b(t) - S(t)`, with `L` the site load and `S` the PV output, and the limits are `-X ≤ G(t) ≤ I` at every time of the window.  With the instantaneous intervals of A2 and A4, the import condition `L⁺ + B⁺ ≤ I + S⁻` and the export condition `L⁻ + B⁻ + X ≥ S⁺` bound `G` on the window.  In the offset representation each condition is a comparison of sums of nonnegative words.

### Acceptance rule

The lower side of `B` determines the energy floor and the export cap, and the upper side determines the energy ceiling and the import cap.  When `B` extends beyond `F` on a side, because the state in force or the new setpoint does, the authorizer tests that side's energy and grid conditions against the limits.  When a side of `B` equals the same side of `F`, the window's trajectories admit on that side only what an immediate return to fallback admits, and the authorizer accepts that side without a test.  For every time `t` of the window and every trajectory admitted until `t`, the theorem then states:

```text
min(E_floor, E⁻ + r_F⁻ (t - t_m)) ≤ E(t) ≤ max(E_max, E⁺ + r_F⁺ (t - t_m))
min(-X, L⁻ + f⁻ - S⁺)            ≤ G(t) ≤ max(I, L⁺ + f⁺ - S⁻)
```

Here `r_F⁻` and `r_F⁺` are the rate bounds of the interval `F`, so the second term of each bound is the model's worst case for a return to fallback at `t_m`, which the gateway can always carry out.  When fallback keeps a limit throughout the window, that bound reduces to the limit, which a lemma of the specification states, and the replay study measures how often fallback breaks each limit.  When the energy starts below the floor with the device in fallback, or when PV output with an idle fallback would exceed the export cap, the authorizer still accepts setpoints that leave the site no further outside the limit, such as charging, while it tests every renewal of a discharge that extends beyond fallback.

A state in force and a setpoint of opposite directions can extend `B` beyond `F` on both sides, and the authorizer then tests both.  A discharge beyond fallback must meet `B⁻ ≥ S⁺ - L⁻ - X` with the floor conditions, and a charge beyond it must meet `B⁺ ≤ I + S⁻ - L⁺` with the ceiling conditions.  A command that stops a discharge near the floor is tested as if the discharge lasted the whole window, so the authorizer rejects some commands that would help, and the device then continues the discharge until its expiry under the earlier window's theorem.  Longer windows widen the load and PV intervals and reduce both margins, and the replay study measures the margins against the window length.

### Worked example

The example's profile has an energy floor of 10,800,000 J (3 kWh), a ceiling of 34,200,000 J (9.5 kWh), charge and discharge limits of 5,000 W, an import cap of 5,000 W, an export cap of 2,000 W, `η = 900,000` ppm, `ℓ⁺ = 20` W, a tracking tolerance of 50 W, an idle fallback with `F = [-50, 50]` W, `τ = 30` s, a send deadline `a = 60` s, and `W = 900` s.  Except where a row states otherwise, the snapshot has stored energy in `[14,400,000, 15,120,000]` J, a setpoint of 0 W in force, so `P = F = [-50, 50]` W, load in `[3,000, 4,000]` W, and PV in `[0, 3,000]` W.  These cases become the first kernel-evaluated examples and module cases.

| Setpoint | `B` (W) | Side tested and its conditions | Decision |
|---|---|---|---|
| Discharge 1,000 W | `[-1,050, 50]` | Lower: export `3,000 - 1,050 + 2,000 ≥ 3,000`; floor `14,400,000 - 1,050,000 - 18,000 = 13,332,000 ≥ 10,800,000` | Accept, expiry `t_m + 870` |
| Discharge 3,000 W | `[-3,050, 50]` | Lower: export `3,000 - 3,050 + 2,000 = 1,950 < 3,000` | Reject: export |
| Discharge 1,000 W with `E⁻ = 11,520,000` | `[-1,050, 50]` | Lower: export as in the first row; floor `11,520,000 - 1,068,000 = 10,452,000 < 10,800,000` | Reject: floor |
| Charge 3,000 W, with load in `[500, 1,000]` W and PV in `[3,000, 5,000]` W | `[-50, 3,050]` | Upper: import `1,000 + 3,050 ≤ 5,000 + 3,000`; ceiling `15,120,000 + 2,745,000 = 17,865,000 ≤ 34,200,000` | Accept, with export relative to fallback's `500 - 50 - 5,000 = -4,550` W |
| Renewal of a 1,000 W discharge, with that discharge in force and `E⁻ = 11,288,000` | `[-1,050, 50]` | Lower: export as in the first row; floor `11,288,000 - 1,068,000 = 10,220,000 < 10,800,000` | Reject: floor |

In the first row fallback keeps every limit, so the theorem gives the absolute limits.  The third row passes the export condition and the floor test at the window's start and fails the floor test at the window's end.  In the fourth row idle fallback would export up to 4,550 W against a cap of 2,000 W, and the charge adds no export, so the authorizer accepts it with an export bound relative to fallback.  In the last row the discharge in force and its renewal extend beyond fallback, so the authorizer tests the floor, which a repeated renewal would otherwise cross.

## Architecture

```text
meters, BMS, inverters, forecasts, tariffs
        |
    ingestion ----------------------------> historian
        |  snapshot words with intervals        ^
    optimizer                                   |
        |  proposed setpoint                    |
    gateway: authorize (in-process module) -----+
        |  exactly the returned setpoint and expiry
    inverter, with BMS protections and fallback mode
```

| Component | Proofs | Responsibility |
|---|---|---|
| Ingestion | None | Reads meters, BMS, inverters, and forecasts, builds the snapshot's intervals, and records the source and time of each value |
| Optimizer | None | Proposes a setpoint from nominal forecasts and tariffs by a short rule |
| Authorizer, export `authorize` | Window theorem | Accepts or rejects one setpoint against a snapshot and returns the command and its expiry |
| Gateway | None in the first release | Holds the only device credentials, builds the authorizer's input, calls the module in-process, follows the rules of [Battery power in a window](#battery-power-in-a-window), and monitors the window |
| Historian | None | Records snapshots, proposals, decisions, commands, acknowledgements, measured responses, and the module's digest |
| Fallback mode | None | The vendor's mode, which runs when a command expires or the gateway requests it |

The gateway builds the input words, runs the module in its own process, and writes the command from the result, so the input that the authorizer saw and the command that the device receives never cross a process boundary.  The gateway's code that reads the result and writes one command is the link between them, and Stage 6 reviews and tests it.  At startup the gateway checks the module file's digest against the release manifest, and the historian records a digest of every input for audit.

| Input | Authority | Route to the authorizer |
|---|---|---|
| Limits, efficiency bound, loss rate, tracking tolerance, fallback interval, `τ`, `a`, `W` | Installer, from equipment qualification, and owner, for the reserve and caps | Compiled into the module as the profile table |
| Energy interval | BMS and meters, through ingestion | Snapshot words |
| State in force | Gateway's record of the commands it sent and the device's acknowledgements | Snapshot words |
| Load and PV intervals | Ingestion's rule for intervals, from recent measurements and forecasts | Snapshot words |
| Snapshot time | Gateway clock | Snapshot words |
| Setpoint | Optimizer | Snapshot words |

The theorem states the limits as the profile table's values, and the file theorem fixes them in the released bytes.  The snapshot holds measurements, the gateway's record, and the proposal, and no snapshot word can change a limit.  A change of profile, including a change of the owner's reserve or caps, requires a new build and a new file theorem for that site.

## Authorizer interface

The export takes one borrowed `Array UInt64` and returns a structure of words with a `Flat` instance.  The authorizer reads the array, calls helpers with scalar results, builds no array, and owns no parameter, so the compiler's `aborts` flag is false for every function, the generated `implements` theorem excludes traps, and the allocation bound is 0.  The program has no recursion, so its theorem has no frames condition.  The export is a wrapper `authorize xs := authorizeWith site xs` over the profile table `site`, and `p.initial` proves that the module's initial store holds the table.  The authorizer checks the input words, and `site_valid` proves by kernel evaluation that the table meets the profile's validity condition, including the ranges, `f⁻ ≤ 0 ≤ f⁺`, and `W > a + 2τ`.  The layouts below are provisional until Stage 1 fixes them with the theorems.

| Profile word | Field | Unit |
|---|---|---|
| 0 | Layout version | |
| 1, 2 | Energy floor `E_floor` and ceiling `E_max` | J |
| 3, 4 | Maximum charge and discharge power | W |
| 5, 6 | Import cap `I` and export cap `X` | W |
| 7 | Efficiency bound `η` | ppm |
| 8 | Maximum auxiliary loss rate `ℓ⁺` | W |
| 9 | Tracking tolerance `e` | W |
| 10, 11 | Fallback interval `f⁻`, `f⁺`, offset | W |
| 12 | Transition time `τ` | s |
| 13 | Window length `W` | s |
| 14 | Send deadline `a`, which only the gateway uses | s |

| Input word | Field | Unit |
|---|---|---|
| 0 | Layout version | |
| 1 | Snapshot time `t_m` | s |
| 2, 3 | Energy interval `E⁻`, `E⁺` | J |
| 4, 5 | State in force: mode (0 command, 1 fallback) and setpoint, offset | W |
| 6, 7 | Load interval `L⁻`, `L⁺` | W |
| 8, 9 | PV interval `S⁻`, `S⁺` | W |
| 10 | Proposed setpoint `s`, offset | W |

The result holds a status, the setpoint, and the expiry `t_x`.  The status is an enumeration with a `Flat` instance: `accepted`, or the first failing condition in a fixed order, among `length`, `version`, `range`, `order`, `power`, `exportCap`, `floor`, `importCap`, and `ceiling`.  `range` covers an input word outside its validity range, `order` a reversed interval, and `power` a setpoint beyond the charge or discharge limit.  A rejection returns zero words for the setpoint and the expiry.

## Theorems

`Spec.lean` defines the profile and snapshot as records of integers, the trajectory as functions from reals to reals, `AdmittedUntil`, which states assumptions A1 to A5 from `t_m` to a time `t`, `Within`, the limits, and `WithinOrFallback`, the bounds of the acceptance rule.  It imports neither the program nor the word layout.  `Words.lean` defines the decoding of words into those records, which both the proofs about the program and the readers of the specification use.  A reviewer who sees only this document's model section and `Spec.lean` checks the specification before the proofs start.

```lean
theorem authorize_sound {xs : Array UInt64} (h : (authorize xs).status = .accepted)
    {x : Trajectory} {t : ℝ} (ht : t ∈ window (profileOf site) (snapshotOf xs))
    (hx : x.AdmittedUntil (profileOf site) (snapshotOf xs) (setpointOf xs) t) :
    x.WithinOrFallback (profileOf site) (snapshotOf xs) t
```

| Theorem | Statement | File |
|---|---|---|
| `fallback_keeps_floor`, `_ceiling`, `_export`, `_import` | When fallback's worst case lies within one limit at `t`, `WithinOrFallback` gives that limit at `t` | `Spec.lean` |
| `site_valid` | The test site's table meets the profile's validity condition, by kernel evaluation | `Theorems.lean` |
| `toNat_add`, `toNat_mul`, `lowDrain_toNat`, `lowB_signed`, and the other word lemmas | Under the validity bounds, each `UInt64` operation of the authorizer equals the natural-number operation | `Arith.lean`, `Authorize.lean` |
| `energy_bounds`, `drainLow_ge` | Rate bounds on a measurable trajectory give the affine energy bounds up to each time of the window, and the integer drain covers the real one | `Window.lean` |
| `window_sound` | The conditions of the acceptance rule imply `WithinOrFallback` at each time `t` of the window for every trajectory admitted until `t` | `Window.lean` |
| `authorizeWith_iff` | Under a valid profile table, the authorizer accepts exactly when the input meets `InputValid` and the conditions of the acceptance rule hold | `Authorize.lean` |
| `authorizeWith_sound`, `authorize_sound` | For an accepted setpoint, every trajectory admitted until a time `t` of the window meets the bounds of the acceptance rule at `t` | `Authorize.lean`, `Theorems.lean` |
| `authorizeWith_accepted`, `authorize_accepted` | An accepted result holds the proposed setpoint and the expiry `t_m + W - τ` | `Authorize.lean`, `Theorems.lean` |
| `example_accept`, `example_export`, `example_floor`, `example_relative`, `example_renewal` | The worked example's decisions, by kernel evaluation | `Examples.lean` |
| `compiled.authorize.implements`, `compiled.bytes`, `compiled.initial` | Generated by `verified_compile` | `Verified.lean` |
| `energy_export`, `energy_authorize` | The module exports `authorize` at its function index, and the module's bytes decode to a module whose export, called from a ready store, returns the authorizer's result without a trap, and every accepted result meets `authorize_sound` | `Theorems.lean` |
| `energy_file`, `energy_file_decode` | The released file holds the module's encoding and decodes to the module | `File.lean` |

`authorizeWith_iff` states the acceptance condition exactly, so an authorizer that rejected every input would contradict it, and `example_accept` and `example_relative` prove acceptance of a nonzero discharge and a nonzero charge, and `example_renewal` proves the rejection of a renewal that would cross the floor.  How often realistic inputs meet the condition is an empirical question, which the replay study answers.  `energy_authorize` follows the pattern of `sha256_call` and `sha256_module` in the SHA-256 compilation, whose entries also read tables: it combines `compiled.bytes`, the wrapper's `implements` theorem through `Verified.ImplementsTables.call`, and `authorize_sound`, and `Verified.Ready.initial` shows that the module's initial store is ready.  `file_theorems energy compiled "../../build/verified/energy.wasm" from compiled.bytes` states the file theorems after the test driver writes the file.  Every theorem must report only the axioms `propext`, `Classical.choice`, and `Quot.sound`.

The module-level statements keep the assumptions that [the trusted base](docs/trusted-base.md) lists for modules of the verified compiler and for files with file theorems.  The statements describe execution in Talos's semantics, the gateway runs the module in Wasmtime, and the agreement of the two is an assumption, as is the decoder's reading of the bytes.  No theorem connects Wasmtime's instantiation or the gateway's placement of the argument array to the store that the statements assume, and the tests that compare Wasmtime with native Lean on every case are evidence for these assumptions, without proving them.

## Repository layout

The Lean code, proofs, and replay tool are in this repository and follow the slew planner's layout.  The gateway and device adapters are in a separate repository that pins a release of the module, so the device protocols and credentials stay apart from the proofs.  The registry entries let `tests/verified/run.sh` emit the module and check its file theorems, and the case executable supplies its cases.

| Path | Contents |
|---|---|
| `Demos/Energy/README.md` | The model, interface, theorem, and limits, as present facts |
| `Demos/Energy/Replay.md` | The replay study: data, simulated site, interval rules, margins, window length, and bills |
| `Demos/Energy/Spec.lean` | Profile, snapshot, trajectory, `AdmittedUntil`, `Within`, `WithinOrFallback`, and the `fallback_keeps` lemmas |
| `Demos/Energy/Words.lean` | Decoding of words into the specification's records, `ProfileValid`, and `InputValid` |
| `Demos/Energy/Program.lean`, `Flat.lean` | `authorizeWith` and its helpers, in the verified compiler's dialect, and the representations of its result |
| `Demos/Energy/Arith.lean`, `Window.lean`, `Authorize.lean` | Exactness of word operations, the energy bound and `window_sound`, and the theorems about the authorizer |
| `Demos/Energy/Site.lean` | The profile table of the test site and the wrapper `authorize`, and later one table per qualified site |
| `Demos/Energy/Verified.lean`, `Theorems.lean`, `File.lean`, `Examples.lean` | Compilation, `site_valid` and the module-level theorems, file theorems, and kernel-evaluated examples |
| `tests/TestSupport/Energy/Cases.lean`, `CasesMain.lean` | Case printer, which the executable `verified-cases-energy` of `lakefile.lean` runs from a branch of `tests/verified/run.sh` |
| `Demos/Verified.lean`, `Verified/Examples/Cases.lean` | Imports of the theorems, the examples, and the cases |
| `tests/energy/` | The axiom audit and the replay tool |
| `tests/verified/modules.txt`, `tests/verified/numerics.txt` | Registry entries for the module and its file theorems |

## Testing and evaluation

### Module cases

The case printer prints cases with results that native Lean computes, and `tests/verified/run.sh` compares them with Wasmtime.  The cases cover empty, short, and long inputs, unknown versions, reversed intervals, words at `2^20`, `2^32`, `2^42`, and `2^64 - 1`, energies on the floor and the ceiling, setpoints at the power limits, states in force and setpoints inside and beyond fallback on each side, renewals, fallback intervals that break each limit, and load and PV intervals that make each condition fail by one watt.  The replay tool computes the same decisions independently and compares them with the printed cases.  Every failing case found later stays in the corpus.

### Replay study

The replay tool, `tests/energy/replay.py`, is a Python program with PEP 723 metadata that runs with `uv run` and uses only the standard library.  It implements the acceptance rule a second time, from this document, with exact integer arithmetic, and `replay.py check` compares its decisions with the module cases.  The dataset must hold simultaneous site load and PV output at one-minute or finer resolution for at least a year.  The study uses the minute data of NIST's Net-Zero Energy Residential Test Facility, an all-electric test house with a 10.2 kW PV array, for its test years of 2013–14 and 2015–16.  Each run fixes a rule for the load and PV intervals: either the true minimum and maximum over the window, which bounds acceptance from above, or a causal rule that widens the extremes of the previous 15 minutes by a percentile of the excursions in the calibration year.  The sweep covers window lengths from the shortest that `W > a + 2τ` allows to 900 seconds, tracking tolerances, efficiency bounds, and grid caps that bind or never bind.  For each window, the report gives the largest charge and the largest discharge that pass and whether the alternative breaks each limit.  It also checks `WithinOrFallback` at every minute of every accepted window up to the first premise failure, both for the nominal device and for a device at the extremes that the premises allow.  [The replay study](Demos/Energy/Replay.md) gives the results.

### Economic evaluation

The evaluation compares the controller, on withheld data, with a simulation of the vendor's self-consumption mode and with a fixed time-of-use schedule with a fixed reserve.  It follows the retail-rate dispatch method of [SAM's battery-dispatch documentation](https://samrepo.nlr.gov/help/battery_dispatch_btm.html), with a one-day look-behind forecast and a wear cost per kWh discharged.  The replay bills a stated tariff, because the test house has no billing rules of its own that value a battery: PG&E's E-ELEC import prices with a flat export credit.  Site operation bills under the site's own rules.  The report gives the bill, import and export energy, battery throughput, the fraction of proposed setpoints accepted, and reserve margins.  The report presents simulated savings from replay and measured savings from site operation separately, and it presents neither as a causal effect without a suitable evaluation design.

## Stages

| Stage | Work | Exit evidence |
|---|---|---|
| 1. Authorizer | Specification and its review, program, proofs, compilation, file theorems, examples, cases | Theorems with only the permitted axioms, cases that pass in Wasmtime against native Lean, and a file theorem checked after emission |
| 2. Replay study, alongside Stage 1 | Dataset, replay tool, sweep | Report of acceptance margins; window length chosen |
| 3. Optimizer and economic replay | Rule-based optimizer, baselines | Report with savings and acceptance rates |
| 4. Site selection and qualification | Equipment with command expiry and fallback; measurement of `e`, `τ`, `F`, `η`, `ℓ⁺`, and the energy estimate's error | Qualification report; signed profile; site module with its file theorem |
| 5. Read-only operation | Ingestion, authorizer, and historian on live data, with no device writes | At least 30 consecutive days logged; comparison of model and measurement; coverage statistics for A1, A3, and A4 |
| 6. Gateway and actuation qualification | Gateway, vendor test rig or hardware-in-the-loop, fault injection | The gateway's rules, expiry, return to fallback, read-back, and credential isolation demonstrated; installer and vendor sign-off |
| 7. Supervised operation | Narrow setpoint limits, short operating periods, rollback to the vendor's mode | Measured outcomes; incident log |
| 8. Extensions | Schedules with time-varying reserves and EV deadlines, owner settings in the input, a theorem that composes consecutive windows, a verified optimizer, limits over metering intervals, the C translation | New theorems and assumptions for each extension |

A site stays in read-only operation when its equipment lacks command expiry or a qualified fallback, when its energy estimate has no characterized error bound, when the meaning of a profile value is ambiguous, or when the installer or utility has not approved control.  An extension that changes the model states new theorems and new assumptions, and an earlier theorem never describes the extended system.  The site's module, with its profile table and file theorem, is the artifact that Stages 5 to 7 run.

### Stage 1 tasks

- [x] `Spec.lean` with `AdmittedUntil`, `Within`, `WithinOrFallback`, and `fallback_keeps`, and its independent review.
- [x] `Words.lean`, with the provisional layouts fixed.
- [x] `Program.lean`: validation, the intervals `P` and `B`, the conditions of the acceptance rule, and the result.
- [x] The word lemmas and the floor and ceiling lemmas.
- [x] `energy_bounds`, `drainLow_ge`, and `window_sound`.
- [x] `authorizeWith_iff`, `authorizeWith_sound`, and `authorizeWith_accepted`.
- [x] `Site.lean` with the worked example's profile, `site_valid`, `Verified.lean`, and `Examples.lean`.
- [x] `energy_export`, `energy_authorize`, registry entries, `File.lean`, and the axiom audit.
- [x] The case printer, its executable, and its branch of `tests/verified/run.sh`.
- [x] `Demos/Energy/README.md`.

### Stage 2 tasks

- [x] Dataset selection against the resolution and length requirements.
- [x] Replay tool, with its comparison against the module cases.
- [x] Interval rules: the true-range rule and a causal rule.
- [x] Sweep, report, and the choice of `W`.

### Stage 3 tasks

- [x] Baselines: the vendor's self-consumption mode and a fixed time-of-use schedule.
- [x] Rule-based optimizer, with its rules chosen on the calibration year.
- [x] Economic replay on the withheld year, and its report.

## Open decisions

| Decision | Options | Recommendation |
|---|---|---|
| Window length `W` | Any length with `W > a + 2τ` | The replay study chose 180 s, the shortest whole-minute length, by a criterion fixed before its runs.  Stage 4's expiry granularity can lengthen it, and Stage 5's measurement of the excursions within a minute can change its margins. |
| Form of the command | A battery setpoint held for the window, or power limits within which the inverter's own self-consumption mode follows the load | Decide before Stage 4.  A held setpoint cost $79 a year against the vendor's mode in the replay, before the changes within a minute.  Power limits make `B` the hull of the state in force, the limits widened by `e`, and `F`, and leave the side tests and the form of the theorem unchanged, but they change the interface and assumption A2. |
| Import cap under uncertain load | Test the cap against the worst-case load as now, narrow the load interval, or bound only the import that the battery adds | Decide with the site's interconnection terms.  With a 10 kW cap at the test house and the causal rule's load bound, the import test blocked charging through the winter, and the authorizer cost $119 a year more than with caps that never bind. |
| Gateway runtime, in Stage 6 | Wasmtime embedded in a small C or Rust program, or the module's C translation with `p.f.native` and CompCert | Choose in Stage 6.  The C translation removes Talos's execution semantics, the decoder, and Wasmtime from the assumptions and adds CompCert, the Lean copy of Clight, and the other items that the trusted base lists for C files. |

## References

- [Verified Compiler Manual](docs/verified-manual.md)
- [Trusted base](docs/trusted-base.md)
- [Slew: constraint-checked attitude slews](Demos/Slew/README.md)
- [Mathlib: interval integrals](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.html)
- [NREL System Advisor Model: behind-the-meter battery dispatch](https://samrepo.nlr.gov/help/battery_dispatch_btm.html)
- [IEEE 1547-2018: interconnection and interoperability of distributed energy resources](https://standards.ieee.org/ieee/1547/5915/)
- [UL Solutions: energy storage system testing and certification](https://www.ul.com/services/energy-storage-system-testing-and-certification)
- [UL Solutions: energy storage system installation codes and requirements](https://www.ul.com/resources/installation-codes-and-requirements-energy-storage-systems-ess-faqs)
