# Verified Energy Controller: Plan and Design

The energy controller schedules the battery of a behind-the-meter solar-and-battery site to lower the electricity bill while it keeps the battery's stored energy and the site's grid import and export within configured limits.  An optimizer without proofs proposes limits of battery power, within which the inverter's own self-consumption mode follows the load, and an authorizer compiled with `verified_compile` decides whether a gateway may send them to the battery inverter for the next window of time.  A held setpoint `s` is the limits `[s, s]`.  The authorizer's theorem states that, for every load, solar output, efficiency, loss, and device response that the stated assumptions admit, accepted limits keep each modeled limit of the site or leave the site no further outside it than an immediate return to fallback would.  The compiler's generated theorems and a file theorem connect that statement to the bytes of the WebAssembly module that the gateway runs.  Stages 1 to 3 and the composition of consecutive windows are complete, and Stages 4 to 7 need a site and its equipment.

## Scope

The first release covers one site with an AC-coupled battery inverter and its battery management system (BMS), a photovoltaic (PV) inverter, the site's loads, and one grid meter.  The controller sets only the limits of the battery's AC power.  The inverters and the BMS keep their own electrical, thermal, state-of-charge, interconnection, and export protections, and the controller never changes their settings.

| Subject | Choice | Reason |
|---|---|---|
| Site | One battery, PV, site load, one grid meter | Small enough for a precise model |
| Electrical architecture | AC-coupled and grid-connected, with no islanding | Islanding and grid-forming behavior remain functions of the inverter |
| Control variable | Lower and upper limits of battery AC power, signed, positive for charging | The inverter's own self-consumption mode follows the load within them, and equal limits hold a setpoint |
| Verified component | One authorizer that accepts or rejects one command's limits for a window of `W` seconds | The window covers the command, its expiry, and the return to fallback |
| Limits | Energy floor and ceiling, and instantaneous grid import and export caps | An instantaneous cap also bounds every average |
| Profile | Installer's and owner's limits and device parameters, compiled into the module | The released bytes hold the limits |
| Arithmetic | `UInt64` words in fixed units with validated ranges | Every operation on a validated input equals the integer operation |
| Specification | Real numbers and Mathlib's interval integral | `Spec.lean` defines the physical model without the program or its word layout |
| Optimizer | A short rule without proofs | The theorem holds for every proposal |
| Tariffs and costs | Outside the authorizer | The evaluation measures savings against baselines |

The first release excludes schedules longer than one window, time-varying reserves, EV charging, grid-forming control, islanding, protection relays, thermal management, cell balancing, breaker control, frequency and voltage regulation, per-phase limits, demand charges, tiered rates, and negative prices.  The theorem takes forecasts and the BMS's energy estimate as premises in the form of intervals and makes no claim about their accuracy, or about the WebAssembly engine, the operating system, the gateway, or the device firmware beyond the assumptions that the next two sections list.

## Guarantees and their limits

The model, module, and file levels of the guarantee are theorems.  The installation level consists of the qualification, commissioning, and operating evidence that Stages 4 to 7 collect.  A claim about the running system needs every level, and each level adds its own assumptions.

| Level | Claim | Evidence | Depends on |
|---|---|---|---|
| Model | An accepted command keeps every admitted trajectory of its window within each limit, or no further outside it than an immediate return to fallback | Theorems about Lean functions and the real-valued model | Assumptions A1 to A5 |
| Module | The module's export computes the authorizer and returns without a trap | `compiled.authorize.implements`, `compiled.bytes`, and `compiled.initial`, which `verified_compile` generates, and `energy_authorize`, which combines them with `authorize_sound` | Talos's semantics and Wasmtime's agreement with it, the binary decoder, Wasmtime's instantiation of the initial store, and the host's placement of the argument array |
| File | The released file holds the module's encoding | `energy_file` and `energy_file_decode` | The file as it was when Lean checked the theorem, and the gateway's digest check when it loads the file |
| Installation | The site behaves as the model states | Equipment qualification, commissioning, read-only operation, and fault-injection tests | Measurements, device firmware, the gateway, communication, and wiring |

A window's theorem covers the interval from one snapshot to the end of the window, including the command's expiry and the device's return to fallback.  The gateway authorizes a new command from a new snapshot before the current command expires, so consecutive windows overlap and each has its own theorem.  `run_covered` shows that, when each accepted snapshot follows the previous one by at most `W`, every time from the first accepted snapshot to the end of the last window lies in the window of the latest accepted snapshot at or before it, and `run_sound` gives that window's bounds there.  The premises of `run_sound` concern that window alone: A1 and A3 to A5 (`ModelUntil`) and the device's response and the gateway's rules (`OperatesIn`) from its snapshot to that time, from which `power_in_window` derives A2.  A fault in one window therefore leaves the theorems of later windows intact.  A run ends where accepted snapshots lie more than `W` apart, and after the last window the device runs in its fallback mode, whose safety depends on the device's own protections (A8).

## Site, equipment, and assumptions

The equipment must accept charge and discharge limits of battery power with an expiry, after which the inverter returns to a fallback mode without help from the controller, and it must report the limits it applies.  For equipment that accepts only a held setpoint, the optimizer proposes limits `[s, s]`, and the gateway sends `s`.  The vendor must document the fallback mode, its power interval, and the time the inverter takes to reach it, and qualification measures each of them.  The equipment must report battery power, site import and export, PV output, and the BMS's usable-energy estimate with a stated error.  A site whose equipment lacks command expiry or a qualified fallback mode runs only in read-only operation.

| ID | Assumption | Role in the theorems | Evidence |
|---|---|---|---|
| A1 | At the snapshot time `t_m`, usable stored energy lies in `[E⁻, E⁺]` | Premise, in `ModelUntil` | Characterization of the BMS estimate against metered charge and discharge |
| A2 | From `t_m` to `t`, battery AC power lies in the window's power interval `B` | Premise of `authorize_sound`, which `power_in_window` derives from `OperatesIn` in the composition | Qualification of the tolerance about the limits, transitions, expiry, and fallback, and the gateway's rules |
| A3 | From `t_m` to `t`, the charge and discharge efficiencies lie between `η` and 1, and the auxiliary loss rate between 0 and `ℓ⁺` | Premise, in `ModelUntil` | Characterization over the permitted power and temperature range |
| A4 | From `t_m` to `t`, instantaneous load and PV output lie within the snapshot's intervals | Premise, in `ModelUntil` | Statistics of high-resolution measurements |
| A5 | Stored energy changes only through battery power, the efficiencies, and the auxiliary loss, as the energy equation states, with measurable power, efficiencies, and loss rate | Premise, in `ModelUntil`, as the model | Comparison of the model with measured energy |
| A6 | The profile matches the installed equipment, the approved interconnection, and the owner's policy | Outside | Installer and owner sign-off |
| A7 | The snapshot time and the gateway's record of the state in force are correct, and every change of state, including an expiry, takes effect within the transition time `τ` of its time on the gateway's clock | Outside `authorize_sound`, and part of `OperatesIn.states` in the composition | Clock synchronization checks and device qualification |
| A8 | The BMS and inverters enforce their protections, and the fallback mode keeps the equipment within its limits without the controller | Outside | Vendor documentation and commissioning tests |

The theorem takes each premise on the interval from `t_m` to a time `t` and concludes the bounds at `t`, because `E(t)` and `G(t)` depend only on the trajectory up to `t`, and it states nothing about a trajectory after a premise fails.  The gateway compares live measurements with the snapshot's intervals during the window and returns the device to fallback when a measurement falls outside them or when telemetry stops, and assumption A2 includes that return.  Coverage statistics for A4 from historical data are evidence about future load and PV, which no theorem can supply.

The controller performs supervisory economic dispatch, and the site's protection consists of the BMS, the inverters, and the installation's protective devices.  The installation remains subject to the local adoption of the electrical code (NFPA 70), the energy-storage installation standard (NFPA 855), equipment listing (UL 9540 for the storage system and UL 1741 for the inverters), and the interconnection standard (IEEE 1547), and to the utility's interconnection approval.  Writes to devices start only after the installer and the equipment vendor approve the fallback mode, the limits, and the monitoring, and the theorem certifies no part of the installation.

## Plant model

### Units and ranges

The authorizer and the specification work in joules, watts, seconds, and parts per million.  The profile's validity condition and the authorizer's input checks bound every quantity, and under those bounds every product that the authorizer computes stays below `2^53`, so each `UInt64` operation on a validated input equals the corresponding operation on natural numbers.  The proofs establish this equality operation by operation, and the authorizer subtracts only where a validated range or a preceding comparison keeps the result nonnegative, so no operation wraps.

| Quantity | Unit | Representation | Range that validity requires |
|---|---|---|---|
| Power, including the tolerance | W | `UInt64`; a signed power `p` as the word `p + 2^32` | `\|p\| ≤ 2^20` W |
| Energy | J | `UInt64` | At most `2^42` J, about 1.2 GWh |
| Time | s, UTC | `UInt64` | Window at most 3,600 s; times below `2^40` |
| Efficiency | ppm | `UInt64` | 500,000 to 1,000,000 |
| Auxiliary loss rate | W | `UInt64` | At most `2^20` W |

### Battery power in a window

A snapshot taken at time `t_m` records the state in force: a command with limits `[h⁻, h⁺]`, whose interval `P` is `[h⁻ - e, h⁺ + e]`, where `e` is the profile's tolerance of battery power about the limits, or fallback, whose interval `P` is the profile's fallback interval `F = [f⁻, f⁺]`.  The gateway takes a snapshot only after the last change of state has completed, so battery power at `t_m` lies in `P`.  The fallback interval contains 0, because a protective trip or derating by the BMS or an inverter moves power toward 0.  The authorizer checks that proposed limits `[c⁻, c⁺]` satisfy `-D ≤ c⁻ ≤ c⁺ ≤ C`, where `D` and `C` are the profile's largest discharge and charge.  The window's power interval `B` is the smallest interval that contains `P`, `[c⁻ - e, c⁺ + e]`, and `F`:

```text
B⁻ = min(P⁻, c⁻ - e, f⁻)
B⁺ = max(P⁺, c⁺ + e, f⁺)
```

Qualification of the equipment establishes the device properties from which assumption A2 follows.  When the device's state changes, by new limits, by the command's expiry, or by a request to return to fallback, its power stays between its value at the change and the new state's interval, and it enters that interval within `τ` seconds of the change's time on the gateway's clock, including the delivery delay, the application delay, the ramp, and the difference between the clocks.  Once settled, power stays in the state's interval, except that a protective trip or derating moves it toward 0 and keeps it between its value and 0.  `B` contains `P`, `[c⁻ - e, c⁺ + e]`, `F`, and 0, so every sequence of these changes inside the window keeps power in `B`, whatever the delays.

The window starts at `t_m` and ends at `t_m + W`.  The authorizer returns the command's expiry `t_x = t_m + W - τ`, and the device reaches fallback by the end of the window unless a later authorization replaced the command.  The gateway follows these rules, which Stage 6 tests:

1. Take a snapshot only after the last change of state has completed, at least `τ` seconds after it, only when the device reports the limits in force, and only when measured battery power lies in the state's interval.
2. Send at most one command for each authorization, only from the authorization of the most recent snapshot, with the expiry `t_x` that the authorizer returned, and only before `t_m + a`, where the profile's send deadline `a` meets `W > a + 2τ`, so that a command sent at the deadline settles, and the next snapshot follows, before the command expires.
3. Send exactly the returned limits, or their common value to equipment that accepts only a setpoint, and nothing on a rejection.
4. Return the device to fallback when load or PV leaves the snapshot's intervals, battery power leaves `B`, or telemetry stops, and send nothing more from the current authorization.
5. Take the next snapshot after the new command has settled and before `t_x`, to continue control without a gap.

`OperatesIn` and `Run.Spaced`, in `Operation.lean`, state the parts of these rules that the theorems use.  The send deadline `a` and rule 4's triggers enter no theorem, and `τ` enters only the expiry that `authorize_accepted` states and the profile's validity condition.  The deadline lets a new command settle before the old one expires, so that the premises of consecutive windows can hold, and rule 4 limits what follows the failure of a premise, about which the theorems state nothing.

| Rule or property | Formal counterpart |
|---|---|
| Rule 1 | `OperatesIn.settled`: at the snapshot, battery power lies in the interval of the recorded state |
| Rules 2 to 4, with A7 | `OperatesIn.states`: until the next accepted snapshot, the applied state is the recorded state, the command authorized from this snapshot, or fallback |
| Rule 5, with the acceptance of a snapshot in each window | `Run.Spaced`: snapshot times increase, each at most `W` after the previous |
| The device's response | `OperatesIn.low` and `OperatesIn.high`: battery power stays within the smallest interval that contains its value at the snapshot, 0, and the intervals of the applied states |

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

The fallback interval contains 0, so `B⁻ ≤ 0 ≤ B⁺`: the lower bound only drains and the upper bound only gains.  The upper bound takes efficiency 1 and no loss, which overstates the gain by the losses and needs no rounding.  The lower bound rounds its drain up, so the integer bound lies below the real one, with `W` in seconds, powers in watts, and `η` in ppm:

```text
drain⁻ = ⌈|B⁻| · W · 10^6 / η⌉ + ℓ⁺ · W
gain⁺  = B⁺ · W
```

The floor test is `E_floor + drain⁻ ≤ E⁻` and the ceiling test `E⁺ + gain⁺ ≤ E_max`, each a comparison of sums of nonnegative words.  Both terms are at least 0, so each test also bounds the start of the window.  The authorizer evaluates only the test of a side on which `B` extends beyond `F`, as the acceptance rule below states.  The largest product, `|B| · W · 10^6`, is below `2^21 · 2^12 · 2^20 = 2^53`, since each endpoint of `B` has magnitude at most `2^20 + e` with `e ≤ 2^20`.

### Grid power

Grid power, positive for import, is `G(t) = L(t) + b(t) - S(t)`, with `L` the site load and `S` the PV output, and the limits are `-X ≤ G(t) ≤ I` at every time of the window.  With the instantaneous intervals of A2 and A4, the import test `L⁺ + B⁺ ≤ I + S⁻` and the export test `L⁻ + B⁻ + X ≥ S⁺` bound `G` on the window.  In the offset representation each test is a comparison of sums of nonnegative words.

### Acceptance rule

The lower end of `B` bounds stored energy and grid power from below, against the floor and the export cap, and the upper end bounds them from above, against the ceiling and the import cap.  When `B` extends beyond `F` on a side, because the state in force or the new limits do, the authorizer tests that side's energy and grid limits.  When a side of `B` equals the same side of `F`, the model admits on that side only what an immediate return to fallback admits, and the authorizer accepts that side without a test.  For every time `t` of the window and every trajectory admitted until `t`, the theorem then states:

```text
min(E_floor, E⁻ + r_F⁻ (t - t_m)) ≤ E(t) ≤ max(E_max, E⁺ + r_F⁺ (t - t_m))
min(-X, L⁻ + f⁻ - S⁺)            ≤ G(t) ≤ max(I, L⁺ + f⁺ - S⁻)
```

Here `r_F⁻` and `r_F⁺` are the rate bounds of the interval `F`, so the second term of each bound is the model's worst case for a return to fallback at `t_m`, which the gateway can request and which the command's expiry produces without the gateway.  When fallback keeps a limit throughout the window, that bound reduces to the limit, as `fallback_keeps_floor`, `fallback_keeps_ceiling`, `fallback_keeps_export`, and `fallback_keeps_import` state, and the replay study measures how often fallback breaks each limit.  When the energy starts below the floor with the device in fallback, or when PV output with an idle fallback would exceed the export cap, the authorizer still accepts limits that leave the site no further outside the limit, such as charging, while it tests every renewal of a discharge that extends beyond fallback.

When `B⁻ < f⁻` and `B⁺ > f⁺`, which wide limits or a state in force and new limits of opposite directions cause, the authorizer tests both sides.  A discharge beyond fallback must meet `B⁻ ≥ S⁺ - L⁻ - X` and the floor test, and a charge beyond it must meet `B⁺ ≤ I + S⁻ - L⁺` and the ceiling test.  The authorizer tests a command that stops a discharge near the floor as if the discharge lasted the whole window, so it rejects some commands that would help, and the device then continues the discharge until its expiry under the earlier window's theorem.  Longer windows widen the load and PV intervals and reduce both margins, and the replay study measures the margins against the window length.

### Worked example

The example's profile has an energy floor of 10,800,000 J (3 kWh), a ceiling of 34,200,000 J (9.5 kWh), charge and discharge limits of 5,000 W, an import cap of 5,000 W, an export cap of 2,000 W, `η = 900,000` ppm, `ℓ⁺ = 20` W, a tolerance of 50 W, an idle fallback with `F = [-50, 50]` W, `τ = 30` s, a send deadline `a = 60` s, and `W = 900` s.  Except where a row states otherwise, the snapshot has stored energy in `[14,400,000, 15,120,000]` J, the limits `[0, 0]` W in force, so `P = F = [-50, 50]` W, load in `[3,000, 4,000]` W, and PV in `[0, 3,000]` W, and a row that names one power proposes the held setpoint `[s, s]`.  For `B⁻ = -1,050` W, the floor test's drain is `⌈1,050 · 900 · 10^6 / 900,000⌉ + 20 · 900 = 1,068,000` J.  `Examples.lean` proves each row's decision by kernel evaluation, and the module cases include every row.

| Proposal | `B` (W) | Side tested and its tests | Decision |
|---|---|---|---|
| Discharge 1,000 W | `[-1,050, 50]` | Lower: export `3,000 - 1,050 + 2,000 = 3,950 ≥ 3,000`; floor `10,800,000 + 1,068,000 = 11,868,000 ≤ 14,400,000` | Accept, expiry `t_m + 870` |
| Discharge 3,000 W | `[-3,050, 50]` | Lower: export `3,000 - 3,050 + 2,000 = 1,950 < 3,000` | Reject: export |
| Discharge 1,000 W, with energy in `[11,520,000, 15,120,000]` J | `[-1,050, 50]` | Lower: export as in the first row; floor `11,868,000 > 11,520,000` | Reject: floor |
| Charge 3,000 W, with load in `[500, 1,000]` W and PV in `[3,000, 5,000]` W | `[-50, 3,050]` | Upper: import `1,000 + 3,050 ≤ 5,000 + 3,000`; ceiling `15,120,000 + 2,745,000 = 17,865,000 ≤ 34,200,000` | Accept, with export relative to fallback's `500 - 50 - 5,000 = -4,550` W |
| Renewal of a 1,000 W discharge, with that discharge in force and energy in `[11,288,000, 12,008,000]` J | `[-1,050, 50]` | Lower: export as in the first row; floor `11,868,000 > 11,288,000` | Reject: floor |
| Limits `[-1,000, 500]` | `[-1,050, 550]` | Lower: as in the first row; upper: import `4,000 + 550 ≤ 5,000 + 0`; ceiling `15,120,000 + 495,000 = 15,615,000 ≤ 34,200,000` | Accept, expiry `t_m + 870` |
| Limits `[-1,000, 1,000]` | `[-1,050, 1,050]` | Lower: as in the first row; upper: import `4,000 + 1,050 = 5,050 > 5,000 + 0` | Reject: import |

In the first row fallback keeps every limit, so `within_of_fallback` gives `Within`.  In the third row the export test passes and the floor test fails.  In the fourth row idle fallback would export up to 4,550 W against a cap of 2,000 W, and the charge adds no export, so the authorizer accepts it with an export bound relative to fallback.  In the fifth row the discharge in force and its renewal extend beyond fallback, so the authorizer tests the floor, which a repeated renewal would otherwise cross.  The last two rows let the inverter follow the load between a discharge and a charge, so the authorizer tests both sides, and the last fails because a charge of 1,050 W, the upper limit plus the 50 W tolerance, with the load at 4,000 W and no PV could import 5,050 W.

## Architecture

```text
meters, BMS, inverters, forecasts, tariffs
        |
    ingestion ----------------------------> historian
        |  snapshot words with intervals        ^
    optimizer                                   |
        |  proposed limits                      |
    gateway: authorize (in-process module) -----+
        |  exactly the returned limits and expiry
    inverter, with BMS protections and fallback mode
```

| Component | Proofs | Responsibility |
|---|---|---|
| Ingestion | None | Reads meters, BMS, inverters, and forecasts, builds the snapshot's intervals, and records the source and time of each value |
| Optimizer | None | Proposes limits from nominal forecasts and tariffs by a short rule |
| Authorizer, export `authorize` | Window and composition theorems | Accepts or rejects one command's limits against a snapshot and returns the accepted limits and their expiry |
| Gateway | None in the first release | Holds the only device credentials, builds the authorizer's input, calls the module in-process, follows the rules of [Battery power in a window](#battery-power-in-a-window), and monitors the window |
| Historian | None | Records snapshots, proposals, decisions, commands, acknowledgements, measured responses, and the module's digest |
| Fallback mode | None | The vendor's mode, which runs when a command expires or the gateway requests it |

The gateway builds the input words, runs the module in its own process, and writes the command from the result, so the authorizer's input and result and the code that writes the command share one process.  That code is the link between the authorizer and the device, and Stage 6 reviews and tests it.  At startup the gateway checks the module file's digest against the release manifest, and the historian records a digest of every input for audit.

| Input | Authority | Route to the authorizer |
|---|---|---|
| Limits, efficiency bound, loss rate, tolerance, fallback interval, `τ`, `a`, `W` | Installer, from equipment qualification, and owner, for the reserve and caps | Compiled into the module as the profile table |
| Energy interval | BMS and meters, through ingestion | Snapshot words |
| State in force | Gateway's record of the commands it sent and the device's acknowledgements | Snapshot words |
| Load and PV intervals | Ingestion's rule for intervals, from recent measurements and forecasts | Snapshot words |
| Snapshot time | Gateway clock | Snapshot words |
| Proposed limits | Optimizer | Snapshot words |

The theorem states the limits as the profile table's values, and the file theorem fixes them in the released bytes.  The snapshot holds measurements, the gateway's record, and the proposal, and no snapshot word can change a limit.  A change of profile, including a change of the owner's reserve or caps, requires a new build and a new file theorem for that site.

## Authorizer interface

The export takes one borrowed `Array UInt64` of 13 words and returns a structure of four words with a `Flat` instance.  The authorizer reads the array, calls helpers with scalar results, builds no array, and owns no parameter, so the compiler's `aborts` flag is false for every function, `compiled.authorize.implements` excludes traps, and the allocation bound is 0.  The program has no loop and no recursion, so its theorem has no frames condition.  The export is a wrapper `authorize xs := authorizeWith site xs` over the profile table `site` of 15 words, and `compiled.initial` proves that the module's initial store holds the table.  `site_valid` proves by kernel evaluation that the table meets the profile's validity condition, including the ranges, `f⁻ ≤ 0 ≤ f⁺`, and `W > a + 2τ`, and the authorizer checks the input words.

| Profile word | Field | Unit |
|---|---|---|
| 0 | Layout version, 1 | |
| 1, 2 | Energy floor `E_floor` and ceiling `E_max` | J |
| 3, 4 | Largest charge `C` and discharge `D` | W |
| 5, 6 | Import cap `I` and export cap `X` | W |
| 7 | Efficiency bound `η` | ppm |
| 8 | Largest auxiliary loss rate `ℓ⁺` | W |
| 9 | Tolerance `e` of battery power about the limits | W |
| 10, 11 | Fallback interval `f⁻`, `f⁺`, offset | W |
| 12 | Transition time `τ` | s |
| 13 | Window length `W` | s |
| 14 | Send deadline `a`, which only the gateway uses | s |

| Input word | Field | Unit |
|---|---|---|
| 0 | Layout version, 1 | |
| 1 | Snapshot time `t_m` | s |
| 2, 3 | Energy interval `E⁻`, `E⁺` | J |
| 4 | State in force: mode (0 command, 1 fallback) | |
| 5, 6 | Limits in force `h⁻`, `h⁺`, offset | W |
| 7, 8 | Load interval `L⁻`, `L⁺` | W |
| 9, 10 | PV interval `S⁻`, `S⁺` | W |
| 11, 12 | Proposed limits `c⁻`, `c⁺`, offset | W |

The result holds the status, the lower and upper limits as offset words, and the expiry `t_x`.  The status is an enumeration with a `Flat` instance, held as its constructor index: 0 `accepted`, or the first failing condition in a fixed order, 1 `length`, 2 `version`, 3 `range`, 4 `order`, 5 `power`, 6 `exportCap`, 7 `floor`, 8 `importCap`, and 9 `ceiling`.  `range` covers an input word outside its validity range, `order` a reversed interval or pair of limits, and `power` proposed limits beyond the largest charge or discharge.  The authorizer checks words 5 and 6 in fallback mode too, so the gateway fills them, for example with `2^32`, the word of 0.  A rejection returns zero words for the limits and the expiry.

## Theorems

`Spec.lean` defines the profile and snapshot as records of integers, a command's limits and the state in force, the trajectory as functions from reals to reals, `ModelUntil`, which states assumptions A1 and A3 to A5 from `t_m` to a time `t`, `AdmittedUntil`, which adds A2, `Within`, the site's limits, and `WithinOrFallback`, the bounds of the acceptance rule.  `Operation.lean` defines a run of accepted authorizations, `Run.Between`, `Run.Spaced`, and `OperatesIn`.  Neither file imports the program or the word layout, and independent reviewers checked both against this document's model section.  `Words.lean` decodes words into those records, and `Window.lean` states the integer tests as `Conditions`, which `window_sound`, `authorizeWith_iff`, and `run_sound` use.

```lean
theorem authorize_sound {xs : Array UInt64} (h : (authorize xs).status = .accepted)
    {x : Trajectory} {t : ℝ} (ht : t ∈ window (profileOf site) (snapshotOf xs))
    (hx : x.AdmittedUntil (profileOf site) (snapshotOf xs) (limitsOf xs) t) :
    x.WithinOrFallback (profileOf site) (snapshotOf xs) t
```

The composition theorem takes a run of `n` inputs, every one accepted, with `0 < n`, snapshot times that `Run.Spaced` relates, and a time `t` from the first snapshot to the end of the last window.  It names the window `j` of the latest accepted snapshot at or before `t`, and that window's bounds hold at `t` for a trajectory that meets the window's `ModelUntil` and `OperatesIn` until `t`.

```lean
theorem authorize_operation {n : ℕ} {ys : ℕ → Array UInt64}
    (h : ∀ j < n, (authorize (ys j)).status = .accepted)
    (hr : (runOf n ys).Spaced (profileOf site)) (h0 : 0 < n) {x : Trajectory}
    {state : ℝ → State} {t : ℝ} (ht0 : (runOf n ys).time 0 ≤ t)
    (ht1 : t ≤ (runOf n ys).time (n - 1) + (profileOf site).window) :
    ∃ j < n, (runOf n ys).Between j t ∧ t ∈ window (profileOf site) (snapshotOf (ys j)) ∧
      (x.ModelUntil (profileOf site) (snapshotOf (ys j)) t →
        x.OperatesIn (profileOf site) (runOf n ys) state j t →
        x.WithinOrFallback (profileOf site) (snapshotOf (ys j)) t)
```

| Theorem | Statement | File |
|---|---|---|
| `fallback_keeps_floor`, `_ceiling`, `_export`, `_import`, `within_of_fallback` | When fallback's worst case lies within one site limit at `t`, `WithinOrFallback` gives that limit at `t`, and within all four it gives `Within` | `Spec.lean` |
| `site_valid` | The test site's table meets the profile's validity condition, by kernel evaluation | `Theorems.lean` |
| `toNat_add`, `toNat_mul`, `lowDrain_toNat`, `lowB_signed`, and the other word lemmas | Under the validity bounds, each `UInt64` operation of the authorizer equals the natural-number operation | `Arith.lean`, `Authorize.lean` |
| `energy_bounds`, `drainLow_ge` | Rate bounds on a measurable trajectory give the affine energy bounds up to each time of the window, and the integer drain covers the real one | `Window.lean` |
| `window_sound` | `Conditions` implies `WithinOrFallback` at each time `t` of the window for every trajectory admitted until `t` | `Window.lean` |
| `admitted_exists`, `authorizeWith_admits`, `authorize_admits` | For ordered intervals, and so for every accepted input, some trajectory is admitted until every time | `Window.lean`, `Authorize.lean`, `Theorems.lean` |
| `power_in_window` | `OperatesIn` gives assumption A2 of an accepted window from its snapshot to the next | `Compose.lean` |
| `run_sound`, `run_covered`, `operation_sound`, `authorizeWith_operation`, `authorize_operation` | Each accepted window's bounds hold from its snapshot to the next, and every time from the first accepted snapshot to the end of the last window lies in the window of the latest accepted snapshot at or before it when accepted snapshots lie at most `W` apart | `Compose.lean`, `Authorize.lean`, `Theorems.lean` |
| `operates_exists` | Some trajectory and applied states meet a window's `ModelUntil` and `OperatesIn` | `Compose.lean` |
| `authorizeWith_iff` | Under a valid profile table, the authorizer accepts exactly when the input meets `InputValid` and `Conditions` holds | `Authorize.lean` |
| `authorizeWith_sound`, `authorize_sound` | For accepted limits, every trajectory admitted until a time `t` of the window meets the bounds of the acceptance rule at `t` | `Authorize.lean`, `Theorems.lean` |
| `authorizeWith_accepted`, `authorize_accepted` | An accepted result holds the proposed limits and the expiry `t_m + W - τ` | `Authorize.lean`, `Theorems.lean` |
| `example_accept`, `example_export`, `example_floor`, `example_relative`, `example_renewal`, `example_limits`, `example_limits_import` | The worked example's decisions, by kernel evaluation | `Examples.lean` |
| `compiled.authorize.implements`, `compiled.bytes`, `compiled.initial` | Generated by `verified_compile` | `Verified.lean` |
| `energy_export`, `authorize_call` | The module exports `authorize` as function 17, and a call of function 17 from a ready store returns `authorize xs` without a trap | `Theorems.lean` |
| `energy_authorize` | The module's bytes decode to the module, whose export `authorize` is function 17, whose initial store is ready, and whose entry returns `authorize xs` without a trap, and every accepted result meets `authorize_sound` | `Theorems.lean` |
| `energy_file`, `energy_file_decode` | The released file holds the module's encoding and decodes to the module | `File.lean` |

`authorizeWith_iff` states the acceptance condition exactly, and the examples exhibit inputs that meet it.  `authorize_admits` and `operates_exists` show that some trajectory meets the premises of `authorize_sound` and of `run_sound`.  `example_accept` and `example_relative` prove acceptance of a nonzero discharge and a nonzero charge, `example_renewal` the rejection of a renewal that would cross the floor, and `example_limits` the acceptance of limits that allow both.  How often realistic inputs meet the condition is an empirical question, which the replay study answers.  `authorize_call` obtains the call theorem from `compiled.authorize.implements` through `Verified.ImplementsTables.call`, and `energy_authorize` combines `compiled.bytes`, `energy_export`, `Verified.Ready.initial` with `compiled.initial`, `authorize_call`, and `authorize_sound`.  `file_theorems energy compiled "../../build/verified/energy.wasm" from compiled.bytes` states the file theorems after the test driver writes the file.  Every theorem that `tests/energy/Axioms.lean` audits depends only on `propext`, `Classical.choice`, and `Quot.sound`, and `tests/verified/run.sh` fails when an audit reports another axiom.

The module-level statements keep the assumptions that [the trusted base](docs/trusted-base.md) lists for modules of the verified compiler and for files with file theorems.  The statements describe execution in Talos's semantics, the gateway runs the module in Wasmtime, and the agreement of the two is an assumption, as is the decoder's reading of the bytes.  No theorem connects Wasmtime's instantiation or the gateway's placement of the argument array to the store that the statements assume, and the tests that compare Wasmtime with native Lean on every case are evidence for these assumptions, without proving them.

## Repository layout

The Lean code, proofs, and replay tool are in this repository and follow the slew planner's layout.  Stage 6 places the gateway and device adapters in a separate repository that pins a release of the module, so that the device protocols and credentials stay apart from the proofs.  The registry entries let `tests/verified/run.sh` emit the module and check its file theorems, and the case executable supplies its cases.

| Path | Contents |
|---|---|
| `Demos/Energy/README.md` | The model, interface, theorems, and limits |
| `Demos/Energy/Replay.md` | The replay study: data, simulated site, interval rules, margins, window length, bills, and excursions within a minute |
| `Demos/Energy/Spec.lean` | Profile, snapshot, command limits, trajectory, `ModelUntil`, `AdmittedUntil`, `Within`, `WithinOrFallback`, and the `fallback_keeps` lemmas |
| `Demos/Energy/Operation.lean` | A run of accepted authorizations, `Run.Between`, `Run.Spaced`, and `OperatesIn` |
| `Demos/Energy/Words.lean` | Decoding of words into the specification's records, `ProfileValid`, and `InputValid` |
| `Demos/Energy/Program.lean`, `Flat.lean` | `authorizeWith` and its helpers, in the verified compiler's dialect, and the representations of its result |
| `Demos/Energy/Arith.lean`, `Window.lean`, `Compose.lean`, `Authorize.lean` | Exactness of word operations, the energy bound, `Conditions`, and `window_sound`, consecutive windows, and the theorems about the authorizer |
| `Demos/Energy/Site.lean` | The profile table of the test site and the wrapper `authorize` |
| `Demos/Energy/Verified.lean`, `Theorems.lean`, `File.lean`, `Examples.lean` | Compilation, `site_valid` and the module-level theorems, file theorems, and kernel-evaluated examples |
| `tests/TestSupport/Energy/Cases.lean`, `CasesMain.lean` | Case printer, which the executable `verified-cases-energy` of `lakefile.lean` runs from a branch of `tests/verified/run.sh` |
| `Demos/Verified.lean`, `Verified/Examples/Cases.lean` | Imports of the theorems, the examples, and the cases |
| `tests/energy/` | The axiom audit and the replay tool |
| `tests/verified/modules.txt`, `tests/verified/numerics.txt` | Registry entries for the module and its file theorems |

## Testing and evaluation

### Module cases

The case printer prints 2,056 cases with results that native Lean computes, and `tests/verified/run.sh` compares them with Wasmtime.  The cases are the worked example, inputs that the checks before the side tests reject, inputs on both sides of each side test's boundary, and 2,000 inputs that SplitMix64 draws from a fixed seed.  The rejected inputs have wrong lengths or versions, a word one past its range, reversed intervals or limits, limits beyond the largest charge or discharge, or every word at `2^64 - 1`.  The boundary inputs also cover the fallback mode in force, a state in force and a proposal of opposite directions, energies on and beyond the floor and the ceiling, where the authorizer accepts limits that leave the site no further outside the limit, and words at the ends of their ranges.  The replay tool computes the same decisions independently and compares them with the printed cases, and every failing case found later stays in the corpus.

### Replay study

The replay tool, `tests/energy/replay.py`, is a Python program with PEP 723 metadata that runs with `uv run` and uses only the standard library.  It implements the acceptance rule a second time, from this document, with exact integer arithmetic, and `replay.py check` compares its decisions with the module cases.  The study uses the minute data of NIST's Net-Zero Energy Residential Test Facility, an all-electric test house with a 10.2 kW PV array, calibrating on the test year 2013–14 and evaluating on the withheld test year 2015–16, and the one-second data of one house of the PTProsumer dataset to estimate the excursions within a minute.  Each run fixes a rule for the load and PV intervals: the true minimum and maximum over the window, which bounds acceptance from above, or a causal rule that widens the extremes of the previous 15 minutes by a percentile of the excursions in the calibration year.  The sweep covers window lengths of 180, 300, 600, and 900 s, of which 180 s is the shortest whole minute that `W > a + 2τ` allows, with tolerances of 25 to 200 W, efficiency bounds of 850,000 and 950,000 ppm, and grid caps that bind or never bind.  It reports the largest accepted charge and discharge, how often fallback's worst case breaks each limit, and the intervals' coverage, and it checks `WithinOrFallback` at every minute of every accepted window up to the first premise failure, for the nominal device and for a device at the extremes that the premises allow.

### Economic evaluation

The evaluation compares the controller, on the withheld year, with no battery, with a simulation of the vendor's self-consumption mode, with a fixed time-of-use schedule with a fixed reserve, and with the vendor's mode within the widest limits that the authorizer accepts.  The controller is the self-consumption rule with a curtailment rule that uses a one-day look-behind forecast, one of the forecasts of SAM's battery dispatch.  The replay bills a stated tariff, because the test house has no billing rules of its own that value a battery: PG&E's E-ELEC import prices, a flat export credit, and a wear cost per kWh discharged.  The report gives the bill, the import, export, curtailed, and discharged energy, the fraction of proposals accepted, and the lowest stored energy against the floor.  Site operation bills under the site's own rules, and the report presents simulated savings from replay and measured savings from site operation separately, and neither as a causal effect without a suitable evaluation design.

### Results

[The replay study](Demos/Energy/Replay.md) chose `W = 600` s, the longest window whose controller bill and wear on the calibration year lie within 1% of the lowest.  With a 24 kW import cap, that of a 100 A, 240 V service, and a 5 kW export cap, the import test rejects at most 1.0% of snapshots on the calibration year and the export test 4.0% to 7.5%, while the floor and ceiling tests reject the most proposals.  On the withheld year, the vendor's mode saves $549 against no battery, and the controller through the authorizer at 600 s saves $448.  The authorizer costs the controller $36 at 600 s and $21 to $48 from 180 to 900 s, against $14 to $41 with caps that never bind, and held setpoints proposed from the previous minute cost $78 against the vendor's mode, which follows each minute's own values.  The causal rule covers 98.2% to 99.7% of each month's windows on the withheld year, and no run found a violation of `WithinOrFallback`, in 0.54 to 6.32 million window-minutes per run.

Fallback's worst case breaks the floor at 29.7% to 44.2% of snapshots, because standby loss drains the idle battery below the floor, so the floor bound is relative to fallback at those snapshots, and stored energy reaches 1.5 to 1.7 kWh below the floor.  At a 10 kW import cap, below the house's peak load of 22.9 kW, the import test rejects 15.9% to 22.3% of the controller's unlimited proposals, and the battery reaches its lower cutoff.  One-second data from another house put the load more than 1.4 kW above its minute maximum in 1% of 180 s windows, so the minute data overstate acceptance and coverage.

## Stages

| Stage | Work | Exit evidence | Status |
|---|---|---|---|
| 1. Authorizer | Specification and its review, program, proofs, compilation, file theorems, examples, cases | Theorems with only the permitted axioms, cases that pass in Wasmtime against native Lean, and a file theorem checked after emission | Complete |
| 2. Replay study | Dataset, replay tool, sweep | Report of acceptance margins; window length chosen | Complete: `W = 600` s |
| 3. Optimizer and economic replay | Rule-based optimizer, baselines | Report with savings and acceptance rates | Complete |
| 4. Site selection and qualification | Equipment with command expiry and fallback; measurement of `e`, `τ`, `F`, `η`, `ℓ⁺`, the expiry's granularity, and the energy estimate's error | Qualification report; signed profile; site module with its file theorem | Not started |
| 5. Read-only operation | Ingestion, authorizer, and historian on live data, with no device writes | At least 30 consecutive days logged; comparison of model and measurement; coverage statistics for A1, A3, and A4 from data finer than a minute | Not started |
| 6. Gateway and actuation qualification | Gateway and its runtime, vendor test rig or hardware-in-the-loop, fault injection | The gateway's rules, expiry, return to fallback, read-back, and credential isolation demonstrated; installer and vendor sign-off | Not started |
| 7. Supervised operation | Narrow power limits, short operating periods, rollback to the vendor's mode | Measured outcomes; incident log | Not started |
| 8. Extensions | Composition of consecutive windows; schedules with time-varying reserves and EV deadlines, owner settings in the input, a verified optimizer, grid limits over metering intervals | New theorems and assumptions for each extension | Composition complete; the others not started |

A site stays in read-only operation when its equipment lacks command expiry or a qualified fallback, when its energy estimate has no characterized error bound, when the meaning of a profile value is ambiguous, or when the installer or utility has not approved control.  An extension that changes the model states new theorems and new assumptions, and an earlier theorem never describes the extended system.  The site's module, with its profile table and file theorem, is the artifact that Stages 5 to 7 run.

## Decisions

| Decision | Choice | Reason |
|---|---|---|
| Command form | Power limits `[c⁻, c⁺]`, with a held setpoint as `[s, s]` | The inverter's own mode follows the load within the limits, which a held setpoint cannot, and the window's power interval and tests keep their form |
| Grid caps | Instantaneous, tested against the worst-case load and PV of the window | Interconnection limits are instantaneous, and a cap at the site's service rating rejects at most 1% of snapshots in the replay.  For a site with an averaged limit, a pro-rata form, in which the import metered since the start of a metering interval stays at or below the cap times the elapsed time, has the form of the ceiling test with no premise after the window.  It needs the metered import since the interval's start as a snapshot interval with its error, and the interval's length and alignment in the profile. |
| Window length | 600 s for the study's site | The longest length whose controller bill and wear on the calibration year lie within 1% of the lowest.  Stage 4's expiry granularity and Stage 5's measurement of the excursions within a minute can change it.  The test site's table keeps the worked example's 900 s. |

## Open decisions

| Decision | Options | Evidence |
|---|---|---|
| Gateway runtime, in Stage 6 | Wasmtime embedded in a small C or Rust program, or the module's C translation compiled by CompCert | The C translation removes Talos's execution semantics, the decoder, and Wasmtime from the assumptions and adds CompCert, the Lean copy of Clight, and the other items that the trusted base lists for C files.  `compiled.authorize.native` covers the translation's `authorize`, and `tests/native/verified.sh` passes the module's 2,056 cases on its CompCert build. |
| The proposer under limits | Held setpoints from the controller's rule, the widest accepted limits for the vendor's mode, or limits from a forecast | With the study's caps at 600 s, the vendor's mode within the widest accepted limits costs $1,505 and the controller's held setpoints $1,560.  Minute data cannot measure what limits gain within a minute, which Stage 5's data can. |
| The floor under standby loss | Accept the bound relative to fallback, with the BMS cutoff as protection; let the optimizer propose charges that offset standby loss at the floor; or require a fallback mode that holds the floor | The idle battery's standby loss drains it below the floor, so fallback's worst case breaks the floor at 29.7% to 44.2% of snapshots in the replay. |

## References

- [Energy: authorization of battery power limits](Demos/Energy/README.md)
- [Energy: replay study](Demos/Energy/Replay.md)
- [Verified Compiler Manual](docs/verified-manual.md)
- [Trusted base](docs/trusted-base.md)
- [Slew: constraint-checked attitude slews](Demos/Slew/README.md)
- [Talos](https://github.com/jsmorph/talos)
- [Wasmtime](https://wasmtime.dev/)
- [CompCert](https://compcert.org/)
- [Mathlib: Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.html)
- [NIST Net-Zero Energy Residential Test Facility data](https://pages.nist.gov/netzero/data.html)
- [PTProsumer dataset](https://osf.io/9xs3a/)
- [PG&E residential rate plan pricing](https://www.pge.com/assets/pge/docs/account/rate-plans/residential-electric-rate-plan-pricing.pdf)
- [NREL System Advisor Model: behind-the-meter battery dispatch](https://samrepo.nlr.gov/help/battery_dispatch_btm.html)
- [IEEE 1547-2018: Standard for Interconnection and Interoperability of Distributed Energy Resources with Associated Electric Power Systems Interfaces](https://standards.ieee.org/ieee/1547/5915/)
- [NFPA 70, National Electrical Code: standard development](https://www.nfpa.org/codes-and-standards/nfpa-70-standard-development/70)
- [NFPA 855, Standard for the Installation of Stationary Energy Storage Systems: standard development](https://www.nfpa.org/codes-and-standards/nfpa-855-standard-development/855)
- [UL Solutions: Energy Storage System Testing and Certification](https://www.ul.com/services/energy-storage-system-testing-and-certification)
