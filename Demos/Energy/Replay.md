# Energy: replay study

The replay study measures how the authorizer's acceptance rule limits battery dispatch, chooses the window length `W`, and compares the bills of dispatch policies.  It replays two years of minute data from a test house through a simulated battery, gateway, and authorizer.  [The replay tool](../../tests/energy/replay.py) implements the acceptance rule of [the plan](../../energy-controller-plan.md) a second time, in Python with exact integer arithmetic, and `replay.py check` agrees with native Lean on all 2,047 module cases.  The results describe a simulated site under the stated assumptions and estimate margins and value.  They do not measure an installation.

## Data

The data are the minute averages of NIST's [Net-Zero Energy Residential Test Facility](https://pages.nist.gov/netzero/data.html), an all-electric house in Gaithersburg, Maryland, with a 10.2 kW PV array, a heat pump, and a heat-pump water heater, which a script operates for a virtual family of four.  The test year from July 2013 to June 2014 calibrates the causal interval rule and the controller, and the test year from February 2015 to January 2016 is withheld for evaluation.  Between the two years NIST changed the dehumidification, the ventilation schedule, and the thermostat settings, so the withheld year also tests the rules under a change of configuration.

Load is the sum of every circuit of the house, the heat pump's indoor and outdoor units, the dehumidifier, the water heater's total power, and the oven.  It leaves out the facility's instrumentation, the electric emulators of the occupants' heat and moisture, the water heater's single-leg circuit, and the `Load` channels that sum circuits.  PV is the power that the two inverters feed into the panel.  A channel that is empty for a whole year is absent from that year, which applies to the dehumidifier in 2013–14.  A minute in which another channel is empty or reads below -100 W is missing, and so is every minute of a day with more than 60 such minutes.

| Test year | Valid minutes | Days dropped | Load (kWh) | PV (kWh) |
|---|---|---|---|---|
| 2013–14 | 507,729 | 7 | 12,502 | 13,227 |
| 2015–16 | 493,393 | 18 | 11,292 | 12,845 |

Scaled to the whole year, the 2013–14 sums lie within 1% of NIST's published consumption of 13,039 kWh and generation of 13,523 kWh.  NIST publishes no consumption for 2015–16, only a net export of 2,240 kWh, against which the sums imply about 1,650 kWh.  The study does not explain the difference.  Thirteen minutes in the two years show PV above 10.5 kW, up to 17.6 kW, which the array cannot produce.  The study keeps them: they are too few to move a total, and they can raise the causal rule's percentile only in the few bins of month and hour where they fall.

## The simulated site

The site keeps the battery of the plan's worked example and caps that the house breaks when the battery is idle: its load exceeds 10 kW in 6,550 minutes of 2013–14 and 96 minutes of 2015–16, and its surplus PV exceeds 5 kW in about 48,000 to 50,000 minutes of each year.  The PV inverter curtails export at the cap.  A second set of runs uses caps of `2^20` W, which never bind, to separate the energy tests from the grid tests.

| Quantity | Value |
|---|---|
| Battery | 10 kWh between the BMS cutoffs, 5,000 W charge and discharge |
| Floor and ceiling | 3 kWh and 9.5 kWh |
| Import and export caps | 10,000 W and 5,000 W, or `2^20` W |
| Profile bounds | `η = 900,000` ppm, `ℓ⁺ = 20` W, `e = 50` W, `F = [-50, 50]` W, `τ = 30` s, `a = 60` s |
| Simulated battery | Charge and discharge efficiencies 0.95, loss 10 W, power equal to the command |
| Energy estimate | The simulated energy ± 360,000 J |

The gateway takes a snapshot every minute and follows the plan's rules.  It sends the proposal when the authorizer accepts it and nothing otherwise, so the command in force runs to its expiry.  It returns the device to fallback when a minute's load or PV leaves the intervals of the command in force, or when data are missing.  The device follows a command from the start of its snapshot's minute until its expiry and runs in the idle fallback otherwise.  A minute is the shortest time that the data resolve, so the replay shows nothing about `a` or `τ` themselves.

## Interval rules

The true-range rule takes the minimum and maximum of the minute values in the window.  It uses future data, so it bounds acceptance from above and serves only Stage 2.  The causal rule takes the extremes of the previous 15 minutes and widens each by a percentile, 99.9% unless a row states otherwise, of the excursions that the calibration year shows for the same window length, month, and hour.  The excursions of each month are pooled with those of its two neighbors, so that the hours of sunrise and sunset fall in like bins.  Lower bounds stop at 0.  Both rules work from minute averages, while assumption A4 concerns instantaneous power, so both overstate acceptance and coverage by the excursions within a minute, which a later section estimates.

## Stage 2: margins

The sweep runs on the calibration year, with the causal rule calibrated on the same year, so that the choice of `W` uses no withheld data.  The proposer is the self-consumption rule: the last minute's surplus PV or deficit, within the setpoint limits and the power that keeps the energy estimate between the floor and the ceiling.  For reference, the vendor's self-consumption mode, which follows each minute's own values, discharges 2,054 kWh in the year, and the one-minute proposer discharges 2,052 kWh when every proposal is sent without the authorizer.

| Rule | Caps | W (s) | Discharged (kWh) | Run-on (kWh) | Snapshots rejected by the import test (%) | Full 5,000 W charge accepted (%) | No charge beyond `F` accepted (%) | Coverage (%) |
|---|---|---|---|---|---|---|---|---|
| True range | Study | 180 | 1,962 | 153 | 0.1 | 75.4 | 2.9 | 100 |
| True range | Study | 300 | 1,953 | 262 | 0.2 | 73.5 | 3.8 | 100 |
| True range | Study | 600 | 1,934 | 491 | 0.3 | 69.2 | 5.8 | 100 |
| True range | Study | 900 | 1,903 | 685 | 0.5 | 65.7 | 7.6 | 100 |
| Causal | Study | 180 | 870 | 128 | 21.1 | 17.3 | 59.5 | 99.5 |
| Causal | Study | 300 | 847 | 213 | 22.7 | 14.8 | 61.7 | 99.3 |
| Causal | Study | 600 | 723 | 329 | 26.7 | 9.2 | 71.0 | 98.8 |
| Causal | Study | 900 | 559 | 391 | 27.8 | 7.7 | 72.8 | 98.3 |
| Causal, 99th percentile | Study | 300 | 1,546 | 229 | 8.7 | 31.8 | 36.0 | 96.7 |
| True range | Open | 180 | 2,001 | 141 | 0 | 78.8 | 1.1 | 100 |
| Causal | Open | 180 | 1,997 | 140 | 0 | 78.6 | 1.2 | 99.5 |
| True range | Open | 900 | 2,021 | 730 | 0 | 72.9 | 3.7 | 100 |
| Causal | Open | 900 | 2,017 | 730 | 0 | 72.9 | 3.7 | 98.3 |

Run-on is the energy that a command delivers after a later proposal is rejected, while the command runs to its expiry.  It counts in the discharged energy, so the discharged energy of a long window overstates what the authorizer allows: with open caps the 900 s window discharges more than the 180 s window only because of run-on.  The largest accepted setpoints come from a search at every snapshot.  They depend on the state in force, which at a one-minute cadence is the last command, so a discharge in force subjects every charge to the floor and export tests.

With the study's caps, the import test decides the result.  The causal rule widens the load's upper bound by the 99.9th percentile of the load's rise over the window.  For 300 s that percentile lies between 9.7 and 12.2 kW in every hour from November to March, the heating season, and below 8.6 kW from June to September.  A charge then fails `L⁺ + B⁺ ≤ I + S⁻` in 21% to 28% of all snapshots, and in 60% to 73% of snapshots no charge beyond the fallback interval passes.  With the same rule and caps that never bind, the authorizer delivers 97% of the ungated proposer's discharge at 180 s.  The 99th percentile delivers 1.8 times the energy of the 99.9th at 300 s, with coverage of 96.7% instead of 99.3%, and in 785 minutes it let a limit break while a premise had failed, against 89 for the 99.9th percentile.

The tracking tolerance and the efficiency bound change little at 300 s with the causal rule: the discharged energy is 849, 847, 844, and 839 kWh for `e` of 25, 50, 100, and 200 W, with `F` widened to `[-e, e]` where `e` exceeds 50 W, and 847 and 848 kWh for `η` of 850,000 and 950,000 ppm.  Fallback's worst case breaks the floor at 32% to 70% of snapshots, because the battery often rests at the floor, where the idle loss drains it below the floor, so the theorem's floor bound is relative to fallback at those snapshots.  Fallback breaks the ceiling at fewer than 0.05% of snapshots, the export cap at 12% to 16% with the true range and 30% to 35% with the causal rule, and the import cap at 2% to 4% with the true range and 59% to 72% with the causal rule.

The causal rule's coverage by month is lowest in July and August, at 97.0% to 97.1% for 900 s, and at least 99.1% in every month for 180 s.  In every run, the simulated energy and grid power met `WithinOrFallback` at every minute of every accepted window up to its first premise failure: 0.56 to 3.6 million window-minutes per run without a violation.  The replay at the premises' extremes runs the device at `s - e` with efficiency `η`, loss `ℓ⁺`, and the energy at the lower end of its interval, or at `s + e` with efficiency 1, no loss, and the energy at the upper end, under a proposer that alternates the largest accepted discharge and charge by the hour.  It checked 1.2 to 4.8 million window-minutes for 180 and 900 s without a violation.

## The window length

The criterion, fixed before the runs: among the window lengths that the gateway's timing allows, choose the longest whose controller bill and wear on the calibration year lies within 1% of the lowest, because a longer window keeps a command in force through a longer loss of communication.  The controller's bills and wear on the calibration year, with the study's caps and the causal rule, are $2,044, $2,067, $2,121, and $2,147 for 180, 300, 600, and 900 s.  The study chooses `W = 180` s, the shortest length in whole minutes that `W > a + 2τ` allows, since 300 s lies 1.1% above it.  The choice is provisional: the equipment's expiry granularity, which Stage 4 measures, can only lengthen it, and the excursions within a minute, which Stage 5 measures at the site, can change the margins of every length.

## Stage 3: bills

The bill uses a tariff that the study states, because the test house has no billing rules that value a battery.  Import follows [PG&E's Electric Home Rate Plan (E-ELEC)](https://www.pge.com/assets/pge/docs/account/rate-plans/residential-electric-rate-plan-pricing.pdf), effective March 1, 2026, for an all-electric home: from June to September 33¢ per kWh off-peak, 39¢ at partial peak (3 to 4 p.m. and 9 p.m. to midnight), and 55¢ at peak (4 to 9 p.m.), and in the other months 28¢, 30¢, and 32¢.  Export earns a flat 5¢ per kWh, an assumption in place of the hourly export rates of PG&E's net billing tariff, and the fixed base services charge, the same for every policy, is omitted.  The tariff applies on the house's local clock, so the study pairs a Maryland house with a California tariff.  Battery wear costs 5¢ per kWh discharged, the assumption of a $400 per kWh replacement over 8,000 full cycles, and the capacity stays constant over the year.

| Policy | Description |
|---|---|
| No battery | The house alone, with export curtailed at the cap |
| Self-consumption mode | The vendor's mode: each minute it charges the minute's surplus PV and covers the minute's deficit, between the floor and the ceiling |
| Time-of-use schedule | As the self-consumption mode, but it covers the deficit only during partial peak and peak, down to a fixed reserve equal to the floor |
| Self-consumption rule, one-minute commands | The self-consumption rule as a command each minute from the previous minute's values, every proposal sent |
| Controller | The self-consumption rule with curtailment-aware charging, as a command each minute, every proposal sent or through the authorizer with the causal rule |
| Self-consumption mode within authorized limits | The vendor's mode, limited each minute to the widest charge and discharge limits that the authorizer accepts, a command form that the plan leaves open |

The controller charges as the self-consumption rule does, except that before 3 p.m., when the previous day's surplus came within 1,000 W of the export cap and stored half again the room left below the ceiling, it charges only the surplus within 1,000 W of the cap, so that the battery takes PV that the cap would curtail.  It limits each proposal to the range that its own copy of the acceptance rule accepts.  The controller began with two further rules, which the calibration year rejected.  An evening reserve kept off-peak energy for the forecast deficit of the partial peak and peak, and summer grid charging bought the forecast shortfall off-peak when the peak price covered the round-trip loss and the wear.  Without the authorizer on the calibration year, the self-consumption rule as one-minute commands costs $1,917 with wear, the curtailment rule alone $1,900, the reserve alone $1,919, the reserve with grid charging $1,931, and all three $1,916.  The curtailment rule in its final form, which applies only when the previous day's surplus came near the cap, costs $1,901.

The withheld year's bills and wear:

| Policy | Study caps ($) | Caps that never bind ($) | Import (kWh) | Export (kWh) | Curtailed (kWh) | Discharged (kWh) |
|---|---|---|---|---|---|---|
| No battery | 2,008 | 1,949 | 7,294 | 7,682 | 1,166 | 0 |
| Self-consumption mode | 1,459 | 1,406 | 5,355 | 5,550 | 1,060 | 1,939 |
| Time-of-use schedule | 1,482 | 1,428 | 5,478 | 5,670 | 1,076 | 1,817 |
| Self-consumption rule, one-minute commands | 1,538 | 1,485 | 5,625 | 5,821 | 1,059 | 1,939 |
| Controller, every proposal sent | 1,524 | 1,485 | 5,679 | 6,395 | 552 | 1,816 |
| Controller through the authorizer, 180 s | 1,657 | 1,499 | 6,280 | 6,965 | 660 | 1,118 |
| Controller through the authorizer, 300 s | 1,684 | 1,503 | 6,389 | 7,036 | 709 | 1,012 |
| Controller through the authorizer, 600 s | 1,757 | 1,513 | 6,632 | 7,214 | 823 | 774 |
| Controller through the authorizer, 900 s | 1,787 | 1,526 | 6,710 | 7,284 | 846 | 711 |
| Self-consumption mode within authorized limits, 180 s | 1,628 | 1,421 | 6,143 | 6,569 | 916 | 1,151 |
| Self-consumption mode within authorized limits, 900 s | 1,723 | 1,423 | 6,512 | 6,937 | 988 | 782 |

The energy columns are those of the study's caps.  With those caps, the vendor's mode saves $549 against no battery and the controller through the authorizer at 180 s saves $351.  The difference has three parts.  Commands that hold a power for a minute cost $79, because the proposer holds the previous minute's net load through the next minute, and the minute data show none of the changes within a minute that the vendor's mode also follows.  With caps that never bind, a proposer that estimates the net load at the snapshot by the mean of the previous and the present minute cuts this cost from $79 to $40.  The controller's curtailment rule saves $14.  The authorizer costs $133, most of it through the grid tests, since with caps that never bind it costs $14 at 180 s and $41 at 900 s.

Through the authorizer the controller's unlimited proposals pass 50% to 56% of the time.  At 180 s the others fail the floor test (29% of snapshots), the import test (16%), the ceiling test (3%), and the export test (2%), and the controller sends a limited proposal at 94% of snapshots.  With the study's caps the import test blocks charging through much of the winter, and the battery drains to its BMS cutoff through its standby loss: the lowest energy is 3 kWh below the floor.  The vendor's modes reach 1.6 kWh below the floor in the same year by the same loss.  The replay checked `WithinOrFallback` over 1.3 to 6.3 million window-minutes for each window length without a violation.

A command of power limits, within which the inverter's own self-consumption mode follows the load, makes the window's power interval the hull of the limits in force widened by `e`, the proposed limits widened by `e`, and `F`.  The side tests are those of the setpoint form, and the widest accepted limits are its largest accepted discharge and charge.  With caps that never bind, the vendor's mode within the widest accepted limits costs $1,421 at 180 s and $1,423 at 900 s, $15 to $17 more than the mode alone, against $93 more for the held setpoints of the controller at 180 s.  Most of that difference comes from the proposer, which holds the previous minute's net load while the limits device follows the present minute.  Through the authorizer at 180 s, a held setpoint proposed from the present minute's net load, which no gateway knows in advance, costs $1,426, and one proposed from the mean of the previous and the present minute costs $1,462.  The minute data therefore cannot measure what limits gain, which lies in the changes of load within each minute.  A setpoint `s` is the limits `[s, s]`, so the limits form also authorizes held setpoints, including the controller's curtailment rule on equipment that accepts them.  With the study's caps limits cost $1,628 at 180 s, because the import test still binds, and the replay checked their windows over 1.2 to 5.9 million window-minutes without a violation.

## Excursions within a minute

Both interval rules work from minute averages, while the premises concern instantaneous power.  One house of the [PTProsumer](https://osf.io/9xs3a/) dataset estimates how much the averages hide: house PR_02 in Madeira, with a three-phase supply of 10.35 kVA and a 2.7 kW array, for 2019, from meters of net load and PV sampled every second.  Load is net load plus PV.  For each window of whole minutes the table compares the extremes of the one-second values with the extremes of the minute averages.

| W (s) | Load above the minutes' maximum: p50, p90, p99, p99.9 (W) | Load below the minutes' minimum | PV above | PV below |
|---|---|---|---|---|
| 60 | 7, 190, 1,427, 2,392 | 7, 171, 1,136, 1,873 | 1, 37, 595, 1,107 | 1, 38, 564, 1,007 |
| 180 | 9, 385, 1,458, 2,586 | 7, 166, 1,083, 1,846 | 1, 43, 608, 1,118 | 1, 36, 541, 962 |
| 300 | 12, 586, 1,482, 2,698 | 7, 162, 1,045, 1,860 | 1, 48, 616, 1,124 | 1, 35, 530, 945 |
| 900 | 28, 810, 1,576, 2,937 | 8, 175, 862, 1,878 | 2, 71, 622, 1,092 | 0, 33, 518, 945 |

In 1% of 180 s windows the one-second load rises more than 1.4 kW above the highest minute average, and PV moves more than 0.5 kW beyond its minute extremes, a fifth of this array's rating.  The test house has larger loads and a larger array, so its excursions within a minute are likely larger, and the true-range rule's acceptance and the causal rule's coverage overstate what one-second data would give.  The two meters sample separately, so part of the load's excursion may come from the difference of their sampling instants while PV changes.

## What the study shows about the design

The authorizer's own tests cost little when the grid caps lie beyond what the house's load and PV can reach: $14 a year at 180 s on the withheld year, and coverage of the causal rule's intervals of 99.4% to 99.7% by month.  Two features of the design cost more.  A command that holds one power cannot follow the load within the window.  In the replay it costs $40 to $79 a year against the vendor's mode at this house, depending on how the gateway estimates the net load at the snapshot, and more once the changes within a minute count, which power limits for the vendor's mode would follow.  An instantaneous import cap that the house's own load can approach makes the causal rule's worst-case load block charging through the winter: with the study's caps the authorizer costs $133 a year at 180 s instead of $14, and the battery drains to its cutoff.  Both are properties of the design as specified, and changing either changes the acceptance rule and the statement of its theorem.

## Limits

The data are minute averages of one test house with scripted occupants in one climate, the load is a sum of circuit channels whose 2015–16 total differs from NIST's net export, and the excursions within a minute come from a different house.  The tariff, the export credit, the wear cost, and the caps are stated assumptions, and the battery's capacity does not fade.  The simulated device follows commands exactly at the start of the minute, so the replay says nothing about the transition time or the send deadline.  The savings are simulated and do not estimate the savings of an installed system.

## Commands

```sh
uv run tests/energy/replay.py check CASES
uv run tests/energy/replay.py prepare NIST_YEAR_DIRECTORY SERIES
uv run tests/energy/replay.py margins CALIBRATION_SERIES CALIBRATION_SERIES
uv run tests/energy/replay.py economics CALIBRATION_SERIES EVALUATION_SERIES --window 180 --window 900
uv run tests/energy/replay.py economics CALIBRATION_SERIES EVALUATION_SERIES --window 180 --open-caps
uv run tests/energy/replay.py within NET_LOAD_FILE PV_FILE
```

`CASES` is the output of `lake exe verified-cases-energy`.  A NIST year directory holds that year's `Elec`, `HVAC`, `DHW`, and `Load` minute files from NIST's data page, and `prepare` writes one series of minute load and PV per year.  The `within` command reads one house-year of a PTProsumer net-load file and its PV file, both compressed.

## References

- [NIST Net-Zero Energy Residential Test Facility data](https://pages.nist.gov/netzero/data.html)
- [Healy et al., Performance Data from the NIST Net-Zero Energy Residential Test Facility, Journal of Research of NIST 122:14 (2017)](https://doi.org/10.6028/jres.122.014)
- [PTProsumer dataset](https://osf.io/9xs3a/)
- [PTProsumer data descriptor](https://pmc.ncbi.nlm.nih.gov/articles/PMC12675649/)
- [PG&E residential rate plan pricing](https://www.pge.com/assets/pge/docs/account/rate-plans/residential-electric-rate-plan-pricing.pdf)
- [NREL System Advisor Model: behind-the-meter battery dispatch](https://samrepo.nlr.gov/help/battery_dispatch_btm.html)
- [Verified Energy Controller: Plan and Design](../../energy-controller-plan.md)
