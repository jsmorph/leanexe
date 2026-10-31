# Energy: replay study

The replay study measures how [the energy authorizer](README.md)'s acceptance rule limits battery dispatch, chooses the window length `W`, and compares the bills of dispatch policies.  It replays two years of minute data from a test house through a simulated battery, gateway, and authorizer.  [The replay tool](../../tests/energy/replay.py) implements the acceptance rule of [the plan](../../energy-controller-plan.md) a second time, in Python with exact integer arithmetic, and `replay.py check` agrees with native Lean on all 2,056 module cases.  The symbols are those of the README: `B` is a window's power interval, `F` the fallback interval, `e` the tolerance about a command's limits, `η` the efficiency bound, and `ℓ⁺` the largest loss rate.

## Data

The data are the minute averages of NIST's [Net-Zero Energy Residential Test Facility](https://pages.nist.gov/netzero/data.html), an all-electric house in Gaithersburg, Maryland, with a 10.2 kW PV array, a heat pump, and a heat-pump water heater, which a script operates for a virtual family of four.  The test year from July 2013 to June 2014 calibrates the causal interval rule and the controller, and the study withholds the test year from February 2015 to January 2016 for evaluation.  Between the two years NIST changed the dehumidification, the ventilation schedule, and the thermostat settings, so the withheld year also tests the rules under a change of configuration.

Load is the sum of every circuit of the house, the heat pump's indoor and outdoor units, the dehumidifier, the water heater's total power, and the oven.  It leaves out the facility's instrumentation, the electric emulators of the occupants' heat and moisture, the water heater's single-leg circuit, and the `Load` channels that sum circuits.  PV is the power that the two inverters feed into the panel.  A channel that is empty for a whole year drops out of that year's sum, as the dehumidifier's does in 2013–14, and a minute has an error reading when another channel is empty or reads below -100 W.  A minute is missing when a file has no row for it, when it has an error reading, when its summed load or PV is negative, or when two rows of one file fall in it, because NIST's timestamps drift within the minute.  Every minute of a day with more than 60 minutes of error readings is missing too.

| Test year | Valid minutes | Days with more than 60 minutes of error readings | Minutes with two rows of one file | Load (kWh) | PV (kWh) | Largest minute of load and of PV (W) |
|---|---|---|---|---|---|---|
| 2013–14 | 507,695 | 7 | 34 | 12,500 | 13,224 | 22,929 and 10,039 |
| 2015–16 | 493,373 | 18 | 21 | 11,292 | 12,845 | 16,066 and 10,017 |

Scaled to the whole year, the 2013–14 load lies 0.8% below NIST's published consumption of 13,039 kWh and the PV 1.2% above its published generation of 13,523 kWh.  NIST publishes no consumption for 2015–16, only a net export of 2,240 kWh, against which the sums imply about 1,650 kWh, and the study does not explain the difference.  The 2015–16 data also lack about three days from October 20, 2015, which NIST attributes to a problem of data acquisition and control.

## The simulated site

The site keeps the battery of the plan's worked example.  Its import cap is that of a 100 A, 240 V service, 24 kW, above the house's largest minute load of 22.9 kW.  With the battery idle, surplus PV exceeds the export cap of 5 kW in 50,326 minutes of 2013–14 and 47,828 of 2015–16, and the PV inverter curtails export at the cap.  A second set of runs uses caps of `2^20` W, which never bind, to separate the energy tests from the grid tests.

| Quantity | Value |
|---|---|
| Battery | 10 kWh between the BMS cutoffs, 5,000 W charge and discharge |
| Floor and ceiling | 3 kWh and 9.5 kWh |
| Import and export caps | 24,000 W and 5,000 W, or `2^20` W |
| Profile bounds | `η = 900,000` ppm, `ℓ⁺ = 20` W, `e = 50` W, `F = [-50, 50]` W, `τ = 30` s, `a = 60` s |
| Simulated battery | Charge and discharge efficiencies 0.95, loss 10 W |
| Energy estimate | The simulated energy ± 360,000 J |

The gateway takes a snapshot every minute and follows the plan's rules.  It sends the proposal when the authorizer accepts it and nothing otherwise, so the command in force runs on, and it returns the device to fallback when a minute's load or PV leaves the intervals of the command in force or when data are missing.  The device follows a command from the start of its snapshot's minute to the first minute boundary at or after its expiry, and runs in the idle fallback otherwise.  A command of held setpoints holds its power, and a command of limits for the vendor's mode follows each minute's net load within them.  The data resolve nothing shorter than a minute, so the replay shows nothing about the send deadline `a` or the transition time `τ`.

## Interval rules

The true-range rule takes the minimum and maximum of the minute values in the window.  It uses future data, so it bounds acceptance from above and serves only Stage 2.  The causal rule takes the extremes of the previous 15 minutes and widens each by a percentile, 99.9% unless a row states otherwise, of the excursions that the calibration year shows for the same window length, month, and hour.  The excursions of each month are pooled with those of its two neighbors, so that the hours of sunrise and sunset fall in like bins.  Lower bounds stop at 0.

| W (s) | Largest widening of the load's upper bound (W) | Largest widening of PV's upper bound (W) |
|---|---|---|
| 180 | 11,215 | 6,561 |
| 300 | 12,239 | 6,953 |
| 600 | 20,624 | 7,395 |
| 900 | 21,071 | 7,610 |

The load's widening is largest from October to April and PV's from April to September.  Both rules work from minute averages, while assumption A4 concerns instantaneous power, so both overstate acceptance and coverage by the excursions within a minute, which a later section estimates.

## Stage 2: margins

The sweep runs on the calibration year, with the causal rule calibrated on the same year, so that the choice of `W` uses no withheld data.  The proposer is the self-consumption rule: the previous minute's surplus PV or deficit, within the largest charge and discharge and the power that keeps the energy estimate between the floor and the ceiling.  The vendor's self-consumption mode, which follows each minute's own values, discharges 2,053 kWh in the year, and the one-minute proposer discharges 2,052 kWh when every proposal is sent without the authorizer.

| Rule | Caps | W (s) | Discharged (kWh) | Run-on discharge (kWh) | Rejected by the export, floor, import, and ceiling tests (%) | Full 5,000 W charge accepted (%) | No charge beyond `F` accepted (%) | Coverage (%) |
|---|---|---|---|---|---|---|---|---|
| True range | Study | 180 | 1,963 | 56 | 0.4, 38.7, 0.0, 18.4 | 78.5 | 1.2 | 100 |
| True range | Study | 300 | 1,954 | 100 | 0.5, 39.7, 0.0, 18.7 | 77.4 | 1.7 | 100 |
| True range | Study | 600 | 1,936 | 192 | 0.9, 41.4, 0.0, 19.3 | 74.7 | 2.7 | 100 |
| True range | Study | 900 | 1,904 | 265 | 1.2, 42.5, 0.0, 19.9 | 72.5 | 3.6 | 100 |
| Causal | Study | 180 | 1,829 | 67 | 4.0, 35.7, 0.3, 19.3 | 72.5 | 1.6 | 99.4 |
| Causal | Study | 300 | 1,827 | 112 | 4.8, 36.2, 0.3, 19.6 | 71.2 | 2.3 | 99.2 |
| Causal | Study | 600 | 1,821 | 190 | 6.5, 36.8, 0.9, 19.6 | 67.6 | 4.0 | 98.7 |
| Causal | Study | 900 | 1,815 | 262 | 7.5, 37.3, 1.0, 20.0 | 64.6 | 5.6 | 98.2 |
| Causal, 99th percentile | Study | 300 | 1,845 | 83 | 2.2, 37.5, 0.0, 19.4 | 72.1 | 1.7 | 96.7 |
| True range | Open | 180 | 2,001 | 45 | 0.0, 38.7, 0.0, 18.3 | 78.8 | 1.1 | 100 |
| Causal | Open | 180 | 1,996 | 44 | 0.0, 38.0, 0.0, 18.4 | 78.6 | 1.2 | 99.4 |
| True range | Open | 900 | 2,020 | 266 | 0.0, 42.9, 0.0, 19.7 | 72.9 | 3.7 | 100 |
| Causal | Open | 900 | 2,016 | 265 | 0.0, 42.6, 0.0, 19.7 | 72.9 | 3.7 | 98.2 |

The columns count over all snapshots of the year.  Discharged is the battery's discharged energy, and run-on discharge the part of it that a command discharged after a later proposal was rejected or absent.  The rejection shares are the snapshots at which the proposal failed each test.  The two charge columns come from a search at every snapshot for the largest accepted charge: the share at which a full 5,000 W charge passes, and the share at which no charge beyond the fallback interval passes, including snapshots at which nothing passes.  Coverage is the share of snapshots whose window's minute values lie in the intervals.  The largest accepted charge and discharge depend on the state in force, which with a snapshot every minute is the last command, so a discharge in force subjects every charge to the floor and export tests.

The floor and ceiling tests reject the most proposals, because the proposer offers small discharges near the floor and charges near the ceiling, where the vendor's mode would stop at the limit and the authorizer needs room for the whole window.  With the causal rule and the study's caps, a full discharge passes at 0.0% to 0.3% of snapshots and no discharge beyond `F` at 63.9% to 70.1%, against 12.2% to 17.6% and 51.3% to 56.9% with the true range.  The authorizer with the causal rule delivers 89% of the ungated proposer's discharge at 180 s with the study's caps, and 97% with caps that never bind.  The export test accounts for most of the difference: it rejects 4.0% to 7.5% of snapshots, because the causal rule widens PV's upper bound by up to 7.6 kW and a discharge fails while PV could exceed the export cap.  The import test rejects at most 1.0% of snapshots at 24 kW.

Run-on discharge grows with the window, and with caps that never bind the 900 s window discharges more than the 180 s window only through run-on.  The 99th percentile delivers 1,845 kWh against 1,827 kWh for the 99.9th at 300 s, with coverage of 96.7% instead of 99.2%.  Of the windows at 300 s that a premise failure ended, `WithinOrFallback` broke in 40 with the 99th percentile and in 3 with the 99.9th, outside the theorem's premises.  The tolerance and the efficiency bound change little at 300 s with the causal rule: the discharged energy is 1,828, 1,827, 1,825, and 1,819 kWh for `e` of 25, 50, 100, and 200 W, with `F` widened to `[-e, e]` where `e` exceeds 50 W, and 1,827 and 1,828 kWh for `η` of 850,000 and 950,000 ppm.

Fallback's worst case breaks the floor at 29.7% to 44.2% of snapshots, because the battery often rests at the floor, where the idle loss drains it below the floor, so the theorem's floor bound is relative to fallback at those snapshots.  With the study's caps, it breaks the ceiling at fewer than 0.05% of snapshots, the export cap at 11.9% to 16.2% with the true range and 29.3% to 35.1% with the causal rule, and the import cap at fewer than 0.05% with the true range and 0.6% to 2.4% with the causal rule.  The causal rule's coverage by month is lowest in July and August, at 97.1% and 97.0% for 900 s, and at least 99.0% in every month for 180 s.

In every run, the simulated energy and grid power met `WithinOrFallback` at every minute of every accepted window up to its first premise failure: 0.54 to 1.67 million window-minutes per run without a violation.  The replay at the premises' extremes runs the device at `s - e` with efficiency `η`, loss `ℓ⁺`, and the energy at the lower end of its interval, or at `s + e` with efficiency 1, no loss, and the energy at the upper end, under the true-range rule and a proposer that alternates the largest accepted discharge and charge every hour.  It checked 1.24 to 4.99 million window-minutes for 180 and 900 s without a violation.

## The window length

The study chooses, among the window lengths that the gateway's timing allows, the longest whose controller bill and wear on the calibration year lie within 1% of the lowest, because a longer window keeps a command in force through a longer loss of communication.  The controller's bills and wear on the calibration year, with the study's caps and the causal rule, are $1,921, $1,924, $1,936, and $1,948 for 180, 300, 600, and 900 s.  The study chooses `W = 600` s, which lies 0.8% above the lowest, while 900 s lies 1.4% above it.  The choice is provisional: the equipment's expiry granularity, which Stage 4 measures, can force another length, and the excursions within a minute, which Stage 5 measures at the site, can change the margins of every length.

## Stage 3: bills

The test house has no tariff that values a battery, so the study assumes one.  Import follows [PG&E's Electric Home Rate Plan (E-ELEC)](https://www.pge.com/assets/pge/docs/account/rate-plans/residential-electric-rate-plan-pricing.pdf), effective March 1, 2026, for an all-electric home: from June to September 33¢ per kWh off-peak, 39¢ at partial peak (3 to 4 p.m. and 9 p.m. to midnight), and 55¢ at peak (4 to 9 p.m.), and in the other months 28¢, 30¢, and 32¢.  Export earns a flat 5¢ per kWh, and the fixed base services charge, the same for every policy, is omitted.  The study applies this California tariff to the Maryland house on its local clock.  Battery wear costs 5¢ per kWh discharged, the assumption of a $400 per kWh replacement over 8,000 full cycles, and the capacity stays constant over the year.

| Policy | Description |
|---|---|
| No battery | The house alone, with export curtailed at the cap |
| Self-consumption mode | The vendor's mode: each minute it charges the minute's surplus PV and covers the minute's deficit, between the floor and the ceiling |
| Time-of-use schedule | As the self-consumption mode, but it covers the deficit only during partial peak and peak, down to a fixed reserve equal to the floor |
| Self-consumption rule, one-minute commands | The self-consumption rule as a held setpoint each minute from the previous minute's values, every proposal sent |
| Controller | The self-consumption rule with curtailment-aware charging, as a held setpoint each minute, every proposal sent or through the authorizer with the causal rule |
| Self-consumption mode within authorized limits | The vendor's mode, limited each minute to the widest limits that the authorizer accepts, which are its largest accepted discharge and charge |

The controller charges as the self-consumption rule does, except before 3 p.m. when the previous day's surplus, from the same time to 3 p.m., peaked above the export cap less 1,000 W and stored half again the room left below the ceiling.  It then charges only the surplus above the cap less 1,000 W, so that the battery takes PV that the cap would curtail.  [SAM's battery dispatch](https://samrepo.nlr.gov/help/battery_dispatch_btm.html) offers the same one-day look-behind forecast.  The controller limits each proposal to the range that its own copy of the acceptance rule accepts.

The table gives each policy's bill and wear on the withheld year under both sets of caps, and its energy flows under the study's caps.

| Policy | Study caps ($) | Caps that never bind ($) | Import (kWh) | Export (kWh) | Curtailed (kWh) | Discharged (kWh) |
|---|---|---|---|---|---|---|
| No battery | 2,008 | 1,949 | 7,294 | 7,682 | 1,165 | 0 |
| Self-consumption mode | 1,459 | 1,406 | 5,355 | 5,550 | 1,059 | 1,939 |
| Time-of-use schedule | 1,481 | 1,428 | 5,477 | 5,670 | 1,076 | 1,817 |
| Self-consumption rule, one-minute commands | 1,537 | 1,485 | 5,625 | 5,820 | 1,059 | 1,939 |
| Controller, every proposal sent | 1,524 | 1,485 | 5,679 | 6,395 | 552 | 1,816 |
| Controller through the authorizer, 180 s | 1,545 | 1,499 | 5,769 | 6,478 | 572 | 1,690 |
| Controller through the authorizer, 300 s | 1,549 | 1,503 | 5,779 | 6,488 | 572 | 1,687 |
| Controller through the authorizer, 600 s | 1,560 | 1,512 | 5,812 | 6,518 | 576 | 1,680 |
| Controller through the authorizer, 900 s | 1,572 | 1,526 | 5,849 | 6,551 | 580 | 1,676 |
| Self-consumption mode within authorized limits, 180 s | 1,501 | 1,421 | 5,528 | 5,727 | 1,074 | 1,766 |
| Self-consumption mode within authorized limits, 300 s | 1,503 | 1,421 | 5,532 | 5,733 | 1,073 | 1,762 |
| Self-consumption mode within authorized limits, 600 s | 1,505 | 1,422 | 5,542 | 5,748 | 1,069 | 1,752 |
| Self-consumption mode within authorized limits, 900 s | 1,506 | 1,423 | 5,548 | 5,758 | 1,066 | 1,746 |

With the study's caps, the vendor's mode saves $549 against no battery and the controller through the authorizer at 600 s, the chosen window, saves $448.  The difference has three parts.  Held setpoints for a minute cost $78, because the proposer holds the previous minute's net load through the next minute, and the minute data omit the changes within a minute, which an installed vendor's mode also follows.  With caps that never bind, a proposer that estimates the net load at the snapshot by the mean of the previous and the present minute cuts this cost from $79 to $40.  The curtailment rule saves $13, and the authorizer costs $36 at 600 s, $21 to $48 from 180 to 900 s, against $14 to $41 with caps that never bind.

Through the authorizer at 600 s, 46% of the controller's unlimited proposals pass, and the others fail the floor test (38% of snapshots), the ceiling test (12%), the export test (4%), and the import test (0.4%), mostly because a proposal near the floor or the ceiling fails the window's energy test.  The authorizer accepts the controller's limited proposal at 92% of snapshots.  The battery's lowest energy is 1.5 to 1.7 kWh below the floor through its standby loss, and the vendor's modes reach 1.6 kWh below the floor in the same year by the same loss.  The replay checked `WithinOrFallback` over 1.25 to 5.33 million window-minutes for each window length without a violation.

A 10 kW import cap lies below the house's peak load of 22.9 kW and below the causal rule's winter load bounds.  At that cap the import test rejects 15.9% to 22.3% of the controller's unlimited proposals, against at most 0.5% at 24 kW, and in every policy through the authorizer the battery reaches its lower cutoff, which from the floor takes 12.5 days of standby loss without a charge.  The controller through the authorizer then costs $1,657, $1,684, $1,756, and $1,787 at 180, 300, 600, and 900 s, and the vendor's mode within authorized limits $1,628, $1,650, $1,701, and $1,723.

The vendor's mode within the widest accepted limits costs $1,421 to $1,423 with caps that never bind, $15 to $17 more than the mode alone, against $93 more for the controller's held setpoints at 180 s.  Most of that difference comes from the proposer, which holds the previous minute's net load while the vendor's mode within the limits follows the present minute: through the authorizer at 180 s, held setpoints proposed from the mean of the previous and the present minute cost $1,462.  The minute data therefore cannot measure what limits gain, which lies in the changes of load within each minute.  With the study's caps the limits cost $1,501 to $1,506, $42 to $47 more than the vendor's mode alone, mostly through the export test, and the replay checked their windows over 1.20 to 5.46 million window-minutes without a violation.

## Excursions within a minute

One house of the [PTProsumer](https://osf.io/9xs3a/) dataset estimates how much the minute averages hide: house PR_02 in Madeira, with a three-phase supply of 10.35 kVA and a 2.7 kW array, for 2019, from meters of net load and PV sampled every second.  Load is net load plus PV, and the timestamps are UTC.  For each window of whole minutes, each with at least 50 samples, the table compares the extremes of the one-second values with the extremes of the minute averages, as percentiles over the windows.

| W (s) | Load above the minutes' maximum: p50, p90, p99, p99.9 (W) | Load below the minutes' minimum | PV above | PV below |
|---|---|---|---|---|
| 60 | 7, 190, 1,427, 2,392 | 7, 171, 1,136, 1,873 | 1, 37, 595, 1,107 | 1, 38, 564, 1,007 |
| 180 | 9, 385, 1,458, 2,586 | 7, 166, 1,083, 1,846 | 1, 43, 608, 1,118 | 1, 36, 541, 962 |
| 300 | 12, 586, 1,482, 2,698 | 7, 162, 1,045, 1,860 | 1, 48, 616, 1,124 | 1, 35, 530, 945 |
| 600 | 17, 757, 1,545, 2,848 | 8, 169, 978, 1,919 | 2, 61, 624, 1,114 | 1, 34, 521, 938 |
| 900 | 28, 810, 1,576, 2,937 | 8, 175, 862, 1,878 | 2, 71, 622, 1,092 | 0, 33, 518, 945 |

In 1% of 180 s windows the one-second load rises more than 1.4 kW above the highest minute average, and PV moves more than 0.5 kW beyond its minute extremes, a fifth of this array's rating.  The test house has larger loads and a larger array, so its excursions within a minute are likely larger, and the true-range rule's acceptance and the causal rule's coverage overstate what one-second data would give.  The two meters sample separately, so part of the load's excursion may come from the difference of their sampling instants while PV changes.

## What the study shows about the design

At a 24 kW import cap and a 5 kW export cap, the authorizer's tests cost the controller $21 to $48 on the withheld year, against $14 to $41 with caps that never bind.  On that year the causal rule's intervals cover 98.2% to 99.7% of each month's windows, against 97.0% in the calibration year's worst month.  A command that holds one power cannot follow the load within the window.  In the replay it costs $40 to $79 a year against the vendor's mode at this house, depending on how the gateway estimates the net load at the snapshot, and more once the changes within a minute count, which the vendor's mode within authorized limits follows.  An instantaneous import cap of 10 kW lets the causal rule's worst-case load block charging until the battery reaches its cutoff, while a cap at the house's service rating rejects at most 1% of snapshots.  The export cap binds whenever the causal rule's PV bound exceeds it, which rejects discharges at midday.

## Limits

The data are minute averages of one test house with scripted occupants in one climate.  The load is a sum of circuit channels whose 2015–16 sums imply a net export of about 1,650 kWh against NIST's 2,240 kWh, and the excursions within a minute come from a different house.  The tariff, the export credit, the wear cost, and the caps are stated assumptions, and the battery's capacity does not fade.  The savings are simulated and do not estimate the savings of an installed system.

## Commands

```sh
lake exe verified-cases-energy > cases.txt
uv run tests/energy/replay.py check cases.txt
uv run tests/energy/replay.py prepare NIST_2014_DIRECTORY nist-2014.csv
uv run tests/energy/replay.py prepare NIST_2015_DIRECTORY nist-2015.csv
uv run tests/energy/replay.py calibration nist-2014.csv --window 180
uv run tests/energy/replay.py margins nist-2014.csv nist-2014.csv
uv run tests/energy/replay.py economics nist-2014.csv nist-2014.csv \
  --window 180 --window 300 --window 600 --window 900
uv run tests/energy/replay.py economics nist-2014.csv nist-2015.csv \
  --window 180 --window 300 --window 600 --window 900
uv run tests/energy/replay.py economics nist-2014.csv nist-2015.csv \
  --window 180 --window 300 --window 600 --window 900 --open-caps
uv run tests/energy/replay.py economics nist-2014.csv nist-2015.csv \
  --window 180 --window 300 --window 600 --window 900 --import-cap 10000
uv run tests/energy/replay.py economics nist-2014.csv nist-2015.csv \
  --window 180 --open-caps --estimate mean
uv run tests/energy/replay.py within pr02_nl_2019.csv.gz pr02_prod_2019.csv.gz
```

A NIST year directory holds that year's `Elec`, `HVAC`, `DHW`, and `Load` minute files from NIST's data page, and `prepare` writes one series of minute load and PV per year.  `calibration` prints the causal rule's widening by month, `margins` the Stage 2 tables, and `economics` the bills of each policy, with notes that give each window's coverage by month, the statuses of the controller's unlimited proposals, and the window checks.  The `within` command reads house PR_02's compressed net-load and PV files for 2019 from the PTProsumer dataset.

## References

- [Energy: authorization of battery power limits](README.md)
- [Verified Energy Controller: Plan and Design](../../energy-controller-plan.md)
- [NIST Net-Zero Energy Residential Test Facility data](https://pages.nist.gov/netzero/data.html)
- [Healy et al., Performance Data from the NIST Net-Zero Energy Residential Test Facility, Journal of Research of NIST 122:14 (2017)](https://doi.org/10.6028/jres.122.014)
- [PTProsumer dataset](https://osf.io/9xs3a/)
- [PTProsumer data descriptor](https://pmc.ncbi.nlm.nih.gov/articles/PMC12675649/)
- [PG&E residential rate plan pricing](https://www.pge.com/assets/pge/docs/account/rate-plans/residential-electric-rate-plan-pricing.pdf)
- [NREL System Advisor Model: behind-the-meter battery dispatch](https://samrepo.nlr.gov/help/battery_dispatch_btm.html)
