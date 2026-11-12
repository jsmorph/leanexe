import Demos.Energy.Loop
import LeanExe.Native.ClightN.Instance
import LeanExe.Native.ClightN.Read
import ClightNGateway.GatewaySpec

/-!
The statement `gateway_reacts` of the instance that `clightn/check.sh` writes for the energy
controller's program, the gateway of `Demos/Energy/Loop.lean` with requests over UART0 of
`mps2-an500`, from the state `gwInit`: there are functions `W` and `P` of the sequence `σ` of the
values of the volatile loads such that, for every `σ`, N's judgment `nreacts` holds of the
definitions and `main` of `clightgen`'s file with no event before the loop and the trace `W σ n`
in iteration `n`, `P σ n` is the trace of the first `n` iterations, and its `k`-th volatile load
reads `σ k`.  `reacts_n` carries the copy's `Demos.Energy.gw_program` and the reads that
`req_reads` states to the statement.
-/

namespace ClightN.Proof

open LClight LeanExe.Native ClightN.Spec

set_option maxHeartbeats 4000000 in
theorem gateway_reacts : stmt_gateway_reacts :=
  reacts_n (by inst_ok) (Demos.Energy.gw_program _ _) fun σ n => req_reads _ _ σ n

end ClightN.Proof

run_cmd ClightN.Read.dump
