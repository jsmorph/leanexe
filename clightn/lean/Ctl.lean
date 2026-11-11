import TestSupport.Bare.Ctl
import LeanExe.Native.ClightN.Instance
import LeanExe.Native.ClightN.Read
import ClightNCtl.CtlSpec

/-!
The statement `ctl_reacts` of the instance that `clightn/check.sh` writes for the controller
program around the step `ctlStep` of `tests/TestSupport/Bare/Ctl.lean`, from the state 0: there
are functions `W` and `P` of the sequence `σ` of the values of the volatile loads such that, for
every `σ`, N's judgment `nreacts` holds of the definitions and `main` of `clightgen`'s file with
no event before the loop and the trace `W σ n` in iteration `n`, `P σ n` is the trace of the
first `n` iterations, and its `k`-th volatile load reads `σ k`.  `reacts_n` carries the copy's
`TestSupport.Bare.filter_program` and the reads that `ctl_reads` states to the statement.
-/

namespace ClightN.Proof

open LClight LeanExe.Native ClightN.Spec

set_option maxHeartbeats 4000000 in
theorem ctl_reacts : stmt_ctl_reacts :=
  reacts_n (by inst_ok) (TestSupport.Bare.filter_program _ _) fun σ n => ctl_reads _ _ σ n

end ClightN.Proof

run_cmd ClightN.Read.dump
