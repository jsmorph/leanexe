import TestSupport.Bare.Input
import LeanExe.Native.ClightN.Instance
import LeanExe.Native.ClightN.Read
import ClightNSha.ShaSpec

/-!
The statement `sha_reads` of the instance that `clightn/check.sh` writes for the program with
input around the export `sha256` of `Library.Hashing.Sha256.compiled`: for every sequence `σ` of
the values of its volatile loads, N's program judgment holds of the definitions and `main` of
`clightgen`'s file with a trace whose `k`-th volatile load reads `σ k`.  `reads_n` carries the
terminations and reads of the copy's theorem `TestSupport.Bare.sha256_input` to the statement.
-/

namespace ClightN.Proof

open LClight LeanExe.Native ClightN.Spec

set_option maxHeartbeats 4000000 in
theorem sha_reads : stmt_sha_reads :=
  reads_n (by inst_ok) fun pre hpre σ =>
    let ⟨t, r, hp, hr, _⟩ := TestSupport.Bare.sha256_input Archi.aarch64 ExtSem.none pre hpre σ
    ⟨t, r, hp, hr⟩

end ClightN.Proof

run_cmd ClightN.Read.dump
