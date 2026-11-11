import Library.Random.Sampling.Compiled
import Verified.Master

namespace Library.Random.Sampling

open LeanExe.Pipeline

/-- The export `shuffle`, called on an array of words `us` and an array of words `xs` that the
caller moves, returns the array of Algorithm P of TAOCP §3.4.2 on `xs`, which reads the words of
`us` as fractions of `2^64`. -/
theorem shuffle_master :
    Verified.Master compiled.module compiled.tables "shuffle" compiled.shuffle.bound
      (fun _ => True)
      (fun (x : Array UInt64 × Moved (Array UInt64)) ys =>
        ys = algorithmP x.1 x.2.val.size (x.2.val.size - 1) x.2.val) :=
  .of_trapFree (.ofA compiled.shuffle.trapFree) nofun shuffle_export (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h) fun _ _ _ x ⟨_, _, _, _, ⟨_, _, hxs⟩⟩ _ =>
      shuffle_method x.1 x.2.val (hxs.values.size_lt_memory32.trans (by norm_num))

#print axioms shuffle_master

/-- The export `sample`, called on arrays of words `us` and `xs` and a count `n`, returns the
`min n N` words of `xs` that Algorithm S of TAOCP §3.4.2 chooses, in order, which reads the words
of `us` as fractions of `2^64`. -/
theorem sample_master :
    Verified.Master compiled.module compiled.tables "sample" compiled.sample.bound
      (fun _ => True)
      (fun (x : Array UInt64 × Array UInt64 × UInt64) ys =>
        ys = algorithmS x.1 x.2.1 x.2.2.toNat) :=
  .of_trapFree (.ofA compiled.sample.trapFree) nofun sample_export (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h) fun _ _ _ x ⟨_, _, _, _, ⟨_, _, _, ⟨_, _, hxs⟩, _⟩⟩ _ =>
      sample_eq x.1 x.2.1 x.2.2 (hxs.values.size_lt_memory32.trans (by norm_num))

#print axioms sample_master

/-- The export `reservoir`, called on arrays of words `us` and `xs` and a count `n`, returns the
`min n N` candidates of Algorithm R of TAOCP §3.4.2 on `xs`, which reads the words of `us` as
fractions of `2^64`. -/
theorem reservoir_master :
    Verified.Master compiled.module compiled.tables "reservoir" compiled.reservoir.bound
      (fun _ => True)
      (fun (x : Array UInt64 × Array UInt64 × UInt64) ys =>
        ys = algorithmR x.1 x.2.1 x.2.2.toNat) :=
  .of_trapFree (.ofA compiled.reservoir.trapFree) nofun reservoir_export (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h) fun _ _ _ x ⟨_, _, _, _, ⟨_, _, _, ⟨_, _, hxs⟩, _⟩⟩ _ =>
      reservoir_eq x.1 x.2.1 x.2.2 (hxs.values.size_lt_memory32.trans (by norm_num))

#print axioms reservoir_master

end Library.Random.Sampling
