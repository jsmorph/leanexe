import Project.Gpt2CachedStep.Program
import LeanExe.Models.Gpt2.Cached
import Project.ProofKit.ConstantFunction
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2CachedStep.Layout
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2

theorem vocabulary_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 0 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat vocabulary)]) :=
  ConstantFunction.exact _ env initial 0 50257 (some 0) rfl rfl

theorem positionOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 1 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat positionOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_
  change wp «module» func1 _ initial { locals := List.replicate 3 (.i64 0) } env
  unfold func1
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  exact ⟨trivial, rfl⟩

theorem blocksOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 2 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat blocksOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def) rfl ?_
  change wp «module» func2 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func2
  refine wp_call_tw (positionOffset_exact env initial) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  exact ⟨trivial, rfl⟩

theorem qkvWeightOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 3 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat qkvWeightOffset)]) :=
  ConstantFunction.exact _ env initial 3 1536 (some 3) rfl rfl

theorem qkvBiasOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 4 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat qkvBiasOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func4Def) rfl ?_
  change wp «module» func4 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func4
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  exact ⟨trivial, rfl⟩

theorem attnWeightOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 5 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat attnWeightOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func5Def) rfl ?_
  change wp «module» func5 _ initial { locals := List.replicate 4 (.i64 0) } env
  unfold func5
  refine wp_call_tw (qkvBiasOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  exact ⟨trivial, rfl⟩

theorem attnBiasOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 6 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat attnBiasOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func6Def) rfl ?_
  change wp «module» func6 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func6
  refine wp_call_tw (attnWeightOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  exact ⟨trivial, rfl⟩

theorem ln2ScaleOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 7 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat ln2ScaleOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func7Def) rfl ?_
  change wp «module» func7 _ initial { locals := List.replicate 4 (.i64 0) } env
  unfold func7
  refine wp_call_tw (attnBiasOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  exact ⟨trivial, rfl⟩

theorem ln2BiasOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 8 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat ln2BiasOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func8Def) rfl ?_
  change wp «module» func8 _ initial { locals := List.replicate 4 (.i64 0) } env
  unfold func8
  refine wp_call_tw (ln2ScaleOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  exact ⟨trivial, rfl⟩

theorem fcWeightOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 9 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat fcWeightOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func9Def) rfl ?_
  change wp «module» func9 _ initial { locals := List.replicate 4 (.i64 0) } env
  unfold func9
  refine wp_call_tw (ln2BiasOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  exact ⟨trivial, rfl⟩

theorem fcBiasOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 10 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat fcBiasOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func10Def) rfl ?_
  change wp «module» func10 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func10
  refine wp_call_tw (fcWeightOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  exact ⟨trivial, rfl⟩

theorem mlpWeightOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 11 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat mlpWeightOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func11Def) rfl ?_
  change wp «module» func11 _ initial { locals := List.replicate 4 (.i64 0) } env
  unfold func11
  refine wp_call_tw (fcBiasOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  exact ⟨trivial, rfl⟩

theorem mlpBiasOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 12 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat mlpBiasOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func12Def) rfl ?_
  change wp «module» func12 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func12
  refine wp_call_tw (mlpWeightOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  exact ⟨trivial, rfl⟩

theorem blockWords_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 13 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat blockWords)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func13Def) rfl ?_
  change wp «module» func13 _ initial { locals := List.replicate 4 (.i64 0) } env
  unfold func13
  refine wp_call_tw (mlpBiasOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  exact ⟨trivial, rfl⟩

theorem finalNormOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 14 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat finalNormOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func14Def) rfl ?_
  change wp «module» func14 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func14
  refine wp_call_tw (blocksOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame
  refine wp_call_tw (blockWords_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  exact ⟨trivial, rfl⟩

theorem parameterWords_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 15 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat parameterWords)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func15Def) rfl ?_
  change wp «module» func15 _ initial { locals := List.replicate 4 (.i64 0) } env
  unfold func15
  refine wp_call_tw (finalNormOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  exact ⟨trivial, rfl⟩

theorem cachePositionWords_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 16 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat cachePositionWords)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func16Def) rfl ?_
  change wp «module» func16 _ initial { locals := List.replicate 3 (.i64 0) } env
  unfold func16
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame
  exact ⟨trivial, rfl⟩

#print axioms vocabulary_exact
#print axioms positionOffset_exact
#print axioms blocksOffset_exact
#print axioms qkvWeightOffset_exact
#print axioms qkvBiasOffset_exact
#print axioms attnWeightOffset_exact
#print axioms attnBiasOffset_exact
#print axioms ln2ScaleOffset_exact
#print axioms ln2BiasOffset_exact
#print axioms fcWeightOffset_exact
#print axioms fcBiasOffset_exact
#print axioms mlpWeightOffset_exact
#print axioms mlpBiasOffset_exact
#print axioms blockWords_exact
#print axioms finalNormOffset_exact
#print axioms parameterWords_exact
#print axioms cachePositionWords_exact

end Project.Gpt2CachedStep.Layout
