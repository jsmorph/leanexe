import Project.Gpt2QuantizedCached.Program
import LeanExe.Models.Gpt2.Quantized.Cached
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2QuantizedCached.Layout
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2.Quantized

theorem headerBytes_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 0 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.headerBytes)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func0Def) rfl ?_
  change wp «module» func0 _ initial { locals := List.replicate 1 (.i64 0) } env
  unfold func0
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem tokenWeightOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 1 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.tokenWeightOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_
  change wp «module» func1 _ initial { locals := List.replicate 2 (.i64 0) } env
  unfold func1
  wp_packed_frame
  refine wp_call_tw (headerBytes_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem tokenScaleOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 2 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.tokenScaleOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def) rfl ?_
  change wp «module» func2 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func2
  wp_packed_frame
  refine wp_call_tw (tokenWeightOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem positionOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 3 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.positionOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func3Def) rfl ?_
  change wp «module» func3 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func3
  wp_packed_frame
  refine wp_call_tw (tokenScaleOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem blocksOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 4 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.blocksOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func4Def) rfl ?_
  change wp «module» func4 _ initial { locals := List.replicate 8 (.i64 0) } env
  unfold func4
  wp_packed_frame
  refine wp_call_tw (positionOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem qkvWeightOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 5 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.qkvWeightOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func5Def) rfl ?_
  change wp «module» func5 _ initial { locals := List.replicate 3 (.i64 0) } env
  unfold func5
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem qkvScaleOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 6 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.qkvScaleOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func6Def) rfl ?_
  change wp «module» func6 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func6
  wp_packed_frame
  refine wp_call_tw (qkvWeightOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem qkvBiasOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 7 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.qkvBiasOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func7Def) rfl ?_
  change wp «module» func7 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func7
  wp_packed_frame
  refine wp_call_tw (qkvScaleOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem attnWeightOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 8 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.attnWeightOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func8Def) rfl ?_
  change wp «module» func8 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func8
  wp_packed_frame
  refine wp_call_tw (qkvBiasOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem attnScaleOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 9 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.attnScaleOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func9Def) rfl ?_
  change wp «module» func9 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func9
  wp_packed_frame
  refine wp_call_tw (attnWeightOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem attnBiasOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 10 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.attnBiasOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func10Def) rfl ?_
  change wp «module» func10 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func10
  wp_packed_frame
  refine wp_call_tw (attnScaleOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem ln2ScaleOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 11 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.ln2ScaleOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func11Def) rfl ?_
  change wp «module» func11 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func11
  wp_packed_frame
  refine wp_call_tw (attnBiasOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem ln2BiasOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 12 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.ln2BiasOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func12Def) rfl ?_
  change wp «module» func12 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func12
  wp_packed_frame
  refine wp_call_tw (ln2ScaleOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem fcWeightOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 13 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.fcWeightOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func13Def) rfl ?_
  change wp «module» func13 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func13
  wp_packed_frame
  refine wp_call_tw (ln2BiasOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem fcScaleOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 14 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.fcScaleOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func14Def) rfl ?_
  change wp «module» func14 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func14
  wp_packed_frame
  refine wp_call_tw (fcWeightOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem fcBiasOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 15 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.fcBiasOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func15Def) rfl ?_
  change wp «module» func15 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func15
  wp_packed_frame
  refine wp_call_tw (fcScaleOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem mlpWeightOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 16 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.mlpWeightOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func16Def) rfl ?_
  change wp «module» func16 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func16
  wp_packed_frame
  refine wp_call_tw (fcBiasOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem mlpScaleOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 17 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.mlpScaleOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func17Def) rfl ?_
  change wp «module» func17 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func17
  wp_packed_frame
  refine wp_call_tw (mlpWeightOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem mlpBiasOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 18 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.mlpBiasOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func18Def) rfl ?_
  change wp «module» func18 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func18
  wp_packed_frame
  refine wp_call_tw (mlpScaleOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem blockBytes_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 19 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.blockBytes)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func19Def) rfl ?_
  change wp «module» func19 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func19
  wp_packed_frame
  refine wp_call_tw (mlpBiasOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem finalNormOffset_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 20 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.finalNormOffset)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func20Def) rfl ?_
  change wp «module» func20 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func20
  wp_packed_frame
  refine wp_call_tw (blocksOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame
  refine wp_call_tw (blockBytes_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem modelBytes_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 21 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.Quantized.modelBytes)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func21Def) rfl ?_
  change wp «module» func21 _ initial { locals := List.replicate 6 (.i64 0) } env
  unfold func21
  wp_packed_frame
  refine wp_call_tw (finalNormOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

theorem cachePositionWords_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 29 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat LeanExe.Models.Gpt2.cachePositionWords)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func29Def) rfl ?_
  change wp «module» func29 _ initial { locals := List.replicate 3 (.i64 0) } env
  unfold func29
  repeat' first
    | wp_packed_frame
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  exact ⟨trivial, rfl⟩

#print axioms headerBytes_exact
#print axioms tokenWeightOffset_exact
#print axioms tokenScaleOffset_exact
#print axioms positionOffset_exact
#print axioms blocksOffset_exact
#print axioms qkvWeightOffset_exact
#print axioms qkvScaleOffset_exact
#print axioms qkvBiasOffset_exact
#print axioms attnWeightOffset_exact
#print axioms attnScaleOffset_exact
#print axioms attnBiasOffset_exact
#print axioms ln2ScaleOffset_exact
#print axioms ln2BiasOffset_exact
#print axioms fcWeightOffset_exact
#print axioms fcScaleOffset_exact
#print axioms fcBiasOffset_exact
#print axioms mlpWeightOffset_exact
#print axioms mlpScaleOffset_exact
#print axioms mlpBiasOffset_exact
#print axioms blockBytes_exact
#print axioms finalNormOffset_exact
#print axioms modelBytes_exact
#print axioms cachePositionWords_exact

end Project.Gpt2QuantizedCached.Layout
