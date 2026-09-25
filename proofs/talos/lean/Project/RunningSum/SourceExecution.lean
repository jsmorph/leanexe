import Project.RunningSum.SourceHost

namespace Project.RunningSum.Source

theorem readStep_eof (host : SuccessfulHost rep) (state final : StreamState)
    (hf : finish state = .ok final) (hr : rep [] state.output world) :
    ∃ world', readStep () (none, state.total, state.pending) world =
      ⟨.done (some 0, state.total, state.pending), world'⟩ ∧ rep [] final.output world' := by
  obtain ⟨readWorld, hread, hr'⟩ := host.read [] state.output world hr
  simp only [List.headD_nil, List.tail_nil] at hread hr'
  by_cases hp : state.pending.size = 0
  · have he : state = final := by simpa [finish, hp] using hf
    subst final
    refine ⟨readWorld, ?_, hr'⟩
    simp [readStep, bind_apply, hread, hp, pure_apply]
  · have he : emitLine state = .ok final := by simpa [finish, hp] using hf
    obtain ⟨writeWorld, hwrite, hw, _⟩ := emitSum_runs host state final he hr'
    refine ⟨writeWorld, ?_, hw⟩
    simp [readStep, bind_apply, hread, hp, hwrite, pure_apply]

theorem readStep_chunk (host : SuccessfulHost rep) (state next : StreamState)
    (chunk : ByteArray) (hn : chunk.size ≠ 0)
    (he : consume state chunk.data.toList = .ok next)
    (hr : rep (chunk :: chunks) state.output world) :
    ∃ world', readStep () (none, state.total, state.pending) world =
      ⟨.yield (none, next.total, next.pending), world'⟩ ∧ rep chunks next.output world' := by
  obtain ⟨readWorld, hread, hr'⟩ := host.read (chunk :: chunks) state.output world hr
  simp only [List.headD_cons, List.tail_cons] at hread hr'
  obtain ⟨nextWorld, hbytes, hr''⟩ := bytes_runs host chunk.data.toList state next he hr'
  refine ⟨nextWorld, ?_, hr''⟩
  simp only [readStep, bind_apply, hread, beq_iff_eq, hn, ↓reduceIte,
    chunkLoop_eq, hbytes, pure_apply]

theorem readLoop_runs (host : SuccessfulHost rep) (chunks : List ByteArray)
    (nonempty : ∀ chunk ∈ chunks, chunk.size ≠ 0)
    (state processed final : StreamState)
    (he : consumeChunks state chunks = .ok processed)
    (hf : finish processed = .ok final) (hr : rep chunks state.output world) :
    ∃ result world', readLoop (none, state.total, state.pending) world = ⟨result, world'⟩ ∧
      result.1 = some 0 ∧ rep [] final.output world' := by
  induction chunks generalizing state world with
  | nil =>
    have he' : state = processed := Except.ok.inj he
    subst processed
    obtain ⟨world', hs, hr'⟩ := readStep_eof host state final hf hr
    refine ⟨(some 0, state.total, state.pending), world', ?_, rfl, hr'⟩
    rw [readLoop_eq]
    simp only [bind_apply, hs, pure_apply]
  | cons chunk chunks ih =>
    have hcons : consumeChunks state (chunk :: chunks) =
        (consume state chunk.data.toList >>= fun next => consumeChunks next chunks) := rfl
    rw [hcons] at he
    cases hc : consume state chunk.data.toList with
    | error code => simp [hc, bind, Except.bind] at he
    | ok next =>
      simp only [hc, bind, Except.bind] at he
      obtain ⟨world', hs, hr'⟩ := readStep_chunk host state next chunk
        (nonempty chunk (by simp)) hc hr
      obtain ⟨result, finalWorld, he', hz, hfinal⟩ :=
        ih (fun byte hb => nonempty byte (by simp [hb])) next he hr'
      refine ⟨result, finalWorld, ?_, hz, hfinal⟩
      rw [readLoop_eq]
      simpa only [bind_apply, hs] using he'

theorem main_correct (host : SuccessfulHost rep) (chunks : List ByteArray)
    (bounded : ∀ chunk ∈ chunks, 0 < chunk.size ∧ chunk.size ≤ 4096)
    (inputs : List ByteArray)
    (valid : ValidInput (chunks.flatMap (fun chunk => chunk.data.toList)) inputs)
    (start : rep chunks [] world) :
    ∃ output world', LeanExe.Examples.RunningSum.main world = ⟨0, world'⟩ ∧
      rep [] output world' ∧ List.Forall₂ DecimalOutput (prefixSums 0 inputs) output := by
  obtain ⟨processed, final, he, hf, hout, _⟩ := stream_correct _ inputs valid
  rw [← consumeChunks_eq] at he
  obtain ⟨result, world', hloop, hz, hrep⟩ := readLoop_runs host chunks
    (fun chunk hc => Nat.ne_of_gt (bounded chunk hc).1) initial processed final he hf start
  refine ⟨final.output, world', ?_, hrep, hout⟩
  rw [main_eq]
  change ((readLoop (none, initial.total, initial.pending)) >>= _) world = _
  simp only [bind_apply, hloop, hz, pure_apply]

#print axioms main_correct

end Project.RunningSum.Source
