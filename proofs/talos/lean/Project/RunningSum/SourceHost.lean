import Project.RunningSum.SourceControl
import Project.RunningSum.BaseIO

namespace Project.RunningSum.Source

open LeanExe.Examples.RunningSum (Decimal parse add render emitSum)

abbrev World := Void IO.RealWorld

structure SuccessfulHost (rep : List ByteArray → List ByteArray → World → Prop) : Prop where
  read : ∀ chunks output world, rep chunks output world →
    ∃ next, LeanExe.ByteIO.read 4096 18446744073709551615 world =
      ⟨.ok (chunks.headD ByteArray.empty), next⟩ ∧ rep chunks.tail output next
  write : ∀ chunks output world bytes, rep chunks output world →
    ∃ next, LeanExe.ByteIO.write bytes 18446744073709551615 world = ⟨0, next⟩ ∧
      rep chunks (output ++ [bytes]) next

theorem emitSum_runs (host : SuccessfulHost rep) (state next : StreamState)
    (he : emitLine state = .ok next) (hr : rep chunks state.output world) :
    ∃ world', emitSum state.total state.pending world = ⟨.ok next.total, world'⟩ ∧
      rep chunks next.output world' ∧ next.pending = ByteArray.empty := by
  cases hp : parse state.pending with
  | none => simp [emitLine, hp] at he
  | some value =>
    simp only [emitLine, hp, Except.ok.injEq] at he
    subst next
    obtain ⟨world', hw, hr'⟩ := host.write chunks state.output world
      (render (add state.total value)) hr
    refine ⟨world', ?_, hr', rfl⟩
    simp only [emitSum, hp, bind_apply, hw]
    rfl

theorem byteStep_runs (host : SuccessfulHost rep) (state next : StreamState)
    (byte : UInt8) (he : consumeByte state byte = .ok next)
    (hr : rep chunks state.output world) :
    ∃ world', byteStep byte (none, state.total, state.pending) world =
      ⟨.yield (none, next.total, next.pending), world'⟩ ∧ rep chunks next.output world' := by
  by_cases hb : byte = 10
  · subst byte
    simp only [consumeByte, beq_self_eq_true, ↓reduceIte] at he
    obtain ⟨world', hw, hr', hp⟩ := emitSum_runs host state next he hr
    refine ⟨world', ?_, hr'⟩
    simp only [byteStep, beq_self_eq_true, ↓reduceIte, bind_apply, hw, pure_apply, hp]
  · have hb' : (byte == 10) = false := by simp [hb]
    simp only [consumeByte, hb', Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at he
    subst next
    exact ⟨world, by simp [byteStep, hb', pure_apply], hr⟩

theorem bytes_runs (host : SuccessfulHost rep) (bytes : List UInt8)
    (state next : StreamState) (he : consume state bytes = .ok next)
    (hr : rep chunks state.output world) :
    ∃ world', forIn bytes (none, state.total, state.pending) byteStep world =
      ⟨(none, next.total, next.pending), world'⟩ ∧ rep chunks next.output world' := by
  induction bytes generalizing state world with
  | nil =>
    have hn : state = next := Except.ok.inj he
    subst state
    exact ⟨world, rfl, hr⟩
  | cons byte bytes ih =>
    rw [consume_cons] at he
    cases hs : consumeByte state byte with
    | error code => simp [hs, bind, Except.bind] at he
    | ok mid =>
      simp only [hs, bind, Except.bind] at he
      obtain ⟨midWorld, hm, hrm⟩ := byteStep_runs host state mid byte hs hr
      obtain ⟨finalWorld, hf, hr'⟩ := ih mid he hrm
      refine ⟨finalWorld, ?_, hr'⟩
      rw [List.forIn_cons]
      simp only [bind_apply, hm]
      exact hf

#print axioms emitSum_runs
#print axioms bytes_runs

end Project.RunningSum.Source
