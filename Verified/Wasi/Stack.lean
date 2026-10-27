import Verified.Wasi.Program

namespace Verified.Wasi

def stackLimitBytes : Nat := 512 * 1024

def guardedFramePositions : Nat := 32

def frameBytes (positions : Nat) : Nat := 8 * positions + 16

def guardedStackBytes : Nat := depthLimit.toNat * frameBytes guardedFramePositions

def EffectProg.extraFrameBytes : {effectSigs : List EffectSig} →
    EffectProg pureSigs effectSigs → Nat
  | _, .nil => 0
  | _, .cons function rest =>
      8 * (function.positions - guardedFramePositions) + rest.extraFrameBytes

inductive EffectProg.FramePath : {effectSigs : List EffectSig} →
    EffectProg pureSigs effectSigs → List Nat → Prop where
  | nil (program : EffectProg pureSigs effectSigs) : FramePath program []
  | skip {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
      {frames : List Nat} (path : FramePath rest frames) : FramePath (.cons function rest) frames
  | cons {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
      {frames : List Nat} (path : FramePath rest frames) :
      FramePath (.cons function rest) (function.positions :: frames)

def extraPathBytes (frames : List Nat) : Nat :=
  (frames.map fun positions => 8 * (positions - guardedFramePositions)).sum

theorem EffectProg.FramePath.extra_le {program : EffectProg pureSigs effectSigs}
    {frames : List Nat} (path : program.FramePath frames) :
    extraPathBytes frames ≤ program.extraFrameBytes := by
  induction path with
  | nil => simp [extraPathBytes]
  | skip _ ih =>
      simp only [EffectProg.extraFrameBytes]
      omega
  | cons _ ih =>
      simp only [extraPathBytes, List.map_cons, List.sum_cons, EffectProg.extraFrameBytes] at *
      omega

def moduleFrameBytes (source : Wasm.Module) : Nat :=
  (source.funcs.map fun function => frameBytes (function.params.length + function.locals.length)).sum

def wrapperFrameBytes : Nat :=
  ([readFunction 0, writeFunction .stdout 0, writeFunction .stderr 0].map fun function =>
    frameBytes (function.params.length + function.locals.length)).sum

def entryFrameBytes (source : Wasm.Module) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) : Nat :=
  match main with
  | none => (entries.map fun entry =>
      let function := entry.function source 0
      frameBytes (function.params.length + function.locals.length)).sum
  | some entry =>
      let function := entry.function source 0
      frameBytes (function.params.length + function.locals.length)

def stackBound (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entryBytes : Nat) : Nat :=
  guardedStackBytes + moduleFrameBytes source + wrapperFrameBytes + program.extraFrameBytes + entryBytes

def StackFits (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entryBytes : Nat) : Prop := stackBound source program entryBytes ≤ stackLimitBytes

instance (source : Wasm.Module) (program : EffectProg pureSigs effectSigs) (entryBytes : Nat) :
    Decidable (StackFits source program entryBytes) := inferInstanceAs (Decidable (_ ≤ _))

theorem stackBound_effects {source : Wasm.Module} {program : EffectProg pureSigs effectSigs}
    {entryBytes : Nat} (fits : StackFits source program entryBytes) :
    program.extraFrameBytes ≤ stackLimitBytes - guardedStackBytes := by
  unfold StackFits stackBound at fits
  omega

theorem stackBound_path {source : Wasm.Module} {program : EffectProg pureSigs effectSigs}
    {entryBytes : Nat} {frames : List Nat} (fits : StackFits source program entryBytes)
    (path : program.FramePath frames) :
    guardedStackBytes + moduleFrameBytes source + wrapperFrameBytes + extraPathBytes frames + entryBytes ≤
      stackLimitBytes := by
  have bounded := path.extra_le
  unfold StackFits stackBound at fits
  omega

end Verified.Wasi
