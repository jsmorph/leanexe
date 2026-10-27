import Demos.StreamFold.StreamHost
import Verified.Wasi.Observed

namespace Demos.StreamFold

open LeanExe LeanExe.Wasi Verified.Wasi

def stdoutWords (events : List Event) : List UInt64 :=
  events.flatMap fun event => match event with
    | .write .stdout offered reply => (byteWords offered).take reply.committed.toNat
    | _ => []

@[simp] theorem stdoutWords_nil : stdoutWords [] = [] := rfl

theorem stdoutWords_append (first rest : List Event) :
    stdoutWords (first ++ rest) = stdoutWords first ++ stdoutWords rest := by
  simp only [stdoutWords, List.flatMap_append]

@[simp] theorem stdoutWords_read (events : List Event) (capacity : UInt64) (reply : Transfer Bytes) :
    stdoutWords (events ++ [.read capacity reply]) = stdoutWords events := by
  simp [stdoutWords, List.flatMap_append]

@[simp] theorem stdoutWords_write_stdout (events : List Event) (offered : Bytes)
    (reply : Transfer UInt64) :
    stdoutWords (events ++ [.write .stdout offered reply]) =
      stdoutWords events ++ (byteWords offered).take reply.committed.toNat := by
  simp [stdoutWords, List.flatMap_append]

@[simp] theorem stdoutWords_write_stderr (events : List Event) (offered : Bytes)
    (reply : Transfer UInt64) :
    stdoutWords (events ++ [.write .stderr offered reply]) = stdoutWords events := by
  simp [stdoutWords, List.flatMap_append]

@[simp] theorem stdoutWords_exit (events : List Event) (code : UInt64) :
    stdoutWords (events ++ [.exit code]) = stdoutWords events := by
  simp [stdoutWords, List.flatMap_append]

@[simp] theorem stdoutWords_exitTrap (events : List Event) (code : UInt64) (message : String) :
    stdoutWords (events ++ [.exitTrap code message]) = stdoutWords events := by
  simp [stdoutWords, List.flatMap_append]

def observedStreamRep (baseRep : StreamPosition → World → Prop)
    (position : StreamPosition) (observed : Observed World) : Prop :=
  baseRep position observed.world ∧ position.output = stdoutWords observed.events

theorem StreamHost.observed {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep) :
    StreamHost (observedHost host) (observedStreamRep rep) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro position before represented
    obtain ⟨bytes, final, operation⟩ := streams.read_available position before.world represented.1
    exact ⟨bytes, ⟨final, before.events ++ [.read 4096 (.returned 0 bytes)]⟩, operation, rfl⟩
  · intro position before bytes represented nonempty
    obtain ⟨count, final, operation⟩ :=
      streams.write_available position before.world bytes represented.1 nonempty
    exact ⟨count, ⟨final, before.events ++ [.write .stdout bytes (.returned 0 count)]⟩,
      operation, rfl⟩
  · intro position before reply final represented operation
    obtain ⟨bytes, next, same, nextRep, consumed, eof, output⟩ :=
      streams.read_reply represented.1 operation.1
    refine ⟨bytes, next, same, ⟨nextRep, ?_⟩, consumed, eof, output⟩
    rw [output, represented.2, operation.2, stdoutWords_read]
  · intro position before bytes reply final represented nonempty operation
    obtain ⟨count, next, same, nextRep, input, output, zero⟩ :=
      streams.write_reply represented.1 nonempty operation.1
    refine ⟨count, next, same, ⟨nextRep, ?_⟩, input, output, zero⟩
    rw [output, represented.2, operation.2, stdoutWords_write_stdout, same]
    rfl

theorem stdoutWords_of_exit {World : Type} {host : Host World} {before after : Observed World}
    {code : UInt64} (operation : (observedHost host).exit before code after) :
    stdoutWords after.events = stdoutWords before.events := by
  rw [operation.2, stdoutWords_exit]

theorem stdoutWords_of_exitTrap {World : Type} {host : Host World}
    {before after : Observed World} {code : UInt64} {message : String}
    (operation : (observedHost host).exitTrap before code message after) :
    stdoutWords after.events = stdoutWords before.events := by
  rw [operation.2, stdoutWords_exitTrap]

theorem observedStreamRep_exit_output {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} {position : StreamPosition}
    {before after : Observed World} {code : UInt64}
    (represented : observedStreamRep rep position before)
    (operation : (observedHost host).exit before code after) :
    position.output = stdoutWords after.events :=
  represented.2.trans (stdoutWords_of_exit operation).symm

theorem observedStreamRep_exitTrap_output {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} {position : StreamPosition}
    {before after : Observed World} {code : UInt64} {message : String}
    (represented : observedStreamRep rep position before)
    (operation : (observedHost host).exitTrap before code message after) :
    position.output = stdoutWords after.events :=
  represented.2.trans (stdoutWords_of_exitTrap operation).symm

end Demos.StreamFold
