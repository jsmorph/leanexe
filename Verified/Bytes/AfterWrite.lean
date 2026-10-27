import Verified.After
import Verified.Bytes.Write

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem After.bytes_rep {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {liveIn live : Nat → Bool} {base : Nat} {heap heap1 : Heap}
    {store store1 : Store Unit} {s s1 : Locals} {mode : Mode} {bytes : LeanExe.Bytes}
    {root length : UInt64}
    (a : After env slots liveIn live base heap store s .bytes mode bytes heap1 store1 s1
      [.i64 root, .i64 length]) : Bytes.Rep heap1 store1 root length bytes := by
  obtain ⟨pointer, count, hWords, hRep⟩ := a.rep
  have hPair : pointer = root ∧ count = length := by
    simpa only [List.cons.injEq, Value.i64.injEq, and_true] using hWords.symm
  simpa only [hPair.1, hPair.2] using hRep

theorem After.writeByte {Γ : List Ty} {env : Env Γ} {slots : List Slot} {liveIn live : Nat → Bool}
    {base : Nat} {heap heap1 : Heap} {store store1 : Store Unit} {s s1 : Locals}
    {bytes : LeanExe.Bytes} {root length index : UInt64}
    (a : After env slots liveIn live base heap store s .bytes .owned bytes heap1 store1 s1
      [.i64 root, .i64 length]) (hi : index.toNat < bytes.data.size) (value : UInt8) :
    After env slots liveIn live base heap store s .bytes .owned
      (Bytes.updated bytes index.toNat value hi) heap1 (Bytes.writeByte store1 root index value)
      s1 [.i64 root, .i64 length] := by
  have hRep := a.bytes_rep
  have hBuffer : Heap.Buffer heap1 store1 root bytes :=
    hRep.buffer.resolve_left fun hEmpty => by omega
  obtain ⟨hWrite, hCapacity⟩ := hBuffer.write_step a.step.at_ index hi value
  have hOutput := (hBuffer.write a.step.at_ index hi value).2
  have hBlock : block (Bytes.writeByte store1 root index value) root = block store1 root :=
    block_eq hCapacity
  have hKeep : ∀ (u : Ty) (y : Var Γ u), live y.index = true → ∀ words,
      LocalsHold s1 (slots.getD y.index default).loc u.types words → words.length = u.width →
      ∀ region ∈ u.regions (slots.getD y.index default).mode store1 words (env.get y),
        regionsDisjoint region (block store1 root) := by
    intro u y hy words hWords hWidth region hRegion
    exact regionsDisjoint_symm (a.apart u y hy (Or.inl rfl) words hWords hWidth
      (block store1 root) (by simp [Ty.regions, Ty.blocks, Bytes.roots, hBuffer.nonzero])
      region hRegion)
  have hStep := a.step.transBoth (keep := Holds.KeepDying env slots liveIn live store s) hWrite
    fun _ hr => ⟨hr, fun hFresh => hFresh _ (by
      simp [Mode.fresh, Ty.blocks, Bytes.roots, hBuffer.nonzero])⟩
  have hSame : Ty.bytes.regions .owned (Bytes.writeByte store1 root index value)
      [.i64 root, .i64 length] bytes = Ty.bytes.regions .owned store1
        [.i64 root, .i64 length] bytes := by
    simp only [Ty.regions, Ty.blocks, Bytes.roots, ite_eq_right hBuffer.nonzero,
      List.map_cons, List.map_nil, hBlock]
  refine ⟨hStep.mono (fun _ h => h) ?_, a.frame, a.holds.step hWrite hKeep,
    ⟨root, length, rfl, ?_⟩, ?_⟩
  · intro region hRegion
    have hEq : region = block store1 root := by
      simpa only [Mode.fresh, Ty.blocks, Bytes.roots, ite_eq_right hOutput.nonzero,
        List.map_cons, List.map_nil, List.mem_singleton, hBlock] using hRegion
    exact List.mem_append_left _ (by
      simp [Mode.fresh, Ty.blocks, Bytes.roots, hBuffer.nonzero, hEq])
  · exact ⟨by rw [Bytes.updated_size]; exact hRep.length_eq, Or.inr hOutput⟩
  · exact Holds.Apart.transfer a.holds a.apart hWrite (Frame.refl base s1) hKeep hSame

end Verified
