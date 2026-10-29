import Verified.FieldsExpr
import Verified.Bytes.Normalize

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime

/-- The words of buffers, a root and a length each, in which the root of every empty buffer
is 0. -/
def Bytes.Normal : List Value → Prop
  | [] => True
  | [_] => True
  | root :: length :: rest => (length = .i64 0 → root = .i64 0) ∧ Bytes.Normal rest

/-- An owned empty buffer whose object a step releases: the value is the same buffer, with
root 0. -/
theorem After.releaseBytes {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap1 heap2 : Heap} {store store1 store2 : Store Unit} {s s1 : Locals}
    {v : LeanExe.Bytes} {p length : UInt64}
    (a : After env slots L0 L base heap store s .bytes .owned v heap1 store1 s1
      [.i64 p, .i64 length])
    (hStep : Step heap1 store1 (fun r => ∀ b ∈ Bytes.regions store1 p, regionsDisjoint r b)
      heap2 store2 [])
    (hEmpty : v.data.size = 0) :
    After env slots L0 L base heap store s .bytes .owned v heap2 store2 s1
      [.i64 0, .i64 length] := by
  have hBlocks : Ty.blocks store1 .bytes [.i64 p, .i64 length] v = Bytes.regions store1 p :=
    Bytes.roots_regions store1 p length
  have hKeep : ∀ (u : Ty) (y : Var Γ u), L y.index = true → ∀ wy,
      LocalsHold s1 (slots.getD y.index default).loc u.types wy → wy.length = u.width →
      ∀ c ∈ u.regions (slots.getD y.index default).mode store1 wy (env.get y),
        ∀ b ∈ Bytes.regions store1 p, regionsDisjoint c b := fun u y hy wy hwy hly c hc b hb =>
    regionsDisjoint_symm (a.apart u y hy (Or.inl rfl) wy hwy hly b
      (by change b ∈ Ty.blocks store1 .bytes [.i64 p, .i64 length] v; rw [hBlocks]; exact hb)
      c hc)
  have hStep2 := a.step.transBoth (keep := Holds.KeepDying env slots L0 L store s) hStep
    fun _ hr => ⟨hr, fun hf b hb => hf b (by
      change b ∈ Ty.blocks store1 .bytes [.i64 p, .i64 length] v; rw [hBlocks]; exact hb)⟩
  obtain ⟨root, len, hWords, hRep⟩ := a.rep
  simp only [List.cons.injEq, Value.i64.injEq, and_true] at hWords
  obtain ⟨rfl, rfl⟩ := hWords
  refine ⟨hStep2.mono (fun _ h => h) fun b hb => by
      simp [Mode.fresh, Ty.blocks, Bytes.roots] at hb,
    a.frame, a.holds.step hStep hKeep,
    ⟨0, _, rfl, hRep.length_eq, Or.inl ⟨rfl, hEmpty⟩⟩, ?_⟩
  intro u y hy _ wy hwy hly b hb
  simp [Ty.regions, Ty.blocks, Bytes.roots] at hb

#print axioms After.releaseBytes
end Verified
