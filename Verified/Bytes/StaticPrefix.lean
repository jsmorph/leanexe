import Verified.Bytes.StaticEnv
import Verified.ContextHEq
import Verified.ContextAppend

namespace Verified.Bytes.LiteralPool.Safe

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem ofHEq {pool : LiteralPool} {Γ Δ : List Ty} {first : Env Γ} {second : Env Δ}
    {slots : List Slot} {live : Nat → Bool} {heap : Heap} {store : Store Unit} {s : Locals}
    (h : Safe pool first slots live heap store s) (hTypes : Γ = Δ)
    (hValues : HEq first second) : Safe pool second slots live heap store s := by
  subst hTypes
  cases hValues
  exact h

theorem bindPrefixStep {pool : LiteralPool} {ps Γ : List Ty} {values : Env ps} {env : Env Γ}
    {first slots : List Slot} {liveIn live bodyLive : Nat → Bool} {base : Nat}
    {heap heap' : Heap} {store store' : Store Unit} {s s' : Locals}
    {fresh : List (Nat × Nat)}
    (h : Safe pool env slots liveIn heap store s)
    (hVars : Holds env slots liveIn base heap store s)
    (hStep : Step heap store (Holds.KeepDying env slots liveIn live store s)
      heap' store' fresh)
    (hFrame : Frame base s s') (hOuter : Holds env slots live base heap' store' s')
    (hLength : first.length = ps.length)
    (hFresh : ∀ (t : Ty) (x : Var ps t), (first.getD x.index default).mode = .owned →
      ∀ words, LocalsHold s' (first.getD x.index default).loc t.types words →
      words.length = t.width → ∀ block ∈ t.blocks store' words (values.get x),
        block ∈ fresh)
    (hLive : ∀ i, live i = true → liveIn i = true)
    (hBody : ∀ i, bodyLive (ps.length + i) = true → live i = true) :
    Safe pool (values.append env) (first ++ slots) bodyLive heap' store' s' := by
  have hKeep : ∀ region ∈ pool.regions,
      Holds.KeepDying env slots liveIn live store s region :=
    fun region hr => (h.apart region hr).mono fun _ hi _ => ⟨hi, rfl⟩
  obtain ⟨hStatic, hNew⟩ := h.static.step hStep hKeep
  have hTail := h.evolves hVars
    ⟨hStep.mono (fun _ hi => hi) (fun _ hi => nomatch hi), hFrame, hOuter⟩ hLive
  refine ⟨hStatic, ?_⟩
  intro region hr t x hx _ hm words hold length block hb
  rcases x.append_cases with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · simp only [Var.prefix_index, slots_append_prefix x first slots hLength,
      Env.get_append_prefix] at hm hold hb
    exact hNew region hr block (hFresh t x hm words hold length block hb)
  · simp only [slots_append_suffix x first slots hLength, Env.get_append_suffix] at hm hold hb
    exact hTail.apart region hr t x (hBody x.index (by simpa using hx)) rfl hm
      words hold length block hb

end Verified.Bytes.LiteralPool.Safe
