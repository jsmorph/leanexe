import Verified.ExprSpec
import Verified.ArgsCorrect
import Verified.Bytes.Literal

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem spec_bytesLiteral {S : List Sig} {Γ : List Ty} {m : Module} {funs : Funs S}
    {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit}
    {pv : List Value} {pool : Bytes.LiteralPool} (hm : Runtime m) (bytes : List UInt8)
    (hCover : (Expr.bytesLiteral (S := S) (Γ := Γ) bytes).Covered pool) :
    ∀ (env : Env Γ) slots paid live, CodeSpec m funs flags bounds fits host pv
      (Expr.bytesLiteral (S := S) (Γ := Γ) bytes) env slots paid live pool := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hSafe hCap hBase hRoom
    hPlace rest Q hTrap hNext
  by_cases hEmpty : bytes = []
  · subst bytes
    have hRep : Ty.bytes.Rep .owned heap store [.i64 0, .i64 0] (Bytes.Literal.value []) :=
      ⟨0, 0, rfl, ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
    have hAfter : After env slots
        (fun i => live i || (Expr.bytesLiteral (S := S) (Γ := Γ) []).uses i) live
        base heap store s .bytes .owned (Bytes.Literal.value []) heap store s [.i64 0, .i64 0] :=
      After.refl hAt hVars (fun i hi => by simp [hi]) hRep rfl
        (fun _ _ _ _ _ _ _ _ hb => nomatch hb)
    have hDone := hNext heap store s [.i64 0, .i64 0] hAfter (fun _ => Nat.le_add_right _ _)
    simpa [Expr.code, Expr.denote] using hDone
  · have hMember : bytes ∈ pool.values := hCover (by simp [Expr.literals, hEmpty])
    obtain ⟨offset, hOffset⟩ := Bytes.literalOffset_exists hMember
    have hWidth : base + 4 ≤ h := by simpa only [Expr.width, ite_eq_right hEmpty] using hRoom
    simp only [Expr.code, hEmpty, ite_false, hOffset]
    refine Bytes.wp_literal hm hAt hSafe.static hOffset hEmpty hBase
      (by rw [hh]; exact hWidth) hCap
      (hTrap.alloc (by simp [Expr.aborts]) fun _ hw => hw.mono (by simp [Expr.allocs]))
      fun heap' store' s' root hStep hRep hFrame hTop => ?_
    have hBlocks : Mode.owned.fresh store' Ty.bytes
        [.i64 root, .i64 (UInt64.ofNat bytes.length)] (Bytes.Literal.value bytes) = Bytes.regions store' root :=
      Bytes.roots_regions store' root (UInt64.ofNat bytes.length)
    have hHold : Holds env slots
        (fun i => live i || (Expr.bytesLiteral (S := S) (Γ := Γ) bytes).uses i)
        base heap' store' s' :=
      (hVars.step hStep (fun _ _ _ _ _ _ _ _ => trivial)).agree hFrame
    have hAfter : After env slots
        (fun i => live i || (Expr.bytesLiteral (S := S) (Γ := Γ) bytes).uses i) live
        base heap store s .bytes .owned (Bytes.Literal.value bytes) heap' store' s'
        [.i64 root, .i64 (UInt64.ofNat bytes.length)] := by
      refine ⟨?_, hFrame, hHold.live_mono (fun i hi => by simp [hi]),
        ⟨root, UInt64.ofNat bytes.length, rfl, hRep⟩, ?_⟩
      · rw [hBlocks]
        exact hStep.mono (fun _ _ => trivial) (fun _ hi => hi)
      · intro u y hy _ words hWords hLength block hBlock region hRegion
        obtain ⟨hSame, hFresh⟩ := hVars.regions_after hStep
          (by simp [hy]) ((hVars.hold_agree hFrame (by simp [hy]) hLength).mp hWords)
          hLength (fun _ _ => trivial)
        rw [hSame] at hRegion
        exact regionsDisjoint_symm (hFresh region hRegion block (by
          simpa only [← hBlocks, Ty.regions, Mode.fresh] using hBlock))
    have hDone := hNext heap' store' s' [.i64 root, .i64 (UInt64.ofNat bytes.length)] hAfter
      fun _ => top_unpaid rfl (by simp only [Expr.allocs]; omega)
    simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] using hDone

end Verified
