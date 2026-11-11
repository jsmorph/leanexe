import LeanExe.Native.ClightN.Exec
import LeanExe.Native.Proof.Input

/-!
The traces of N (`clightn/N.nsx`) hold only volatile loads and stores (`nprog_events`).  The
trace of a run of the Lean copy that reads the sequence `σ` in the sense of `Reads`, the twin of
Rocq's `reads`, therefore satisfies N's `nreads σ 0` when it holds only such events
(`reads_nreads`), and a renaming of identifiers keeps both facts (`nreads_ren`, `events_ren`).
-/

namespace ClightN.Proof

open LClight LeanExe.Native ClightN.Base ClightN.Spec

/-- A volatile load or store. -/
def isLS : event → Bool
  | .Event_vload .. => true
  | .Event_vstore .. => true
  | _ => false

theorem nexec_events {defs : Defs} {le gv : ident → Option val} {mb : ident → Int → Int}
    {s : statement} {t : List event} {le' gv' : ident → Option val} {mb' : ident → Int → Int}
    {out : outcome} (h : nexec defs le gv mb s t le' gv' mb' out) : t.all isLS = true := by
  induction h <;> simp_all [app, List.all_append, isLS]

theorem nprog_events {defs : Defs} {main : ident} {t : List event} {r : UInt32}
    (h : nprog defs main t r) : t.all isLS = true := by
  cases h with
  | np_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ hx _ => exact nexec_events hx

theorem countVloads_app (t1 t2 : trace) :
    countVloads (t1 ++ t2) = countVloads t1 + countVloads t2 := by
  simp [countVloads, List.filter_append]

theorem nreads_of_reads (σ : Nat → UInt32) : ∀ (t pre : trace), t.all isLS = true →
    (∀ tp ev u, pre ++ t = tp ++ ev :: u →
      match ev with
      | .Event_syscall _ _ _ => False
      | .Event_vload _ _ _ v => v = .EVint (σ (countVloads tp))
      | _ => True) →
    nreads σ (countVloads pre) t
  | [], pre, _, _ => .nr_nil σ _
  | ev :: t, pre, hls, hr => by
      simp only [List.all_cons, Bool.and_eq_true] at hls
      have h0 := hr pre ev t rfl
      have ih := nreads_of_reads σ t (pre ++ [ev]) hls.2
        (fun tp e u h => hr tp e u (by simpa using h))
      rw [countVloads_app] at ih
      cases ev with
      | Event_vload ch x o v =>
          simp only at h0
          subst h0
          exact .nr_load σ _ ch x o t ih
      | Event_vstore ch x o v => exact .nr_store σ _ ch x o v t ih
      | Event_syscall => simp [isLS] at hls
      | Event_annot => simp [isLS] at hls

theorem reads_nreads {σ : Nat → UInt32} {t : trace} (h : Reads σ t) (hls : t.all isLS = true) :
    nreads σ 0 t :=
  nreads_of_reads σ t [] hls fun tp ev u e => h tp ev u (by simpa using e)

theorem nreads_ren (g : ident → ident) {σ : Nat → UInt32} {c : Nat} {t : trace}
    (h : nreads σ c t) : nreads σ c (renTrace g t) := by
  induction h with
  | nr_nil c => exact .nr_nil σ c
  | nr_load c ch x o t _ ih => exact .nr_load σ c ch (g x) o (renTrace g t) ih
  | nr_store c ch x o ev t _ ih =>
      exact .nr_store σ c ch (g x) o (renEventval g ev) (renTrace g t) ih

theorem events_ren (g : ident → ident) {t : trace} (h : (renTrace g t).all isLS = true) :
    t.all isLS = true := by
  have e : (isLS ∘ renEvent g) = isLS := by
    funext ev
    cases ev <;> rfl
  simpa [renTrace, List.all_map, e] using h

end ClightN.Proof
