import LeanExe.Native.Proof.Ops
import Interpreter.Wasm.Semantics.Lemmas

/-!
The simulation of instruction lists, of `block`, `loop`, and `iff`, and of `br`, `br_if`, and
`ret`.  A construct's C statement is the loop `wrapLoop` of its body followed by `dispatch`;
`ConstructOutcome` relates the loop alone to Talos's result for the construct, with a pending
branch `k` levels out recorded as `brk = k + 1`, and `dispatch_outcome` adds the dispatch.
-/

namespace LeanExe.Native

open Wasm LClight

/-- The enclosing constructs' bases lie at or below the current one. -/
def LabelsOk (L : List Label) : Prop :=
  ∀ (k : Nat) (l : Label), L[k]? = some l → l.base ≤ curBase L

section

variable (A : Archi) (X : ExtSem) (E : Env) (mod : Module) (c : FCtx)

/-- The simulation of `inst` at fuel `F`, for code whose calls go to functions that `CallOk`
accepts. -/
def InstrSimL (CallOk : Nat → Prop) (F : Nat) (inst : Instruction) : Prop :=
  ∀ (L : List Label) (σ : List VT) (n : Nat) (s : statement) (σ' : Option (List VT)) (n' : Nat),
    trInstr c L σ n inst = some (s, σ', n') → curBase L ≤ σ.length → LabelsOk L →
    (∀ k, funId k ∈ callees s → CallOk k) →
    ∀ {α : Type} (st : Store α) (sl : Locals) (le : temp_env) (m : mem) (env : HostEnv α),
      Inv E c σ st sl le m → Outcome A X E c L σ' (execOne F mod st sl inst env) s le m

/-- The simulation of an instruction list at fuel `F`. -/
def ProgSim (CallOk : Nat → Prop) (F : Nat) : Prop :=
  ∀ (L : List Label) (σ σend : List VT) (n : Nat) (p : Program) (s : statement) (n' : Nat),
    trProg c L σ σend n p = some (s, n') → curBase L ≤ σ.length → LabelsOk L →
    (∀ k, funId k ∈ callees s → CallOk k) →
    ∀ {α : Type} (st : Store α) (sl : Locals) (le : temp_env) (m : mem) (env : HostEnv α),
      Inv E c σ st sl le m → Outcome A X E c L (some σend) (exec F mod st sl p env) s le m

variable {A X E mod c}

theorem InstrSim.toL {CallOk : Nat → Prop} {F : Nat} {inst : Instruction}
    (h : InstrSim A X E mod c F inst) : InstrSimL A X E mod c CallOk F inst :=
  fun L σ n s σ' n' htr hb _ _ _ st sl le m env hinv => h L σ n s σ' n' htr hb st sl le m env hinv

/-! ## Outcomes of sequences -/

theorem BreakRel.ne_normal {L : List Label} {k : Nat} {α : Type} {st : Store α} {sl : Locals}
    {le : temp_env} {m : mem} {out : outcome} (h : BreakRel E c L k st sl le m out) :
    out ≠ .Out_normal := by
  by_cases hk : k = 0
  · obtain ⟨l, _, h0, _⟩ := h.target
    rw [h0 hk]
    cases l.isLoop <;> simp
  · rw [h.outer hk]; simp

theorem ReturnRel.ne_normal {r : Option VT} {vs : List Value} {out : outcome}
    (h : ReturnRel r vs out) : out ≠ .Out_normal := by
  cases r with
  | none => rw [h]; simp
  | some t => obtain ⟨_, _, _, h⟩ := h; rw [h]; simp

theorem trapOut_ne_normal (r : Option VT) : trapOut r ≠ .Out_normal := by
  cases r <;> simp [trapOut]

/-- Talos's result `r` of the head of a list that does not fall through is the list's. -/
theorem Outcome.seq_abrupt {L : List Label} {σ' : Option (List VT)} (σend : List VT) {α : Type}
    {r : Continuation α} {s1 s2 : statement} {le : temp_env} {m : mem}
    (hr : ∀ st sl, r ≠ .Fallthrough st sl) (h : Outcome A X E c L σ' r s1 le m) :
    Outcome A X E c L (some σend) r (.Ssequence s1 s2) le m := by
  cases r with
  | Fallthrough st sl => exact absurd rfl (hr st sl)
  | Break k st' sl' =>
      obtain ⟨t, le', m', out, hx, hrel, hf⟩ := h
      exact ⟨t, le', m', out, .exec_Sseq_2 _ _ _ _ _ _ _ _ _ hx hrel.ne_normal, hrel, hf⟩
  | Return st' vs =>
      obtain ⟨t, le', m', out, hx, hrel, hg, hs⟩ := h
      exact ⟨t, le', m', out, .exec_Sseq_2 _ _ _ _ _ _ _ _ _ hx hrel.ne_normal, hrel, hg, hs⟩
  | Trap st' msg =>
      obtain ⟨t, le', m', hx, hg, hs, hc⟩ := h
      exact ⟨t, le', m', .exec_Sseq_2 _ _ _ _ _ _ _ _ _ hx (trapOut_ne_normal _), hg, hs, hc⟩
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact h
  | Throwing _ _ _ _ => exact h

/-- `s1` completed normally from `le` to `le'`; `s2` continues from there. -/
theorem Outcome.seq_normal {L : List Label} (hL : LabelsOk L) {σend : List VT} {α : Type}
    {r : Continuation α} {s1 s2 : statement} {le le' : temp_env} {m m' : mem} {t1 : trace}
    (h1 : exec_stmt A X E.ge empty_env le m s1 t1 le' m' .Out_normal)
    (hf : Frame (curBase L) le le') (h : Outcome A X E c L (some σend) r s2 le' m') :
    Outcome A X E c L (some σend) r (.Ssequence s1 s2) le m := by
  cases r with
  | Fallthrough st' sl' =>
      obtain ⟨σ'', h', hb, t, le'', m'', hx, hinv, hf2⟩ := h
      exact ⟨σ'', h', hb, t1 ++ t, le'', m'', .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 hx, hinv,
        hf.trans hf2⟩
  | Break k st' sl' =>
      obtain ⟨t, le'', m'', out, hx, hrel, hf2⟩ := h
      exact ⟨t1 ++ t, le'', m'', out, .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 hx, hrel,
        fun l hl => (hf.mono (hL k l hl)).trans (hf2 l hl)⟩
  | Return st' vs =>
      obtain ⟨t, le'', m'', out, hx, hrel, hg, hs⟩ := h
      exact ⟨t1 ++ t, le'', m'', out, .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 hx, hrel, hg, hs⟩
  | Trap st' msg =>
      obtain ⟨t, le'', m'', hx, hg, hs, hc⟩ := h
      exact ⟨t1 ++ t, le'', m'', .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 hx, hg, hs, hc⟩
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact h
  | Throwing _ _ _ _ => exact h

theorem exec_cons {α : Type} (F : Nat) (st : Store α) (sl : Locals) (env : HostEnv α)
    (i : Instruction) (rest : Program) :
    exec F mod st sl (i :: rest) env =
      match execOne F mod st sl i env with
      | .Fallthrough st s => exec F mod st s rest env
      | other => other := by
  simp only [exec]
  rfl

theorem exec_nil {α : Type} (F : Nat) (st : Store α) (sl : Locals) (env : HostEnv α) :
    exec F mod st sl [] env = .Fallthrough st sl := by
  simp only [exec]

theorem callees_seq (s1 s2 : statement) :
    callees (.Ssequence s1 s2) = callees s1 ++ callees s2 := rfl

/-- A list's simulation from its instructions'. -/
theorem prog_sim {CallOk : Nat → Prop} {F : Nat}
    (hI : ∀ inst, InstrSimL A X E mod c CallOk F inst) : ProgSim A X E mod c CallOk F := by
  intro L σ σend n p
  induction p generalizing σ n with
  | nil =>
      intro s n' h hbase hL hcalls α st sl le m env hinv
      simp [trProg] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [exec_nil]
      exact ⟨σ, rfl, hbase, E0, le, m, .exec_Sskip _ _ _, hinv, Frame.refl _ _⟩
  | cons i rest ih =>
      intro s n' h hbase hL hcalls α st sl le m env hinv
      simp [trProg, Option.bind_eq_some_iff] at h
      obtain ⟨si, σi, ni, hi, h⟩ := h
      cases rest with
      | nil =>
          cases σi with
          | none =>
              simp at h
              obtain ⟨hs, hn⟩ := h
              subst hs hn
              have ho := hI i L σ n si none ni hi hbase hL hcalls st sl le m env hinv
              rw [exec_cons]
              cases hr : execOne F mod st sl i env with
              | Fallthrough st' sl' =>
                  rw [hr] at ho
                  obtain ⟨_, h', _⟩ := ho
                  cases h'
              | _ => rw [hr] at ho; exact ho
          | some σ'' =>
              simp at h
              obtain ⟨hσ, hs, hn⟩ := h
              subst hσ hs hn
              have ho := hI i L σ n si (some σ'') ni hi hbase hL hcalls st sl le m env hinv
              rw [exec_cons]
              cases hr : execOne F mod st sl i env with
              | Fallthrough st' sl' =>
                  rw [hr] at ho
                  simp only [exec_nil]
                  exact ho
              | _ => rw [hr] at ho; exact ho
      | cons j rest' =>
          cases σi with
          | none => simp at h
          | some σ'' =>
              simp [Option.bind_eq_some_iff] at h
              obtain ⟨s2, h2, rfl⟩ := h
              have hcalls1 : ∀ k, funId k ∈ callees si → CallOk k := fun k hk =>
                hcalls k (by rw [callees_seq]; exact List.mem_append_left _ hk)
              have hcalls2 : ∀ k, funId k ∈ callees s2 → CallOk k := fun k hk =>
                hcalls k (by rw [callees_seq]; exact List.mem_append_right _ hk)
              have ho := hI i L σ n si (some σ'') ni hi hbase hL hcalls1 st sl le m env hinv
              rw [exec_cons]
              cases hr : execOne F mod st sl i env with
              | Fallthrough st' sl' =>
                  rw [hr] at ho
                  obtain ⟨σ3, h3, hb3, t1, le', m', hx, hinv', hf⟩ := ho
                  cases h3
                  exact Outcome.seq_normal hL hx hf
                    (ih σ'' ni s2 n' h2 hb3 hL hcalls2 st' sl' le' m' env hinv')
              | _ =>
                  rw [hr] at ho
                  exact Outcome.seq_abrupt σend (fun _ _ h => by cases h) ho

end

end LeanExe.Native
