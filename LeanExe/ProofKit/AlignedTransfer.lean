import LeanExe.ProofKit.AlignedExec
import LeanExe.ProofKit.Sequencing
import LeanExe.ProofKit.AlignedSimpAttr
import LeanExe.ProofKit.AlignedFlag

/-!
Transfer of Talos's `wp` to `wpA` for code without 64-bit accesses.  `Instruction.accessFree`
holds of an instruction that makes no 64-bit access, calls nothing, and whose bodies, if any,
are of the same kind, and every run of such code is aligned at every fuel
(`alignedExec_of_accessFree`).  `wpA_append_of_wp` derives `wpA` of `c ++ rest` from Talos's
`wp` of `c` and the alignment of `c`'s runs, with `wpA` of `rest` after a fall-through, so that
a `wp` specification of access-free code, instantiated with that continuation, gives its
`wpA` form unchanged (`wpA_append_accessFree`).

`wpA_close` closes the bound tests and alignment conditions that `simp` leaves of the 64-bit
accesses in straight-line code.
-/

namespace LeanExe.ProofKit

open Wasm

variable {α : Type}

mutual

/-- The instruction makes no 64-bit access, calls nothing, and its bodies are of the same kind. -/
def _root_.Wasm.Instruction.accessFree : Instruction → Bool
  | .load64 _ | .store64 _ | .call _ | .callIndirect _ _ | .callRef _ | .returnCall _
  | .returnCallIndirect _ _ | .returnCallRef _ | .tryTable _ _ _ _ _ _ => false
  | .block _ _ body _ _ => accessFreeCode body
  | .loop _ _ body _ _ => accessFreeCode body
  | .iff _ _ thn els _ _ => accessFreeCode thn && accessFreeCode els
  | _ => true

/-- Every instruction of the program is `Instruction.accessFree`. -/
def accessFreeCode : List Instruction → Bool
  | [] => true
  | i :: is => i.accessFree && accessFreeCode is

end

theorem accessFreeCode_append {c d : Program} :
    accessFreeCode (c ++ d) = (accessFreeCode c && accessFreeCode d) := by
  induction c with
  | nil => simp [accessFreeCode]
  | cons i c ih => simp [accessFreeCode, ih, Bool.and_assoc]

variable {m : Module} {env : HostEnv α}

theorem alignedExec_append (f : Nat) :
    ∀ (c rest : Program) (st : Store α) (s : Locals),
      AlignedExec f m st s (c ++ rest) env ↔
        AlignedExec f m st s c env ∧
          match exec f m st s c env with
          | .Fallthrough st' s' => AlignedExec f m st' s' rest env
          | _ => True
  | [], rest, st, s => by simp [AlignedExec, exec]
  | i :: c, rest, st, s => by
    rw [List.cons_append, AlignedExec, AlignedExec, exec]
    cases execOne f m st s i env with
    | Fallthrough st' s' => simp only [alignedExec_append f c rest st' s', and_assoc]
    | _ => simp

/-- Every run of access-free code is aligned, at every fuel. -/
theorem alignedExec_of_accessFree (f : Nat) :
    (∀ (i : Instruction) (st : Store α) (s : Locals), i.accessFree = true →
      AlignedOne f m st s i env) ∧
    (∀ (p : Program) (st : Store α) (s : Locals), accessFreeCode p = true →
      AlignedExec f m st s p env) := by
  induction f using Nat.strong_induction_on with
  | _ f IH =>
  have hOne : ∀ (i : Instruction) (st : Store α) (s : Locals), i.accessFree = true →
      AlignedOne f m st s i env := by
    intro i st s hi
    rcases f with _ | f
    · simp [AlignedOne]
    · have IHf := IH f (by omega)
      cases i with
      | load64 => simp [Instruction.accessFree] at hi
      | store64 => simp [Instruction.accessFree] at hi
      | call => simp [Instruction.accessFree] at hi
      | block ps rs body pt rt =>
        simp only [AlignedOne]
        exact IHf.2 body st s (by simpa [Instruction.accessFree] using hi)
      | loop ps rs body pt rt =>
        simp only [AlignedOne]
        refine ⟨IHf.2 body st s (by simpa [Instruction.accessFree] using hi), ?_⟩
        split
        · exact IHf.1 _ _ _ hi
        · trivial
      | iff ps rs thn els pt rt =>
        simp only [AlignedOne]
        simp only [Instruction.accessFree, Bool.and_eq_true] at hi
        split
        · exact IHf.2 _ _ _ (by split <;> simp [hi])
        · trivial
      | _ => simp [AlignedOne]
  refine ⟨hOne, fun p => ?_⟩
  induction p with
  | nil => intro st s _; rw [AlignedExec]; trivial
  | cons i p ih =>
    intro st s hp
    simp only [accessFreeCode, Bool.and_eq_true] at hp
    rw [AlignedExec]
    refine ⟨hOne i st s hp.1, ?_⟩
    split
    · exact ih _ _ hp.2
    · trivial

variable {Q : Assertion α} {st : Store α} {s : Locals}

/-- `wpA` of `c ++ rest` from Talos's `wp` of `c`, continued by `wpA` of `rest` after a
fall-through, when the runs of `c` are aligned from some fuel on. -/
theorem wpA_append_of_wp {c rest : Program}
    (hAl : ∃ N, ∀ f ≥ N, AlignedExec f m st s c env)
    (h : wp m c (fun k => match k with
      | .Fallthrough st' s' => wpA m rest Q st' s' env
      | other => Q other) st s env) :
    wpA m (c ++ rest) Q st s env := by
  unfold Wasm.wp at h
  obtain ⟨N, hN⟩ := h
  obtain ⟨Na, hNa⟩ := hAl
  by_cases hOOF : ∀ f ≥ N, exec f m st s c env = .OutOfFuel
  · have hQ : Q .OutOfFuel := by
      have := hN N (Nat.le_refl _)
      rwa [hOOF N (Nat.le_refl _)] at this
    refine ⟨N + Na, fun f hf => ?_⟩
    have hc := hOOF f (by omega)
    refine ⟨?_, ?_⟩
    · rw [exec_append_match, hc]; exact hQ
    · rw [alignedExec_append, hc]; exact ⟨hNa f (by omega), trivial⟩
  · push Not at hOOF
    obtain ⟨f₀, hf₀, hne⟩ := hOOF
    have hstable : ∀ f ≥ f₀, exec f m st s c env = exec f₀ m st s c env :=
      fun f hf => exec_fuel_mono hf hne
    have hK := hN f₀ hf₀
    generalize hk : exec f₀ m st s c env = k at hstable hK hne
    cases k with
    | Fallthrough st' s' =>
      obtain ⟨Nr, hNr⟩ := hK
      refine ⟨f₀ + Na + Nr, fun f hf => ?_⟩
      have hr := hNr f (by omega)
      refine ⟨?_, ?_⟩
      · rw [exec_append_match, hstable f (by omega)]; exact hr.1
      · rw [alignedExec_append, hstable f (by omega)]; exact ⟨hNa f (by omega), hr.2⟩
    | OutOfFuel => exact absurd rfl hne
    | Break _ _ _ | Return _ _ | Trap _ _ | Invalid _ | ReturnCall _ _ _ | Throwing _ _ _ _ =>
      refine ⟨f₀ + Na, fun f hf => ?_⟩
      refine ⟨?_, ?_⟩
      · rw [exec_append_match, hstable f (by omega)]; exact hK
      · rw [alignedExec_append, hstable f (by omega)]; exact ⟨hNa f (by omega), trivial⟩

/-- `wpA_append_of_wp` for access-free code. -/
theorem wpA_append_accessFree {c rest : Program} (hc : accessFreeCode c = true)
    (h : wp m c (fun k => match k with
      | .Fallthrough st' s' => wpA m rest Q st' s' env
      | other => Q other) st s env) :
    wpA m (c ++ rest) Q st s env :=
  wpA_append_of_wp ⟨0, fun f _ => (alignedExec_of_accessFree f).2 c st s hc⟩ h

/-! ## Straight-line code

`simp` with the `wpA_simp` rules and Talos's `wp_simp` rules runs straight-line code under `wpA`
as it runs under `wp`.  The rule for each atomic access-free instruction turns `wpA` of the
instruction and the rest into Talos's `wp` of the instruction alone, continued by `thenA`, whose
`wp_*_cons` rule then applies.  What remains of a `load64` or a `store64` is its bound test and
its alignment, and `wpA_close` discharges both with `omega` from the hypotheses in context. -/

/-- The continuation of an instruction run alone: `wpA` of `rest` after a fall-through, and `Q`
of every other outcome. -/
@[wpA_simp] def thenA (m : Module) (rest : Program) (Q : Assertion α) (env : HostEnv α) :
    Assertion α :=
  fun c => match c with
    | .Fallthrough st' s' => wpA m rest Q st' s' env
    | other => Q other

theorem wpA_free_cons {i : Instruction} {rest : Program} (hi : i.accessFree = true) :
    wpA m (i :: rest) Q st s env ↔ wp m [i] (thenA m rest Q env) st s env :=
  wpA_cons_wp fun f => (alignedExec_of_accessFree (f + 1)).1 i st s hi

attribute [wpA_simp] wpA_nil wpA_load64_cons wpA_store64_cons

section
variable {rest : Program} {n : Nat} {v : UInt64} {c : UInt32}
@[wpA_simp] theorem wpA_localGet_free : wpA m (.localGet n :: rest) Q st s env ↔
    wp m [.localGet n] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_localSet_free : wpA m (.localSet n :: rest) Q st s env ↔
    wp m [.localSet n] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_localTee_free : wpA m (.localTee n :: rest) Q st s env ↔
    wp m [.localTee n] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_globalGet_free : wpA m (.globalGet n :: rest) Q st s env ↔
    wp m [.globalGet n] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_globalSet_free : wpA m (.globalSet n :: rest) Q st s env ↔
    wp m [.globalSet n] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_const_free : wpA m (.const c :: rest) Q st s env ↔
    wp m [.const c] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_constI64_free : wpA m (.constI64 v :: rest) Q st s env ↔
    wp m [.constI64 v] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_eq_free : wpA m (.eq :: rest) Q st s env ↔
    wp m [.eq] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_addI64_free : wpA m (.addI64 :: rest) Q st s env ↔
    wp m [.addI64] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_subI64_free : wpA m (.subI64 :: rest) Q st s env ↔
    wp m [.subI64] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_mulI64_free : wpA m (.mulI64 :: rest) Q st s env ↔
    wp m [.mulI64] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_divUI64_free : wpA m (.divUI64 :: rest) Q st s env ↔
    wp m [.divUI64] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_andI64_free : wpA m (.andI64 :: rest) Q st s env ↔
    wp m [.andI64] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_shrUI64_free : wpA m (.shrUI64 :: rest) Q st s env ↔
    wp m [.shrUI64] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_eqI64_free : wpA m (.eqI64 :: rest) Q st s env ↔
    wp m [.eqI64] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_neI64_free : wpA m (.neI64 :: rest) Q st s env ↔
    wp m [.neI64] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_ltUI64_free : wpA m (.ltUI64 :: rest) Q st s env ↔
    wp m [.ltUI64] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_geUI64_free : wpA m (.geUI64 :: rest) Q st s env ↔
    wp m [.geUI64] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_wrapI64_free : wpA m (.wrapI64 :: rest) Q st s env ↔
    wp m [.wrapI64] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_extendUI32_free : wpA m (.extendUI32 :: rest) Q st s env ↔
    wp m [.extendUI32] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_memorySize_free : wpA m (.memorySize :: rest) Q st s env ↔
    wp m [.memorySize] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_memoryGrow_free : wpA m (.memoryGrow :: rest) Q st s env ↔
    wp m [.memoryGrow] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_drop_free : wpA m (.drop :: rest) Q st s env ↔
    wp m [.drop] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_br_free : wpA m (.br n :: rest) Q st s env ↔
    wp m [.br n] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_br_if_free : wpA m (.br_if n :: rest) Q st s env ↔
    wp m [.br_if n] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_ret_free : wpA m (.ret :: rest) Q st s env ↔
    wp m [.ret] (thenA m rest Q env) st s env := wpA_free_cons rfl
@[wpA_simp] theorem wpA_unreachable_free : wpA m (.unreachable :: rest) Q st s env ↔
    wp m [.unreachable] (thenA m rest Q env) st s env := wpA_free_cons rfl
end

theorem mod8_eq_true {x : Nat} (h : x % 8 = 0) : (x % 8 = 0) = True := eq_true h

theorem toUInt32_sub_toNat {p : UInt64} {k : UInt32} (hk : k.toNat ≤ p.toNat)
    (h32 : p.toNat < 4294967296 + k.toNat) : (p.toUInt32 - k).toNat = p.toNat - k.toNat := by
  rw [UInt32.toNat_sub, UInt64.toNat_toUInt32]
  have := k.toNat_lt
  simp only [Nat.reducePow] at this ⊢
  omega

theorem lt_eq_false {a b : Nat} (h : ¬a < b) : (a < b) = False := eq_false h

/-- Discharges the bound tests and the alignment conditions of 64-bit accesses with `omega`. -/
macro "wpA_close" : tactic =>
  `(tactic| simp (disch := omega) only [mod8_eq_true, lt_eq_false, ↓reduceIte, true_and])

end LeanExe.ProofKit
