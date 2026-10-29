import Interpreter.Wasm.Wp.Defs
import Interpreter.Wasm.Semantics.Lemmas
import LeanExe.ProofKit.AlignedDefs

/-!
Aligned runs.  `AlignedExec fuel m st s p env` states that every 64-bit load and store that
`exec fuel m st s p env` performs inside memory has an address that is a multiple of 8.  The
predicates `AlignedOne`, `AlignedExec`, `AlignedRun`, and `AlignedRunTail` are in
[the aligned run definitions](AlignedDefs.lean), which import only Talos's semantics.

`wpA` is `wp` with `AlignedExec` at every fuel from some bound on.  `wpA.wp` forgets the alignment,
and the rules for single instructions have the form of Talos's `wp_*_cons` rules, with the
alignment of the address as a conjunct in the rules for `load64` and `store64`.
-/

namespace LeanExe.ProofKit

open Wasm

variable {α : Type}

/-! ## Residues modulo 8

The moduli of `UInt64` and `UInt32` are multiples of 8, so sums, differences, and truncations
keep residues modulo 8 whether or not they wrap. -/

theorem UInt64.add_mod8 {a b : UInt64} (ha : a.toNat % 8 = 0) (hb : b.toNat % 8 = 0) :
    (a + b).toNat % 8 = 0 := by
  rw [UInt64.toNat_add]
  omega

theorem UInt64.sub_mod8 {a b : UInt64} (ha : a.toNat % 8 = 0) (hb : b.toNat % 8 = 0) :
    (a - b).toNat % 8 = 0 := by
  rw [UInt64.toNat_sub]
  have := b.toNat_lt
  simp only [Nat.reducePow] at this ⊢
  omega

theorem UInt64.toUInt32_mod8 {a : UInt64} (ha : a.toNat % 8 = 0) :
    a.toUInt32.toNat % 8 = 0 := by
  rw [UInt64.toNat_toUInt32]
  simp only [Nat.reducePow]
  omega

/-- `wp` with aligned 64-bit accesses: from some fuel on, the run of `c` satisfies `Q` and every
64-bit access that it makes inside memory is aligned. -/
def wpA (m : Module) (c : Program) (Q : Assertion α) (st : Store α) (s : Locals)
    (env : HostEnv α := {}) : Prop :=
  ∃ N, ∀ fuel ≥ N, Q (exec fuel m st s c env) ∧ AlignedExec fuel m st s c env

section

variable {m : Module} {Q Q' : Assertion α} {st : Store α} {s : Locals} {env : HostEnv α}

theorem wpA.wp {c : Program} (h : wpA m c Q st s env) : wp m c Q st s env := by
  obtain ⟨N, hN⟩ := h
  unfold Wasm.wp
  exact ⟨N, fun f hf => (hN f hf).1⟩

theorem wpA.conseq {c : Program} (hq : Q ⇛ Q') (h : wpA m c Q st s env) :
    wpA m c Q' st s env := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun f hf => ⟨hq _ (hN f hf).1, (hN f hf).2⟩⟩

theorem wpA_nil : wpA m [] Q st s env ↔ Q (.Fallthrough st s) := by
  constructor
  · rintro ⟨N, hN⟩
    simpa [exec] using (hN N (Nat.le_refl _)).1
  · intro hQ
    exact ⟨0, fun f _ => ⟨by simpa [exec] using hQ, by simp [AlignedExec]⟩⟩

/-- An instruction that falls through to the same state at every fuel from 1, with the
alignment of its access equivalent to `P` at every such fuel. -/
theorem wpA_cons_fall_iff {i : Instruction} {rest : Program} {st' : Store α} {s' : Locals}
    {P : Prop} (hstep : ∀ f, execOne (f + 1) m st s i env = .Fallthrough st' s')
    (hal : ∀ f, AlignedOne (f + 1) m st s i env ↔ P) :
    wpA m (i :: rest) Q st s env ↔ P ∧ wpA m rest Q st' s' env := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨?_, N + 1, fun fuel hf => ?_⟩
    · have h := (hN (N + 1) (by omega)).2
      rw [AlignedExec] at h
      exact (hal N).mp h.1
    · obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have h := hN (f + 1) (by omega)
      rw [exec, hstep f] at h
      rw [AlignedExec, hstep f] at h
      exact ⟨h.1, h.2.2⟩
  · rintro ⟨hP, N, hN⟩
    refine ⟨N + 1, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have h := hN (f + 1) (by omega)
    refine ⟨?_, ?_⟩
    · rw [exec, hstep f]
      exact h.1
    · rw [AlignedExec, hstep f]
      exact ⟨(hal f).mpr hP, h.2⟩

/-- `wpA_cons_fall_iff` for an instruction that makes no 64-bit access. -/
theorem wpA_cons_fall {i : Instruction} {rest : Program} {st' : Store α} {s' : Locals}
    (hstep : ∀ f, execOne (f + 1) m st s i env = .Fallthrough st' s')
    (hal : ∀ f, AlignedOne (f + 1) m st s i env) :
    wpA m (i :: rest) Q st s env ↔ wpA m rest Q st' s' env := by
  rw [wpA_cons_fall_iff (P := True) hstep (fun f => iff_true_intro (hal f)), true_and]

/-- An instruction that ends in the same continuation `k` other than a fall-through at every
fuel from 1. -/
theorem wpA_cons_stop {i : Instruction} {rest : Program} {k : Continuation α}
    (hstep : ∀ f, execOne (f + 1) m st s i env = k) (hk : ∀ st' s', k ≠ .Fallthrough st' s')
    (hal : ∀ f, AlignedOne (f + 1) m st s i env) :
    wpA m (i :: rest) Q st s env ↔ Q k := by
  have hexec : ∀ f, exec (f + 1) m st s (i :: rest) env = k := by
    intro f
    rw [exec, hstep f]
    cases k with
    | Fallthrough st' s' => exact absurd rfl (hk st' s')
    | _ => rfl
  constructor
  · rintro ⟨N, hN⟩
    have h := (hN (N + 1) (by omega)).1
    rwa [hexec N] at h
  · intro hQ
    refine ⟨1, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    refine ⟨by rw [hexec f]; exact hQ, ?_⟩
    rw [AlignedExec, hstep f]
    refine ⟨hal f, ?_⟩
    cases k with
    | Fallthrough st' s' => exact absurd rfl (hk st' s')
    | _ => trivial

/-! ## Single instructions -/

theorem wpA_localGet_cons {i : Nat} {rest : Program} :
    wpA m (.localGet i :: rest) Q st s env ↔
    (match s.get i with
     | some v => wpA m rest Q st { s with values := v :: s.values } env
     | none => Q (.Invalid "localGet index out of bounds")) := by
  have hal : ∀ f, AlignedOne (f + 1) m st s (.localGet i) env := fun f => by
    simp [AlignedOne]
  cases h : s.get i with
  | some v => exact wpA_cons_fall (fun f => by simp_all [execOne.eq_def]) hal
  | none => exact wpA_cons_stop (fun f => by simp_all [execOne.eq_def]) (by simp) hal

theorem wpA_constI64_cons {v : UInt64} {rest : Program} :
    wpA m (.constI64 v :: rest) Q st s env ↔
    wpA m rest Q st { s with values := .i64 v :: s.values } env :=
  wpA_cons_fall (fun f => by simp [execOne.eq_def]) (fun f => by simp [AlignedOne])

theorem wpA_addI64_cons {rest : Program} :
    wpA m (.addI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wpA m rest Q st { s with values := .i64 (a + b) :: vs } env
     | _ => Q (.Invalid "addI64: ill-shaped operand stack")) := by
  have hal : ∀ f, AlignedOne (f + 1) m st s .addI64 env := fun f => by simp [AlignedOne]
  split
  · rename_i b a vs hv
    exact wpA_cons_fall (fun f => by simp [execOne.eq_def, hv]) hal
  · rename_i hv
    refine wpA_cons_stop (fun f => ?_) (by simp) hal
    simp only [execOne.eq_def]

theorem wpA_mulI64_cons {rest : Program} :
    wpA m (.mulI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wpA m rest Q st { s with values := .i64 (a * b) :: vs } env
     | _ => Q (.Invalid "mulI64: ill-shaped operand stack")) := by
  have hal : ∀ f, AlignedOne (f + 1) m st s .mulI64 env := fun f => by simp [AlignedOne]
  split
  · rename_i b a vs hv
    exact wpA_cons_fall (fun f => by simp [execOne.eq_def, hv]) hal
  · rename_i hv
    refine wpA_cons_stop (fun f => ?_) (by simp) hal
    simp only [execOne.eq_def]

theorem wpA_wrapI64_cons {rest : Program} :
    wpA m (.wrapI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs =>
       wpA m rest Q st { s with values := .i32 (UInt32.ofNat (a.toNat % 2 ^ 32)) :: vs } env
     | _ => Q (.Invalid "wrapI64: ill-shaped operand stack")) := by
  have hal : ∀ f, AlignedOne (f + 1) m st s .wrapI64 env := fun f => by simp [AlignedOne]
  split
  · rename_i a vs hv
    exact wpA_cons_fall (fun f => by simp [execOne.eq_def, hv]) hal
  · rename_i hv
    refine wpA_cons_stop (fun f => ?_) (by simp) hal
    simp only [execOne.eq_def]

/-- `load64` at an `i32` address: inside memory, the address must be a multiple of 8. -/
theorem wpA_load64_i32 {off a : UInt32} {vs : List Value} {rest : Program}
    (hv : s.values = .i32 a :: vs) :
    wpA m (.load64 off :: rest) Q st s env ↔
    (if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
       Q (.Trap st "out of bounds memory access")
     else (a.toNat + off.toNat) % 8 = 0 ∧
       wpA m rest Q st { s with values := .i64 (st.mem.read64 (a + off)) :: vs } env) := by
  split
  · rename_i hout
    refine wpA_cons_stop (fun f => by simp [execOne.eq_def, hv, hout]) (by simp) (fun f => ?_)
    simp only [AlignedOne, hv]
    omega
  · rename_i hin
    refine wpA_cons_fall_iff (fun f => by simp [execOne.eq_def, hv, hin]) (fun f => ?_)
    simp only [AlignedOne, hv]
    exact ⟨fun h => h (by omega), fun h _ => h⟩

/-- `store64` at an `i32` address: inside memory, the address must be a multiple of 8. -/
theorem wpA_store64_i32 {off a : UInt32} {x : UInt64} {vs : List Value} {rest : Program}
    (hv : s.values = .i64 x :: .i32 a :: vs) :
    wpA m (.store64 off :: rest) Q st s env ↔
    (if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
       Q (.Trap st "out of bounds memory access")
     else (a.toNat + off.toNat) % 8 = 0 ∧
       wpA m rest Q { st with mem := st.mem.write64 (a + off) x } { s with values := vs } env) := by
  split
  · rename_i hout
    refine wpA_cons_stop (fun f => by simp [execOne.eq_def, hv, hout]) (by simp) (fun f => ?_)
    simp only [AlignedOne, hv]
    omega
  · rename_i hin
    refine wpA_cons_fall_iff (fun f => by simp [execOne.eq_def, hv, hin]) (fun f => ?_)
    simp only [AlignedOne, hv]
    exact ⟨fun h => h (by omega), fun h _ => h⟩

theorem wpA_subI64_cons {rest : Program} :
    wpA m (.subI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wpA m rest Q st { s with values := .i64 (a - b) :: vs } env
     | _ => Q (.Invalid "subI64: ill-shaped operand stack")) := by
  have hal : ∀ f, AlignedOne (f + 1) m st s .subI64 env := fun f => by simp [AlignedOne]
  split
  · rename_i b a vs hv
    exact wpA_cons_fall (fun f => by simp [execOne.eq_def, hv]) hal
  · rename_i hv
    refine wpA_cons_stop (fun f => ?_) (by simp) hal
    simp only [execOne.eq_def]

/-- `store64` in the form of Talos's `wp_store64_cons`, with the alignment of an access inside
memory as a conjunct, for proofs that run `simp` over straight-line code. -/
theorem wpA_store64_cons {off : UInt32} {rest : Program} :
    wpA m (.store64 off :: rest) Q st s env ↔
    (match s.values with
     | .i64 v :: .i32 a :: vs =>
       if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else (a.toNat + off.toNat) % 8 = 0 ∧
         wpA m rest Q { st with mem := st.mem.write64 (a + off) v } { s with values := vs } env
     | .i64 v :: .i64 a :: vs =>
       if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else (a.toUInt32.toNat + off.toNat) % 8 = 0 ∧
         wpA m rest Q { st with mem := st.mem.write64 (a.toUInt32 + off) v }
           { s with values := vs } env
     | _ => Q (.Invalid "store64: ill-shaped operand stack")) := by
  split
  · rename_i v a vs hv
    exact wpA_store64_i32 hv
  · rename_i v a vs hv
    split
    · rename_i hout
      refine wpA_cons_stop (fun f => by simp [execOne.eq_def, hv, hout]) (by simp)
        (fun f => ?_)
      simp only [AlignedOne, hv]
      omega
    · rename_i hin
      refine wpA_cons_fall_iff (fun f => by simp [execOne.eq_def, hv, hin]) (fun f => ?_)
      simp only [AlignedOne, hv]
      exact ⟨fun h => h (by omega), fun h _ => h⟩
  · rename_i hv
    refine wpA_cons_stop (fun f => ?_) (by simp) (fun f => ?_)
    · simp only [execOne.eq_def]
    · simp only [AlignedOne]

/-! ## Instructions without a 64-bit access or a body

`wpA_cons_wp` reduces `wpA` of such an instruction to Talos's `wp` of the instruction alone,
whose continuation is `wpA` of the rest, so that Talos's `wp_*_cons` rules apply unchanged. -/

theorem wpA_cons_wp {i : Instruction} {rest : Program}
    (hal : ∀ f, AlignedOne (f + 1) m st s i env) :
    wpA m (i :: rest) Q st s env ↔
      wp m [i] (fun c => match c with
        | .Fallthrough st' s' => wpA m rest Q st' s' env
        | other => Q other) st s env := by
  have hone : ∀ f, exec f m st s [i] env = execOne f m st s i env := by
    intro f
    simp only [exec]
    cases execOne f m st s i env <;> rfl
  have hal' : ∀ f, 1 ≤ f → AlignedOne f m st s i env := fun f hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact hal g
  constructor
  · rintro ⟨N, hN⟩
    unfold Wasm.wp
    refine ⟨N + 1, fun f hf => ?_⟩
    rw [hone f]
    have hf' := hN f (by omega)
    rw [exec] at hf'
    rw [AlignedExec] at hf'
    generalize hk : execOne f m st s i env = k at hf'
    cases k with
    | Fallthrough st' s' =>
      refine ⟨N + f, fun g hg => ?_⟩
      have hg' := hN g (by omega)
      have hmono : execOne g m st s i env = .Fallthrough st' s' := by
        rw [execOne_fuel_mono (by omega : f ≤ g) (by rw [hk]; simp)]
        exact hk
      rw [exec, hmono] at hg'
      rw [AlignedExec, hmono] at hg'
      exact ⟨hg'.1, hg'.2.2⟩
    | _ => exact hf'.1
  · intro h
    unfold Wasm.wp at h
    obtain ⟨N, hN⟩ := h
    by_cases hOOF : ∀ f ≥ N + 1, execOne f m st s i env = .OutOfFuel
    · refine ⟨N + 1, fun f hf => ?_⟩
      have hQ := hN f (by omega)
      rw [hone f, hOOF f hf] at hQ
      refine ⟨?_, ?_⟩
      · rw [exec, hOOF f hf]; exact hQ
      · rw [AlignedExec, hOOF f hf]; exact ⟨hal' f (by omega), trivial⟩
    · push Not at hOOF
      obtain ⟨f₀, hf₀, hne⟩ := hOOF
      have hstable : ∀ f ≥ f₀, execOne f m st s i env = execOne f₀ m st s i env :=
        fun f hf => execOne_fuel_mono hf hne
      have hK := hN f₀ (by omega)
      rw [hone f₀] at hK
      generalize hk : execOne f₀ m st s i env = k at hstable hK hne
      cases k with
      | Fallthrough st' s' =>
        obtain ⟨Nr, hNr⟩ := hK
        refine ⟨f₀ + Nr, fun f hf => ?_⟩
        have hr := hNr f (by omega)
        refine ⟨?_, ?_⟩
        · rw [exec, hstable f (by omega)]; exact hr.1
        · rw [AlignedExec, hstable f (by omega)]; exact ⟨hal' f (by omega), hr.2⟩
      | OutOfFuel => exact absurd rfl hne
      | Break _ _ _ | Return _ _ | Trap _ _ | Invalid _ | ReturnCall _ _ _ | Throwing _ _ _ _ =>
        refine ⟨f₀, fun f hf => ?_⟩
        refine ⟨?_, ?_⟩
        · rw [exec, hstable f hf]; exact hK
        · rw [AlignedExec, hstable f hf]; exact ⟨hal' f (by omega), trivial⟩

/-! ## Blocks and conditionals

The rules need no fuel monotonicity of `AlignedExec`: the body's `wpA` gives its alignment at
every fuel from its bound on, and the construct runs its body at one fuel less.  `wpA_of_body`
is the part that `block` and `iff` share. -/

/-- An instruction whose step at fuel `f + 1` runs `body` from `s0` at fuel `f`, keeps the top
`rs` values above `below` when the body falls through or breaks to it, and passes on every other
continuation, and whose alignment is the body's. -/
theorem wpA_of_body {i : Instruction} {rest body : Program} {s0 : Locals} {rs : Nat}
    {below : List Value}
    (hstep : ∀ f, execOne (f + 1) m st s i env =
      (match exec f m st s0 body env with
       | .Fallthrough r' s' => .Fallthrough r' { s' with values := s'.values.take rs ++ below }
       | .Break 0 r' s' => .Fallthrough r' { s' with values := s'.values.take rs ++ below }
       | .Break (k + 1) r' s' => .Break k r' s'
       | other => other))
    (hal : ∀ f, AlignedOne (f + 1) m st s i env ↔ AlignedExec f m st s0 body env)
    (h : wpA m body
          (fun c => match c with
            | .Fallthrough st' s' =>
              wpA m rest Q st' { s' with values := s'.values.take rs ++ below } env
            | .Break 0 st' s' =>
              wpA m rest Q st' { s' with values := s'.values.take rs ++ below } env
            | .Break (k + 1) st' s' => Q (.Break k st' s')
            | other => Q other)
          st s0 env) :
    wpA m (i :: rest) Q st s env := by
  obtain ⟨Nb, hNb⟩ := h
  have hOne : ∀ f, Nb ≤ f → AlignedOne (f + 1) m st s i env :=
    fun f hf => (hal f).mpr (hNb f hf).2
  by_cases hOOF : ∀ f ≥ Nb, exec f m st s0 body env = .OutOfFuel
  · have hQ : Q .OutOfFuel := by
      have := (hNb Nb (Nat.le_refl _)).1
      rwa [hOOF Nb (Nat.le_refl _)] at this
    refine ⟨Nb + 1, fun F hF => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
    have hs : execOne (f + 1) m st s i env = .OutOfFuel := by
      rw [hstep, hOOF f (by omega)]
    refine ⟨?_, ?_⟩
    · rw [exec, hs]; exact hQ
    · rw [AlignedExec, hs]; exact ⟨hOne f (by omega), trivial⟩
  · push Not at hOOF
    obtain ⟨f₀, hf₀, hne⟩ := hOOF
    have hstable : ∀ f ≥ f₀, exec f m st s0 body env = exec f₀ m st s0 body env :=
      fun f hf => exec_fuel_mono hf hne
    have hQb := (hNb f₀ hf₀).1
    generalize hc : exec f₀ m st s0 body env = c at hstable hQb hne
    cases c with
    | Fallthrough st' s' =>
      obtain ⟨Nr, hNr⟩ := hQb
      refine ⟨f₀ + Nr + 1, fun F hF => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
      have hs : execOne (f + 1) m st s i env =
          .Fallthrough st' { s' with values := s'.values.take rs ++ below } := by
        rw [hstep, hstable f (by omega)]
      have hr := hNr (f + 1) (by omega)
      refine ⟨?_, ?_⟩
      · rw [exec, hs]; exact hr.1
      · rw [AlignedExec, hs]; exact ⟨hOne f (by omega), hr.2⟩
    | Break n st' s' =>
      cases n with
      | zero =>
        obtain ⟨Nr, hNr⟩ := hQb
        refine ⟨f₀ + Nr + 1, fun F hF => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
        have hs : execOne (f + 1) m st s i env =
            .Fallthrough st' { s' with values := s'.values.take rs ++ below } := by
          rw [hstep, hstable f (by omega)]
        have hr := hNr (f + 1) (by omega)
        refine ⟨?_, ?_⟩
        · rw [exec, hs]; exact hr.1
        · rw [AlignedExec, hs]; exact ⟨hOne f (by omega), hr.2⟩
      | succ k =>
        refine ⟨f₀ + 1, fun F hF => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
        have hs : execOne (f + 1) m st s i env = .Break k st' s' := by
          rw [hstep, hstable f (by omega)]
        refine ⟨?_, ?_⟩
        · rw [exec, hs]; exact hQb
        · rw [AlignedExec, hs]; exact ⟨hOne f (by omega), trivial⟩
    | OutOfFuel => exact absurd rfl hne
    | Return _ _ | Trap _ _ | Invalid _ | ReturnCall _ _ _ | Throwing _ _ _ _ =>
      refine ⟨f₀ + 1, fun F hF => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
      have hs := hstep f
      rw [hstable f (by omega)] at hs
      refine ⟨?_, ?_⟩
      · rw [exec, hs]; exact hQb
      · rw [AlignedExec, hs]; exact ⟨hOne f (by omega), trivial⟩

theorem wpA_block_cons {ps rs : Nat} {pt rt : List ValueType} {body rest : Program}
    (h : wpA m body
          (fun c => match c with
            | .Fallthrough st' s' =>
              wpA m rest Q st' { s' with values := s'.values.take rs ++ s.values.drop ps } env
            | .Break 0 st' s' =>
              wpA m rest Q st' { s' with values := s'.values.take rs ++ s.values.drop ps } env
            | .Break (k + 1) st' s' => Q (.Break k st' s')
            | other => Q other)
          st s env) :
    wpA m (.block ps rs body pt rt :: rest) Q st s env :=
  wpA_of_body (fun f => by rw [execOne.eq_def]; rfl) (fun f => by simp only [AlignedOne]) h

/-- The rule for `iff`, with any block types: the branch that the condition selects runs as a
block's body. -/
theorem wpA_iff_cons {ps rs : Nat} {pt rt : List ValueType} {thn els rest : Program}
    {c : UInt32} {vs : List Value} (hStack : s.values = .i32 c :: vs)
    (h : wpA m (if c ≠ 0 then thn else els)
          (fun cont => match cont with
            | .Fallthrough st' s' =>
              wpA m rest Q st' { s' with values := s'.values.take rs ++ vs.drop ps } env
            | .Break 0 st' s' =>
              wpA m rest Q st' { s' with values := s'.values.take rs ++ vs.drop ps } env
            | .Break (k + 1) st' s' => Q (.Break k st' s')
            | other => Q other)
          st { s with values := vs } env) :
    wpA m (.iff ps rs thn els pt rt :: rest) Q st s env :=
  wpA_of_body (fun f => by rw [execOne.eq_def]; simp only [hStack]; rfl)
    (fun f => by simp only [AlignedOne, hStack]) h

end

end LeanExe.ProofKit
