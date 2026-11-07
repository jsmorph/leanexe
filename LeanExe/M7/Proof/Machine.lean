import LeanExe.M7.Encode

/-!
Facts about runs of the Cortex-M7 model that the proofs about emitted code use: `Reach`, the states
that zero or more steps reach; `codeSize`, the bytes of a list of instructions; `CodeAt`,
instructions placed at an address in the halfwords that `encode` gives; and the step at a placed
instruction, which executes it.  Addresses are 32-bit words, so code that a theorem places at `a`
covers the addresses `a + UInt32.ofNat k`, which wrap at 2^32 as the processor's do.
-/

namespace LeanExe.M7

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-- The states that zero or more steps reach from a state. -/
inductive Reach (P : Platform) (σ : Nat → UInt32) (code : UInt32 → Option UInt16) :
    State → State → Prop
  | refl (s : State) : Reach P σ code s s
  | next {s t u : State} : step P σ code s = some t → Reach P σ code t u → Reach P σ code s u

theorem Reach.trans {s t u : State} (h1 : Reach P σ code s t) (h2 : Reach P σ code t u) :
    Reach P σ code s u := by
  induction h1 with
  | refl => exact h2
  | next hs _ ih => exact .next hs (ih h2)

theorem Reach.single {s t : State} (h : step P σ code s = some t) : Reach P σ code s t :=
  .next h (.refl t)

/-- The bytes of the instruction `i`: 2 for `BX LR` and 4 for every other form. -/
def Instr.size : Instr → Nat
  | .bxLr => 2
  | _ => 4

theorem size_bcondTo (c : Fin 14) (off : Int) : (Instr.bcondTo c off).size = 4 := rfl

theorem size_lslBy (d m : Fin 8) (k : Nat) : (Instr.lslBy d m k).size = 4 := rfl

theorem size_lsrBy (d m : Fin 8) (k : Nat) : (Instr.lsrBy d m k).size = 4 := rfl

theorem size_addLsl (sf : Fin 2) (d n m : Fin 8) (k : Nat) : (Instr.addLsl sf d n m k).size = 4 :=
  rfl

/-- The bytes of the instructions `is`. -/
def codeSize (is : List Instr) : Nat := (is.map Instr.size).sum

theorem codeSize_nil : codeSize [] = 0 := rfl

theorem codeSize_cons (i : Instr) (is : List Instr) :
    codeSize (i :: is) = i.size + codeSize is := by
  simp [codeSize]

theorem codeSize_append (l1 l2 : List Instr) : codeSize (l1 ++ l2) = codeSize l1 + codeSize l2 := by
  simp [codeSize]

theorem length_encode (i : Instr) : 2 * (encode i).length = i.size := by
  by_cases h : i = .bxLr
  · subst h; rfl
  · rw [length_encode_of_ne h]
    cases i <;> first | rfl | exact absurd rfl h

theorem length_flatMap_encode (is : List Instr) : 2 * (is.flatMap encode).length = codeSize is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      rw [List.flatMap_cons, List.length_append, Nat.mul_add, ih, length_encode, codeSize_cons]

theorem add_ofNat_add (a : UInt32) (x y : Nat) :
    a + UInt32.ofNat x + UInt32.ofNat y = a + UInt32.ofNat (x + y) := by
  rw [UInt32.ofNat_add, UInt32.add_assoc]

/-- The halfwords `hs` lie at `a`, the first at `a` and each at the next halfword's address. -/
def HalfsAt (code : UInt32 → Option UInt16) (a : UInt32) (hs : List UInt16) : Prop :=
  ∀ k (h : k < hs.length), code (a + UInt32.ofNat (2 * k)) = some hs[k]

theorem HalfsAt.append {a : UInt32} {l1 l2 : List UInt16} :
    HalfsAt code a (l1 ++ l2) ↔
      HalfsAt code a l1 ∧ HalfsAt code (a + UInt32.ofNat (2 * l1.length)) l2 := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have := h k (by simp; omega)
      rwa [List.getElem_append_left hk] at this
    · have := h (l1.length + k) (by simp; omega)
      rw [add_ofNat_add, ← Nat.mul_add]
      simpa [List.getElem_append] using this
  · rintro ⟨h1, h2⟩ k hk
    by_cases hl : k < l1.length
    · rw [List.getElem_append_left hl]
      exact h1 k hl
    · have hk2 : k - l1.length < l2.length := by simp at hk; omega
      have := h2 (k - l1.length) hk2
      rw [add_ofNat_add, ← Nat.mul_add, Nat.add_sub_cancel' (by omega)] at this
      rw [List.getElem_append_right (by omega)]
      exact this

/-- The instructions `is` lie at `a`, each in the halfwords that `encode` gives and each after the
one before it. -/
def CodeAt (code : UInt32 → Option UInt16) (a : UInt32) (is : List Instr) : Prop :=
  HalfsAt code a (is.flatMap encode)

theorem CodeAt.append {a : UInt32} {l1 l2 : List Instr} :
    CodeAt code a (l1 ++ l2) ↔
      CodeAt code a l1 ∧ CodeAt code (a + UInt32.ofNat (codeSize l1)) l2 := by
  unfold CodeAt
  rw [List.flatMap_append, HalfsAt.append, length_flatMap_encode]

theorem CodeAt.at_eq {a b : UInt32} {is : List Instr} (h : CodeAt code a is) (e : a = b) :
    CodeAt code b is := e ▸ h

theorem CodeAt.cons {a : UInt32} {i : Instr} {l : List Instr} :
    CodeAt code a (i :: l) ↔ CodeAt code a [i] ∧ CodeAt code (a + UInt32.ofNat i.size) l := by
  rw [show i :: l = [i] ++ l from rfl, CodeAt.append]
  simp [codeSize]

/-- At a placed instruction, a step executes it.  A 32-bit instruction's second halfword lies at
the program counter plus 2, and the decoder reads a 16-bit instruction from its first halfword
whatever follows it. -/
theorem step_at {s : State} {i : Instr} (h : CodeAt code s.pc [i]) :
    step P σ code s = exec P σ i s := by
  simp only [CodeAt, HalfsAt, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
  have hpos : 0 < (encode i).length := by unfold encode; split <;> simp
  have h0 := h 0 hpos
  rw [show s.pc + UInt32.ofNat (2 * 0) = s.pc from UInt32.add_zero s.pc] at h0
  by_cases hb : i = .bxLr
  · subst hb
    simp only [step, h0, Option.bind_eq_bind, Option.bind_some]
    rw [show (encode .bxLr)[0] :: (code (s.pc + 2)).toList =
      encode .bxLr ++ (code (s.pc + 2)).toList from rfl, decode_encode]
    rfl
  · have hl := length_encode_of_ne hb
    have h1 := h 1 (by omega)
    rw [show s.pc + UInt32.ofNat (2 * 1) = s.pc + 2 from rfl] at h1
    obtain ⟨h1', h2', he⟩ : ∃ x y, encode i = [x, y] := by
      simp only [encode, (wide_encodeNat i).mpr hb, ↓reduceIte]
      exact ⟨_, _, rfl⟩
    simp only [he, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    simp only [step, h0, h1, Option.toList_some, Option.bind_eq_bind, Option.bind_some]
    rw [show [h1', h2'] = encode i ++ [] by rw [he]; rfl, decode_encode]
    rfl

/-- A step at a placed instruction that executes, followed by more steps. -/
theorem reach_exec {s t u : State} {i : Instr} (hc : CodeAt code s.pc [i])
    (he : exec P σ i s = some t) (hr : Reach P σ code t u) : Reach P σ code s u :=
  .next (by rw [step_at hc]; exact he) hr

end LeanExe.M7
