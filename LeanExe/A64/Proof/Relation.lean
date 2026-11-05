import LeanExe.A64.Proof.Machine
import Interpreter.Wasm.Semantics

/-!
The relation of the simulation proof between a Talos frame and a state of the AArch64 model, at
a point of a function's code whose operand stack has a known height.  The value at height `k`,
counted from the bottom, lies in the register `regOf k`; local `i` lies in the 8 bytes at
`SP + 8 * i`, whose bytes are Normal memory; and `SP` is a multiple of 16.  `ValRel` relates a
Talos value to a 64-bit register or memory word: an `i32` or an `f32` zero-extended, an `i64` or
an `f64` as is.
-/

namespace LeanExe.A64

open Wasm

/-- The register of height `k`, which `opReg k` gives for the 26 heights that have one. -/
def regOf (k : Nat) : Fin 32 := ⟨opRegs.getD k 0 % 32, Nat.mod_lt _ (by decide)⟩

theorem opRegs_length : opRegs.length = 26 := by decide

theorem opReg_ok {k : Nat} (h : k < 26) : opReg k = .ok (regOf k) := by
  rw [← opRegs_length] at h
  simp [opReg, regOf, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD]
  rfl

theorem opReg_error {k : Nat} (h : ¬ k < 26) : ∃ e, opReg k = .error e := by
  have : opRegs[k]? = none := List.getElem?_eq_none (by rw [opRegs_length]; omega)
  exact ⟨_, by simp only [opReg, this]; rfl⟩

theorem regOf_lt_31 : ∀ k < 26, (regOf k).val < 31 := by decide

theorem regOf_ne_scratch : ∀ k < 26, regOf k ≠ scratch := by decide

theorem regOf_inj : ∀ k < 26, ∀ j < 26, regOf k = regOf j → k = j := by decide

/-- The register word `r` holds the Talos value `v`. -/
def ValRel : Value → UInt64 → Prop
  | .i32 x, r => r = x.toUInt64
  | .i64 x, r => r = x
  | .f32 x, r => r = x.toUInt64
  | .f64 x, r => r = x
  | _, _ => False

/-- The operand stack `vs`, top first, lies in the registers of its heights. -/
def StackRel (s : State) (vs : List Value) : Prop :=
  vs.length ≤ 26 ∧
    ∀ k (hk : k < vs.length), ValRel (vs.reverse[k]'(by simpa using hk)) (s.x (regOf k))

/-- The address of local `i` in the frame at `sp`. -/
def slotAddr (sp : UInt64) (i : Nat) : UInt64 := sp + 8 * UInt64.ofNat i

/-- The locals `ls` lie in the frame at `SP`. -/
def LocalsRel (s : State) (ls : List Value) : Prop :=
  ∀ i (hi : i < ls.length), ValRel ls[i] (load64 s.mem (slotAddr s.sp i))

/-- The relation at a point of a function with `n` locals, parameters included. -/
structure Inv (P : Platform) (n : Nat) (sl : Locals) (s : State) : Prop where
  stack : StackRel s sl.values
  locals : LocalsRel s (sl.params ++ sl.locals)
  count : (sl.params ++ sl.locals).length = n
  aligned : s.sp % 16 = 0
  mapped : ∀ j < 8 * n, P.normal (s.sp + UInt64.ofNat j) = true

/-- The registers of the heights below `b` keep their values from `s` to `s'`. -/
def Frame (b : Nat) (s s' : State) : Prop :=
  ∀ k < b, s'.x (regOf k) = s.x (regOf k)

namespace State

theorem x_setX_same {s : State} {r : Fin 32} {v : UInt64} (h : r.val < 31) :
    (s.setX r v).x r = v := by
  simp [setX, x, h]

theorem x_setX_ne {s : State} {r q : Fin 32} {v : UInt64} (h : r ≠ q) :
    (s.setX r v).x q = s.x q := by
  unfold setX x
  by_cases hr : r.val < 31
  · have : q.val ≠ r.val := fun e => h (Fin.ext e.symm)
    simp [hr, this]
  · simp [hr]

@[simp] theorem setX_sp {s : State} {r : Fin 32} {v : UInt64} : (s.setX r v).sp = s.sp := by
  unfold setX; split <;> rfl

@[simp] theorem setX_mem {s : State} {r : Fin 32} {v : UInt64} :
    (s.setX r v).mem = s.mem := by
  unfold setX; split <;> rfl

@[simp] theorem setX_out {s : State} {r : Fin 32} {v : UInt64} :
    (s.setX r v).out = s.out := by
  unfold setX; split <;> rfl

@[simp] theorem setX_pc {s : State} {r : Fin 32} {v : UInt64} : (s.setX r v).pc = s.pc := by
  unfold setX; split <;> rfl

end State

end LeanExe.A64
