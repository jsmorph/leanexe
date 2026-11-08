import LeanExe.A64.Proof.Machine
import LeanExe.ProofKit.Typed
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

export LeanExe.ProofKit (HasType Typed Typed.length Typed.cons Typed.tail Typed.drop Typed.take
  Typed.append Typed.getElem Typed.set Typed.reverse)

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

/-- No register of a height is X18, which holds the stack's limit. -/
theorem regOf_ne_18 : ∀ k < 26, regOf k ≠ 18 := by decide

theorem regOf_ne_17 : ∀ k < 26, regOf k ≠ 17 := by decide

theorem regOf_ne_29 : ∀ k < 26, regOf k ≠ 29 := by decide

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

/-- The stack at SP: SP is a multiple of 16, and the stack's limit in X18 lies from 4096 up to SP,
with the bytes from it to SP Normal memory, while SP lies below `2 ^ 63`. -/
structure StackOk (P : Platform) (s : State) : Prop where
  aligned : s.sp % 16 = 0
  limit : 4096 ≤ (s.x 18).toNat ∧ (s.x 18).toNat ≤ s.sp.toNat ∧ s.sp.toNat < 2 ^ 63
  below : ∀ j < (s.sp - s.x 18).toNat, P.normal (s.x 18 + UInt64.ofNat j) = true

/-- The frame at `SP` of a function with `n` locals, parameters included: SP is a multiple of 16,
the bytes of the locals, of the spill slots above them, and of the return address's slot above
those are Normal memory, the frame has fewer than 512 slots, and the stack's limit in X18 lies
from 4096 up to SP, with the bytes from it to SP Normal memory, while SP lies below `2 ^ 63`. -/
structure FrameOk (P : Platform) (n : Nat) (s : State) : Prop where
  aligned : s.sp % 16 = 0
  mapped : ∀ j < 8 * (n + spillSlots + 1), P.normal (s.sp + UInt64.ofNat j) = true
  bound : n + spillSlots + 1 < 512
  limit : 4096 ≤ (s.x 18).toNat ∧ (s.x 18).toNat ≤ s.sp.toNat ∧ s.sp.toNat < 2 ^ 63
  below : ∀ j < (s.sp - s.x 18).toNat, P.normal (s.x 18 + UInt64.ofNat j) = true

/-- `StackOk` depends on SP and X18 alone. -/
theorem StackOk.congr {P : Platform} {s s' : State} (h : StackOk P s) (hsp : s'.sp = s.sp)
    (h18 : s'.x 18 = s.x 18) : StackOk P s' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hsp]; exact h.aligned
  · rw [hsp, h18]; exact h.limit
  · rw [hsp, h18]; exact h.below

theorem FrameOk.stack {P : Platform} {n : Nat} {s : State} (h : FrameOk P n s) : StackOk P s :=
  ⟨h.aligned, h.limit, h.below⟩

/-- `FrameOk` depends on SP and X18 alone. -/
theorem FrameOk.congr {P : Platform} {n : Nat} {s s' : State} (h : FrameOk P n s)
    (hsp : s'.sp = s.sp) (h18 : s'.x 18 = s.x 18) : FrameOk P n s' := by
  refine ⟨?_, ?_, h.bound, ?_, ?_⟩
  · rw [hsp]; exact h.aligned
  · rw [hsp]; exact h.mapped
  · rw [hsp, h18]; exact h.limit
  · rw [hsp, h18]; exact h.below

/-- An address outside the bytes from the stack's limit to the end of a frame's spill slots lies
outside the frame's first `m` slots. -/
theorem FrameOk.outside {P : Platform} {n : Nat} {s : State} (hf : FrameOk P n s) {a : UInt64}
    {m : Nat} (hm : m ≤ n + spillSlots) (h : s.sp.toNat + 8 * (n + spillSlots) ≤ a.toNat) :
    ¬ a - s.sp < UInt64.ofNat (8 * m) := by
  intro hc
  obtain ⟨h1, h2, h3⟩ := hf.limit
  have hb := hf.bound
  have ha := a.toNat_lt
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, UInt64.toNat_ofNat'] at hc
  simp only [Nat.reducePow] at *
  omega

/-- The relation at a point of a function whose locals, parameters included, have the types
`lts`, with an operand stack of the types `σ`, top first. -/
structure Inv (P : Platform) (lts σ : List ValueType) (sl : Locals) (s : State) : Prop where
  stack : StackRel s sl.values
  locals : LocalsRel s (sl.params ++ sl.locals)
  count : (sl.params ++ sl.locals).length = lts.length
  frame : FrameOk P lts.length s
  types : Typed σ sl.values
  ltypes : Typed lts (sl.params ++ sl.locals)

theorem Inv.aligned {P : Platform} {lts σ : List ValueType} {sl : Locals} {s : State}
    (h : Inv P lts σ sl s) : s.sp % 16 = 0 := h.frame.aligned

theorem Inv.mapped {P : Platform} {lts σ : List ValueType} {sl : Locals} {s : State}
    (h : Inv P lts σ sl s) : ∀ j < 8 * lts.length, P.normal (s.sp + UInt64.ofNat j) = true :=
  fun j hj => h.frame.mapped j (by omega)

theorem Inv.bound {P : Platform} {lts σ : List ValueType} {sl : Locals} {s : State}
    (h : Inv P lts σ sl s) : lts.length < 512 := by
  have := h.frame.bound; omega

theorem Inv.len {P : Platform} {lts σ : List ValueType} {sl : Locals} {s : State}
    (h : Inv P lts σ sl s) : sl.values.length = σ.length := h.types.length.symm

/-- The registers of the heights below `b` keep their values from `s` to `s'`. -/
def Frame (b : Nat) (s s' : State) : Prop :=
  ∀ k < b, s'.x (regOf k) = s.x (regOf k)

/-- The machine holds Talos's store `st` in the area at X17, below the stack's limit in X18: the
memory's size less 8 at X17, global `i`, of the type `gts[i]`, at `X17 + 8 (i + 1)`, and byte `j`
of the memory at `X17 + 4096 + j` for every `j` below `cap` pages.  The memory's cap is `cap`
pages, below 4096, and it holds at least 1 page, and the globals are at most 511. -/
structure StoreRel (P : Platform) (cap : Nat) (gts : List ValueType) {α : Type} (st : Store α)
    (s : State) : Prop where
  caps : st.memoryCaps = [cap]
  cap_lt : cap < 4096
  glen : gts.length ≤ 511
  pages : 1 ≤ st.mem.pages ∧ st.mem.pages ≤ cap
  size : load64 s.mem (s.x 17) = UInt64.ofNat (st.mem.pages * 65536 - 8)
  types : Typed gts st.globals.globals
  globals : ∀ i (hi : i < st.globals.globals.length),
    ValRel st.globals.globals[i] (load64 s.mem (s.x 17 + UInt64.ofNat (8 * (i + 1))))
  bytes : ∀ j < cap * 65536, s.mem (s.x 17 + UInt64.ofNat (4096 + j)) = st.mem.bytes j
  mapped : ∀ j < areaSize cap, P.normal (s.x 17 + UInt64.ofNat j) = true
  below : (s.x 17).toNat + areaSize cap ≤ (s.x 18).toNat

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

@[simp] theorem x_setD {s : State} {r q : Fin 32} {v : UInt64} : (s.setD r v).x q = s.x q := rfl

@[simp] theorem setD_sp {s : State} {r : Fin 32} {v : UInt64} : (s.setD r v).sp = s.sp := rfl

@[simp] theorem setD_mem {s : State} {r : Fin 32} {v : UInt64} : (s.setD r v).mem = s.mem := rfl

@[simp] theorem setD_out {s : State} {r : Fin 32} {v : UInt64} : (s.setD r v).out = s.out := rfl

@[simp] theorem setD_pc {s : State} {r : Fin 32} {v : UInt64} : (s.setD r v).pc = s.pc := rfl

theorem dregs_setD_same (s : State) (r : Fin 32) (v : UInt64) : (s.setD r v).dregs r = v := by
  simp [setD]

theorem dregs_setD_ne (s : State) {r q : Fin 32} (v : UInt64) (h : q ≠ r) :
    (s.setD r v).dregs q = s.dregs q := by
  simp [setD, h]

end State

end LeanExe.A64
