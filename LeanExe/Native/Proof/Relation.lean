import LeanExe.Native.Proof.Eval
import Interpreter.Wasm.Semantics

/-!
The relation between a Talos state and a state of the translated C function, and the outcomes
that the simulation relates.

A Talos value is a C value of the same bits, `cval`.  At a point whose static stack is `σ`, the
temporary of the slot at height `h` and type `σ`'s entry holds the Talos stack's value at that
height (`StackRel`), the temporary `l<i>` holds local `i` (`LocalsRel`), the C global `lx_g<i>`
holds global `i` (`GlobalsRel`), `lx_status` is 0, and `brk` is 0.  The blocks of the globals and
`lx_status` are fixed by an environment `Env` that `EnvOk` relates to a translation.
-/

namespace LeanExe.Native

open Wasm LClight

/-! ## Values -/

/-- The C value of a Talos value. -/
def cval : Value → val
  | .i32 n => .Vint n
  | .i64 n => .Vlong n
  | .f32 b => .Vsingle b
  | .f64 b => .Vfloat b
  | _ => .Vundef

def VT.has : VT → Value → Bool
  | .i32, .i32 _ => true
  | .i64, .i64 _ => true
  | .f32, .f32 _ => true
  | .f64, .f64 _ => true
  | _, _ => false

/-- The value of `t.zero`. -/
def zval : VT → val
  | .i32 => .Vint 0
  | .i64 => .Vlong 0
  | .f32 => .Vsingle 0
  | .f64 => .Vfloat 0

theorem VT.has_ofValueType {vt : ValueType} {t : VT} (h : VT.ofValueType vt = some t) :
    t.has vt.zero = true ∧ cval vt.zero = zval t := by
  cases vt <;> simp [VT.ofValueType] at h <;> subst h <;> exact ⟨rfl, rfl⟩

theorem cast_cval {t : VT} {v : Value} (h : t.has v = true) (m : mem) :
    sem_cast (cval v) t.ty t.ty m = some (cval v) := by
  cases t <;> cases v <;> simp [VT.has] at h <;> rfl

theorem cast_zval (t : VT) (m : mem) : sem_cast (zval t) t.ty t.ty m = some (zval t) := by
  cases t <;> rfl

theorem eval_zero (A : Archi) (ge : genv) (e : env) (le : temp_env) (m : mem) (t : VT) :
    eval_expr A ge e le m t.zero (zval t) := by
  cases t
  · exact .eval_Econst_int _ _
  · exact .eval_Econst_long _ _
  · exact .eval_Econst_single _ _
  · exact .eval_Econst_float _ _

/-! ## Identifiers -/

theorem VT.code_pos (t : VT) : 1 ≤ t.code ∧ t.code ≤ 4 := by cases t <;> decide

theorem VT.code_inj {t t' : VT} (h : t.code = t'.code) : t = t' := by
  cases t <;> cases t' <;> first | rfl | simp [VT.code] at h

theorem slotId_ne_localId (h : Nat) (t : VT) (i : Nat) : slotId h t ≠ localId i := by
  have := VT.code_pos t
  show ¬ ((8 * h + t.code : Nat) = 8 * i + 8)
  omega

theorem slotId_ne_brkId (h : Nat) (t : VT) : slotId h t ≠ brkId := by
  have := VT.code_pos t
  show ¬ ((8 * h + t.code : Nat) = 5)
  omega

theorem localId_ne_brkId (i : Nat) : localId i ≠ brkId := by
  show ¬ ((8 * i + 8 : Nat) = 5)
  omega

theorem callId_ne_slotId (k h : Nat) (t : VT) : callId k ≠ slotId h t := by
  have := VT.code_pos t
  show ¬ ((8 * k + 6 : Nat) = 8 * h + t.code)
  omega

theorem callId_ne_localId (k i : Nat) : callId k ≠ localId i := by
  show ¬ ((8 * k + 6 : Nat) = 8 * i + 8)
  omega

theorem callId_ne_brkId (k : Nat) : callId k ≠ brkId := by
  show ¬ ((8 * k + 6 : Nat) = 5)
  omega

theorem slotId_ne_of_height {h h' : Nat} (t t' : VT) (hne : h ≠ h') : slotId h t ≠ slotId h' t' := by
  have := VT.code_pos t
  have := VT.code_pos t'
  show ¬ ((8 * h + t.code : Nat) = 8 * h' + t'.code)
  omega

theorem slotId_ne_of_type (h : Nat) {t t' : VT} (hne : t ≠ t') : slotId h t ≠ slotId h t' := by
  intro e
  have e' : (8 * h + t.code : Nat) = 8 * h + t'.code := e
  exact hne (VT.code_inj (by omega))

theorem localId_inj {i j : Nat} (h : localId i = localId j) : i = j := by
  have e : (8 * i + 8 : Nat) = 8 * j + 8 := h
  omega

/-! ## The relation -/

/-- The slot temporaries hold the Talos stack `vs` of static types `σ`, top first. -/
def StackRel (le : temp_env) : List VT → List Value → Prop
  | [], [] => True
  | t :: σ, v :: vs => t.has v = true ∧ le[slotId σ.length t]? = some (cval v) ∧ StackRel le σ vs
  | _, _ => False

/-- The local temporaries hold the values `vals`, the parameters and then the declared locals,
of the types `tys`. -/
def LocalsRel (le : temp_env) (tys : List VT) (vals : List Value) : Prop :=
  vals.length = tys.length ∧
    ∀ i (hi : i < tys.length), ∃ v, vals[i]? = some v ∧ tys[i].has v = true ∧
      le[localId i]? = some (cval v)

/-- The blocks of `lx_status` and of the C globals `lx_g<i>`, and the global environment. -/
structure Env where
  ge : genv
  status : block
  globals : List block

/-- The C globals hold the Talos globals `gs`, each an `i64`, and can be written. -/
def GlobalsRel (E : Env) (gs : List Value) (m : mem) : Prop :=
  gs.length = E.globals.length ∧
    ∀ i (hi : i < E.globals.length), ∃ n, gs[i]? = some (.i64 n) ∧
      Mem.load .Mint64 m E.globals[i] 0 = some (.Vlong n) ∧
      Mem.valid_access m .Mint64 E.globals[i] 0 .Writable

/-- `lx_status` holds `code` and can be written. -/
def StatusRel (E : Env) (m : mem) (code : Nat) : Prop :=
  Mem.load .Mint32 m E.status 0 = some (.Vint (UInt32.ofNat code)) ∧
    Mem.valid_access m .Mint32 E.status 0 .Writable

/-- The relation at a point whose static stack is `σ`. -/
structure Inv (E : Env) (c : FCtx) (σ : List VT) {α : Type} (st : Store α) (sl : Locals)
    (le : temp_env) (m : mem) : Prop where
  stack : StackRel le σ sl.values
  locals : LocalsRel le c.locals (sl.params ++ sl.locals)
  globals : GlobalsRel E st.globals.globals m
  status : StatusRel E m 0
  brk : le[brkId]? = some (.Vint 0)

/-- The slots below height `h` keep their values. -/
def Frame (h : Nat) (le le' : temp_env) : Prop :=
  ∀ h' < h, ∀ t, le'[slotId h' t]? = le[slotId h' t]?

/-- A branch `k` levels out: the C statement ended with `break` or `continue` for `k = 0` and
with `brk = k` and `break` otherwise, and the kept value is in the target's result slot. -/
structure BreakRel (E : Env) (c : FCtx) (L : List Label) (k : Nat) {α : Type} (st : Store α)
    (sl : Locals) (le : temp_env) (m : mem) (out : outcome) : Prop where
  target : ∃ l, L[k]? = some l ∧
    (k = 0 → out = (if l.isLoop then .Out_continue else .Out_break)) ∧
    (l.isLoop = false → ∀ t, l.result = some t →
      ∃ v, sl.values.head? = some v ∧ t.has v = true ∧ le[slotId l.base t]? = some (cval v))
  outer : k ≠ 0 → out = .Out_break
  brk : le[brkId]? = some (.Vint (UInt32.ofNat k))
  small : k < 2 ^ 31
  locals : LocalsRel le c.locals (sl.params ++ sl.locals)
  globals : GlobalsRel E st.globals.globals m
  status : StatusRel E m 0

/-- A return with the values `vs`, top first, from a function with result `r`. -/
def ReturnRel (r : Option VT) (vs : List Value) (out : outcome) : Prop :=
  match r with
  | none => out = .Out_return none
  | some t => ∃ v, vs.head? = some v ∧ t.has v = true ∧ out = .Out_return (some (cval v, t.ty))

/-- The outcome of the `return` after a trap. -/
def trapOut : Option VT → outcome
  | none => .Out_return none
  | some t => .Out_return (some (zval t, t.ty))

/-- What the C statement `s` does from `le` and `m` when Talos's instruction or body gives `r`
from the static stack `σ` under the labels `L`: `σ'` is the static stack after it, `none` when
control does not continue past it. -/
def Outcome (A : Archi) (X : ExtSem) (E : Env) (c : FCtx) (L : List Label) (σ' : Option (List VT))
    {α : Type} (r : Continuation α) (s : statement) (le : temp_env) (m : mem) : Prop :=
  match r with
  | .Fallthrough st' sl' => ∃ σ'', σ' = some σ'' ∧ curBase L ≤ σ''.length ∧ ∃ t le' m',
      exec_stmt A X E.ge empty_env le m s t le' m' .Out_normal ∧ Inv E c σ'' st' sl' le' m' ∧
      Frame (curBase L) le le'
  | .Break k st' sl' => ∃ t le' m' out,
      exec_stmt A X E.ge empty_env le m s t le' m' out ∧ BreakRel E c L k st' sl' le' m' out ∧
      ∀ l, L[k]? = some l → Frame l.base le le'
  | .Return st' vs => ∃ t le' m' out,
      exec_stmt A X E.ge empty_env le m s t le' m' out ∧ ReturnRel c.result vs out ∧
      GlobalsRel E st'.globals.globals m' ∧ StatusRel E m' 0
  | .Trap st' msg => ∃ t le' m',
      exec_stmt A X E.ge empty_env le m s t le' m' (trapOut c.result) ∧
      GlobalsRel E st'.globals.globals m' ∧ StatusRel E m' (trapCode msg) ∧ trapCode msg ≠ 0
  | .Invalid _ => True
  | .OutOfFuel => True
  | .ReturnCall _ _ _ => False
  | .Throwing _ _ _ _ => False

/-! ## Facts about the relation -/

theorem StackRel.length {le : temp_env} {σ : List VT} {vs : List Value} (h : StackRel le σ vs) :
    vs.length = σ.length := by
  induction σ generalizing vs with
  | nil => cases vs <;> simp_all [StackRel]
  | cons t σ ih =>
      cases vs with
      | nil => simp [StackRel] at h
      | cons v vs => simp only [StackRel] at h; simp [ih h.2.2]

/-- `StackRel` depends only on the slots of the heights below `σ.length`. -/
theorem StackRel.frame {le le' : temp_env} {σ : List VT} {vs : List Value}
    (h : StackRel le σ vs) (hf : Frame σ.length le le') : StackRel le' σ vs := by
  induction σ generalizing vs with
  | nil => cases vs <;> simp_all [StackRel]
  | cons t σ ih =>
      cases vs with
      | nil => simp [StackRel] at h
      | cons v vs =>
          simp only [StackRel] at h ⊢
          refine ⟨h.1, ?_, ih h.2.2 (fun h' hh t' => hf h' (by simp; omega) t')⟩
          rw [hf σ.length (by simp) t]
          exact h.2.1

theorem Frame.refl (h : Nat) (le : temp_env) : Frame h le le := fun _ _ _ => rfl

theorem Frame.trans {h : Nat} {le1 le2 le3 : temp_env} (a : Frame h le1 le2) (b : Frame h le2 le3) :
    Frame h le1 le3 := fun h' hh t => (b h' hh t).trans (a h' hh t)

theorem Frame.mono {h h' : Nat} {le le' : temp_env} (a : Frame h le le') (hle : h' ≤ h) :
    Frame h' le le' := fun x hx t => a x (by omega) t

theorem Frame.insert_slot {h : Nat} (le : temp_env) (h' : Nat) (t : VT) (v : val) (hh : h ≤ h') :
    Frame h le (le.insert (slotId h' t) v) := fun x hx t' => by
  rw [te_insert_ne _ (slotId_ne_of_height t t' (by omega))]

theorem Frame.insert_other {h : Nat} (le : temp_env) (id : ident) (v : val)
    (hid : ∀ x t, id ≠ slotId x t) : Frame h le (le.insert id v) := fun x _ t => by
  rw [te_insert_ne _ (hid x t)]

theorem LocalsRel.insert_other {le : temp_env} {tys : List VT} {vals : List Value} {id : ident}
    (v : val) (h : LocalsRel le tys vals) (hid : ∀ i, id ≠ localId i) :
    LocalsRel (le.insert id v) tys vals := by
  refine ⟨h.1, fun i hi => ?_⟩
  obtain ⟨w, hw, ht, hl⟩ := h.2 i hi
  exact ⟨w, hw, ht, by rw [te_insert_ne _ (hid i)]; exact hl⟩

theorem StackRel.insert_other {le : temp_env} {σ : List VT} {vs : List Value} {id : ident}
    (v : val) (h : StackRel le σ vs) (hid : ∀ x t, id ≠ slotId x t) :
    StackRel (le.insert id v) σ vs :=
  h.frame (Frame.insert_other le id v hid)

theorem brk_insert_slot {le : temp_env} {k : Nat} (h' : Nat) (t : VT) (v : val)
    (h : le[brkId]? = some (.Vint (UInt32.ofNat k))) :
    (le.insert (slotId h' t) v)[brkId]? = some (.Vint (UInt32.ofNat k)) := by
  rw [te_insert_ne _ (slotId_ne_brkId h' t)]; exact h

theorem brk_insert_local {le : temp_env} {k : Nat} (i : Nat) (v : val)
    (h : le[brkId]? = some (.Vint (UInt32.ofNat k))) :
    (le.insert (localId i) v)[brkId]? = some (.Vint (UInt32.ofNat k)) := by
  rw [te_insert_ne _ (localId_ne_brkId i)]; exact h

end LeanExe.Native
