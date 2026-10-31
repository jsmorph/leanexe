import Verified.WGSL.Context
import LeanExe.WGSL.Build

namespace Verified.WGSL

inductive Param : Ty → Type where
  | word : Param .word
  | bool : Param .bool
  | float32 : Param .float32
  | words : Param (.array .word)
  | bools : Param (.array .bool)
  | floats32 : Param (.array .float32)

def Param.ofTy : (t : Ty) → Option (Param t)
  | .word => some .word
  | .bool => some .bool
  | .float32 => some .float32
  | .array .word => some .words
  | .array .bool => some .bools
  | .array .float32 => some .floats32
  | _ => none

def Param.kind : {t : Ty} → Param t → LeanExe.WGSL.Kind
  | _, .word | _, .bool => .word
  | _, .float32 => .float
  | _, .words | _, .bools | _, .floats32 => .array

def Param.arg : {t : Ty} → Param t → t.denote → LeanExe.WGSL.Arg
  | _, .word, x => .word x
  | _, .bool, x => .word (boolWord x)
  | _, .float32, x => .float x.toBits
  | _, .words, xs => .array xs
  | _, .bools, xs => .array (xs.map boolWord)
  | _, .floats32, xs => .array (xs.map fun x => x.toBits.toUInt64)

theorem Param.arg_kind {t : Ty} (p : Param t) (x : t.denote) : (p.arg x).kind = p.kind := by
  cases p <;> rfl

def countSize (count : LeanExe.WGSL.Count) (index : Nat) : Option (LeanExe.WGSL.Source.Expr .u64) :=
  match count with
  | .size sizeSlot src => if index = src then some (.get sizeSlot) else none
  | .param _ => none

def Param.rep : {t : Ty} → Param t → Nat → LeanExe.WGSL.Count → Rep t
  | _, .word, index, _ => .word (.get index)
  | _, .bool, index, _ => .bool (.ne (.get index) (.const 0))
  | _, .float32, index, _ => .float32 (.getF32 index)
  | _, .words, index, count => .words index (countSize count index)
  | _, .bools, index, count => .bools index (countSize count index)
  | _, .floats32, index, count => .floats32 index (countSize count index)

theorem countSize_bound (count : LeanExe.WGSL.Count) (index base : Nat)
    (h : ∀ j, count.sizeLocal? = some j → j < base) : sizeLocals (countSize count index) ≤ base := by
  cases count with
  | param j => exact Nat.zero_le _
  | size sizeSlot src =>
      have := h sizeSlot rfl
      by_cases hi : index = src
      · simp only [countSize, hi, ↓reduceIte, sizeLocals, LeanExe.WGSL.Source.Expr.denoteLocals]
        omega
      · simp [countSize, hi, sizeLocals]

theorem Param.rep_bound {t : Ty} (p : Param t) (index base : Nat) (count : LeanExe.WGSL.Count)
    (hi : index < base) (hs : ∀ j, count.sizeLocal? = some j → j < base) :
    (p.rep index count).locals ≤ base := by
  cases p <;> simp only [Param.rep, Rep.locals, LeanExe.WGSL.Source.Expr.denoteLocals]
  all_goals first | exact countSize_bound count index base hs | omega

def argHolds (arg : LeanExe.WGSL.Arg) (index : Nat) (count : LeanExe.WGSL.Count)
    (locals : Locals) (arrays : Arrays) : Prop :=
  match arg with
  | .word v => locals index = some (.i64 v)
  | .float bits => locals index = some (.f32 bits)
  | .array xs => arrays index = some xs ∧
      ∀ sizeSlot, count = .size sizeSlot index → locals sizeSlot = some (.i64 xs.size.toUInt64)

theorem Param.rep_holds {t : Ty} (p : Param t) (x : t.denote) (index : Nat)
    (count : LeanExe.WGSL.Count) (locals : Locals) (arrays : Arrays)
    (h : argHolds (p.arg x) index count locals arrays) :
    (p.rep index count).Holds locals arrays x := by
  cases p with
  | word | float32 =>
    simp_all [argHolds, Param.arg, Param.rep, Rep.Holds, LeanExe.WGSL.Source.Expr.denote]
  | bool =>
      cases x <;> simp_all [argHolds, Param.arg, Param.rep, Rep.Holds,
        LeanExe.WGSL.Source.Expr.denote, boolWord]
  | words | bools | floats32 =>
      simp only [Param.arg, argHolds] at h
      refine ⟨h.1, ?_⟩
      cases count with
      | param j => simp [countSize, sizeHolds]
      | size sizeSlot src =>
          by_cases hi : index = src
          · subst src
            have hs : locals sizeSlot = some (.i64 x.size.toUInt64) := by
              simpa only [Array.size_map] using h.2 sizeSlot rfl
            simp [countSize, sizeHolds, LeanExe.WGSL.Source.Expr.denote, hs]
          · simp [countSize, hi, sizeHolds]

inductive Params : List Ty → Type where
  | nil : Params []
  | cons (param : Param t) (rest : Params Γ) : Params (t :: Γ)

def Params.ofTypes : (Γ : List Ty) → Option (Params Γ)
  | [] => some .nil
  | t :: rest => do pure (.cons (← Param.ofTy t) (← ofTypes rest))

def Params.kinds : {Γ : List Ty} → Params Γ → List LeanExe.WGSL.Kind
  | _, .nil => []
  | _, .cons p rest => p.kind :: rest.kinds

def Params.args : {Γ : List Ty} → Params Γ → Verified.Env Γ → List LeanExe.WGSL.Arg
  | _, .nil, .nil => []
  | _, .cons p rest, .cons x env => p.arg x :: rest.args env

theorem Params.args_kinds (params : Params Γ) (env : Verified.Env Γ) :
    (params.args env).map LeanExe.WGSL.Arg.kind = params.kinds := by
  induction params with
  | nil => cases env; rfl
  | cons p rest ih => cases env; simp [Params.args, Params.kinds, Param.arg_kind, ih]

theorem Params.kinds_length (params : Params Γ) : params.kinds.length = Γ.length := by
  induction params <;> simp_all [Params.kinds]

def Params.context (count : LeanExe.WGSL.Count) : {Γ : List Ty} → Params Γ → Nat → Context Γ
  | _, .nil, _ => .nil
  | _, .cons p rest, start => .cons (p.rep start count) (rest.context count (start + 1))

theorem Params.context_bound (params : Params Γ) (count : LeanExe.WGSL.Count) (start base : Nat)
    (hEnd : start + Γ.length ≤ base) (hSize : ∀ j, count.sizeLocal? = some j → j < base) :
    (params.context count start).Bounded base := by
  induction params generalizing start with
  | nil => intro t v; cases v
  | cons p rest ih =>
      apply (ih (start + 1) (by simp only [List.length_cons] at hEnd; omega)).cons
      exact p.rep_bound start base count (by simp only [List.length_cons] at hEnd; omega) hSize

theorem Params.context_agrees (params : Params Γ) (env : Verified.Env Γ)
    (count : LeanExe.WGSL.Count) (start : Nat) (locals : Locals) (arrays : Arrays)
    (h : ∀ j arg, (params.args env)[j]? = some arg → argHolds arg (start + j) count locals arrays) :
    (params.context count start).Agrees env locals arrays := by
  induction params generalizing start with
  | nil => intro t v; cases v
  | cons p rest ih =>
      cases env with
      | cons x env =>
          apply (ih env (start + 1) (by
            intro j arg hj
            have h' := h (j + 1) arg (by simpa only [Params.args, List.getElem?_cons_succ] using hj)
            simpa only [Nat.add_right_comm, Nat.add_assoc] using h')).cons
          exact p.rep_holds x start count locals arrays (by simpa only [Nat.add_zero] using h 0 _ rfl)

end Verified.WGSL
