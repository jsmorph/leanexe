import Verified.Source
import LeanExe.IR.DenoteFrame

namespace Verified.WGSL

abbrev Locals := Nat → Option Wasm.Value
abbrev Arrays := Nat → Option (Array UInt64)

inductive Rep : Ty → Type where
  | word (value : LeanExe.IR.Expr .u64) : Rep .word
  | bool (value : LeanExe.IR.Expr .bool) : Rep .bool
  | float32 (value : LeanExe.IR.Expr .f32) : Rep .float32
  | words (index : Nat) (size : Option (LeanExe.IR.Expr .u64)) : Rep (.array .word)
  | bools (index : Nat) (size : Option (LeanExe.IR.Expr .u64)) : Rep (.array .bool)
  | floats32 (index : Nat) (size : Option (LeanExe.IR.Expr .u64)) : Rep (.array .float32)

def sizeHolds (size : Option (LeanExe.IR.Expr .u64)) (locals : Locals) (arrays : Arrays)
    (n : Nat) : Prop :=
  ∀ e, size = some e → e.denote locals arrays = some n.toUInt64

def Rep.Holds : {t : Ty} → Rep t → Locals → Arrays → t.denote → Prop
  | _, .word e, locals, arrays, value => e.denote locals arrays = some value
  | _, .bool e, locals, arrays, value => e.denote locals arrays = some value
  | _, .float32 e, locals, arrays, value => e.denote locals arrays = some value.toBits
  | _, .words index size, locals, arrays, value =>
      arrays index = some value ∧ sizeHolds size locals arrays value.size
  | _, .bools index size, locals, arrays, value =>
      arrays index = some (value.map boolWord) ∧ sizeHolds size locals arrays value.size
  | _, .floats32 index size, locals, arrays, value =>
      arrays index = some (value.map fun x => x.toBits.toUInt64) ∧
        sizeHolds size locals arrays value.size

def sizeLocals : Option (LeanExe.IR.Expr .u64) → Nat
  | none => 0
  | some e => e.denoteLocals

def Rep.locals : {t : Ty} → Rep t → Nat
  | _, .word e | _, .bool e | _, .float32 e => e.denoteLocals
  | _, .words _ size | _, .bools _ size | _, .floats32 _ size => sizeLocals size

theorem sizeHolds.congr {size : Option (LeanExe.IR.Expr .u64)} {locals next : Locals}
    {arrays : Arrays} {n base : Nat} (h : sizeHolds size locals arrays n)
    (bound : sizeLocals size ≤ base) (same : ∀ j, j < base → next j = locals j) :
    sizeHolds size next arrays n := by
  intro e he
  cases he
  rw [LeanExe.IR.Expr.denote_congr e locals next arrays (fun j hj => same j (by
    simp only [sizeLocals] at bound
    omega))]
  exact h e rfl

theorem Rep.Holds.congr {t : Ty} {rep : Rep t} {locals next : Locals} {arrays : Arrays}
    {value : t.denote} {base : Nat} (h : rep.Holds locals arrays value)
    (bound : rep.locals ≤ base) (same : ∀ j, j < base → next j = locals j) :
    rep.Holds next arrays value := by
  cases rep with
  | word e | bool e | float32 e =>
      exact (LeanExe.IR.Expr.denote_congr e locals next arrays
        (fun j hj => same j (by simp only [Rep.locals] at bound; omega))).trans h
  | words index size | bools index size | floats32 index size =>
      exact ⟨h.1, h.2.congr bound same⟩

inductive Context : List Ty → Type where
  | nil : Context []
  | cons (rep : Rep t) (rest : Context Γ) : Context (t :: Γ)

def Context.get : {Γ : List Ty} → {t : Ty} → Context Γ → Var Γ t → Rep t
  | _, _, .cons rep _, .here => rep
  | _, _, .cons _ rest, .there v => rest.get v

def Context.Bounded (ctx : Context Γ) (base : Nat) : Prop :=
  ∀ t (v : Var Γ t), (ctx.get v).locals ≤ base

def Context.Agrees (ctx : Context Γ) (env : Verified.Env Γ) (locals : Locals)
    (arrays : Arrays) : Prop :=
  ∀ t (v : Var Γ t), (ctx.get v).Holds locals arrays (env.get v)

theorem Context.Bounded.mono {ctx : Context Γ} {base next : Nat}
    (h : ctx.Bounded base) (hle : base ≤ next) : ctx.Bounded next :=
  fun t v => Nat.le_trans (h t v) hle

theorem Context.Bounded.cons {ctx : Context Γ} {rep : Rep t} {base : Nat}
    (h : ctx.Bounded base) (bound : rep.locals ≤ base) :
    (Context.cons rep ctx).Bounded base := by
  intro s v
  cases v with
  | here => exact bound
  | there v => exact h s v

theorem Context.Agrees.cons {ctx : Context Γ} {rep : Rep t} {env : Verified.Env Γ}
    {locals : Locals} {arrays : Arrays} {value : t.denote}
    (h : ctx.Agrees env locals arrays) (valueHolds : rep.Holds locals arrays value) :
    (Context.cons rep ctx).Agrees (.cons value env) locals arrays := by
  intro s v
  cases v with
  | here => exact valueHolds
  | there v => exact h s v

theorem Context.Agrees.frame {ctx : Context Γ} {env : Verified.Env Γ}
    {locals next : Locals} {arrays : Arrays} {base : Nat}
    (h : ctx.Agrees env locals arrays) (bound : ctx.Bounded base)
    (same : ∀ j, j < base → next j = locals j) : ctx.Agrees env next arrays :=
  fun t v => (h t v).congr (bound t v) same

end Verified.WGSL
