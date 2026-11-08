import Verified.Kernel.Code
import LeanExe.ProofKit.F32Bits

namespace Verified.Kernel

open LeanExe.ProofKit

def Rep.wordExpr : Rep .word → LeanExe.Source.Expr .u64
  | .word e => e

def Rep.boolExpr : Rep .bool → LeanExe.Source.Expr .bool
  | .bool e => e

def Rep.float32Expr : Rep .float32 → LeanExe.Source.Expr .f32
  | .float32 e => e

/-- The kernel language's operation of a word operation, or `none` for the arithmetic shift,
which the kernel language lacks. -/
def binOp : BinOp → Option LeanExe.Source.U64Op
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .div => some .divU
  | .rem => some .remU
  | .and => some .bitAnd
  | .or => some .bitOr
  | .xor => some .bitXor
  | .shl => some .shiftLeft
  | .shr => some .shiftRight
  | .sar => none

theorem binOp_apply {op : BinOp} {k : LeanExe.Source.U64Op} (hk : binOp op = some k)
    (a b : UInt64) : k.apply a b = op.apply a b := by
  cases op <;> simp only [binOp, Option.some.injEq, reduceCtorEq] at hk <;> subst hk <;>
    simp [LeanExe.Source.U64Op.apply, BinOp.apply,
      ← UInt64.shiftLeft_eq_shiftLeft_mod, ← UInt64.shiftRight_eq_shiftRight_mod]
  all_goals
    intro hb
    subst b
    apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_div, UInt64.toNat_mod]

/-- The kernel language's comparison of a word comparison, or `none` for the signed
comparisons, which the kernel language lacks. -/
def cmpExpr : CmpOp →
    Option (LeanExe.Source.Expr .u64 → LeanExe.Source.Expr .u64 → LeanExe.Source.Expr .bool)
  | .eq => some .eq
  | .ne => some .ne
  | .lt => some .ltU
  | .le => some .leU
  | .slt | .sle => none

def fbinOp : FBinOp → LeanExe.Source.F32Op
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .div

def fcmpExpr (op : FCmpOp) (a b : LeanExe.Source.Expr .f32) : LeanExe.Source.Expr .bool :=
  match op with
  | .eq => .eqF32 a b
  | .lt => .ltF32 a b
  | .le => .leF32 a b

variable {ctx : Context Γ} {base : Nat} {S : List Sig}

def Code.word (v : UInt64) : Code ctx base (S := S) (t := .word) (fun _ _ => v) :=
  .atom (.word (.const v)) (Nat.zero_le _) (fun _ _ _ _ _ => rfl)

def Code.bool (v : Bool) : Code ctx base (S := S) (t := .bool) (fun _ _ => v) :=
  .atom (.bool (.bconst v)) (Nat.zero_le _) (fun _ _ _ _ _ => rfl)

def Code.float32 (bits : UInt32) :
    Code ctx base (S := S) (t := .float32) (fun _ _ => Float32.ofBits bits) :=
  .atom (.float32 (.constF32 (Float32.ofBits bits).toBits)) (Nat.zero_le _)
    (fun _ _ _ _ _ => rfl)

def Code.var (v : Var Γ t) (bound : ctx.Bounded base) :
    Code ctx base (S := S) (t := t) (fun _ env => env.get v) :=
  .atom (ctx.get v) (bound _ v) (fun _ _ _ _ agree => agree _ v)

def Code.bin (op : BinOp) {k : LeanExe.Source.U64Op} (hk : binOp op = some k)
    {left right : Funs S → Verified.Env Γ → UInt64}
    (a : Code ctx base (t := .word) left) (b : Code ctx a.next (t := .word) right) :
    Code ctx base (t := .word) (fun funs env => op.apply (left funs env) (right funs env)) :=
  a.map₂ b op.apply (fun l r => .word (.bin k l.wordExpr r.wordExpr))
    (by intro l r; cases l; cases r; exact Nat.le_refl _)
    (by
      intro l r locals arrays x y hl hr
      cases l; cases r
      simp only [Rep.Holds] at hl hr
      simpa [Rep.Holds, Rep.wordExpr, LeanExe.Source.Expr.denote, hl, hr, binOp_apply hk])

def Code.cmp (op : CmpOp)
    {f : LeanExe.Source.Expr .u64 → LeanExe.Source.Expr .u64 → LeanExe.Source.Expr .bool}
    (hf : cmpExpr op = some f) {left right : Funs S → Verified.Env Γ → UInt64}
    (a : Code ctx base (t := .word) left) (b : Code ctx a.next (t := .word) right) :
    Code ctx base (t := .bool) (fun funs env => op.apply (left funs env) (right funs env)) :=
  a.map₂ b op.apply (fun l r => .bool (f l.wordExpr r.wordExpr))
    (by
      intro l r; cases l; cases r
      cases op <;> simp only [cmpExpr, Option.some.injEq, reduceCtorEq] at hf <;> subst hf <;>
        exact Nat.le_refl _)
    (by
      intro l r locals arrays x y hl hr
      cases l; cases r
      simp only [Rep.Holds] at hl hr
      cases op <;> simp only [cmpExpr, Option.some.injEq, reduceCtorEq] at hf <;> subst hf <;>
        simpa [Rep.Holds, Rep.wordExpr, LeanExe.Source.Expr.denote, hl, hr, CmpOp.apply])

def Code.not {value : Funs S → Verified.Env Γ → Bool} (a : Code ctx base (t := .bool) value) :
    Code ctx base (t := .bool) (fun funs env => !value funs env) :=
  a.map (!·) (fun r => .bool (.not r.boolExpr))
    (by intro r; cases r; exact Nat.le_refl _)
    (by intro r locals arrays x h; cases r; simpa [Rep.Holds, Rep.boolExpr,
      LeanExe.Source.Expr.denote, h])

def Code.and {left right : Funs S → Verified.Env Γ → Bool}
    (a : Code ctx base (t := .bool) left) (b : Code ctx a.next (t := .bool) right) :
    Code ctx base (t := .bool) (fun funs env => left funs env && right funs env) :=
  a.map₂ b (· && ·) (fun l r => .bool (.and l.boolExpr r.boolExpr))
    (by intro l r; cases l; cases r; exact Nat.le_refl _)
    (by
      intro l r locals arrays x y hl hr
      cases l; cases r
      simp only [Rep.Holds] at hl hr
      cases x <;>
        simp [Rep.Holds, Rep.boolExpr, LeanExe.Source.Expr.denote, hl, hr])

def Code.or {left right : Funs S → Verified.Env Γ → Bool}
    (a : Code ctx base (t := .bool) left) (b : Code ctx a.next (t := .bool) right) :
    Code ctx base (t := .bool) (fun funs env => left funs env || right funs env) :=
  a.map₂ b (· || ·) (fun l r => .bool (.or l.boolExpr r.boolExpr))
    (by intro l r; cases l; cases r; exact Nat.le_refl _)
    (by
      intro l r locals arrays x y hl hr
      cases l; cases r
      simp only [Rep.Holds] at hl hr
      cases x <;>
        simp [Rep.Holds, Rep.boolExpr, LeanExe.Source.Expr.denote, hl, hr])

def Code.fbin32 (op : FBinOp) {left right : Funs S → Verified.Env Γ → Float32}
    (a : Code ctx base (t := .float32) left) (b : Code ctx a.next (t := .float32) right) :
    Code ctx base (t := .float32) (fun funs env => op.apply32 (left funs env) (right funs env)) :=
  a.map₂ b op.apply32 (fun l r => .float32 (.binF32 (fbinOp op) l.float32Expr r.float32Expr))
    (by intro l r; cases l; cases r; exact Nat.le_refl _)
    (by
      intro l r locals arrays x y hl hr
      cases l; cases r
      simp only [Rep.Holds] at hl hr
      cases op <;>
        simpa [Rep.Holds, Rep.float32Expr, LeanExe.Source.Expr.denote, hl, hr, fbinOp,
          LeanExe.Source.F32Op.apply, FBinOp.apply32, F32Bits.toBits_add, F32Bits.toBits_sub,
          F32Bits.toBits_mul, F32Bits.toBits_div])

def Code.fcmp32 (op : FCmpOp) {left right : Funs S → Verified.Env Γ → Float32}
    (a : Code ctx base (t := .float32) left) (b : Code ctx a.next (t := .float32) right) :
    Code ctx base (t := .bool) (fun funs env => op.apply32 (left funs env) (right funs env)) :=
  a.map₂ b op.apply32 (fun l r => .bool (fcmpExpr op l.float32Expr r.float32Expr))
    (by intro l r; cases l; cases r; cases op <;> exact Nat.le_refl _)
    (by
      intro l r locals arrays x y hl hr
      cases l; cases r
      simp only [Rep.Holds] at hl hr
      cases op <;>
        simpa [Rep.Holds, Rep.float32Expr, fcmpExpr, LeanExe.Source.Expr.denote, hl, hr,
          FCmpOp.apply32, F32Bits.decide_lt, F32Bits.decide_le, F32Bits.beq_eq])

end Verified.Kernel
