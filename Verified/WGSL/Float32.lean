import Verified.WGSL.Scalar
import Verified.Float32Facts
import LeanExe.ProofKit.F32Nearest

namespace Verified.WGSL

open LeanExe.ProofKit

def funaryExpr (op : F32UnOp) (e : LeanExe.WGSL.Source.Expr .f32) : LeanExe.WGSL.Source.Expr .f32 :=
  match op with
  | .sqrt => .unF32 .sqrt e
  | .abs => .unF32 .abs e
  | .nearest => .unF32 .nearest e
  | .neg => .binF32 .sub (.constF32 0x80000000) e

variable {ctx : Context Γ} {base : Nat} {S : List Sig}

def Code.funary32 (op : F32UnOp) {value : Funs S → Verified.Env Γ → Float32}
    (a : Code ctx base (t := .float32) value) :
    Code ctx base (t := .float32) (fun funs env => op.apply (value funs env)) :=
  a.map op.apply (fun r => .float32 (funaryExpr op r.float32Expr))
    (by intro r; cases r; cases op <;> simp [Rep.locals, Rep.float32Expr,
      funaryExpr, LeanExe.WGSL.Source.Expr.denoteLocals])
    (by
      intro r locals arrays x h
      cases r
      simp only [Rep.Holds] at h
      cases op <;> simp [Rep.Holds, Rep.float32Expr, funaryExpr, LeanExe.WGSL.Source.Expr.denote,
        h, LeanExe.WGSL.Source.F32UnOp.apply, LeanExe.WGSL.Source.F32Op.apply, F32UnOp.apply,
        F32Bits.toBits_sqrt, F32Bits.toBits_abs, F32Bits.toBits_neg, F32Nearest.toBits_nearest])

def Code.ofBits32 {value : Funs S → Verified.Env Γ → UInt64}
    (a : Code ctx base (t := .word) value) :
    Code ctx base (t := .float32) (fun funs env => Float32.ofBits (value funs env).toUInt32) :=
  a.map (fun x => Float32.ofBits x.toUInt32)
    (fun r => .float32 (.binF32 .add (.ofBits32 r.wordExpr) (.constF32 0x80000000)))
    (by intro r; cases r; simp [Rep.locals, Rep.wordExpr, LeanExe.WGSL.Source.Expr.denoteLocals])
    (by
      intro r locals arrays x h
      cases r
      simp only [Rep.Holds] at h
      simp [Rep.Holds, Rep.wordExpr, LeanExe.WGSL.Source.Expr.denote, h,
        LeanExe.WGSL.Source.F32Op.apply, Float32Facts.add_negZero, F32Bits.toBits_ofBits])

def Code.toBits32 {value : Funs S → Verified.Env Γ → Float32}
    (a : Code ctx base (t := .float32) value) :
    Code ctx base (t := .word) (fun funs env => (value funs env).toBits.toUInt64) :=
  a.map (fun x => x.toBits.toUInt64) (fun r => .word (.toBits32 r.float32Expr))
    (by intro r; cases r; exact Nat.le_refl _)
    (by
      intro r locals arrays x h
      cases r
      simp only [Rep.Holds] at h
      simp [Rep.Holds, Rep.float32Expr, LeanExe.WGSL.Source.Expr.denote, h])

end Verified.WGSL
