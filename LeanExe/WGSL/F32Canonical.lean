import LeanExe.WGSL.Semantics

namespace LeanExe.WGSL

def nanBits (bits : UInt32) : Bool :=
  decide ((0xff000000 : UInt32) < bits * 2)

theorem nanBits_eq (bits : UInt32) : nanBits bits = Wasm.IEEE32.isNaN bits := by
  apply Bool.eq_iff_iff.mpr
  simp only [nanBits, decide_eq_true_eq, Bool.and_eq_true,
    UInt32.lt_iff_toNat_lt, UInt32.toNat_mul, UInt32.reduceToNat,
    Wasm.IEEE32.isNaN, Wasm.IEEE32.exponent,
    Wasm.IEEE32.fraction, beq_iff_eq, bne_iff_ne]
  have := bits.toNat_lt
  omega

def nanExpr (bits : Expr) : Expr :=
  .bin .lt (.lit 0xff000000) (.bin .mul bits (.lit 2))

def canonical32 (bits : UInt32) : UInt32 :=
  if Wasm.IEEE32.isNaN bits then Wasm.IEEE32.canonicalNaN else bits

def canonicalF32 (value : Expr) : Expr :=
  .toF32 (.select (.toU32 value) (.lit 0x7fc00000) (nanExpr (.toU32 value)))

theorem eval_nanExpr (ctx : Context) (env : Env) (e : Expr) (bits : UInt32)
    (h : e.eval ctx env = some (.u32 bits)) :
    (nanExpr e).eval ctx env = some (.bool (Wasm.IEEE32.isNaN bits)) := by
  rw [← nanBits_eq bits]
  simp [nanExpr, nanBits, Expr.eval, BinOp.apply, h]

theorem eval_canonicalF32 (ctx : Context) (env : Env) (e : Expr) (bits : UInt32)
    (h : e.eval ctx env = some (.f32 bits)) :
    (canonicalF32 e).eval ctx env = some (.f32 (canonical32 bits)) := by
  have hn := eval_nanExpr ctx env (.toU32 e) bits (by simp [Expr.eval, h])
  simp only [canonicalF32, Expr.eval, h, hn, Value.sameType]
  cases hi : Wasm.IEEE32.isNaN bits <;> simp [canonical32, hi, Wasm.IEEE32.canonicalNaN]

end LeanExe.WGSL
