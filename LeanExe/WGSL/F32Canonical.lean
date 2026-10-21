import LeanExe.WGSL.Semantics

namespace LeanExe.WGSL

def nanBits (bits : UInt32) : Bool :=
  (decide ((0x7f800000 : UInt32) < bits) && decide (bits < 0x80000000)) ||
    decide ((0xff800000 : UInt32) < bits)

theorem nanBits_eq (bits : UInt32) : nanBits bits = Wasm.IEEE32.isNaN bits := by
  apply Bool.eq_iff_iff.mpr
  simp only [nanBits, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    UInt32.lt_iff_toNat_lt, UInt32.reduceToNat, Wasm.IEEE32.isNaN, Wasm.IEEE32.exponent,
    Wasm.IEEE32.fraction, beq_iff_eq, bne_iff_ne]
  have := bits.toNat_lt
  omega

def nanExpr (bits : Expr) : Expr :=
  .bin .or (.bin .and (.bin .lt (.lit 0x7f800000) bits) (.bin .lt bits (.lit 0x80000000)))
    (.bin .lt (.lit 0xff800000) bits)

def canonical32 (bits : UInt32) : UInt32 :=
  if Wasm.IEEE32.isNaN bits then Wasm.IEEE32.canonicalNaN else bits

def canonicalF32 (value : Expr) : Expr :=
  .toF32 (.select (.toU32 value) (.lit 0x7fc00000) (nanExpr (.toU32 value)))

theorem eval_nanExpr (ctx : Context) (env : Env) (e : Expr) (bits : UInt32)
    (h : e.eval ctx env = some (.u32 bits)) :
    (nanExpr e).eval ctx env = some (.bool (Wasm.IEEE32.isNaN bits)) := by
  rw [← nanBits_eq bits]
  cases h1 : decide ((0x7f800000 : UInt32) < bits) <;>
    cases h2 : decide (bits < (0x80000000 : UInt32)) <;>
    cases h3 : decide ((0xff800000 : UInt32) < bits) <;>
    simp [nanExpr, nanBits, Expr.eval, BinOp.apply, h, h1, h2, h3]

theorem eval_canonicalF32 (ctx : Context) (env : Env) (e : Expr) (bits : UInt32)
    (h : e.eval ctx env = some (.f32 bits)) :
    (canonicalF32 e).eval ctx env = some (.f32 (canonical32 bits)) := by
  have hn := eval_nanExpr ctx env (.toU32 e) bits (by simp [Expr.eval, h])
  simp only [canonicalF32, Expr.eval, h, hn, Value.sameType]
  cases hi : Wasm.IEEE32.isNaN bits <;> simp [canonical32, hi, Wasm.IEEE32.canonicalNaN]

end LeanExe.WGSL
