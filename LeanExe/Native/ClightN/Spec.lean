-- Rendered by clightn/nsx.py from the specification of N.  Do not edit.
import LeanExe.Native.ClightN.Base

set_option autoImplicit false
set_option maxRecDepth 100000

namespace ClightN.Spec

def eqn_fadd64 : (LClight.float → (LClight.float → LClight.float)) :=
  (@LClight.Float.add LClight.Archi.aarch64)

def eqn_fsub64 : (LClight.float → (LClight.float → LClight.float)) :=
  (@LClight.Float.sub LClight.Archi.aarch64)

def eqn_fmul64 : (LClight.float → (LClight.float → LClight.float)) :=
  (@LClight.Float.mul LClight.Archi.aarch64)

def eqn_fdiv64 : (LClight.float → (LClight.float → LClight.float)) :=
  (@LClight.Float.div LClight.Archi.aarch64)

def eqn_fcmp64 : (LClight.comparison → (LClight.float → (LClight.float → Bool))) :=
  LClight.Float.cmp

def eqn_fneg64 : (LClight.float → LClight.float) :=
  LClight.Float.neg

def eqn_fabs64 : (LClight.float → LClight.float) :=
  LClight.Float.abs

def eqn_fsqrt64 : (LClight.float → LClight.float) :=
  (@LClight.Float.sqrt LClight.Archi.aarch64)

def eqn_f64_of_longu : (UInt64 → LClight.float) :=
  LClight.Float.of_longu

def eqn_f64_to_longu : (LClight.float → (Option UInt64)) :=
  LClight.Float.to_longu

def eqn_f64_of_single : (LClight.float32 → LClight.float) :=
  LClight.Float.of_single

def eqn_f64_to_single : (LClight.float → LClight.float32) :=
  LClight.Float.to_single

def eqn_fadd32 : (LClight.float32 → (LClight.float32 → LClight.float32)) :=
  (@LClight.Float32.add LClight.Archi.aarch64)

def eqn_fsub32 : (LClight.float32 → (LClight.float32 → LClight.float32)) :=
  (@LClight.Float32.sub LClight.Archi.aarch64)

def eqn_fmul32 : (LClight.float32 → (LClight.float32 → LClight.float32)) :=
  (@LClight.Float32.mul LClight.Archi.aarch64)

def eqn_fdiv32 : (LClight.float32 → (LClight.float32 → LClight.float32)) :=
  (@LClight.Float32.div LClight.Archi.aarch64)

def eqn_fcmp32 : (LClight.comparison → (LClight.float32 → (LClight.float32 → Bool))) :=
  LClight.Float32.cmp

def eqn_fneg32 : (LClight.float32 → LClight.float32) :=
  LClight.Float32.neg

def eqn_f32_of_int : (UInt32 → LClight.float32) :=
  LClight.Float32.of_int

def eqn_f32_of_intu : (UInt32 → LClight.float32) :=
  LClight.Float32.of_intu

def eqn_f32_of_longu : (UInt64 → LClight.float32) :=
  LClight.Float32.of_longu

def eqn_f32_to_int : (LClight.float32 → (Option UInt32)) :=
  LClight.Float32.to_int

def eqn_f32_to_longu : (LClight.float32 → (Option UInt64)) :=
  LClight.Float32.to_longu

inductive binop_ok : LClight.binary_operation → LClight.type → LClight.type → LClight.val →
    LClight.val → LClight.val → Prop where
  | bo_add_ul : (∀ (x : UInt64) (y : UInt64),
    (binop_ok LClight.binary_operation.Oadd
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
      (@LClight.val.Vlong y)
      (@LClight.val.Vlong
        (@ClightN.Base.r64
          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@ClightN.Base.u64 x)
            (@ClightN.Base.u64 y))))))
  | bo_sub_ul : (∀ (x : UInt64) (y : UInt64),
    (binop_ok LClight.binary_operation.Osub
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
      (@LClight.val.Vlong y)
      (@LClight.val.Vlong
        (@ClightN.Base.r64
          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@ClightN.Base.u64 x)
            (@ClightN.Base.u64 y))))))
  | bo_mul_ul : (∀ (x : UInt64) (y : UInt64),
    (binop_ok LClight.binary_operation.Omul
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
      (@LClight.val.Vlong y)
      (@LClight.val.Vlong
        (@ClightN.Base.r64
          (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@ClightN.Base.u64 x)
            (@ClightN.Base.u64 y))))))
  | bo_div_ul : (∀ (x : UInt64) (y : UInt64),
    ((¬ (@Eq _ (@ClightN.Base.u64 y) (0 : Int)))
      → (binop_ok LClight.binary_operation.Odiv
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y)
          (@LClight.val.Vlong
            (@ClightN.Base.r64 (@ClightN.Base.zdiv (@ClightN.Base.u64 x) (@ClightN.Base.u64 y)))))))
  | bo_mod_ul : (∀ (x : UInt64) (y : UInt64),
    ((¬ (@Eq _ (@ClightN.Base.u64 y) (0 : Int)))
      → (binop_ok LClight.binary_operation.Omod
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y)
          (@LClight.val.Vlong
            (@ClightN.Base.r64 (@ClightN.Base.zmod (@ClightN.Base.u64 x) (@ClightN.Base.u64 y)))))))
  | bo_and_ul : (∀ (x : UInt64) (y : UInt64),
    (binop_ok LClight.binary_operation.Oand
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
      (@LClight.val.Vlong y)
      (@LClight.val.Vlong
        (@ClightN.Base.r64 (@ClightN.Base.land (@ClightN.Base.u64 x) (@ClightN.Base.u64 y))))))
  | bo_or_ul : (∀ (x : UInt64) (y : UInt64),
    (binop_ok LClight.binary_operation.Oor
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
      (@LClight.val.Vlong y)
      (@LClight.val.Vlong
        (@ClightN.Base.r64 (@ClightN.Base.lor (@ClightN.Base.u64 x) (@ClightN.Base.u64 y))))))
  | bo_xor_ul : (∀ (x : UInt64) (y : UInt64),
    (binop_ok LClight.binary_operation.Oxor
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
      (@LClight.val.Vlong y)
      (@LClight.val.Vlong
        (@ClightN.Base.r64 (@ClightN.Base.lxor (@ClightN.Base.u64 x) (@ClightN.Base.u64 y))))))
  | bo_shl_ul : (∀ (x : UInt64) (y : UInt64),
    ((@LT.lt Int Int.instLTInt (@ClightN.Base.u64 y) (64 : Int))
      → (binop_ok LClight.binary_operation.Oshl
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y)
          (@LClight.val.Vlong
            (@ClightN.Base.r64
              (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@ClightN.Base.u64 x)
                (@ClightN.Base.pow2 (@ClightN.Base.u64 y))))))))
  | bo_shr_ul : (∀ (x : UInt64) (y : UInt64),
    ((@LT.lt Int Int.instLTInt (@ClightN.Base.u64 y) (64 : Int))
      → (binop_ok LClight.binary_operation.Oshr
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y)
          (@LClight.val.Vlong
            (@ClightN.Base.r64
              (@ClightN.Base.zdiv (@ClightN.Base.u64 x)
                (@ClightN.Base.pow2 (@ClightN.Base.u64 y))))))))
  | bo_eq_ul_1 : (∀ (x : UInt64) (y : UInt64),
    ((@Eq _ (@ClightN.Base.u64 x) (@ClightN.Base.u64 y))
      → (binop_ok LClight.binary_operation.Oeq
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_eq_ul_0 : (∀ (x : UInt64) (y : UInt64),
    ((¬ (@Eq _ (@ClightN.Base.u64 x) (@ClightN.Base.u64 y)))
      → (binop_ok LClight.binary_operation.Oeq
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_ne_ul_1 : (∀ (x : UInt64) (y : UInt64),
    ((¬ (@Eq _ (@ClightN.Base.u64 x) (@ClightN.Base.u64 y)))
      → (binop_ok LClight.binary_operation.One
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_ne_ul_0 : (∀ (x : UInt64) (y : UInt64),
    ((@Eq _ (@ClightN.Base.u64 x) (@ClightN.Base.u64 y))
      → (binop_ok LClight.binary_operation.One
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_lt_ul_1 : (∀ (x : UInt64) (y : UInt64),
    ((@LT.lt Int Int.instLTInt (@ClightN.Base.u64 x) (@ClightN.Base.u64 y))
      → (binop_ok LClight.binary_operation.Olt
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_lt_ul_0 : (∀ (x : UInt64) (y : UInt64),
    ((@LE.le Int Int.instLEInt (@ClightN.Base.u64 y) (@ClightN.Base.u64 x))
      → (binop_ok LClight.binary_operation.Olt
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_le_ul_1 : (∀ (x : UInt64) (y : UInt64),
    ((@LE.le Int Int.instLEInt (@ClightN.Base.u64 x) (@ClightN.Base.u64 y))
      → (binop_ok LClight.binary_operation.Ole
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_le_ul_0 : (∀ (x : UInt64) (y : UInt64),
    ((@LT.lt Int Int.instLTInt (@ClightN.Base.u64 y) (@ClightN.Base.u64 x))
      → (binop_ok LClight.binary_operation.Ole
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_gt_ul_1 : (∀ (x : UInt64) (y : UInt64),
    ((@LT.lt Int Int.instLTInt (@ClightN.Base.u64 y) (@ClightN.Base.u64 x))
      → (binop_ok LClight.binary_operation.Ogt
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_gt_ul_0 : (∀ (x : UInt64) (y : UInt64),
    ((@LE.le Int Int.instLEInt (@ClightN.Base.u64 x) (@ClightN.Base.u64 y))
      → (binop_ok LClight.binary_operation.Ogt
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_ge_ul_1 : (∀ (x : UInt64) (y : UInt64),
    ((@LE.le Int Int.instLEInt (@ClightN.Base.u64 y) (@ClightN.Base.u64 x))
      → (binop_ok LClight.binary_operation.Oge
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_ge_ul_0 : (∀ (x : UInt64) (y : UInt64),
    ((@LT.lt Int Int.instLTInt (@ClightN.Base.u64 x) (@ClightN.Base.u64 y))
      → (binop_ok LClight.binary_operation.Oge
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_lt_sl_1 : (∀ (x : UInt64) (y : UInt64),
    ((@LT.lt Int Int.instLTInt (@ClightN.Base.s64 x) (@ClightN.Base.s64 y))
      → (binop_ok LClight.binary_operation.Olt
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_lt_sl_0 : (∀ (x : UInt64) (y : UInt64),
    ((@LE.le Int Int.instLEInt (@ClightN.Base.s64 y) (@ClightN.Base.s64 x))
      → (binop_ok LClight.binary_operation.Olt
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_le_sl_1 : (∀ (x : UInt64) (y : UInt64),
    ((@LE.le Int Int.instLEInt (@ClightN.Base.s64 x) (@ClightN.Base.s64 y))
      → (binop_ok LClight.binary_operation.Ole
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_le_sl_0 : (∀ (x : UInt64) (y : UInt64),
    ((@LT.lt Int Int.instLTInt (@ClightN.Base.s64 y) (@ClightN.Base.s64 x))
      → (binop_ok LClight.binary_operation.Ole
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_shr_sl_ul : (∀ (x : UInt64) (y : UInt64),
    ((@LT.lt Int Int.instLTInt (@ClightN.Base.u64 y) (64 : Int))
      → (binop_ok LClight.binary_operation.Oshr
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
          (@LClight.val.Vlong y)
          (@LClight.val.Vlong
            (@ClightN.Base.r64
              (@ClightN.Base.zdiv (@ClightN.Base.s64 x)
                (@ClightN.Base.pow2 (@ClightN.Base.u64 y))))))))
  | bo_add_ui : (∀ (x : UInt32) (y : UInt32),
    (binop_ok LClight.binary_operation.Oadd
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x) (@LClight.val.Vint y)
      (@LClight.val.Vint
        (@ClightN.Base.r32
          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@ClightN.Base.u32 x)
            (@ClightN.Base.u32 y))))))
  | bo_sub_ui : (∀ (x : UInt32) (y : UInt32),
    (binop_ok LClight.binary_operation.Osub
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x) (@LClight.val.Vint y)
      (@LClight.val.Vint
        (@ClightN.Base.r32
          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@ClightN.Base.u32 x)
            (@ClightN.Base.u32 y))))))
  | bo_and_ui : (∀ (x : UInt32) (y : UInt32),
    (binop_ok LClight.binary_operation.Oand
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x) (@LClight.val.Vint y)
      (@LClight.val.Vint
        (@ClightN.Base.r32 (@ClightN.Base.land (@ClightN.Base.u32 x) (@ClightN.Base.u32 y))))))
  | bo_shl_ui : (∀ (x : UInt32) (y : UInt32),
    ((@LT.lt Int Int.instLTInt (@ClightN.Base.u32 y) (32 : Int))
      → (binop_ok LClight.binary_operation.Oshl
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
          (@LClight.val.Vint y)
          (@LClight.val.Vint
            (@ClightN.Base.r32
              (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@ClightN.Base.u32 x)
                (@ClightN.Base.pow2 (@ClightN.Base.u32 y))))))))
  | bo_shr_ui : (∀ (x : UInt32) (y : UInt32),
    ((@LT.lt Int Int.instLTInt (@ClightN.Base.u32 y) (32 : Int))
      → (binop_ok LClight.binary_operation.Oshr
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
          (@LClight.val.Vint y)
          (@LClight.val.Vint
            (@ClightN.Base.r32
              (@ClightN.Base.zdiv (@ClightN.Base.u32 x)
                (@ClightN.Base.pow2 (@ClightN.Base.u32 y))))))))
  | bo_eq_ui_1 : (∀ (x : UInt32) (y : UInt32),
    ((@Eq _ (@ClightN.Base.u32 x) (@ClightN.Base.u32 y))
      → (binop_ok LClight.binary_operation.Oeq
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
          (@LClight.val.Vint y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_eq_ui_0 : (∀ (x : UInt32) (y : UInt32),
    ((¬ (@Eq _ (@ClightN.Base.u32 x) (@ClightN.Base.u32 y)))
      → (binop_ok LClight.binary_operation.Oeq
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
          (@LClight.val.Vint y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_ne_ui_1 : (∀ (x : UInt32) (y : UInt32),
    ((¬ (@Eq _ (@ClightN.Base.u32 x) (@ClightN.Base.u32 y)))
      → (binop_ok LClight.binary_operation.One
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
          (@LClight.val.Vint y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_ne_ui_0 : (∀ (x : UInt32) (y : UInt32),
    ((@Eq _ (@ClightN.Base.u32 x) (@ClightN.Base.u32 y))
      → (binop_ok LClight.binary_operation.One
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
          (@LClight.val.Vint y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_lt_ui_1 : (∀ (x : UInt32) (y : UInt32),
    ((@LT.lt Int Int.instLTInt (@ClightN.Base.u32 x) (@ClightN.Base.u32 y))
      → (binop_ok LClight.binary_operation.Olt
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
          (@LClight.val.Vint y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_lt_ui_0 : (∀ (x : UInt32) (y : UInt32),
    ((@LE.le Int Int.instLEInt (@ClightN.Base.u32 y) (@ClightN.Base.u32 x))
      → (binop_ok LClight.binary_operation.Olt
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
          (@LClight.val.Vint y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_gt_ui_1 : (∀ (x : UInt32) (y : UInt32),
    ((@LT.lt Int Int.instLTInt (@ClightN.Base.u32 y) (@ClightN.Base.u32 x))
      → (binop_ok LClight.binary_operation.Ogt
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
          (@LClight.val.Vint y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_gt_ui_0 : (∀ (x : UInt32) (y : UInt32),
    ((@LE.le Int Int.instLEInt (@ClightN.Base.u32 x) (@ClightN.Base.u32 y))
      → (binop_ok LClight.binary_operation.Ogt
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
          (@LClight.val.Vint y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_ge_ui_1 : (∀ (x : UInt32) (y : UInt32),
    ((@LE.le Int Int.instLEInt (@ClightN.Base.u32 y) (@ClightN.Base.u32 x))
      → (binop_ok LClight.binary_operation.Oge
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
          (@LClight.val.Vint y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_ge_ui_0 : (∀ (x : UInt32) (y : UInt32),
    ((@LT.lt Int Int.instLTInt (@ClightN.Base.u32 x) (@ClightN.Base.u32 y))
      → (binop_ok LClight.binary_operation.Oge
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
          (@LClight.val.Vint y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_add_d : (∀ (x : LClight.float) (y : LClight.float),
    (binop_ok LClight.binary_operation.Oadd
      (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vfloat x) (@LClight.val.Vfloat y)
      (@LClight.val.Vfloat (@LClight.Float.add LClight.Archi.aarch64 x y))))
  | bo_sub_d : (∀ (x : LClight.float) (y : LClight.float),
    (binop_ok LClight.binary_operation.Osub
      (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vfloat x) (@LClight.val.Vfloat y)
      (@LClight.val.Vfloat (@LClight.Float.sub LClight.Archi.aarch64 x y))))
  | bo_mul_d : (∀ (x : LClight.float) (y : LClight.float),
    (binop_ok LClight.binary_operation.Omul
      (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vfloat x) (@LClight.val.Vfloat y)
      (@LClight.val.Vfloat (@LClight.Float.mul LClight.Archi.aarch64 x y))))
  | bo_div_d : (∀ (x : LClight.float) (y : LClight.float),
    (binop_ok LClight.binary_operation.Odiv
      (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vfloat x) (@LClight.val.Vfloat y)
      (@LClight.val.Vfloat (@LClight.Float.div LClight.Archi.aarch64 x y))))
  | bo_eq_d_1 : (∀ (x : LClight.float) (y : LClight.float),
    ((@Eq _ (@LClight.Float.cmp LClight.comparison.Ceq x y) Bool.true)
      → (binop_ok LClight.binary_operation.Oeq
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vfloat x)
          (@LClight.val.Vfloat y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_eq_d_0 : (∀ (x : LClight.float) (y : LClight.float),
    ((@Eq _ (@LClight.Float.cmp LClight.comparison.Ceq x y) Bool.false)
      → (binop_ok LClight.binary_operation.Oeq
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vfloat x)
          (@LClight.val.Vfloat y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_ne_d_1 : (∀ (x : LClight.float) (y : LClight.float),
    ((@Eq _ (@LClight.Float.cmp LClight.comparison.Cne x y) Bool.true)
      → (binop_ok LClight.binary_operation.One
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vfloat x)
          (@LClight.val.Vfloat y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_ne_d_0 : (∀ (x : LClight.float) (y : LClight.float),
    ((@Eq _ (@LClight.Float.cmp LClight.comparison.Cne x y) Bool.false)
      → (binop_ok LClight.binary_operation.One
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vfloat x)
          (@LClight.val.Vfloat y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_lt_d_1 : (∀ (x : LClight.float) (y : LClight.float),
    ((@Eq _ (@LClight.Float.cmp LClight.comparison.Clt x y) Bool.true)
      → (binop_ok LClight.binary_operation.Olt
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vfloat x)
          (@LClight.val.Vfloat y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_lt_d_0 : (∀ (x : LClight.float) (y : LClight.float),
    ((@Eq _ (@LClight.Float.cmp LClight.comparison.Clt x y) Bool.false)
      → (binop_ok LClight.binary_operation.Olt
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vfloat x)
          (@LClight.val.Vfloat y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_le_d_1 : (∀ (x : LClight.float) (y : LClight.float),
    ((@Eq _ (@LClight.Float.cmp LClight.comparison.Cle x y) Bool.true)
      → (binop_ok LClight.binary_operation.Ole
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vfloat x)
          (@LClight.val.Vfloat y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_le_d_0 : (∀ (x : LClight.float) (y : LClight.float),
    ((@Eq _ (@LClight.Float.cmp LClight.comparison.Cle x y) Bool.false)
      → (binop_ok LClight.binary_operation.Ole
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vfloat x)
          (@LClight.val.Vfloat y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_ge_d_1 : (∀ (x : LClight.float) (y : LClight.float),
    ((@Eq _ (@LClight.Float.cmp LClight.comparison.Cge x y) Bool.true)
      → (binop_ok LClight.binary_operation.Oge
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vfloat x)
          (@LClight.val.Vfloat y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_ge_d_0 : (∀ (x : LClight.float) (y : LClight.float),
    ((@Eq _ (@LClight.Float.cmp LClight.comparison.Cge x y) Bool.false)
      → (binop_ok LClight.binary_operation.Oge
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vfloat x)
          (@LClight.val.Vfloat y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_add_f : (∀ (x : LClight.float32) (y : LClight.float32),
    (binop_ok LClight.binary_operation.Oadd
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vsingle x) (@LClight.val.Vsingle y)
      (@LClight.val.Vsingle (@LClight.Float32.add LClight.Archi.aarch64 x y))))
  | bo_sub_f : (∀ (x : LClight.float32) (y : LClight.float32),
    (binop_ok LClight.binary_operation.Osub
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vsingle x) (@LClight.val.Vsingle y)
      (@LClight.val.Vsingle (@LClight.Float32.sub LClight.Archi.aarch64 x y))))
  | bo_mul_f : (∀ (x : LClight.float32) (y : LClight.float32),
    (binop_ok LClight.binary_operation.Omul
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vsingle x) (@LClight.val.Vsingle y)
      (@LClight.val.Vsingle (@LClight.Float32.mul LClight.Archi.aarch64 x y))))
  | bo_div_f : (∀ (x : LClight.float32) (y : LClight.float32),
    (binop_ok LClight.binary_operation.Odiv
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vsingle x) (@LClight.val.Vsingle y)
      (@LClight.val.Vsingle (@LClight.Float32.div LClight.Archi.aarch64 x y))))
  | bo_eq_f_1 : (∀ (x : LClight.float32) (y : LClight.float32),
    ((@Eq _ (@LClight.Float32.cmp LClight.comparison.Ceq x y) Bool.true)
      → (binop_ok LClight.binary_operation.Oeq
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vsingle x)
          (@LClight.val.Vsingle y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_eq_f_0 : (∀ (x : LClight.float32) (y : LClight.float32),
    ((@Eq _ (@LClight.Float32.cmp LClight.comparison.Ceq x y) Bool.false)
      → (binop_ok LClight.binary_operation.Oeq
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vsingle x)
          (@LClight.val.Vsingle y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_ne_f_1 : (∀ (x : LClight.float32) (y : LClight.float32),
    ((@Eq _ (@LClight.Float32.cmp LClight.comparison.Cne x y) Bool.true)
      → (binop_ok LClight.binary_operation.One
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vsingle x)
          (@LClight.val.Vsingle y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_ne_f_0 : (∀ (x : LClight.float32) (y : LClight.float32),
    ((@Eq _ (@LClight.Float32.cmp LClight.comparison.Cne x y) Bool.false)
      → (binop_ok LClight.binary_operation.One
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vsingle x)
          (@LClight.val.Vsingle y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_lt_f_1 : (∀ (x : LClight.float32) (y : LClight.float32),
    ((@Eq _ (@LClight.Float32.cmp LClight.comparison.Clt x y) Bool.true)
      → (binop_ok LClight.binary_operation.Olt
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vsingle x)
          (@LClight.val.Vsingle y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_lt_f_0 : (∀ (x : LClight.float32) (y : LClight.float32),
    ((@Eq _ (@LClight.Float32.cmp LClight.comparison.Clt x y) Bool.false)
      → (binop_ok LClight.binary_operation.Olt
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vsingle x)
          (@LClight.val.Vsingle y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_le_f_1 : (∀ (x : LClight.float32) (y : LClight.float32),
    ((@Eq _ (@LClight.Float32.cmp LClight.comparison.Cle x y) Bool.true)
      → (binop_ok LClight.binary_operation.Ole
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vsingle x)
          (@LClight.val.Vsingle y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_le_f_0 : (∀ (x : LClight.float32) (y : LClight.float32),
    ((@Eq _ (@LClight.Float32.cmp LClight.comparison.Cle x y) Bool.false)
      → (binop_ok LClight.binary_operation.Ole
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vsingle x)
          (@LClight.val.Vsingle y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))
  | bo_ge_f_1 : (∀ (x : LClight.float32) (y : LClight.float32),
    ((@Eq _ (@LClight.Float32.cmp LClight.comparison.Cge x y) Bool.true)
      → (binop_ok LClight.binary_operation.Oge
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vsingle x)
          (@LClight.val.Vsingle y) (@LClight.val.Vint (@ClightN.Base.r32 (1 : Int))))))
  | bo_ge_f_0 : (∀ (x : LClight.float32) (y : LClight.float32),
    ((@Eq _ (@LClight.Float32.cmp LClight.comparison.Cge x y) Bool.false)
      → (binop_ok LClight.binary_operation.Oge
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vsingle x)
          (@LClight.val.Vsingle y) (@LClight.val.Vint (@ClightN.Base.r32 (0 : Int))))))

inductive cast_ok : LClight.type → LClight.type → LClight.val → LClight.val → Prop where
  | co_si_ui : (∀ (x : UInt32),
    (cast_ok
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
      (@LClight.val.Vint x)))
  | co_ui_si : (∀ (x : UInt32),
    (cast_ok
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
      (@LClight.val.Vint x)))
  | co_ul_ui : (∀ (x : UInt64),
    (cast_ok
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
      (@LClight.val.Vint (@ClightN.Base.r32 (@ClightN.Base.u64 x)))))
  | co_ui_ul : (∀ (x : UInt32),
    (cast_ok
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
      (@LClight.val.Vlong (@ClightN.Base.r64 (@ClightN.Base.u32 x)))))
  | co_ul_sl : (∀ (x : UInt64),
    (cast_ok
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tlong LClight.signedness.Signed (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vlong x) (@LClight.val.Vlong x)))
  | co_ul_sl_ptr : (∀ (b : LClight.block) (o : LClight.ptrofs),
    (cast_ok
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tlong LClight.signedness.Signed (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vptr b o) (@LClight.val.Vptr b o)))
  | co_sl_ul : (∀ (x : UInt64),
    (cast_ok
      (@LClight.type.Tlong LClight.signedness.Signed (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
      (@LClight.val.Vlong x)))
  | co_sl_ul_ptr : (∀ (b : LClight.block) (o : LClight.ptrofs),
    (cast_ok
      (@LClight.type.Tlong LClight.signedness.Signed (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vptr b o)
      (@LClight.val.Vptr b o)))
  | co_uc_ul : (∀ (x : UInt32),
    (cast_ok
      (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
      (@LClight.val.Vlong (@ClightN.Base.r64 (@ClightN.Base.u32 x)))))
  | co_uc_ui : (∀ (x : UInt32),
    (cast_ok
      (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
      (@LClight.val.Vint x)))
  | co_ul_uc : (∀ (x : UInt64),
    (cast_ok
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
      (@LClight.val.Vint
        (@ClightN.Base.r32 (@ClightN.Base.zmod (@ClightN.Base.u64 x) (256 : Int))))))
  | co_ui_uc : (∀ (x : UInt32),
    (cast_ok
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
      (@LClight.val.Vint
        (@ClightN.Base.r32 (@ClightN.Base.zmod (@ClightN.Base.u32 x) (256 : Int))))))
  | co_vuc_ul : (∀ (x : UInt32),
    (cast_ok
      (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.true (@Option.none _)))
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
      (@LClight.val.Vlong (@ClightN.Base.r64 (@ClightN.Base.u32 x)))))
  | co_vui_ul : (∀ (x : UInt32),
    (cast_ok
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.true (@Option.none _)))
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
      (@LClight.val.Vlong (@ClightN.Base.r64 (@ClightN.Base.u32 x)))))
  | co_ui_vui : (∀ (x : UInt32),
    (cast_ok
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.true (@Option.none _))) (@LClight.val.Vint x) (@LClight.val.Vint x)))
  | co_ul_ul : (∀ (x : UInt64),
    (cast_ok
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)
      (@LClight.val.Vlong x)))
  | co_ul_ul_ptr : (∀ (b : LClight.block) (o : LClight.ptrofs),
    (cast_ok
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vptr b o)
      (@LClight.val.Vptr b o)))
  | co_ui_ui : (∀ (x : UInt32),
    (cast_ok
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
      (@LClight.val.Vint x)))
  | co_uc_uc : (∀ (x : UInt32),
    (cast_ok
      (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
      (@LClight.val.Vint
        (@ClightN.Base.r32 (@ClightN.Base.zmod (@ClightN.Base.u32 x) (256 : Int))))))
  | co_si_si : (∀ (x : UInt32),
    (cast_ok
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)
      (@LClight.val.Vint x)))
  | co_d_d : (∀ (x : LClight.float),
    (cast_ok
      (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vfloat x) (@LClight.val.Vfloat x)))
  | co_f_f : (∀ (x : LClight.float32),
    (cast_ok
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vsingle x) (@LClight.val.Vsingle x)))
  | co_ul_d : (∀ (x : UInt64),
    (cast_ok
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vlong x) (@LClight.val.Vfloat (@LClight.Float.of_longu x))))
  | co_d_ul : (∀ (x : LClight.float) (y : UInt64),
    ((@Eq _ (@LClight.Float.to_longu x) (@Option.some _ y))
      → (cast_ok
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vfloat x)
          (@LClight.val.Vlong y))))
  | co_f_d : (∀ (x : LClight.float32),
    (cast_ok
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vsingle x) (@LClight.val.Vfloat (@LClight.Float.of_single x))))
  | co_d_f : (∀ (x : LClight.float),
    (cast_ok
      (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vfloat x) (@LClight.val.Vsingle (@LClight.Float.to_single x))))
  | co_si_f : (∀ (x : UInt32),
    (cast_ok
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vint x) (@LClight.val.Vsingle (@LClight.Float32.of_int x))))
  | co_ui_f : (∀ (x : UInt32),
    (cast_ok
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vint x) (@LClight.val.Vsingle (@LClight.Float32.of_intu x))))
  | co_ul_f : (∀ (x : UInt64),
    (cast_ok
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vlong x) (@LClight.val.Vsingle (@LClight.Float32.of_longu x))))
  | co_f_si : (∀ (x : LClight.float32) (y : UInt32),
    ((@Eq _ (@LClight.Float32.to_int x) (@Option.some _ y))
      → (cast_ok
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vsingle x)
          (@LClight.val.Vint y))))
  | co_f_ul : (∀ (x : LClight.float32) (y : UInt64),
    ((@Eq _ (@LClight.Float32.to_longu x) (@Option.some _ y))
      → (cast_ok
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vsingle x)
          (@LClight.val.Vlong y))))

inductive bool_ok : LClight.type → LClight.val → Bool → Prop where
  | bv_si_true : (∀ (x : UInt32),
    ((¬ (@Eq _ (@ClightN.Base.u32 x) (0 : Int)))
      → (bool_ok
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x) Bool.true)))
  | bv_si_false : (∀ (x : UInt32),
    ((@Eq _ (@ClightN.Base.u32 x) (0 : Int))
      → (bool_ok
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x) Bool.false)))
  | bv_ui_true : (∀ (x : UInt32),
    ((¬ (@Eq _ (@ClightN.Base.u32 x) (0 : Int)))
      → (bool_ok
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x) Bool.true)))
  | bv_ui_false : (∀ (x : UInt32),
    ((@Eq _ (@ClightN.Base.u32 x) (0 : Int))
      → (bool_ok
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x) Bool.false)))

inductive unop_ok : LClight.unary_operation → LClight.type → LClight.val → LClight.val → Prop where
  | uo_neg_d : (∀ (x : LClight.float),
    (unop_ok LClight.unary_operation.Oneg
      (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vfloat x) (@LClight.val.Vfloat (@LClight.Float.neg x))))
  | uo_abs_d : (∀ (x : LClight.float),
    (unop_ok LClight.unary_operation.Oabsfloat
      (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vfloat x) (@LClight.val.Vfloat (@LClight.Float.abs x))))
  | uo_neg_f : (∀ (x : LClight.float32),
    (unop_ok LClight.unary_operation.Oneg
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vsingle x) (@LClight.val.Vsingle (@LClight.Float32.neg x))))

inductive in_defs :
    (List (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type))) →
    LClight.ident → (@LClight.globdef (@LClight.fundef LClight.function) LClight.type) → Prop where
  | in_here : (∀ (x : LClight.ident)
      (g : (@LClight.globdef (@LClight.fundef LClight.function) LClight.type))
      (rest :
        (List
          (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type)))),
    (in_defs (@List.cons _ (@Prod.mk _ _ x g) rest) x g))
  | in_there : (∀ (d :
        (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type)))
      (rest :
        (List (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type))))
      (x : LClight.ident) (g : (@LClight.globdef (@LClight.fundef LClight.function) LClight.type)),
    ((in_defs rest x g) → (in_defs (@List.cons _ d rest) x g)))

inductive out_defs : LClight.ident →
    (List (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type))) →
    Prop where
  | od_nil : (∀ (x : LClight.ident), (out_defs x (@List.nil _)))
  | od_cons : (∀ (x : LClight.ident) (y : LClight.ident)
      (g : (@LClight.globdef (@LClight.fundef LClight.function) LClight.type))
      (rest :
        (List
          (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type)))),
    ((¬ (@Eq _ x y)) → ((out_defs x rest) → (out_defs x (@List.cons _ (@Prod.mk _ _ y g) rest)))))

inductive norepet_defs :
    (List (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type))) →
    Prop where
  | nd_nil : (norepet_defs (@List.nil _))
  | nd_cons : (∀ (x : LClight.ident)
      (g : (@LClight.globdef (@LClight.fundef LClight.function) LClight.type))
      (rest :
        (List
          (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type)))),
    ((out_defs x rest)
      → ((norepet_defs rest) → (norepet_defs (@List.cons _ (@Prod.mk _ _ x g) rest)))))

inductive out_names : LClight.ident → (List (LClight.ident × LClight.type)) → Prop where
  | on_nil : (∀ (x : LClight.ident), (out_names x (@List.nil _)))
  | on_cons : (∀ (x : LClight.ident) (y : LClight.ident) (ty : LClight.type)
      (rest : (List (LClight.ident × LClight.type))),
    ((¬ (@Eq _ x y))
      → ((out_names x rest) → (out_names x (@List.cons _ (@Prod.mk _ _ y ty) rest)))))

inductive norepet_names : (List (LClight.ident × LClight.type)) → Prop where
  | nn_nil : (norepet_names (@List.nil _))
  | nn_cons : (∀ (x : LClight.ident) (ty : LClight.type)
      (rest : (List (LClight.ident × LClight.type))),
    ((out_names x rest)
      → ((norepet_names rest) → (norepet_names (@List.cons _ (@Prod.mk _ _ x ty) rest)))))

inductive disjoint_names : (List (LClight.ident × LClight.type)) →
    (List (LClight.ident × LClight.type)) → Prop where
  | dn_nil : (∀ (l : (List (LClight.ident × LClight.type))), (disjoint_names (@List.nil _) l))
  | dn_cons : (∀ (x : LClight.ident) (ty : LClight.type)
      (rest : (List (LClight.ident × LClight.type))) (l : (List (LClight.ident × LClight.type))),
    ((out_names x l)
      → ((disjoint_names rest l) → (disjoint_names (@List.cons _ (@Prod.mk _ _ x ty) rest) l))))

inductive params_types : (List (LClight.ident × LClight.type)) → (List LClight.type) → Prop where
  | pt_nil : (params_types (@List.nil _) (@List.nil _))
  | pt_cons : (∀ (x : LClight.ident) (ty : LClight.type)
      (rest : (List (LClight.ident × LClight.type))) (tys : (List LClight.type)),
    ((params_types rest tys)
      → (params_types (@List.cons _ (@Prod.mk _ _ x ty) rest) (@List.cons _ ty tys))))

inductive undef_temps : (List (LClight.ident × LClight.type)) →
    (LClight.ident → (Option LClight.val)) → Prop where
  | ut_nil : (∀ (le : (LClight.ident → (Option LClight.val))),
    ((∀ (x : LClight.ident), (@Eq _ (le x) (@Option.none _))) → (undef_temps (@List.nil _) le)))
  | ut_cons : (∀ (x : LClight.ident) (ty : LClight.type)
      (rest : (List (LClight.ident × LClight.type))) (le0 : (LClight.ident → (Option LClight.val)))
      (le : (LClight.ident → (Option LClight.val))),
    ((undef_temps rest le0)
      → ((∀ (x_upd : LClight.ident),
            (((@Eq _ x_upd x) → (@Eq _ (le x_upd) (@Option.some _ LClight.val.Vundef)))
              ∧ ((¬ (@Eq _ x_upd x)) → (@Eq _ (le x_upd) (le0 x_upd)))))
          → (undef_temps (@List.cons _ (@Prod.mk _ _ x ty) rest) le))))

inductive bind_params : (List (LClight.ident × LClight.type)) → (List LClight.val) →
    (LClight.ident → (Option LClight.val)) → (LClight.ident → (Option LClight.val)) → Prop where
  | bp_nil : (∀ (le : (LClight.ident → (Option LClight.val))),
    (bind_params (@List.nil _) (@List.nil _) le le))
  | bp_cons : (∀ (x : LClight.ident) (ty : LClight.type)
      (rest : (List (LClight.ident × LClight.type))) (v : LClight.val) (vs : (List LClight.val))
      (le : (LClight.ident → (Option LClight.val))) (le1 : (LClight.ident → (Option LClight.val)))
      (le2 : (LClight.ident → (Option LClight.val))),
    ((∀ (x_upd : LClight.ident),
        (((@Eq _ x_upd x) → (@Eq _ (le1 x_upd) (@Option.some _ v)))
          ∧ ((¬ (@Eq _ x_upd x)) → (@Eq _ (le1 x_upd) (le x_upd)))))
      → ((bind_params rest vs le1 le2)
          → (bind_params (@List.cons _ (@Prod.mk _ _ x ty) rest) (@List.cons _ v vs) le le2))))

inductive set_opt : (Option LClight.ident) → LClight.val → (LClight.ident → (Option LClight.val)) →
    (LClight.ident → (Option LClight.val)) → Prop where
  | so_none : (∀ (v : LClight.val) (le : (LClight.ident → (Option LClight.val))),
    (set_opt (@Option.none _) v le le))
  | so_some : (∀ (x : LClight.ident) (v : LClight.val) (le : (LClight.ident → (Option LClight.val)))
      (le2 : (LClight.ident → (Option LClight.val))),
    ((∀ (x_upd : LClight.ident),
        (((@Eq _ x_upd x) → (@Eq _ (le2 x_upd) (@Option.some _ v)))
          ∧ ((¬ (@Eq _ x_upd x)) → (@Eq _ (le2 x_upd) (le x_upd)))))
      → (set_opt (@Option.some _ x) v le le2)))

inductive has_type : LClight.expr → LClight.type → Prop where
  | ht_int : (∀ (i : UInt32) (ty : LClight.type), (has_type (@LClight.expr.Econst_int i ty) ty))
  | ht_long : (∀ (i : UInt64) (ty : LClight.type), (has_type (@LClight.expr.Econst_long i ty) ty))
  | ht_float : (∀ (f : LClight.float) (ty : LClight.type),
    (has_type (@LClight.expr.Econst_float f ty) ty))
  | ht_single : (∀ (f : LClight.float32) (ty : LClight.type),
    (has_type (@LClight.expr.Econst_single f ty) ty))
  | ht_temp : (∀ (x : LClight.ident) (ty : LClight.type),
    (has_type (@LClight.expr.Etempvar x ty) ty))
  | ht_var : (∀ (x : LClight.ident) (ty : LClight.type), (has_type (@LClight.expr.Evar x ty) ty))
  | ht_deref : (∀ (a : LClight.expr) (ty : LClight.type), (has_type (@LClight.expr.Ederef a ty) ty))
  | ht_binop : (∀ (op : LClight.binary_operation) (a1 : LClight.expr) (a2 : LClight.expr)
      (ty : LClight.type), (has_type (@LClight.expr.Ebinop op a1 a2 ty) ty))
  | ht_cast : (∀ (a : LClight.expr) (ty : LClight.type), (has_type (@LClight.expr.Ecast a ty) ty))
  | ht_unop : (∀ (op : LClight.unary_operation) (a : LClight.expr) (ty : LClight.type),
    (has_type (@LClight.expr.Eunop op a ty) ty))

inductive scalar : LClight.type → Prop where
  | sc_ui : (scalar
    (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
      (@LClight.attr.mk Bool.false (@Option.none _))))
  | sc_ul : (scalar
    (@LClight.type.Tlong LClight.signedness.Unsigned
      (@LClight.attr.mk Bool.false (@Option.none _))))
  | sc_d : (scalar
    (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _))))
  | sc_f : (scalar
    (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _))))

inductive gval : LClight.type → LClight.val → Prop where
  | gv_ui : (∀ (x : UInt32),
    (gval
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint x)))
  | gv_ul : (∀ (x : UInt64),
    (gval
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vlong x)))
  | gv_d : (∀ (f : LClight.float),
    (gval
      (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vfloat f)))
  | gv_f : (∀ (f : LClight.float32),
    (gval
      (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
      (@LClight.val.Vsingle f)))

inductive ginit : LClight.type → (List LClight.init_data) → LClight.val → Prop where
  | gi_ui : (∀ (x : UInt32),
    (ginit
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@List.cons _ (@LClight.init_data.Init_int32 x) (@List.nil _)) (@LClight.val.Vint x)))
  | gi_ul : (∀ (x : UInt64),
    (ginit
      (@LClight.type.Tlong LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.false (@Option.none _)))
      (@List.cons _ (@LClight.init_data.Init_int64 x) (@List.nil _)) (@LClight.val.Vlong x)))
  | gi_d : (ginit
    (@LClight.type.Tfloat LClight.floatsize.F64 (@LClight.attr.mk Bool.false (@Option.none _)))
    (@List.cons _ (@LClight.init_data.Init_space (8 : Int)) (@List.nil _))
    (@LClight.val.Vfloat (@ClightN.Base.f64_of_bits (@ClightN.Base.r64 (0 : Int)))))
  | gi_f : (ginit
    (@LClight.type.Tfloat LClight.floatsize.F32 (@LClight.attr.mk Bool.false (@Option.none _)))
    (@List.cons _ (@LClight.init_data.Init_space (4 : Int)) (@List.nil _))
    (@LClight.val.Vsingle (@ClightN.Base.f32_of_bits (@ClightN.Base.r32 (0 : Int)))))

inductive init_ok : (List LClight.init_data) → Prop where
  | io_nil : (init_ok (@List.nil _))
  | io_int32 : (∀ (x : UInt32),
    (init_ok (@List.cons _ (@LClight.init_data.Init_int32 x) (@List.nil _))))
  | io_int64 : (∀ (x : UInt64),
    (init_ok (@List.cons _ (@LClight.init_data.Init_int64 x) (@List.nil _))))
  | io_space : (∀ (n : Int),
    (init_ok (@List.cons _ (@LClight.init_data.Init_space n) (@List.nil _))))

inductive vload_ok : LClight.memory_chunk → LClight.type → Int → UInt32 → LClight.val → Prop where
  | vl_uchar : (∀ (j : UInt32),
    (vload_ok LClight.memory_chunk.Mint8unsigned
      (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.true (@Option.none _))) (1 : Int) j
      (@LClight.val.Vint
        (@ClightN.Base.r32 (@ClightN.Base.zmod (@ClightN.Base.u32 j) (256 : Int))))))
  | vl_uint : (∀ (j : UInt32),
    (vload_ok LClight.memory_chunk.Mint32
      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
        (@LClight.attr.mk Bool.true (@Option.none _))) (4 : Int) j (@LClight.val.Vint j)))

inductive result_ok : LClight.outcome → LClight.type → LClight.val → Prop where
  | rs_normal : (result_ok LClight.outcome.Out_normal LClight.type.Tvoid LClight.val.Vundef)
  | rs_none : (result_ok (@LClight.outcome.Out_return (@Option.none _)) LClight.type.Tvoid
    LClight.val.Vundef)
  | rs_some : (∀ (v : LClight.val) (t : LClight.type) (ty : LClight.type) (v2 : LClight.val),
    ((¬ (@Eq _ ty LClight.type.Tvoid))
      → ((cast_ok t ty v v2)
          → (result_ok (@LClight.outcome.Out_return (@Option.some _ (@Prod.mk _ _ v t))) ty v2))))

inductive neval
    (defs :
      (List (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type))))
    (le : (LClight.ident → (Option LClight.val))) (gv : (LClight.ident → (Option LClight.val)))
    (mb : (LClight.ident → (Int → Int))) : LClight.expr → LClight.val → Prop where
  | nv_int : (∀ (i : UInt32) (ty : LClight.type),
    (neval defs le gv mb (@LClight.expr.Econst_int i ty) (@LClight.val.Vint i)))
  | nv_long : (∀ (i : UInt64) (ty : LClight.type),
    (neval defs le gv mb (@LClight.expr.Econst_long i ty) (@LClight.val.Vlong i)))
  | nv_float : (∀ (f : LClight.float) (ty : LClight.type),
    (neval defs le gv mb (@LClight.expr.Econst_float f ty) (@LClight.val.Vfloat f)))
  | nv_single : (∀ (f : LClight.float32) (ty : LClight.type),
    (neval defs le gv mb (@LClight.expr.Econst_single f ty) (@LClight.val.Vsingle f)))
  | nv_temp : (∀ (x : LClight.ident) (ty : LClight.type) (v : LClight.val),
    ((@Eq _ (le x) (@Option.some _ v)) → (neval defs le gv mb (@LClight.expr.Etempvar x ty) v)))
  | nv_global : (∀ (x : LClight.ident) (ty : LClight.type) (init : (List LClight.init_data))
      (v : LClight.val),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type ty init Bool.false Bool.false)))
      → ((scalar ty)
          → ((@Eq _ (gv x) (@Option.some _ v))
              → (neval defs le gv mb (@LClight.expr.Evar x ty) v)))))
  | nv_word : (∀ (x : LClight.ident) (n : Int) (i : LClight.expr) (k : UInt64),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type
            (@LClight.type.Tarray
              (@LClight.type.Tlong LClight.signedness.Unsigned
                (@LClight.attr.mk Bool.false (@Option.none _))) n
              (@LClight.attr.mk Bool.false (@Option.none _)))
            (@List.cons _
              (@LClight.init_data.Init_space
                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n)) (@List.nil _))
            Bool.false Bool.false)))
      → ((neval defs le gv mb i (@LClight.val.Vlong k))
          → ((has_type i
                (@LClight.type.Tlong LClight.signedness.Unsigned
                  (@LClight.attr.mk Bool.false (@Option.none _))))
              → ((@LE.le Int Int.instLEInt
                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                      (@ClightN.Base.zmod
                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int)
                          (@ClightN.Base.u64 k)) (18446744073709551616 : Int)) (8 : Int))
                    (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n))
                  → (neval defs le gv mb
                      (@LClight.expr.Ederef
                        (@LClight.expr.Ebinop LClight.binary_operation.Oadd
                          (@LClight.expr.Evar x
                            (@LClight.type.Tarray
                              (@LClight.type.Tlong LClight.signedness.Unsigned
                                (@LClight.attr.mk Bool.false (@Option.none _))) n
                              (@LClight.attr.mk Bool.false (@Option.none _)))) i
                          (@LClight.type.Tpointer
                            (@LClight.type.Tlong LClight.signedness.Unsigned
                              (@LClight.attr.mk Bool.false (@Option.none _)))
                            (@LClight.attr.mk Bool.false (@Option.none _))))
                        (@LClight.type.Tlong LClight.signedness.Unsigned
                          (@LClight.attr.mk Bool.false (@Option.none _))))
                      (@LClight.val.Vlong
                        (@ClightN.Base.r64
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                              (mb x
                                (@ClightN.Base.zmod
                                  (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int)
                                    (@ClightN.Base.u64 k)) (18446744073709551616 : Int)))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (256 : Int)
                                  (mb x
                                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                      (@ClightN.Base.zmod
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int) (@ClightN.Base.u64 k))
                                        (18446744073709551616 : Int)) (1 : Int))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (65536 : Int)
                                    (mb x
                                      (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (@ClightN.Base.zmod
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int) (@ClightN.Base.u64 k))
                                        (18446744073709551616 : Int)) (2 : Int))))
                                  (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                    (16777216 : Int)
                                    (mb x
                                      (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (@ClightN.Base.zmod
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int) (@ClightN.Base.u64 k))
                                        (18446744073709551616 : Int)) (3 : Int)))))))
                            (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (4294967296 : Int)
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                (mb x
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    (@ClightN.Base.zmod
                                      (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int)
                                        (@ClightN.Base.u64 k)) (18446744073709551616 : Int))
                                    (4 : Int)))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (256 : Int)
                                    (mb x
                                      (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (@ClightN.Base.zmod
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int) (@ClightN.Base.u64 k))
                                        (18446744073709551616 : Int)) (4 : Int)) (1 : Int))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                      (65536 : Int)
                                      (mb x
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (@ClightN.Base.zmod
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int) (@ClightN.Base.u64 k))
                                        (18446744073709551616 : Int)) (4 : Int)) (2 : Int))))
                                    (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                      (16777216 : Int)
                                      (mb x
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (@ClightN.Base.zmod
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int) (@ClightN.Base.u64 k))
                                        (18446744073709551616 : Int)) (4 : Int))
                                        (3 : Int)))))))))))))))))
  | nv_byte : (∀ (x : LClight.ident) (n : Int) (i : LClight.expr) (k : UInt64),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type
            (@LClight.type.Tarray
              (@LClight.type.Tlong LClight.signedness.Unsigned
                (@LClight.attr.mk Bool.false (@Option.none _))) n
              (@LClight.attr.mk Bool.false (@Option.none _)))
            (@List.cons _
              (@LClight.init_data.Init_space
                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n)) (@List.nil _))
            Bool.false Bool.false)))
      → ((neval defs le gv mb i (@LClight.val.Vlong k))
          → ((has_type i
                (@LClight.type.Tlong LClight.signedness.Unsigned
                  (@LClight.attr.mk Bool.false (@Option.none _))))
              → ((@LT.lt Int Int.instLTInt (@ClightN.Base.u64 k)
                    (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n))
                  → (neval defs le gv mb
                      (@LClight.expr.Ederef
                        (@LClight.expr.Ebinop LClight.binary_operation.Oadd
                          (@LClight.expr.Ecast
                            (@LClight.expr.Evar x
                              (@LClight.type.Tarray
                                (@LClight.type.Tlong LClight.signedness.Unsigned
                                  (@LClight.attr.mk Bool.false (@Option.none _))) n
                                (@LClight.attr.mk Bool.false (@Option.none _))))
                            (@LClight.type.Tpointer
                              (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
                                (@LClight.attr.mk Bool.false (@Option.none _)))
                              (@LClight.attr.mk Bool.false (@Option.none _)))) i
                          (@LClight.type.Tpointer
                            (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
                              (@LClight.attr.mk Bool.false (@Option.none _)))
                            (@LClight.attr.mk Bool.false (@Option.none _))))
                        (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
                          (@LClight.attr.mk Bool.false (@Option.none _))))
                      (@LClight.val.Vint (@ClightN.Base.r32 (mb x (@ClightN.Base.u64 k))))))))))
  | nv_cell64 : (∀ (x : LClight.ident) (n : Int),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type
            (@LClight.type.Tarray
              (@LClight.type.Tlong LClight.signedness.Unsigned
                (@LClight.attr.mk Bool.false (@Option.none _))) n
              (@LClight.attr.mk Bool.false (@Option.none _)))
            (@List.cons _
              (@LClight.init_data.Init_space
                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n)) (@List.nil _))
            Bool.false Bool.false)))
      → ((@LE.le Int Int.instLEInt (1 : Int) n)
          → (neval defs le gv mb
              (@LClight.expr.Ederef
                (@LClight.expr.Ecast
                  (@LClight.expr.Evar x
                    (@LClight.type.Tarray
                      (@LClight.type.Tlong LClight.signedness.Unsigned
                        (@LClight.attr.mk Bool.false (@Option.none _))) n
                      (@LClight.attr.mk Bool.false (@Option.none _))))
                  (@LClight.type.Tpointer
                    (@LClight.type.Tlong LClight.signedness.Unsigned
                      (@LClight.attr.mk Bool.false (@Option.none _)))
                    (@LClight.attr.mk Bool.false (@Option.none _))))
                (@LClight.type.Tlong LClight.signedness.Unsigned
                  (@LClight.attr.mk Bool.false (@Option.none _))))
              (@LClight.val.Vlong
                (@ClightN.Base.r64
                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (mb x (0 : Int))
                      (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (256 : Int)
                          (mb x
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                              (1 : Int))))
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                          (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (65536 : Int)
                            (mb x
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                                (2 : Int))))
                          (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (16777216 : Int)
                            (mb x
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                                (3 : Int)))))))
                    (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (4294967296 : Int)
                      (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                        (mb x
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int) (4 : Int)))
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                          (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (256 : Int)
                            (mb x
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                                  (4 : Int)) (1 : Int))))
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                            (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (65536 : Int)
                              (mb x
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                                    (4 : Int)) (2 : Int))))
                            (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (16777216 : Int)
                              (mb x
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                                    (4 : Int)) (3 : Int)))))))))))))))
  | nv_cell32 : (∀ (x : LClight.ident) (n : Int),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type
            (@LClight.type.Tarray
              (@LClight.type.Tlong LClight.signedness.Unsigned
                (@LClight.attr.mk Bool.false (@Option.none _))) n
              (@LClight.attr.mk Bool.false (@Option.none _)))
            (@List.cons _
              (@LClight.init_data.Init_space
                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n)) (@List.nil _))
            Bool.false Bool.false)))
      → ((@LE.le Int Int.instLEInt (1 : Int) n)
          → (neval defs le gv mb
              (@LClight.expr.Ederef
                (@LClight.expr.Ecast
                  (@LClight.expr.Evar x
                    (@LClight.type.Tarray
                      (@LClight.type.Tlong LClight.signedness.Unsigned
                        (@LClight.attr.mk Bool.false (@Option.none _))) n
                      (@LClight.attr.mk Bool.false (@Option.none _))))
                  (@LClight.type.Tpointer
                    (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
                      (@LClight.attr.mk Bool.false (@Option.none _)))
                    (@LClight.attr.mk Bool.false (@Option.none _))))
                (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
                  (@LClight.attr.mk Bool.false (@Option.none _))))
              (@LClight.val.Vint
                (@ClightN.Base.r32
                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (mb x (0 : Int))
                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                      (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (256 : Int)
                        (mb x
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int) (1 : Int))))
                      (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (65536 : Int)
                          (mb x
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                              (2 : Int))))
                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (16777216 : Int)
                          (mb x
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                              (3 : Int)))))))))))))
  | nv_cellf64 : (∀ (x : LClight.ident) (n : Int),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type
            (@LClight.type.Tarray
              (@LClight.type.Tlong LClight.signedness.Unsigned
                (@LClight.attr.mk Bool.false (@Option.none _))) n
              (@LClight.attr.mk Bool.false (@Option.none _)))
            (@List.cons _
              (@LClight.init_data.Init_space
                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n)) (@List.nil _))
            Bool.false Bool.false)))
      → ((@LE.le Int Int.instLEInt (1 : Int) n)
          → (neval defs le gv mb
              (@LClight.expr.Ederef
                (@LClight.expr.Ecast
                  (@LClight.expr.Evar x
                    (@LClight.type.Tarray
                      (@LClight.type.Tlong LClight.signedness.Unsigned
                        (@LClight.attr.mk Bool.false (@Option.none _))) n
                      (@LClight.attr.mk Bool.false (@Option.none _))))
                  (@LClight.type.Tpointer
                    (@LClight.type.Tfloat LClight.floatsize.F64
                      (@LClight.attr.mk Bool.false (@Option.none _)))
                    (@LClight.attr.mk Bool.false (@Option.none _))))
                (@LClight.type.Tfloat LClight.floatsize.F64
                  (@LClight.attr.mk Bool.false (@Option.none _))))
              (@LClight.val.Vfloat
                (@ClightN.Base.f64_of_bits
                  (@ClightN.Base.r64
                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                      (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (mb x (0 : Int))
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                          (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (256 : Int)
                            (mb x
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                                (1 : Int))))
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                            (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (65536 : Int)
                              (mb x
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                                  (2 : Int))))
                            (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (16777216 : Int)
                              (mb x
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                                  (3 : Int)))))))
                      (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (4294967296 : Int)
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                          (mb x
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                              (4 : Int)))
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                            (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (256 : Int)
                              (mb x
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                                    (4 : Int)) (1 : Int))))
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                              (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (65536 : Int)
                                (mb x
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                                      (4 : Int)) (2 : Int))))
                              (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (16777216 : Int)
                                (mb x
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                                      (4 : Int)) (3 : Int))))))))))))))))
  | nv_cellf32 : (∀ (x : LClight.ident) (n : Int),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type
            (@LClight.type.Tarray
              (@LClight.type.Tlong LClight.signedness.Unsigned
                (@LClight.attr.mk Bool.false (@Option.none _))) n
              (@LClight.attr.mk Bool.false (@Option.none _)))
            (@List.cons _
              (@LClight.init_data.Init_space
                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n)) (@List.nil _))
            Bool.false Bool.false)))
      → ((@LE.le Int Int.instLEInt (1 : Int) n)
          → (neval defs le gv mb
              (@LClight.expr.Ederef
                (@LClight.expr.Ecast
                  (@LClight.expr.Evar x
                    (@LClight.type.Tarray
                      (@LClight.type.Tlong LClight.signedness.Unsigned
                        (@LClight.attr.mk Bool.false (@Option.none _))) n
                      (@LClight.attr.mk Bool.false (@Option.none _))))
                  (@LClight.type.Tpointer
                    (@LClight.type.Tfloat LClight.floatsize.F32
                      (@LClight.attr.mk Bool.false (@Option.none _)))
                    (@LClight.attr.mk Bool.false (@Option.none _))))
                (@LClight.type.Tfloat LClight.floatsize.F32
                  (@LClight.attr.mk Bool.false (@Option.none _))))
              (@LClight.val.Vsingle
                (@ClightN.Base.f32_of_bits
                  (@ClightN.Base.r32
                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (mb x (0 : Int))
                      (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (256 : Int)
                          (mb x
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                              (1 : Int))))
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                          (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (65536 : Int)
                            (mb x
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                                (2 : Int))))
                          (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (16777216 : Int)
                            (mb x
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (0 : Int)
                                (3 : Int))))))))))))))
  | nv_binop : (∀ (op : LClight.binary_operation) (a1 : LClight.expr) (a2 : LClight.expr)
      (ty : LClight.type) (t1 : LClight.type) (t2 : LClight.type) (v1 : LClight.val)
      (v2 : LClight.val) (v : LClight.val),
    ((neval defs le gv mb a1 v1)
      → ((has_type a1 t1)
          → ((neval defs le gv mb a2 v2)
              → ((has_type a2 t2)
                  → ((binop_ok op t1 t2 v1 v2 v)
                      → (neval defs le gv mb (@LClight.expr.Ebinop op a1 a2 ty) v)))))))
  | nv_cast : (∀ (a : LClight.expr) (ty : LClight.type) (t1 : LClight.type) (v1 : LClight.val)
      (v : LClight.val),
    ((neval defs le gv mb a v1)
      → ((has_type a t1)
          → ((cast_ok t1 ty v1 v) → (neval defs le gv mb (@LClight.expr.Ecast a ty) v)))))
  | nv_unop : (∀ (op : LClight.unary_operation) (a : LClight.expr) (ty : LClight.type)
      (t1 : LClight.type) (v1 : LClight.val) (v : LClight.val),
    ((neval defs le gv mb a v1)
      → ((has_type a t1)
          → ((unop_ok op t1 v1 v) → (neval defs le gv mb (@LClight.expr.Eunop op a ty) v)))))

inductive neval_list
    (defs :
      (List (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type))))
    (le : (LClight.ident → (Option LClight.val))) (gv : (LClight.ident → (Option LClight.val)))
    (mb : (LClight.ident → (Int → Int))) : (List LClight.expr) → (List LClight.type) →
    (List LClight.val) → Prop where
  | nl_nil : (neval_list defs le gv mb (@List.nil _) (@List.nil _) (@List.nil _))
  | nl_cons : (∀ (a : LClight.expr) (al : (List LClight.expr)) (ty : LClight.type)
      (tys : (List LClight.type)) (t1 : LClight.type) (v1 : LClight.val) (v : LClight.val)
      (vs : (List LClight.val)),
    ((neval defs le gv mb a v1)
      → ((has_type a t1)
          → ((cast_ok t1 ty v1 v)
              → ((neval_list defs le gv mb al tys vs)
                  → (neval_list defs le gv mb (@List.cons _ a al) (@List.cons _ ty tys)
                      (@List.cons _ v vs)))))))

inductive nexec
    (defs :
      (List (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type)))) :
    (LClight.ident → (Option LClight.val)) → (LClight.ident → (Option LClight.val)) →
    (LClight.ident → (Int → Int)) → LClight.statement → (List LClight.event) →
    (LClight.ident → (Option LClight.val)) → (LClight.ident → (Option LClight.val)) →
    (LClight.ident → (Int → Int)) → LClight.outcome → Prop where
  | nx_skip : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int))),
    (nexec defs le gv mb LClight.statement.Sskip (@List.nil _) le gv mb LClight.outcome.Out_normal))
  | nx_set : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (x : LClight.ident) (a : LClight.expr) (v : LClight.val)
      (le2 : (LClight.ident → (Option LClight.val))),
    ((neval defs le gv mb a v)
      → ((∀ (x_upd : LClight.ident),
            (((@Eq _ x_upd x) → (@Eq _ (le2 x_upd) (@Option.some _ v)))
              ∧ ((¬ (@Eq _ x_upd x)) → (@Eq _ (le2 x_upd) (le x_upd)))))
          → (nexec defs le gv mb (@LClight.statement.Sset x a) (@List.nil _) le2 gv mb
              LClight.outcome.Out_normal))))
  | nx_store : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (x : LClight.ident) (ty : LClight.type) (init : (List LClight.init_data)) (a : LClight.expr)
      (t1 : LClight.type) (v1 : LClight.val) (v : LClight.val)
      (gv2 : (LClight.ident → (Option LClight.val))),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type ty init Bool.false Bool.false)))
      → ((scalar ty)
          → ((neval defs le gv mb a v1)
              → ((has_type a t1)
                  → ((cast_ok t1 ty v1 v)
                      → ((gval ty v)
                          → ((∀ (x_upd : LClight.ident),
                                (((@Eq _ x_upd x) → (@Eq _ (gv2 x_upd) (@Option.some _ v)))
                                  ∧ ((¬ (@Eq _ x_upd x)) → (@Eq _ (gv2 x_upd) (gv x_upd)))))
                              → (nexec defs le gv mb
                                  (@LClight.statement.Sassign (@LClight.expr.Evar x ty) a)
                                  (@List.nil _) le gv2 mb LClight.outcome.Out_normal)))))))))
  | nx_store_word : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (x : LClight.ident) (n : Int) (i : LClight.expr) (k : UInt64) (a : LClight.expr)
      (t1 : LClight.type) (v1 : LClight.val) (w : UInt64) (mb2 : (LClight.ident → (Int → Int))),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type
            (@LClight.type.Tarray
              (@LClight.type.Tlong LClight.signedness.Unsigned
                (@LClight.attr.mk Bool.false (@Option.none _))) n
              (@LClight.attr.mk Bool.false (@Option.none _)))
            (@List.cons _
              (@LClight.init_data.Init_space
                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n)) (@List.nil _))
            Bool.false Bool.false)))
      → ((neval defs le gv mb i (@LClight.val.Vlong k))
          → ((has_type i
                (@LClight.type.Tlong LClight.signedness.Unsigned
                  (@LClight.attr.mk Bool.false (@Option.none _))))
              → ((@LE.le Int Int.instLEInt
                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                      (@ClightN.Base.zmod
                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int)
                          (@ClightN.Base.u64 k)) (18446744073709551616 : Int)) (8 : Int))
                    (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n))
                  → ((neval defs le gv mb a v1)
                      → ((has_type a t1)
                          → ((cast_ok t1
                                (@LClight.type.Tlong LClight.signedness.Unsigned
                                  (@LClight.attr.mk Bool.false (@Option.none _))) v1
                                (@LClight.val.Vlong w))
                              → ((∀ (y_sb : LClight.ident) (j_sb : Int),
                                    ((((@Eq _ y_sb x)
                                        ∧ ((@LE.le Int Int.instLEInt
                                        (@ClightN.Base.zmod
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int) (@ClightN.Base.u64 k))
                                        (18446744073709551616 : Int)) j_sb)
                                        ∧ (@LT.lt Int Int.instLTInt j_sb
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (@ClightN.Base.zmod
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int) (@ClightN.Base.u64 k))
                                        (18446744073709551616 : Int)) (8 : Int)))))
                                        → (@Eq _ (mb2 y_sb j_sb)
                                        (@ClightN.Base.zmod
                                        (@ClightN.Base.zdiv (@ClightN.Base.u64 w)
                                        (@ClightN.Base.pow2
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int)
                                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) j_sb
                                        (@ClightN.Base.zmod
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int) (@ClightN.Base.u64 k))
                                        (18446744073709551616 : Int)))))) (256 : Int))))
                                      ∧ ((¬ ((@Eq _ y_sb x)
                                        ∧ ((@LE.le Int Int.instLEInt
                                        (@ClightN.Base.zmod
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int) (@ClightN.Base.u64 k))
                                        (18446744073709551616 : Int)) j_sb)
                                        ∧ (@LT.lt Int Int.instLTInt j_sb
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (@ClightN.Base.zmod
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int) (@ClightN.Base.u64 k))
                                        (18446744073709551616 : Int)) (8 : Int))))))
                                        → (@Eq _ (mb2 y_sb j_sb) (mb y_sb j_sb)))))
                                  → (nexec defs le gv mb
                                      (@LClight.statement.Sassign
                                        (@LClight.expr.Ederef
                                        (@LClight.expr.Ebinop LClight.binary_operation.Oadd
                                        (@LClight.expr.Evar x
                                        (@LClight.type.Tarray
                                        (@LClight.type.Tlong LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.false (@Option.none _))) n
                                        (@LClight.attr.mk Bool.false (@Option.none _)))) i
                                        (@LClight.type.Tpointer
                                        (@LClight.type.Tlong LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.false (@Option.none _)))
                                        (@LClight.attr.mk Bool.false (@Option.none _))))
                                        (@LClight.type.Tlong LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.false (@Option.none _)))) a)
                                      (@List.nil _) le gv mb2 LClight.outcome.Out_normal))))))))))
  | nx_store_byte : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (x : LClight.ident) (n : Int) (i : LClight.expr) (k : UInt64) (a : LClight.expr)
      (t1 : LClight.type) (v1 : LClight.val) (c : UInt32) (mb2 : (LClight.ident → (Int → Int))),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type
            (@LClight.type.Tarray
              (@LClight.type.Tlong LClight.signedness.Unsigned
                (@LClight.attr.mk Bool.false (@Option.none _))) n
              (@LClight.attr.mk Bool.false (@Option.none _)))
            (@List.cons _
              (@LClight.init_data.Init_space
                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n)) (@List.nil _))
            Bool.false Bool.false)))
      → ((neval defs le gv mb i (@LClight.val.Vlong k))
          → ((has_type i
                (@LClight.type.Tlong LClight.signedness.Unsigned
                  (@LClight.attr.mk Bool.false (@Option.none _))))
              → ((@LT.lt Int Int.instLTInt (@ClightN.Base.u64 k)
                    (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n))
                  → ((neval defs le gv mb a v1)
                      → ((has_type a t1)
                          → ((cast_ok t1
                                (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
                                  (@LClight.attr.mk Bool.false (@Option.none _))) v1
                                (@LClight.val.Vint c))
                              → ((∀ (y_sb : LClight.ident) (j_sb : Int),
                                    ((((@Eq _ y_sb x)
                                        ∧ ((@LE.le Int Int.instLEInt (@ClightN.Base.u64 k) j_sb)
                                        ∧ (@LT.lt Int Int.instLTInt j_sb
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (@ClightN.Base.u64 k) (1 : Int)))))
                                        → (@Eq _ (mb2 y_sb j_sb)
                                        (@ClightN.Base.zmod
                                        (@ClightN.Base.zdiv (@ClightN.Base.u32 c)
                                        (@ClightN.Base.pow2
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int)
                                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) j_sb
                                        (@ClightN.Base.u64 k))))) (256 : Int))))
                                      ∧ ((¬ ((@Eq _ y_sb x)
                                        ∧ ((@LE.le Int Int.instLEInt (@ClightN.Base.u64 k) j_sb)
                                        ∧ (@LT.lt Int Int.instLTInt j_sb
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (@ClightN.Base.u64 k) (1 : Int))))))
                                        → (@Eq _ (mb2 y_sb j_sb) (mb y_sb j_sb)))))
                                  → (nexec defs le gv mb
                                      (@LClight.statement.Sassign
                                        (@LClight.expr.Ederef
                                        (@LClight.expr.Ebinop LClight.binary_operation.Oadd
                                        (@LClight.expr.Ecast
                                        (@LClight.expr.Evar x
                                        (@LClight.type.Tarray
                                        (@LClight.type.Tlong LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.false (@Option.none _))) n
                                        (@LClight.attr.mk Bool.false (@Option.none _))))
                                        (@LClight.type.Tpointer
                                        (@LClight.type.Tint LClight.intsize.I8
                                        LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.false (@Option.none _)))
                                        (@LClight.attr.mk Bool.false (@Option.none _)))) i
                                        (@LClight.type.Tpointer
                                        (@LClight.type.Tint LClight.intsize.I8
                                        LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.false (@Option.none _)))
                                        (@LClight.attr.mk Bool.false (@Option.none _))))
                                        (@LClight.type.Tint LClight.intsize.I8
                                        LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.false (@Option.none _)))) a)
                                      (@List.nil _) le gv mb2 LClight.outcome.Out_normal))))))))))
  | nx_store_cell64 : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (x : LClight.ident) (n : Int) (a : LClight.expr) (t1 : LClight.type) (v1 : LClight.val)
      (w : UInt64) (mb2 : (LClight.ident → (Int → Int))),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type
            (@LClight.type.Tarray
              (@LClight.type.Tlong LClight.signedness.Unsigned
                (@LClight.attr.mk Bool.false (@Option.none _))) n
              (@LClight.attr.mk Bool.false (@Option.none _)))
            (@List.cons _
              (@LClight.init_data.Init_space
                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n)) (@List.nil _))
            Bool.false Bool.false)))
      → ((@LE.le Int Int.instLEInt (1 : Int) n)
          → ((neval defs le gv mb a v1)
              → ((has_type a t1)
                  → ((cast_ok t1
                        (@LClight.type.Tlong LClight.signedness.Unsigned
                          (@LClight.attr.mk Bool.false (@Option.none _))) v1 (@LClight.val.Vlong w))
                      → ((∀ (y_sb : LClight.ident) (j_sb : Int),
                            ((((@Eq _ y_sb x)
                                  ∧ ((@LE.le Int Int.instLEInt (0 : Int) j_sb)
                                      ∧ (@LT.lt Int Int.instLTInt j_sb
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (0 : Int) (8 : Int)))))
                                → (@Eq _ (mb2 y_sb j_sb)
                                    (@ClightN.Base.zmod
                                      (@ClightN.Base.zdiv (@ClightN.Base.u64 w)
                                        (@ClightN.Base.pow2
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int)
                                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) j_sb
                                        (0 : Int))))) (256 : Int))))
                              ∧ ((¬ ((@Eq _ y_sb x)
                                        ∧ ((@LE.le Int Int.instLEInt (0 : Int) j_sb)
                                        ∧ (@LT.lt Int Int.instLTInt j_sb
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (0 : Int) (8 : Int))))))
                                  → (@Eq _ (mb2 y_sb j_sb) (mb y_sb j_sb)))))
                          → (nexec defs le gv mb
                              (@LClight.statement.Sassign
                                (@LClight.expr.Ederef
                                  (@LClight.expr.Ecast
                                    (@LClight.expr.Evar x
                                      (@LClight.type.Tarray
                                        (@LClight.type.Tlong LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.false (@Option.none _))) n
                                        (@LClight.attr.mk Bool.false (@Option.none _))))
                                    (@LClight.type.Tpointer
                                      (@LClight.type.Tlong LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.false (@Option.none _)))
                                      (@LClight.attr.mk Bool.false (@Option.none _))))
                                  (@LClight.type.Tlong LClight.signedness.Unsigned
                                    (@LClight.attr.mk Bool.false (@Option.none _)))) a)
                              (@List.nil _) le gv mb2 LClight.outcome.Out_normal))))))))
  | nx_store_cell32 : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (x : LClight.ident) (n : Int) (a : LClight.expr) (t1 : LClight.type) (v1 : LClight.val)
      (c : UInt32) (mb2 : (LClight.ident → (Int → Int))),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type
            (@LClight.type.Tarray
              (@LClight.type.Tlong LClight.signedness.Unsigned
                (@LClight.attr.mk Bool.false (@Option.none _))) n
              (@LClight.attr.mk Bool.false (@Option.none _)))
            (@List.cons _
              (@LClight.init_data.Init_space
                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n)) (@List.nil _))
            Bool.false Bool.false)))
      → ((@LE.le Int Int.instLEInt (1 : Int) n)
          → ((neval defs le gv mb a v1)
              → ((has_type a t1)
                  → ((cast_ok t1
                        (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
                          (@LClight.attr.mk Bool.false (@Option.none _))) v1 (@LClight.val.Vint c))
                      → ((∀ (y_sb : LClight.ident) (j_sb : Int),
                            ((((@Eq _ y_sb x)
                                  ∧ ((@LE.le Int Int.instLEInt (0 : Int) j_sb)
                                      ∧ (@LT.lt Int Int.instLTInt j_sb
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (0 : Int) (4 : Int)))))
                                → (@Eq _ (mb2 y_sb j_sb)
                                    (@ClightN.Base.zmod
                                      (@ClightN.Base.zdiv (@ClightN.Base.u32 c)
                                        (@ClightN.Base.pow2
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int)
                                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) j_sb
                                        (0 : Int))))) (256 : Int))))
                              ∧ ((¬ ((@Eq _ y_sb x)
                                        ∧ ((@LE.le Int Int.instLEInt (0 : Int) j_sb)
                                        ∧ (@LT.lt Int Int.instLTInt j_sb
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (0 : Int) (4 : Int))))))
                                  → (@Eq _ (mb2 y_sb j_sb) (mb y_sb j_sb)))))
                          → (nexec defs le gv mb
                              (@LClight.statement.Sassign
                                (@LClight.expr.Ederef
                                  (@LClight.expr.Ecast
                                    (@LClight.expr.Evar x
                                      (@LClight.type.Tarray
                                        (@LClight.type.Tlong LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.false (@Option.none _))) n
                                        (@LClight.attr.mk Bool.false (@Option.none _))))
                                    (@LClight.type.Tpointer
                                      (@LClight.type.Tint LClight.intsize.I32
                                        LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.false (@Option.none _)))
                                      (@LClight.attr.mk Bool.false (@Option.none _))))
                                  (@LClight.type.Tint LClight.intsize.I32
                                    LClight.signedness.Unsigned
                                    (@LClight.attr.mk Bool.false (@Option.none _)))) a)
                              (@List.nil _) le gv mb2 LClight.outcome.Out_normal))))))))
  | nx_store_cellf64 : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (x : LClight.ident) (n : Int) (a : LClight.expr) (t1 : LClight.type) (v1 : LClight.val)
      (f : LClight.float) (mb2 : (LClight.ident → (Int → Int))),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type
            (@LClight.type.Tarray
              (@LClight.type.Tlong LClight.signedness.Unsigned
                (@LClight.attr.mk Bool.false (@Option.none _))) n
              (@LClight.attr.mk Bool.false (@Option.none _)))
            (@List.cons _
              (@LClight.init_data.Init_space
                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n)) (@List.nil _))
            Bool.false Bool.false)))
      → ((@LE.le Int Int.instLEInt (1 : Int) n)
          → ((neval defs le gv mb a v1)
              → ((has_type a t1)
                  → ((cast_ok t1
                        (@LClight.type.Tfloat LClight.floatsize.F64
                          (@LClight.attr.mk Bool.false (@Option.none _))) v1
                        (@LClight.val.Vfloat f))
                      → ((∀ (y_sb : LClight.ident) (j_sb : Int),
                            ((((@Eq _ y_sb x)
                                  ∧ ((@LE.le Int Int.instLEInt (0 : Int) j_sb)
                                      ∧ (@LT.lt Int Int.instLTInt j_sb
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (0 : Int) (8 : Int)))))
                                → (@Eq _ (mb2 y_sb j_sb)
                                    (@ClightN.Base.zmod
                                      (@ClightN.Base.zdiv
                                        (@ClightN.Base.u64 (@ClightN.Base.f64_bits f))
                                        (@ClightN.Base.pow2
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int)
                                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) j_sb
                                        (0 : Int))))) (256 : Int))))
                              ∧ ((¬ ((@Eq _ y_sb x)
                                        ∧ ((@LE.le Int Int.instLEInt (0 : Int) j_sb)
                                        ∧ (@LT.lt Int Int.instLTInt j_sb
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (0 : Int) (8 : Int))))))
                                  → (@Eq _ (mb2 y_sb j_sb) (mb y_sb j_sb)))))
                          → (nexec defs le gv mb
                              (@LClight.statement.Sassign
                                (@LClight.expr.Ederef
                                  (@LClight.expr.Ecast
                                    (@LClight.expr.Evar x
                                      (@LClight.type.Tarray
                                        (@LClight.type.Tlong LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.false (@Option.none _))) n
                                        (@LClight.attr.mk Bool.false (@Option.none _))))
                                    (@LClight.type.Tpointer
                                      (@LClight.type.Tfloat LClight.floatsize.F64
                                        (@LClight.attr.mk Bool.false (@Option.none _)))
                                      (@LClight.attr.mk Bool.false (@Option.none _))))
                                  (@LClight.type.Tfloat LClight.floatsize.F64
                                    (@LClight.attr.mk Bool.false (@Option.none _)))) a)
                              (@List.nil _) le gv mb2 LClight.outcome.Out_normal))))))))
  | nx_store_cellf32 : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (x : LClight.ident) (n : Int) (a : LClight.expr) (t1 : LClight.type) (v1 : LClight.val)
      (f : LClight.float32) (mb2 : (LClight.ident → (Int → Int))),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type
            (@LClight.type.Tarray
              (@LClight.type.Tlong LClight.signedness.Unsigned
                (@LClight.attr.mk Bool.false (@Option.none _))) n
              (@LClight.attr.mk Bool.false (@Option.none _)))
            (@List.cons _
              (@LClight.init_data.Init_space
                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n)) (@List.nil _))
            Bool.false Bool.false)))
      → ((@LE.le Int Int.instLEInt (1 : Int) n)
          → ((neval defs le gv mb a v1)
              → ((has_type a t1)
                  → ((cast_ok t1
                        (@LClight.type.Tfloat LClight.floatsize.F32
                          (@LClight.attr.mk Bool.false (@Option.none _))) v1
                        (@LClight.val.Vsingle f))
                      → ((∀ (y_sb : LClight.ident) (j_sb : Int),
                            ((((@Eq _ y_sb x)
                                  ∧ ((@LE.le Int Int.instLEInt (0 : Int) j_sb)
                                      ∧ (@LT.lt Int Int.instLTInt j_sb
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (0 : Int) (4 : Int)))))
                                → (@Eq _ (mb2 y_sb j_sb)
                                    (@ClightN.Base.zmod
                                      (@ClightN.Base.zdiv
                                        (@ClightN.Base.u32 (@ClightN.Base.f32_bits f))
                                        (@ClightN.Base.pow2
                                        (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                                        (8 : Int)
                                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) j_sb
                                        (0 : Int))))) (256 : Int))))
                              ∧ ((¬ ((@Eq _ y_sb x)
                                        ∧ ((@LE.le Int Int.instLEInt (0 : Int) j_sb)
                                        ∧ (@LT.lt Int Int.instLTInt j_sb
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        (0 : Int) (4 : Int))))))
                                  → (@Eq _ (mb2 y_sb j_sb) (mb y_sb j_sb)))))
                          → (nexec defs le gv mb
                              (@LClight.statement.Sassign
                                (@LClight.expr.Ederef
                                  (@LClight.expr.Ecast
                                    (@LClight.expr.Evar x
                                      (@LClight.type.Tarray
                                        (@LClight.type.Tlong LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.false (@Option.none _))) n
                                        (@LClight.attr.mk Bool.false (@Option.none _))))
                                    (@LClight.type.Tpointer
                                      (@LClight.type.Tfloat LClight.floatsize.F32
                                        (@LClight.attr.mk Bool.false (@Option.none _)))
                                      (@LClight.attr.mk Bool.false (@Option.none _))))
                                  (@LClight.type.Tfloat LClight.floatsize.F32
                                    (@LClight.attr.mk Bool.false (@Option.none _)))) a)
                              (@List.nil _) le gv mb2 LClight.outcome.Out_normal))))))))
  | nx_out : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (x : LClight.ident) (init : (List LClight.init_data)) (a : LClight.expr) (t1 : LClight.type)
      (v1 : LClight.val) (i : UInt32),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type
            (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
              (@LClight.attr.mk Bool.true (@Option.none _))) init Bool.false Bool.true)))
      → ((neval defs le gv mb a v1)
          → ((has_type a t1)
              → ((cast_ok t1
                    (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
                      (@LClight.attr.mk Bool.true (@Option.none _))) v1 (@LClight.val.Vint i))
                  → (nexec defs le gv mb
                      (@LClight.statement.Sbuiltin (@Option.none _)
                        (@LClight.external_function.EF_vstore LClight.memory_chunk.Mint32)
                        (@List.cons _
                          (@LClight.type.Tpointer
                            (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
                              (@LClight.attr.mk Bool.true (@Option.none _)))
                            (@LClight.attr.mk Bool.false (@Option.none _)))
                          (@List.cons _
                            (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
                              (@LClight.attr.mk Bool.true (@Option.none _))) (@List.nil _)))
                        (@List.cons _
                          (@LClight.expr.Eaddrof
                            (@LClight.expr.Evar x
                              (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
                                (@LClight.attr.mk Bool.true (@Option.none _))))
                            (@LClight.type.Tpointer
                              (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
                                (@LClight.attr.mk Bool.true (@Option.none _)))
                              (@LClight.attr.mk Bool.false (@Option.none _))))
                          (@List.cons _ a (@List.nil _))))
                      (@List.cons _
                        (@LClight.event.Event_vstore LClight.memory_chunk.Mint32 x
                          (@ClightN.Base.rptr (0 : Int)) (@LClight.eventval.EVint i)) (@List.nil _))
                      le gv mb LClight.outcome.Out_normal))))))
  | nx_vload : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (t : LClight.ident) (x : LClight.ident) (ty : LClight.type) (n : Int)
      (init : (List LClight.init_data)) (ch : LClight.memory_chunk) (sz : Int) (i : LClight.expr)
      (k : UInt64) (j : UInt32) (v : LClight.val) (le2 : (LClight.ident → (Option LClight.val))),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type
            (@LClight.type.Tarray ty n (@LClight.attr.mk Bool.false (@Option.none _))) init
            Bool.false Bool.true)))
      → ((neval defs le gv mb i (@LClight.val.Vlong k))
          → ((has_type i
                (@LClight.type.Tlong LClight.signedness.Unsigned
                  (@LClight.attr.mk Bool.false (@Option.none _))))
              → ((vload_ok ch ty sz j v)
                  → ((∀ (x_upd : LClight.ident),
                        (((@Eq _ x_upd t) → (@Eq _ (le2 x_upd) (@Option.some _ v)))
                          ∧ ((¬ (@Eq _ x_upd t)) → (@Eq _ (le2 x_upd) (le x_upd)))))
                      → (nexec defs le gv mb
                          (@LClight.statement.Sbuiltin (@Option.some _ t)
                            (@LClight.external_function.EF_vload ch)
                            (@List.cons _
                              (@LClight.type.Tpointer ty
                                (@LClight.attr.mk Bool.false (@Option.none _))) (@List.nil _))
                            (@List.cons _
                              (@LClight.expr.Eaddrof
                                (@LClight.expr.Ederef
                                  (@LClight.expr.Ebinop LClight.binary_operation.Oadd
                                    (@LClight.expr.Evar x
                                      (@LClight.type.Tarray ty n
                                        (@LClight.attr.mk Bool.false (@Option.none _)))) i
                                    (@LClight.type.Tpointer ty
                                      (@LClight.attr.mk Bool.false (@Option.none _)))) ty)
                                (@LClight.type.Tpointer ty
                                  (@LClight.attr.mk Bool.false (@Option.none _)))) (@List.nil _)))
                          (@List.cons _
                            (@LClight.event.Event_vload ch x
                              (@ClightN.Base.rptr
                                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) sz
                                  (@ClightN.Base.u64 k))) (@LClight.eventval.EVint j))
                            (@List.nil _)) le2 gv mb LClight.outcome.Out_normal)))))))
  | nx_vstore : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (x : LClight.ident) (n : Int) (init : (List LClight.init_data)) (i : LClight.expr)
      (k : UInt64) (a : LClight.expr) (t1 : LClight.type) (v1 : LClight.val) (c : UInt32),
    ((in_defs defs x
        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
          (@LClight.globvar.mk LClight.type
            (@LClight.type.Tarray
              (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
                (@LClight.attr.mk Bool.true (@Option.none _))) n
              (@LClight.attr.mk Bool.false (@Option.none _))) init Bool.false Bool.true)))
      → ((neval defs le gv mb i (@LClight.val.Vlong k))
          → ((has_type i
                (@LClight.type.Tlong LClight.signedness.Unsigned
                  (@LClight.attr.mk Bool.false (@Option.none _))))
              → ((neval defs le gv mb a v1)
                  → ((has_type a t1)
                      → ((cast_ok t1
                            (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
                              (@LClight.attr.mk Bool.true (@Option.none _))) v1
                            (@LClight.val.Vint c))
                          → (nexec defs le gv mb
                              (@LClight.statement.Sbuiltin (@Option.none _)
                                (@LClight.external_function.EF_vstore LClight.memory_chunk.Mint32)
                                (@List.cons _
                                  (@LClight.type.Tpointer
                                    (@LClight.type.Tint LClight.intsize.I32
                                      LClight.signedness.Unsigned
                                      (@LClight.attr.mk Bool.true (@Option.none _)))
                                    (@LClight.attr.mk Bool.false (@Option.none _)))
                                  (@List.cons _
                                    (@LClight.type.Tint LClight.intsize.I32
                                      LClight.signedness.Unsigned
                                      (@LClight.attr.mk Bool.true (@Option.none _))) (@List.nil _)))
                                (@List.cons _
                                  (@LClight.expr.Eaddrof
                                    (@LClight.expr.Ederef
                                      (@LClight.expr.Ebinop LClight.binary_operation.Oadd
                                        (@LClight.expr.Evar x
                                        (@LClight.type.Tarray
                                        (@LClight.type.Tint LClight.intsize.I32
                                        LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.true (@Option.none _))) n
                                        (@LClight.attr.mk Bool.false (@Option.none _)))) i
                                        (@LClight.type.Tpointer
                                        (@LClight.type.Tint LClight.intsize.I32
                                        LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.true (@Option.none _)))
                                        (@LClight.attr.mk Bool.false (@Option.none _))))
                                      (@LClight.type.Tint LClight.intsize.I32
                                        LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.true (@Option.none _))))
                                    (@LClight.type.Tpointer
                                      (@LClight.type.Tint LClight.intsize.I32
                                        LClight.signedness.Unsigned
                                        (@LClight.attr.mk Bool.true (@Option.none _)))
                                      (@LClight.attr.mk Bool.false (@Option.none _))))
                                  (@List.cons _ a (@List.nil _))))
                              (@List.cons _
                                (@LClight.event.Event_vstore LClight.memory_chunk.Mint32 x
                                  (@ClightN.Base.rptr
                                    (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (4 : Int)
                                      (@ClightN.Base.u64 k))) (@LClight.eventval.EVint c))
                                (@List.nil _)) le gv mb LClight.outcome.Out_normal))))))))
  | nx_call : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (optid : (Option LClight.ident)) (x : LClight.ident) (tys : (List LClight.type))
      (ret : LClight.type) (cc : LClight.calling_convention) (al : (List LClight.expr))
      (vs : (List LClight.val)) (params : (List (LClight.ident × LClight.type)))
      (temps : (List (LClight.ident × LClight.type))) (body : LClight.statement)
      (le0 : (LClight.ident → (Option LClight.val))) (le1 : (LClight.ident → (Option LClight.val)))
      (t : (List LClight.event)) (le2 : (LClight.ident → (Option LClight.val)))
      (gv2 : (LClight.ident → (Option LClight.val))) (mb2 : (LClight.ident → (Int → Int)))
      (out : LClight.outcome) (v : LClight.val) (le3 : (LClight.ident → (Option LClight.val))),
    ((in_defs defs x
        (@LClight.globdef.Gfun (@LClight.fundef LClight.function) LClight.type
          (@LClight.fundef.Internal LClight.function
            (@LClight.function.mk ret cc params (@List.nil _) temps body))))
      → ((params_types params tys)
          → ((neval_list defs le gv mb al tys vs)
              → ((norepet_names params)
                  → ((disjoint_names params temps)
                      → ((undef_temps temps le0)
                          → ((bind_params params vs le0 le1)
                              → ((nexec defs le1 gv mb body t le2 gv2 mb2 out)
                                  → ((result_ok out ret v)
                                      → ((set_opt optid v le le3)
                                        → (nexec defs le gv mb
                                        (@LClight.statement.Scall optid
                                        (@LClight.expr.Evar x (@LClight.type.Tfunction tys ret cc))
                                        al) t le3 gv2 mb2 LClight.outcome.Out_normal))))))))))))
  | nx_sqrt : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (optid : (Option LClight.ident)) (x : LClight.ident) (al : (List LClight.expr))
      (f : LClight.float) (le2 : (LClight.ident → (Option LClight.val))),
    ((in_defs defs x
        (@LClight.globdef.Gfun (@LClight.fundef LClight.function) LClight.type
          (@LClight.fundef.External LClight.function
            (@LClight.external_function.EF_builtin "__builtin_fsqrt"
              (@LClight.signature.mk (@List.cons _ LClight.xtype.Xfloat (@List.nil _))
                LClight.xtype.Xfloat
                (@LClight.calling_convention.mk (@Option.none _) Bool.false Bool.false)))
            (@List.cons _
              (@LClight.type.Tfloat LClight.floatsize.F64
                (@LClight.attr.mk Bool.false (@Option.none _))) (@List.nil _))
            (@LClight.type.Tfloat LClight.floatsize.F64
              (@LClight.attr.mk Bool.false (@Option.none _)))
            (@LClight.calling_convention.mk (@Option.none _) Bool.false Bool.false))))
      → ((neval_list defs le gv mb al
            (@List.cons _
              (@LClight.type.Tfloat LClight.floatsize.F64
                (@LClight.attr.mk Bool.false (@Option.none _))) (@List.nil _))
            (@List.cons _ (@LClight.val.Vfloat f) (@List.nil _)))
          → ((set_opt optid (@LClight.val.Vfloat (@LClight.Float.sqrt LClight.Archi.aarch64 f)) le
                le2)
              → (nexec defs le gv mb
                  (@LClight.statement.Scall optid
                    (@LClight.expr.Evar x
                      (@LClight.type.Tfunction
                        (@List.cons _
                          (@LClight.type.Tfloat LClight.floatsize.F64
                            (@LClight.attr.mk Bool.false (@Option.none _))) (@List.nil _))
                        (@LClight.type.Tfloat LClight.floatsize.F64
                          (@LClight.attr.mk Bool.false (@Option.none _)))
                        (@LClight.calling_convention.mk (@Option.none _) Bool.false Bool.false)))
                    al) (@List.nil _) le2 gv mb LClight.outcome.Out_normal)))))
  | nx_seq1 : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (s1 : LClight.statement) (s2 : LClight.statement) (t1 : (List LClight.event))
      (le1 : (LClight.ident → (Option LClight.val))) (gv1 : (LClight.ident → (Option LClight.val)))
      (mb1 : (LClight.ident → (Int → Int))) (t2 : (List LClight.event))
      (le2 : (LClight.ident → (Option LClight.val))) (gv2 : (LClight.ident → (Option LClight.val)))
      (mb2 : (LClight.ident → (Int → Int))) (out : LClight.outcome),
    ((nexec defs le gv mb s1 t1 le1 gv1 mb1 LClight.outcome.Out_normal)
      → ((nexec defs le1 gv1 mb1 s2 t2 le2 gv2 mb2 out)
          → (nexec defs le gv mb (@LClight.statement.Ssequence s1 s2) (@ClightN.Base.app t1 t2) le2
              gv2 mb2 out))))
  | nx_seq2 : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (s1 : LClight.statement) (s2 : LClight.statement) (t1 : (List LClight.event))
      (le1 : (LClight.ident → (Option LClight.val))) (gv1 : (LClight.ident → (Option LClight.val)))
      (mb1 : (LClight.ident → (Int → Int))) (out : LClight.outcome),
    ((nexec defs le gv mb s1 t1 le1 gv1 mb1 out)
      → ((¬ (@Eq _ out LClight.outcome.Out_normal))
          → (nexec defs le gv mb (@LClight.statement.Ssequence s1 s2) t1 le1 gv1 mb1 out))))
  | nx_if_true : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (a : LClight.expr) (s1 : LClight.statement) (s2 : LClight.statement) (v : LClight.val)
      (ta : LClight.type) (t : (List LClight.event)) (le2 : (LClight.ident → (Option LClight.val)))
      (gv2 : (LClight.ident → (Option LClight.val))) (mb2 : (LClight.ident → (Int → Int)))
      (out : LClight.outcome),
    ((neval defs le gv mb a v)
      → ((has_type a ta)
          → ((bool_ok ta v Bool.true)
              → ((nexec defs le gv mb s1 t le2 gv2 mb2 out)
                  → (nexec defs le gv mb (@LClight.statement.Sifthenelse a s1 s2) t le2 gv2 mb2
                      out))))))
  | nx_if_false : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (a : LClight.expr) (s1 : LClight.statement) (s2 : LClight.statement) (v : LClight.val)
      (ta : LClight.type) (t : (List LClight.event)) (le2 : (LClight.ident → (Option LClight.val)))
      (gv2 : (LClight.ident → (Option LClight.val))) (mb2 : (LClight.ident → (Int → Int)))
      (out : LClight.outcome),
    ((neval defs le gv mb a v)
      → ((has_type a ta)
          → ((bool_ok ta v Bool.false)
              → ((nexec defs le gv mb s2 t le2 gv2 mb2 out)
                  → (nexec defs le gv mb (@LClight.statement.Sifthenelse a s1 s2) t le2 gv2 mb2
                      out))))))
  | nx_return_none : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int))),
    (nexec defs le gv mb (@LClight.statement.Sreturn (@Option.none _)) (@List.nil _) le gv mb
      (@LClight.outcome.Out_return (@Option.none _))))
  | nx_return_some : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (a : LClight.expr) (v : LClight.val) (ta : LClight.type),
    ((neval defs le gv mb a v)
      → ((has_type a ta)
          → (nexec defs le gv mb (@LClight.statement.Sreturn (@Option.some _ a)) (@List.nil _) le gv
              mb (@LClight.outcome.Out_return (@Option.some _ (@Prod.mk _ _ v ta)))))))
  | nx_break : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int))),
    (nexec defs le gv mb LClight.statement.Sbreak (@List.nil _) le gv mb LClight.outcome.Out_break))
  | nx_continue : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int))),
    (nexec defs le gv mb LClight.statement.Scontinue (@List.nil _) le gv mb
      LClight.outcome.Out_continue))
  | nx_loop_stop1 : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (s1 : LClight.statement) (s2 : LClight.statement) (t : (List LClight.event))
      (le1 : (LClight.ident → (Option LClight.val))) (gv1 : (LClight.ident → (Option LClight.val)))
      (mb1 : (LClight.ident → (Int → Int))) (out1 : LClight.outcome) (out : LClight.outcome),
    ((nexec defs le gv mb s1 t le1 gv1 mb1 out1)
      → ((((@Eq _ out1 LClight.outcome.Out_break) ∧ (@Eq _ out LClight.outcome.Out_normal))
            ∨ (∃ (r : (Option (LClight.val × LClight.type))),
                ((@Eq _ out1 (@LClight.outcome.Out_return r))
                  ∧ (@Eq _ out (@LClight.outcome.Out_return r)))))
          → (nexec defs le gv mb (@LClight.statement.Sloop s1 s2) t le1 gv1 mb1 out))))
  | nx_loop_stop2 : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (s1 : LClight.statement) (s2 : LClight.statement) (t1 : (List LClight.event))
      (le1 : (LClight.ident → (Option LClight.val))) (gv1 : (LClight.ident → (Option LClight.val)))
      (mb1 : (LClight.ident → (Int → Int))) (out1 : LClight.outcome) (t2 : (List LClight.event))
      (le2 : (LClight.ident → (Option LClight.val))) (gv2 : (LClight.ident → (Option LClight.val)))
      (mb2 : (LClight.ident → (Int → Int))) (out2 : LClight.outcome) (out : LClight.outcome),
    ((nexec defs le gv mb s1 t1 le1 gv1 mb1 out1)
      → (((@Eq _ out1 LClight.outcome.Out_normal) ∨ (@Eq _ out1 LClight.outcome.Out_continue))
          → ((nexec defs le1 gv1 mb1 s2 t2 le2 gv2 mb2 out2)
              → ((((@Eq _ out2 LClight.outcome.Out_break) ∧ (@Eq _ out LClight.outcome.Out_normal))
                    ∨ (∃ (r : (Option (LClight.val × LClight.type))),
                        ((@Eq _ out2 (@LClight.outcome.Out_return r))
                          ∧ (@Eq _ out (@LClight.outcome.Out_return r)))))
                  → (nexec defs le gv mb (@LClight.statement.Sloop s1 s2) (@ClightN.Base.app t1 t2)
                      le2 gv2 mb2 out))))))
  | nx_loop : (∀ (le : (LClight.ident → (Option LClight.val)))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int)))
      (s1 : LClight.statement) (s2 : LClight.statement) (t1 : (List LClight.event))
      (le1 : (LClight.ident → (Option LClight.val))) (gv1 : (LClight.ident → (Option LClight.val)))
      (mb1 : (LClight.ident → (Int → Int))) (out1 : LClight.outcome) (t2 : (List LClight.event))
      (le2 : (LClight.ident → (Option LClight.val))) (gv2 : (LClight.ident → (Option LClight.val)))
      (mb2 : (LClight.ident → (Int → Int))) (t3 : (List LClight.event))
      (le3 : (LClight.ident → (Option LClight.val))) (gv3 : (LClight.ident → (Option LClight.val)))
      (mb3 : (LClight.ident → (Int → Int))) (out : LClight.outcome),
    ((nexec defs le gv mb s1 t1 le1 gv1 mb1 out1)
      → (((@Eq _ out1 LClight.outcome.Out_normal) ∨ (@Eq _ out1 LClight.outcome.Out_continue))
          → ((nexec defs le1 gv1 mb1 s2 t2 le2 gv2 mb2 LClight.outcome.Out_normal)
              → ((nexec defs le2 gv2 mb2 (@LClight.statement.Sloop s1 s2) t3 le3 gv3 mb3 out)
                  → (nexec defs le gv mb (@LClight.statement.Sloop s1 s2)
                      (@ClightN.Base.app t1 (@ClightN.Base.app t2 t3)) le3 gv3 mb3 out))))))

inductive ninit :
    (List (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type))) →
    (LClight.ident → (Option LClight.val)) → (LClight.ident → (Int → Int)) → Prop where
  | ni_intro : (∀ (defs :
        (List (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type))))
      (gv : (LClight.ident → (Option LClight.val))) (mb : (LClight.ident → (Int → Int))),
    ((norepet_defs defs)
      → ((∀ (x : LClight.ident) (ty : LClight.type) (init : (List LClight.init_data)) (ro : Bool)
              (vol : Bool),
            ((in_defs defs x
                (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
                  (@LClight.globvar.mk LClight.type ty init ro vol))) → (init_ok init)))
          → ((∀ (x : LClight.ident) (ty : LClight.type) (init : (List LClight.init_data)),
                ((in_defs defs x
                    (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
                      (@LClight.globvar.mk LClight.type ty init Bool.false Bool.false)))
                  → ((scalar ty)
                      → (∃ (v : LClight.val),
                          ((ginit ty init v) ∧ (@Eq _ (gv x) (@Option.some _ v)))))))
              → ((∀ (x : LClight.ident) (n : Int) (j : Int),
                    ((in_defs defs x
                        (@LClight.globdef.Gvar (@LClight.fundef LClight.function) LClight.type
                          (@LClight.globvar.mk LClight.type
                            (@LClight.type.Tarray
                              (@LClight.type.Tlong LClight.signedness.Unsigned
                                (@LClight.attr.mk Bool.false (@Option.none _))) n
                              (@LClight.attr.mk Bool.false (@Option.none _)))
                            (@List.cons _
                              (@LClight.init_data.Init_space
                                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n))
                              (@List.nil _)) Bool.false Bool.false)))
                      → ((@LE.le Int Int.instLEInt (0 : Int) j)
                          → ((@LT.lt Int Int.instLTInt j
                                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (8 : Int) n))
                              → (@Eq _ (mb x j) (0 : Int)))))) → (ninit defs gv mb))))))

inductive nprog :
    (List (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type))) →
    LClight.ident → (List LClight.event) → UInt32 → Prop where
  | np_intro : (∀ (defs :
        (List (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type))))
      (main : LClight.ident) (temps : (List (LClight.ident × LClight.type)))
      (body : LClight.statement) (gv0 : (LClight.ident → (Option LClight.val)))
      (mb0 : (LClight.ident → (Int → Int))) (le0 : (LClight.ident → (Option LClight.val)))
      (t : (List LClight.event)) (le2 : (LClight.ident → (Option LClight.val)))
      (gv2 : (LClight.ident → (Option LClight.val))) (mb2 : (LClight.ident → (Int → Int)))
      (out : LClight.outcome) (r : UInt32),
    ((ninit defs gv0 mb0)
      → ((in_defs defs main
            (@LClight.globdef.Gfun (@LClight.fundef LClight.function) LClight.type
              (@LClight.fundef.Internal LClight.function
                (@LClight.function.mk
                  (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
                    (@LClight.attr.mk Bool.false (@Option.none _)))
                  (@LClight.calling_convention.mk (@Option.none _) Bool.false Bool.false)
                  (@List.nil _) (@List.nil _) temps body))))
          → ((undef_temps temps le0)
              → ((nexec defs le0 gv0 mb0 body t le2 gv2 mb2 out)
                  → ((result_ok out
                        (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
                          (@LClight.attr.mk Bool.false (@Option.none _))) (@LClight.val.Vint r))
                      → (nprog defs main t r)))))))

inductive loop_in : LClight.statement → LClight.statement → LClight.statement → LClight.statement →
    Prop where
  | li_loop : (∀ (body : LClight.statement) (post : LClight.statement),
    (loop_in (@LClight.statement.Sloop body post) LClight.statement.Sskip body post))
  | li_after : (∀ (s : LClight.statement) (init : LClight.statement) (body : LClight.statement)
      (post : LClight.statement) (rest : LClight.statement),
    ((loop_in s init body post) → (loop_in (@LClight.statement.Ssequence s rest) init body post)))
  | li_before : (∀ (s : LClight.statement) (init : LClight.statement) (body : LClight.statement)
      (post : LClight.statement) (pre : LClight.statement),
    ((loop_in s init body post)
      → (loop_in (@LClight.statement.Ssequence pre s) (@LClight.statement.Ssequence pre init) body
          post)))

inductive nreacts :
    (List (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type))) →
    LClight.ident → (List LClight.event) → (Nat → (List LClight.event)) → Prop where
  | nr_intro : (∀ (defs :
        (List (LClight.ident × (@LClight.globdef (@LClight.fundef LClight.function) LClight.type))))
      (main : LClight.ident) (temps : (List (LClight.ident × LClight.type)))
      (body : LClight.statement) (gv0 : (LClight.ident → (Option LClight.val)))
      (mb0 : (LClight.ident → (Int → Int))) (le0 : (LClight.ident → (Option LClight.val)))
      (init : LClight.statement) (lbody : LClight.statement) (lpost : LClight.statement)
      (t0 : (List LClight.event)) (W : (Nat → (List LClight.event)))
      (Inv :
        (Nat
          → ((LClight.ident → (Option LClight.val))
              → ((LClight.ident → (Option LClight.val))
                  → ((LClight.ident → (Int → Int)) → Prop))))),
    ((∀ (n : Nat), (¬ (@Eq _ (W n) (@List.nil _))))
      → ((ninit defs gv0 mb0)
          → ((in_defs defs main
                (@LClight.globdef.Gfun (@LClight.fundef LClight.function) LClight.type
                  (@LClight.fundef.Internal LClight.function
                    (@LClight.function.mk
                      (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
                        (@LClight.attr.mk Bool.false (@Option.none _)))
                      (@LClight.calling_convention.mk (@Option.none _) Bool.false Bool.false)
                      (@List.nil _) (@List.nil _) temps body))))
              → ((undef_temps temps le0)
                  → ((loop_in body init lbody lpost)
                      → ((∃ (le : (LClight.ident → (Option LClight.val)))
                              (gv : (LClight.ident → (Option LClight.val)))
                              (mb : (LClight.ident → (Int → Int))),
                            ((nexec defs le0 gv0 mb0 init t0 le gv mb LClight.outcome.Out_normal)
                              ∧ (Inv Nat.zero le gv mb)))
                          → ((∀ (n : Nat) (le : (LClight.ident → (Option LClight.val)))
                                  (gv : (LClight.ident → (Option LClight.val)))
                                  (mb : (LClight.ident → (Int → Int))),
                                ((Inv n le gv mb)
                                  → (∃ (le2 : (LClight.ident → (Option LClight.val)))
                                        (gv2 : (LClight.ident → (Option LClight.val)))
                                        (mb2 : (LClight.ident → (Int → Int))),
                                      ((nexec defs le gv mb
                                        (@LClight.statement.Ssequence lbody lpost) (W n) le2 gv2 mb2
                                        LClight.outcome.Out_normal)
                                        ∧ (Inv (@Nat.succ n) le2 gv2 mb2)))))
                              → (nreacts defs main t0 W)))))))))

inductive nreads : (Nat → UInt32) → Nat → (List LClight.event) → Prop where
  | nr_nil : (∀ (s : (Nat → UInt32)) (c : Nat), (nreads s c (@List.nil _)))
  | nr_load : (∀ (s : (Nat → UInt32)) (c : Nat) (ch : LClight.memory_chunk) (x : LClight.ident)
      (o : LClight.ptrofs) (t : (List LClight.event)),
    ((nreads s (@Nat.succ c) t)
      → (nreads s c
          (@List.cons _ (@LClight.event.Event_vload ch x o (@LClight.eventval.EVint (s c))) t))))
  | nr_store : (∀ (s : (Nat → UInt32)) (c : Nat) (ch : LClight.memory_chunk) (x : LClight.ident)
      (o : LClight.ptrofs) (ev : LClight.eventval) (t : (List LClight.event)),
    ((nreads s c t) → (nreads s c (@List.cons _ (@LClight.event.Event_vstore ch x o ev) t))))

def stmt_add_ul_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oadd v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oadd
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_sub_ul_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Osub v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Osub
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_mul_ul_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Omul v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Omul
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_div_ul_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Odiv v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Odiv
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_mod_ul_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Omod v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Omod
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_and_ul_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oand v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oand
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_or_ul_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oor v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oor
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_xor_ul_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oxor v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oxor
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_shl_ul_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oshl v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oshl
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_shr_ul_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oshr v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oshr
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_eq_ul_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oeq v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oeq
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_ne_ul_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.One v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.One
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_lt_ul_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Olt v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Olt
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_le_ul_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Ole v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Ole
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_gt_ul_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Ogt v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Ogt
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_ge_ul_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oge v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oge
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_lt_sl_sl : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Olt v1
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Olt
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_le_sl_sl : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Ole v1
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Ole
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_shr_sl_ul : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oshr v1
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oshr
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_add_ui_ui : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oadd v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oadd
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_sub_ui_ui : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Osub v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Osub
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_and_ui_ui : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oand v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oand
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_shl_ui_ui : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oshl v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oshl
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_shr_ui_ui : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oshr v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oshr
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_eq_ui_ui : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oeq v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oeq
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_ne_ui_ui : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.One v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.One
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_lt_ui_ui : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Olt v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Olt
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_gt_ui_ui : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Ogt v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Ogt
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_ge_ui_ui : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oge v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oge
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_add_d_d : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oadd v1
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oadd
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_sub_d_d : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Osub v1
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Osub
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_mul_d_d : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Omul v1
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Omul
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_div_d_d : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Odiv v1
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Odiv
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_eq_d_d : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oeq v1
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oeq
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_ne_d_d : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.One v1
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.One
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_lt_d_d : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Olt v1
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Olt
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_le_d_d : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Ole v1
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Ole
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_ge_d_d : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oge v1
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oge
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_add_f_f : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oadd v1
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oadd
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_sub_f_f : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Osub v1
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Osub
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_mul_f_f : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Omul v1
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Omul
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_div_f_f : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Odiv v1
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Odiv
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_eq_f_f : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oeq v1
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oeq
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_ne_f_f : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.One v1
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.One
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_lt_f_f : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Olt v1
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Olt
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_le_f_f : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Ole v1
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Ole
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_ge_f_f : Prop :=
  (∀ (ce : Unit) (v1 : LClight.val) (v2 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_binop ce LClight.binary_operation.Oge v1
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v2
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (binop_ok LClight.binary_operation.Oge
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v2 v)))

def stmt_cast_si_ui : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_ui_si : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_ul_ui : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_ui_ul : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_ul_sl : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_sl_ul : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tlong LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_uc_ul : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_uc_ui : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_ul_uc : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_ui_uc : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_vuc_ul : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.true (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.true (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_vui_ul : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.true (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.true (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_ui_vui : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.true (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.true (@Option.none _))) v1 v)))

def stmt_cast_ul_ul : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_ui_ui : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_uc_uc : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I8 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_si_si : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_d_d : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_f_f : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_ul_d : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_d_ul : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_f_d : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_d_f : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_si_f : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_ui_f : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_ul_f : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_f_si : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_cast_f_ul : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_cast v1
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (cast_ok
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _)))
          (@LClight.type.Tlong LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_bool_si : Prop :=
  (∀ (v : LClight.val) (b : Bool) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.bool_val v
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ b))
      ↔ (bool_ok
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Signed
            (@LClight.attr.mk Bool.false (@Option.none _))) v b)))

def stmt_bool_ui : Prop :=
  (∀ (v : LClight.val) (b : Bool) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.bool_val v
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ b))
      ↔ (bool_ok
          (@LClight.type.Tint LClight.intsize.I32 LClight.signedness.Unsigned
            (@LClight.attr.mk Bool.false (@Option.none _))) v b)))

def stmt_neg_d : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_unop LClight.unary_operation.Oneg v1
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (unop_ok LClight.unary_operation.Oneg
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_abs_d : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_unop LClight.unary_operation.Oabsfloat v1
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (unop_ok LClight.unary_operation.Oabsfloat
          (@LClight.type.Tfloat LClight.floatsize.F64
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_neg_f : Prop :=
  (∀ (v1 : LClight.val) (v : LClight.val) (m : LClight.mem),
    ((@Eq _
        (@ClightN.Base.sem_unop LClight.unary_operation.Oneg v1
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) m) (@Option.some _ v))
      ↔ (unop_ok LClight.unary_operation.Oneg
          (@LClight.type.Tfloat LClight.floatsize.F32
            (@LClight.attr.mk Bool.false (@Option.none _))) v1 v)))

def stmt_const_int : Prop :=
  (∀ (ge : LClight.genv) (e : LClight.env) (le : LClight.temp_env) (m : LClight.mem) (i : UInt32)
      (ty : LClight.type) (v : LClight.val),
    ((@ClightN.Base.eval_expr ge e le m (@LClight.expr.Econst_int i ty) v)
      ↔ (@Eq _ v (@LClight.val.Vint i))))

def stmt_const_long : Prop :=
  (∀ (ge : LClight.genv) (e : LClight.env) (le : LClight.temp_env) (m : LClight.mem) (i : UInt64)
      (ty : LClight.type) (v : LClight.val),
    ((@ClightN.Base.eval_expr ge e le m (@LClight.expr.Econst_long i ty) v)
      ↔ (@Eq _ v (@LClight.val.Vlong i))))

def stmt_u32_range : Prop :=
  (∀ (x : UInt32),
    ((@LE.le Int Int.instLEInt (0 : Int) (@ClightN.Base.u32 x))
      ∧ (@LT.lt Int Int.instLTInt (@ClightN.Base.u32 x) (4294967296 : Int))))

def stmt_u32_r32 : Prop :=
  (∀ (z : Int),
    (@Eq _ (@ClightN.Base.u32 (@ClightN.Base.r32 z)) (@ClightN.Base.zmod z (4294967296 : Int))))

def stmt_r32_u32 : Prop :=
  (∀ (x : UInt32), (@Eq _ (@ClightN.Base.r32 (@ClightN.Base.u32 x)) x))

def stmt_u64_range : Prop :=
  (∀ (x : UInt64),
    ((@LE.le Int Int.instLEInt (0 : Int) (@ClightN.Base.u64 x))
      ∧ (@LT.lt Int Int.instLTInt (@ClightN.Base.u64 x) (18446744073709551616 : Int))))

def stmt_u64_r64 : Prop :=
  (∀ (z : Int),
    (@Eq _ (@ClightN.Base.u64 (@ClightN.Base.r64 z))
      (@ClightN.Base.zmod z (18446744073709551616 : Int))))

def stmt_r64_u64 : Prop :=
  (∀ (x : UInt64), (@Eq _ (@ClightN.Base.r64 (@ClightN.Base.u64 x)) x))

def stmt_s64_low : Prop :=
  (∀ (x : UInt64),
    ((@LT.lt Int Int.instLTInt (@ClightN.Base.u64 x) (9223372036854775808 : Int))
      → (@Eq _ (@ClightN.Base.s64 x) (@ClightN.Base.u64 x))))

def stmt_s64_high : Prop :=
  (∀ (x : UInt64),
    ((@LE.le Int Int.instLEInt (9223372036854775808 : Int) (@ClightN.Base.u64 x))
      → (@Eq _ (@ClightN.Base.s64 x)
          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@ClightN.Base.u64 x)
            (18446744073709551616 : Int)))))

def stmt_zdiv_zmod : Prop :=
  (∀ (a : Int) (b : Int),
    ((@LT.lt Int Int.instLTInt (0 : Int) b)
      → ((@Eq _ a
            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
              (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) b (@ClightN.Base.zdiv a b))
              (@ClightN.Base.zmod a b)))
          ∧ ((@LE.le Int Int.instLEInt (0 : Int) (@ClightN.Base.zmod a b))
              ∧ (@LT.lt Int Int.instLTInt (@ClightN.Base.zmod a b) b)))))

def stmt_pow2_zero : Prop :=
  (@Eq _ (@ClightN.Base.pow2 (0 : Int)) (1 : Int))

def stmt_pow2_succ : Prop :=
  (∀ (k : Int),
    ((@LE.le Int Int.instLEInt (0 : Int) k)
      → (@Eq _ (@ClightN.Base.pow2 (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k (1 : Int)))
          (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (2 : Int) (@ClightN.Base.pow2 k)))))

def stmt_land_bits : Prop :=
  (∀ (a : Int) (b : Int) (k : Int),
    ((@LE.le Int Int.instLEInt (0 : Int) a)
      → ((@LE.le Int Int.instLEInt (0 : Int) b)
          → ((@LE.le Int Int.instLEInt (0 : Int) k)
              → (@Eq _
                  (@ClightN.Base.zmod
                    (@ClightN.Base.zdiv (@ClightN.Base.land a b) (@ClightN.Base.pow2 k)) (2 : Int))
                  (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                    (@ClightN.Base.zmod (@ClightN.Base.zdiv a (@ClightN.Base.pow2 k)) (2 : Int))
                    (@ClightN.Base.zmod (@ClightN.Base.zdiv b (@ClightN.Base.pow2 k))
                      (2 : Int))))))))

def stmt_land_nonneg : Prop :=
  (∀ (a : Int) (b : Int),
    ((@LE.le Int Int.instLEInt (0 : Int) a)
      → ((@LE.le Int Int.instLEInt (0 : Int) b)
          → (@LE.le Int Int.instLEInt (0 : Int) (@ClightN.Base.land a b)))))

def stmt_lor_bits : Prop :=
  (∀ (a : Int) (b : Int) (k : Int),
    ((@LE.le Int Int.instLEInt (0 : Int) a)
      → ((@LE.le Int Int.instLEInt (0 : Int) b)
          → ((@LE.le Int Int.instLEInt (0 : Int) k)
              → (@Eq _
                  (@ClightN.Base.zmod
                    (@ClightN.Base.zdiv (@ClightN.Base.lor a b) (@ClightN.Base.pow2 k)) (2 : Int))
                  (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                      (@ClightN.Base.zmod (@ClightN.Base.zdiv a (@ClightN.Base.pow2 k)) (2 : Int))
                      (@ClightN.Base.zmod (@ClightN.Base.zdiv b (@ClightN.Base.pow2 k)) (2 : Int)))
                    (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                      (@ClightN.Base.zmod (@ClightN.Base.zdiv a (@ClightN.Base.pow2 k)) (2 : Int))
                      (@ClightN.Base.zmod (@ClightN.Base.zdiv b (@ClightN.Base.pow2 k))
                        (2 : Int)))))))))

def stmt_lor_nonneg : Prop :=
  (∀ (a : Int) (b : Int),
    ((@LE.le Int Int.instLEInt (0 : Int) a)
      → ((@LE.le Int Int.instLEInt (0 : Int) b)
          → (@LE.le Int Int.instLEInt (0 : Int) (@ClightN.Base.lor a b)))))

def stmt_lxor_bits : Prop :=
  (∀ (a : Int) (b : Int) (k : Int),
    ((@LE.le Int Int.instLEInt (0 : Int) a)
      → ((@LE.le Int Int.instLEInt (0 : Int) b)
          → ((@LE.le Int Int.instLEInt (0 : Int) k)
              → (@Eq _
                  (@ClightN.Base.zmod
                    (@ClightN.Base.zdiv (@ClightN.Base.lxor a b) (@ClightN.Base.pow2 k)) (2 : Int))
                  (@ClightN.Base.zmod
                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                      (@ClightN.Base.zmod (@ClightN.Base.zdiv a (@ClightN.Base.pow2 k)) (2 : Int))
                      (@ClightN.Base.zmod (@ClightN.Base.zdiv b (@ClightN.Base.pow2 k)) (2 : Int)))
                    (2 : Int)))))))

def stmt_lxor_nonneg : Prop :=
  (∀ (a : Int) (b : Int),
    ((@LE.le Int Int.instLEInt (0 : Int) a)
      → ((@LE.le Int Int.instLEInt (0 : Int) b)
          → (@LE.le Int Int.instLEInt (0 : Int) (@ClightN.Base.lxor a b)))))

def stmt_uptr_range : Prop :=
  (∀ (x : LClight.ptrofs),
    ((@LE.le Int Int.instLEInt (0 : Int) (@ClightN.Base.uptr x))
      ∧ (@LT.lt Int Int.instLTInt (@ClightN.Base.uptr x) (18446744073709551616 : Int))))

def stmt_uptr_rptr : Prop :=
  (∀ (z : Int),
    (@Eq _ (@ClightN.Base.uptr (@ClightN.Base.rptr z))
      (@ClightN.Base.zmod z (18446744073709551616 : Int))))

def stmt_rptr_uptr : Prop :=
  (∀ (x : LClight.ptrofs), (@Eq _ (@ClightN.Base.rptr (@ClightN.Base.uptr x)) x))

def stmt_app_nil : Prop :=
  (∀ (t : (List LClight.event)), (@Eq _ (@ClightN.Base.app (@List.nil _) t) t))

def stmt_app_cons : Prop :=
  (∀ (e : LClight.event) (t1 : (List LClight.event)) (t2 : (List LClight.event)),
    (@Eq _ (@ClightN.Base.app (@List.cons _ e t1) t2) (@List.cons _ e (@ClightN.Base.app t1 t2))))

def stmt_f64_bits_of_bits : Prop :=
  (∀ (x : UInt64), (@Eq _ (@ClightN.Base.f64_bits (@ClightN.Base.f64_of_bits x)) x))

def stmt_f64_of_bits_bits : Prop :=
  (∀ (f : LClight.float), (@Eq _ (@ClightN.Base.f64_of_bits (@ClightN.Base.f64_bits f)) f))

def stmt_f32_bits_of_bits : Prop :=
  (∀ (x : UInt32), (@Eq _ (@ClightN.Base.f32_bits (@ClightN.Base.f32_of_bits x)) x))

def stmt_f32_of_bits_bits : Prop :=
  (∀ (f : LClight.float32), (@Eq _ (@ClightN.Base.f32_of_bits (@ClightN.Base.f32_bits f)) f))

end ClightN.Spec
