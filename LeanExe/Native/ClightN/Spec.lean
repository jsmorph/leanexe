-- Rendered by clightn/nsx.py from clightn/N.nsx.  Do not edit.
import LeanExe.Native.ClightN.Base

set_option autoImplicit false

namespace ClightN.Spec

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

end ClightN.Spec
