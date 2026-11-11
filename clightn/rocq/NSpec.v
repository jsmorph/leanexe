(* Rendered by clightn/nsx.py from clightn/N.nsx.  Do not edit. *)
From Coq Require Import ZArith.
Require Coqlib Integers Values AST Memory Ctypes Cop Clight.
Require NBase.

Inductive binop_ok : Cop.binary_operation -> Ctypes.type -> Ctypes.type -> Values.val ->
    Values.val -> Values.val -> Prop :=
  | bo_add_ul : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    (binop_ok Cop.Oadd (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
      (@Values.Vlong y) (@Values.Vlong (@NBase.r64 (@BinInt.Z.add (@NBase.u64 x) (@NBase.u64 y))))))
  | bo_sub_ul : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    (binop_ok Cop.Osub (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
      (@Values.Vlong y) (@Values.Vlong (@NBase.r64 (@BinInt.Z.sub (@NBase.u64 x) (@NBase.u64 y))))))
  | bo_mul_ul : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    (binop_ok Cop.Omul (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
      (@Values.Vlong y) (@Values.Vlong (@NBase.r64 (@BinInt.Z.mul (@NBase.u64 x) (@NBase.u64 y))))))
  | bo_div_ul : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((~ (@eq _ (@NBase.u64 y) (0)%Z))
      -> (binop_ok Cop.Odiv (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y)
          (@Values.Vlong (@NBase.r64 (@NBase.zdiv (@NBase.u64 x) (@NBase.u64 y)))))))
  | bo_mod_ul : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((~ (@eq _ (@NBase.u64 y) (0)%Z))
      -> (binop_ok Cop.Omod (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y)
          (@Values.Vlong (@NBase.r64 (@NBase.zmod (@NBase.u64 x) (@NBase.u64 y)))))))
  | bo_and_ul : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    (binop_ok Cop.Oand (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
      (@Values.Vlong y) (@Values.Vlong (@NBase.r64 (@NBase.land (@NBase.u64 x) (@NBase.u64 y))))))
  | bo_or_ul : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    (binop_ok Cop.Oor (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
      (@Values.Vlong y) (@Values.Vlong (@NBase.r64 (@NBase.lor (@NBase.u64 x) (@NBase.u64 y))))))
  | bo_xor_ul : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    (binop_ok Cop.Oxor (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
      (@Values.Vlong y) (@Values.Vlong (@NBase.r64 (@NBase.lxor (@NBase.u64 x) (@NBase.u64 y))))))
  | bo_shl_ul : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@BinInt.Z.lt (@NBase.u64 y) (64)%Z)
      -> (binop_ok Cop.Oshl (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y)
          (@Values.Vlong
            (@NBase.r64 (@BinInt.Z.mul (@NBase.u64 x) (@NBase.pow2 (@NBase.u64 y))))))))
  | bo_shr_ul : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@BinInt.Z.lt (@NBase.u64 y) (64)%Z)
      -> (binop_ok Cop.Oshr (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y)
          (@Values.Vlong (@NBase.r64 (@NBase.zdiv (@NBase.u64 x) (@NBase.pow2 (@NBase.u64 y))))))))
  | bo_eq_ul_1 : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@eq _ (@NBase.u64 x) (@NBase.u64 y))
      -> (binop_ok Cop.Oeq (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_eq_ul_0 : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((~ (@eq _ (@NBase.u64 x) (@NBase.u64 y)))
      -> (binop_ok Cop.Oeq (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_ne_ul_1 : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((~ (@eq _ (@NBase.u64 x) (@NBase.u64 y)))
      -> (binop_ok Cop.One (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_ne_ul_0 : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@eq _ (@NBase.u64 x) (@NBase.u64 y))
      -> (binop_ok Cop.One (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_lt_ul_1 : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@BinInt.Z.lt (@NBase.u64 x) (@NBase.u64 y))
      -> (binop_ok Cop.Olt (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_lt_ul_0 : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@BinInt.Z.le (@NBase.u64 y) (@NBase.u64 x))
      -> (binop_ok Cop.Olt (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_le_ul_1 : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@BinInt.Z.le (@NBase.u64 x) (@NBase.u64 y))
      -> (binop_ok Cop.Ole (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_le_ul_0 : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@BinInt.Z.lt (@NBase.u64 y) (@NBase.u64 x))
      -> (binop_ok Cop.Ole (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_gt_ul_1 : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@BinInt.Z.lt (@NBase.u64 y) (@NBase.u64 x))
      -> (binop_ok Cop.Ogt (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_gt_ul_0 : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@BinInt.Z.le (@NBase.u64 x) (@NBase.u64 y))
      -> (binop_ok Cop.Ogt (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_ge_ul_1 : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@BinInt.Z.le (@NBase.u64 y) (@NBase.u64 x))
      -> (binop_ok Cop.Oge (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_ge_ul_0 : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@BinInt.Z.lt (@NBase.u64 x) (@NBase.u64 y))
      -> (binop_ok Cop.Oge (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_lt_sl_1 : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@BinInt.Z.lt (@NBase.s64 x) (@NBase.s64 y))
      -> (binop_ok Cop.Olt (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_lt_sl_0 : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@BinInt.Z.le (@NBase.s64 y) (@NBase.s64 x))
      -> (binop_ok Cop.Olt (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_le_sl_1 : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@BinInt.Z.le (@NBase.s64 x) (@NBase.s64 y))
      -> (binop_ok Cop.Ole (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_le_sl_0 : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@BinInt.Z.lt (@NBase.s64 y) (@NBase.s64 x))
      -> (binop_ok Cop.Ole (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_shr_sl_ul : (forall (x : Integers.Int64.int) (y : Integers.Int64.int),
    ((@BinInt.Z.lt (@NBase.u64 y) (64)%Z)
      -> (binop_ok Cop.Oshr (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
          (@Values.Vlong y)
          (@Values.Vlong (@NBase.r64 (@NBase.zdiv (@NBase.s64 x) (@NBase.pow2 (@NBase.u64 y))))))))
  | bo_add_ui : (forall (x : Integers.Int.int) (y : Integers.Int.int),
    (binop_ok Cop.Oadd (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vint x)
      (@Values.Vint y) (@Values.Vint (@NBase.r32 (@BinInt.Z.add (@NBase.u32 x) (@NBase.u32 y))))))
  | bo_sub_ui : (forall (x : Integers.Int.int) (y : Integers.Int.int),
    (binop_ok Cop.Osub (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vint x)
      (@Values.Vint y) (@Values.Vint (@NBase.r32 (@BinInt.Z.sub (@NBase.u32 x) (@NBase.u32 y))))))
  | bo_and_ui : (forall (x : Integers.Int.int) (y : Integers.Int.int),
    (binop_ok Cop.Oand (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vint x)
      (@Values.Vint y) (@Values.Vint (@NBase.r32 (@NBase.land (@NBase.u32 x) (@NBase.u32 y))))))
  | bo_shl_ui : (forall (x : Integers.Int.int) (y : Integers.Int.int),
    ((@BinInt.Z.lt (@NBase.u32 y) (32)%Z)
      -> (binop_ok Cop.Oshl
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Values.Vint x) (@Values.Vint y)
          (@Values.Vint (@NBase.r32 (@BinInt.Z.mul (@NBase.u32 x) (@NBase.pow2 (@NBase.u32 y))))))))
  | bo_shr_ui : (forall (x : Integers.Int.int) (y : Integers.Int.int),
    ((@BinInt.Z.lt (@NBase.u32 y) (32)%Z)
      -> (binop_ok Cop.Oshr
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Values.Vint x) (@Values.Vint y)
          (@Values.Vint (@NBase.r32 (@NBase.zdiv (@NBase.u32 x) (@NBase.pow2 (@NBase.u32 y))))))))
  | bo_eq_ui_1 : (forall (x : Integers.Int.int) (y : Integers.Int.int),
    ((@eq _ (@NBase.u32 x) (@NBase.u32 y))
      -> (binop_ok Cop.Oeq
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Values.Vint x) (@Values.Vint y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_eq_ui_0 : (forall (x : Integers.Int.int) (y : Integers.Int.int),
    ((~ (@eq _ (@NBase.u32 x) (@NBase.u32 y)))
      -> (binop_ok Cop.Oeq
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Values.Vint x) (@Values.Vint y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_ne_ui_1 : (forall (x : Integers.Int.int) (y : Integers.Int.int),
    ((~ (@eq _ (@NBase.u32 x) (@NBase.u32 y)))
      -> (binop_ok Cop.One
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Values.Vint x) (@Values.Vint y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_ne_ui_0 : (forall (x : Integers.Int.int) (y : Integers.Int.int),
    ((@eq _ (@NBase.u32 x) (@NBase.u32 y))
      -> (binop_ok Cop.One
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Values.Vint x) (@Values.Vint y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_lt_ui_1 : (forall (x : Integers.Int.int) (y : Integers.Int.int),
    ((@BinInt.Z.lt (@NBase.u32 x) (@NBase.u32 y))
      -> (binop_ok Cop.Olt
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Values.Vint x) (@Values.Vint y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_lt_ui_0 : (forall (x : Integers.Int.int) (y : Integers.Int.int),
    ((@BinInt.Z.le (@NBase.u32 y) (@NBase.u32 x))
      -> (binop_ok Cop.Olt
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Values.Vint x) (@Values.Vint y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_gt_ui_1 : (forall (x : Integers.Int.int) (y : Integers.Int.int),
    ((@BinInt.Z.lt (@NBase.u32 y) (@NBase.u32 x))
      -> (binop_ok Cop.Ogt
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Values.Vint x) (@Values.Vint y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_gt_ui_0 : (forall (x : Integers.Int.int) (y : Integers.Int.int),
    ((@BinInt.Z.le (@NBase.u32 x) (@NBase.u32 y))
      -> (binop_ok Cop.Ogt
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Values.Vint x) (@Values.Vint y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_ge_ui_1 : (forall (x : Integers.Int.int) (y : Integers.Int.int),
    ((@BinInt.Z.le (@NBase.u32 y) (@NBase.u32 x))
      -> (binop_ok Cop.Oge
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Values.Vint x) (@Values.Vint y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_ge_ui_0 : (forall (x : Integers.Int.int) (y : Integers.Int.int),
    ((@BinInt.Z.lt (@NBase.u32 x) (@NBase.u32 y))
      -> (binop_ok Cop.Oge
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Values.Vint x) (@Values.Vint y) (@Values.Vint (@NBase.r32 (0)%Z))))).

Inductive cast_ok : Ctypes.type -> Ctypes.type -> Values.val -> Values.val -> Prop :=
  | co_si_ui : (forall (x : Integers.Int.int),
    (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vint x)
      (@Values.Vint x)))
  | co_ui_si : (forall (x : Integers.Int.int),
    (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _))) (@Values.Vint x)
      (@Values.Vint x)))
  | co_ul_ui : (forall (x : Integers.Int64.int),
    (cast_ok (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
      (@Values.Vint (@NBase.r32 (@NBase.u64 x)))))
  | co_ui_ul : (forall (x : Integers.Int.int),
    (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vint x)
      (@Values.Vlong (@NBase.r64 (@NBase.u32 x)))))
  | co_ul_sl : (forall (x : Integers.Int64.int),
    (cast_ok (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
      (@Values.Vlong x)))
  | co_ul_sl_ptr : (forall (b : Values.block) (o : Integers.Ptrofs.int),
    (cast_ok (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _))) (@Values.Vptr b o)
      (@Values.Vptr b o)))
  | co_sl_ul : (forall (x : Integers.Int64.int),
    (cast_ok (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
      (@Values.Vlong x)))
  | co_sl_ul_ptr : (forall (b : Values.block) (o : Integers.Ptrofs.int),
    (cast_ok (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vptr b o)
      (@Values.Vptr b o)))
  | co_uc_ul : (forall (x : Integers.Int.int),
    (cast_ok (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vint x)
      (@Values.Vlong (@NBase.r64 (@NBase.u32 x)))))
  | co_uc_ui : (forall (x : Integers.Int.int),
    (cast_ok (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vint x)
      (@Values.Vint x)))
  | co_ul_uc : (forall (x : Integers.Int64.int),
    (cast_ok (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
      (@Values.Vint (@NBase.r32 (@NBase.zmod (@NBase.u64 x) (256)%Z)))))
  | co_ui_uc : (forall (x : Integers.Int.int),
    (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vint x)
      (@Values.Vint (@NBase.r32 (@NBase.zmod (@NBase.u32 x) (256)%Z)))))
  | co_vuc_ul : (forall (x : Integers.Int.int),
    (cast_ok (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr true (@None _)))
      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vint x)
      (@Values.Vlong (@NBase.r64 (@NBase.u32 x)))))
  | co_vui_ul : (forall (x : Integers.Int.int),
    (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr true (@None _)))
      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vint x)
      (@Values.Vlong (@NBase.r64 (@NBase.u32 x)))))
  | co_ui_vui : (forall (x : Integers.Int.int),
    (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr true (@None _))) (@Values.Vint x)
      (@Values.Vint x)))
  | co_ul_ul : (forall (x : Integers.Int64.int),
    (cast_ok (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
      (@Values.Vlong x)))
  | co_ul_ul_ptr : (forall (b : Values.block) (o : Integers.Ptrofs.int),
    (cast_ok (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vptr b o)
      (@Values.Vptr b o)))
  | co_ui_ui : (forall (x : Integers.Int.int),
    (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vint x)
      (@Values.Vint x)))
  | co_uc_uc : (forall (x : Integers.Int.int),
    (cast_ok (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vint x)
      (@Values.Vint (@NBase.r32 (@NBase.zmod (@NBase.u32 x) (256)%Z)))))
  | co_si_si : (forall (x : Integers.Int.int),
    (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _))) (@Values.Vint x)
      (@Values.Vint x))).

Inductive bool_ok : Ctypes.type -> Values.val -> bool -> Prop :=
  | bv_si_true : (forall (x : Integers.Int.int),
    ((~ (@eq _ (@NBase.u32 x) (0)%Z))
      -> (bool_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Values.Vint x) true)))
  | bv_si_false : (forall (x : Integers.Int.int),
    ((@eq _ (@NBase.u32 x) (0)%Z)
      -> (bool_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Values.Vint x) false)))
  | bv_ui_true : (forall (x : Integers.Int.int),
    ((~ (@eq _ (@NBase.u32 x) (0)%Z))
      -> (bool_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Values.Vint x) true)))
  | bv_ui_false : (forall (x : Integers.Int.int),
    ((@eq _ (@NBase.u32 x) (0)%Z)
      -> (bool_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Values.Vint x) false))).

Definition stmt_add_ul_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oadd v1
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Oadd (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_sub_ul_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Osub v1
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Osub (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_mul_ul_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Omul v1
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Omul (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_div_ul_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Odiv v1
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Odiv (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_mod_ul_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Omod v1
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Omod (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_and_ul_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oand v1
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Oand (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_or_ul_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oor v1
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Oor (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_xor_ul_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oxor v1
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Oxor (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_shl_ul_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oshl v1
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Oshl (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_shr_ul_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oshr v1
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Oshr (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_eq_ul_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oeq v1
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Oeq (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_ne_ul_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.One v1
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.One (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_lt_ul_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Olt v1
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Olt (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_le_ul_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Ole v1
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Ole (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_gt_ul_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Ogt v1
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Ogt (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_ge_ul_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oge v1
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Oge (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_lt_sl_sl : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Olt v1
          (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Olt (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_le_sl_sl : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Ole v1
          (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Ole (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_shr_sl_ul : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oshr v1
          (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Oshr (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_add_ui_ui : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oadd v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m)
        (@Some _ v))
      <-> (binop_ok Cop.Oadd
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_sub_ui_ui : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Osub v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m)
        (@Some _ v))
      <-> (binop_ok Cop.Osub
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_and_ui_ui : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oand v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m)
        (@Some _ v))
      <-> (binop_ok Cop.Oand
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_shl_ui_ui : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oshl v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m)
        (@Some _ v))
      <-> (binop_ok Cop.Oshl
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_shr_ui_ui : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oshr v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m)
        (@Some _ v))
      <-> (binop_ok Cop.Oshr
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_eq_ui_ui : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oeq v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m)
        (@Some _ v))
      <-> (binop_ok Cop.Oeq
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_ne_ui_ui : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.One v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m)
        (@Some _ v))
      <-> (binop_ok Cop.One
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_lt_ui_ui : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Olt v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m)
        (@Some _ v))
      <-> (binop_ok Cop.Olt
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_gt_ui_ui : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Ogt v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m)
        (@Some _ v))
      <-> (binop_ok Cop.Ogt
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_ge_ui_ui : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oge v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m)
        (@Some _ v))
      <-> (binop_ok Cop.Oge
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_cast_si_ui : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m)
        (@Some _ v))
      <-> (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_ui_si : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_ul_ui : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1 (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m)
        (@Some _ v))
      <-> (cast_ok (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_ui_ul : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_ul_sl : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1 (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_sl_ul : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1 (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tlong Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_uc_ul : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1
          (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_uc_ui : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1
          (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m)
        (@Some _ v))
      <-> (cast_ok (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_ul_uc : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1 (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_ui_uc : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_vuc_ul : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1
          (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr true (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr true (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_vui_ul : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr true (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr true (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_ui_vui : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr true (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr true (@None _))) v1 v))).

Definition stmt_cast_ul_ul : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1 (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_ui_ui : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m)
        (@Some _ v))
      <-> (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_uc_uc : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1
          (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_si_si : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_bool_si : Prop :=
  (forall (v : Values.val) (b : bool) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.bool_val v (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          m) (@Some _ b))
      <-> (bool_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _))) v b))).

Definition stmt_bool_ui : Prop :=
  (forall (v : Values.val) (b : bool) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.bool_val v
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m)
        (@Some _ b))
      <-> (bool_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v
          b))).

Definition stmt_const_int : Prop :=
  (forall (ge : Clight.genv) (e : Clight.env) (le : Clight.temp_env) (m : Memory.Mem.mem)
      (i : Integers.Int.int) (ty : Ctypes.type) (v : Values.val),
    ((@NBase.eval_expr ge e le m (@Clight.Econst_int i ty) v) <-> (@eq _ v (@Values.Vint i)))).

Definition stmt_const_long : Prop :=
  (forall (ge : Clight.genv) (e : Clight.env) (le : Clight.temp_env) (m : Memory.Mem.mem)
      (i : Integers.Int64.int) (ty : Ctypes.type) (v : Values.val),
    ((@NBase.eval_expr ge e le m (@Clight.Econst_long i ty) v) <-> (@eq _ v (@Values.Vlong i)))).

Definition stmt_u32_range : Prop :=
  (forall (x : Integers.Int.int),
    ((@BinInt.Z.le (0)%Z (@NBase.u32 x)) /\ (@BinInt.Z.lt (@NBase.u32 x) (4294967296)%Z))).

Definition stmt_u32_r32 : Prop :=
  (forall (z : BinNums.Z), (@eq _ (@NBase.u32 (@NBase.r32 z)) (@NBase.zmod z (4294967296)%Z))).

Definition stmt_r32_u32 : Prop :=
  (forall (x : Integers.Int.int), (@eq _ (@NBase.r32 (@NBase.u32 x)) x)).

Definition stmt_u64_range : Prop :=
  (forall (x : Integers.Int64.int),
    ((@BinInt.Z.le (0)%Z (@NBase.u64 x))
      /\ (@BinInt.Z.lt (@NBase.u64 x) (18446744073709551616)%Z))).

Definition stmt_u64_r64 : Prop :=
  (forall (z : BinNums.Z),
    (@eq _ (@NBase.u64 (@NBase.r64 z)) (@NBase.zmod z (18446744073709551616)%Z))).

Definition stmt_r64_u64 : Prop :=
  (forall (x : Integers.Int64.int), (@eq _ (@NBase.r64 (@NBase.u64 x)) x)).

Definition stmt_s64_low : Prop :=
  (forall (x : Integers.Int64.int),
    ((@BinInt.Z.lt (@NBase.u64 x) (9223372036854775808)%Z)
      -> (@eq _ (@NBase.s64 x) (@NBase.u64 x)))).

Definition stmt_s64_high : Prop :=
  (forall (x : Integers.Int64.int),
    ((@BinInt.Z.le (9223372036854775808)%Z (@NBase.u64 x))
      -> (@eq _ (@NBase.s64 x) (@BinInt.Z.sub (@NBase.u64 x) (18446744073709551616)%Z)))).

Definition stmt_zdiv_zmod : Prop :=
  (forall (a : BinNums.Z) (b : BinNums.Z),
    ((@BinInt.Z.lt (0)%Z b)
      -> ((@eq _ a (@BinInt.Z.add (@BinInt.Z.mul b (@NBase.zdiv a b)) (@NBase.zmod a b)))
          /\ ((@BinInt.Z.le (0)%Z (@NBase.zmod a b)) /\ (@BinInt.Z.lt (@NBase.zmod a b) b))))).

Definition stmt_pow2_zero : Prop :=
  (@eq _ (@NBase.pow2 (0)%Z) (1)%Z).

Definition stmt_pow2_succ : Prop :=
  (forall (k : BinNums.Z),
    ((@BinInt.Z.le (0)%Z k)
      -> (@eq _ (@NBase.pow2 (@BinInt.Z.add k (1)%Z)) (@BinInt.Z.mul (2)%Z (@NBase.pow2 k))))).

Definition stmt_land_bits : Prop :=
  (forall (a : BinNums.Z) (b : BinNums.Z) (k : BinNums.Z),
    ((@BinInt.Z.le (0)%Z a)
      -> ((@BinInt.Z.le (0)%Z b)
          -> ((@BinInt.Z.le (0)%Z k)
              -> (@eq _ (@NBase.zmod (@NBase.zdiv (@NBase.land a b) (@NBase.pow2 k)) (2)%Z)
                  (@BinInt.Z.mul (@NBase.zmod (@NBase.zdiv a (@NBase.pow2 k)) (2)%Z)
                    (@NBase.zmod (@NBase.zdiv b (@NBase.pow2 k)) (2)%Z))))))).

Definition stmt_land_nonneg : Prop :=
  (forall (a : BinNums.Z) (b : BinNums.Z),
    ((@BinInt.Z.le (0)%Z a) -> ((@BinInt.Z.le (0)%Z b) -> (@BinInt.Z.le (0)%Z (@NBase.land a b))))).

Definition stmt_lor_bits : Prop :=
  (forall (a : BinNums.Z) (b : BinNums.Z) (k : BinNums.Z),
    ((@BinInt.Z.le (0)%Z a)
      -> ((@BinInt.Z.le (0)%Z b)
          -> ((@BinInt.Z.le (0)%Z k)
              -> (@eq _ (@NBase.zmod (@NBase.zdiv (@NBase.lor a b) (@NBase.pow2 k)) (2)%Z)
                  (@BinInt.Z.sub
                    (@BinInt.Z.add (@NBase.zmod (@NBase.zdiv a (@NBase.pow2 k)) (2)%Z)
                      (@NBase.zmod (@NBase.zdiv b (@NBase.pow2 k)) (2)%Z))
                    (@BinInt.Z.mul (@NBase.zmod (@NBase.zdiv a (@NBase.pow2 k)) (2)%Z)
                      (@NBase.zmod (@NBase.zdiv b (@NBase.pow2 k)) (2)%Z)))))))).

Definition stmt_lor_nonneg : Prop :=
  (forall (a : BinNums.Z) (b : BinNums.Z),
    ((@BinInt.Z.le (0)%Z a) -> ((@BinInt.Z.le (0)%Z b) -> (@BinInt.Z.le (0)%Z (@NBase.lor a b))))).

Definition stmt_lxor_bits : Prop :=
  (forall (a : BinNums.Z) (b : BinNums.Z) (k : BinNums.Z),
    ((@BinInt.Z.le (0)%Z a)
      -> ((@BinInt.Z.le (0)%Z b)
          -> ((@BinInt.Z.le (0)%Z k)
              -> (@eq _ (@NBase.zmod (@NBase.zdiv (@NBase.lxor a b) (@NBase.pow2 k)) (2)%Z)
                  (@NBase.zmod
                    (@BinInt.Z.add (@NBase.zmod (@NBase.zdiv a (@NBase.pow2 k)) (2)%Z)
                      (@NBase.zmod (@NBase.zdiv b (@NBase.pow2 k)) (2)%Z)) (2)%Z)))))).

Definition stmt_lxor_nonneg : Prop :=
  (forall (a : BinNums.Z) (b : BinNums.Z),
    ((@BinInt.Z.le (0)%Z a) -> ((@BinInt.Z.le (0)%Z b) -> (@BinInt.Z.le (0)%Z (@NBase.lxor a b))))).
