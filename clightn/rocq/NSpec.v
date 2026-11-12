(* Rendered by clightn/nsx.py from the specification of N.  Do not edit. *)
From Coq Require Import ZArith String.
Require Coqlib Integers Floats Values AST Memory Events Ctypes Cop Clight ClightBigstep.
Require NBase.

Definition eqn_fadd64 : (Floats.float -> (Floats.float -> Floats.float)) :=
  Floats.Float.add.

Definition eqn_fsub64 : (Floats.float -> (Floats.float -> Floats.float)) :=
  Floats.Float.sub.

Definition eqn_fmul64 : (Floats.float -> (Floats.float -> Floats.float)) :=
  Floats.Float.mul.

Definition eqn_fdiv64 : (Floats.float -> (Floats.float -> Floats.float)) :=
  Floats.Float.div.

Definition eqn_fcmp64 : (Integers.comparison -> (Floats.float -> (Floats.float -> bool))) :=
  Floats.Float.cmp.

Definition eqn_fneg64 : (Floats.float -> Floats.float) :=
  Floats.Float.neg.

Definition eqn_fabs64 : (Floats.float -> Floats.float) :=
  Floats.Float.abs.

Definition eqn_fsqrt64 : (Floats.float -> Floats.float) :=
  Floats.Float.sqrt.

Definition eqn_f64_of_longu : (Integers.Int64.int -> Floats.float) :=
  Floats.Float.of_longu.

Definition eqn_f64_to_longu : (Floats.float -> (option Integers.Int64.int)) :=
  Floats.Float.to_longu.

Definition eqn_f64_of_single : (Floats.float32 -> Floats.float) :=
  Floats.Float.of_single.

Definition eqn_f64_to_single : (Floats.float -> Floats.float32) :=
  Floats.Float.to_single.

Definition eqn_fadd32 : (Floats.float32 -> (Floats.float32 -> Floats.float32)) :=
  Floats.Float32.add.

Definition eqn_fsub32 : (Floats.float32 -> (Floats.float32 -> Floats.float32)) :=
  Floats.Float32.sub.

Definition eqn_fmul32 : (Floats.float32 -> (Floats.float32 -> Floats.float32)) :=
  Floats.Float32.mul.

Definition eqn_fdiv32 : (Floats.float32 -> (Floats.float32 -> Floats.float32)) :=
  Floats.Float32.div.

Definition eqn_fcmp32 : (Integers.comparison -> (Floats.float32 -> (Floats.float32 -> bool))) :=
  Floats.Float32.cmp.

Definition eqn_fneg32 : (Floats.float32 -> Floats.float32) :=
  Floats.Float32.neg.

Definition eqn_f32_of_int : (Integers.Int.int -> Floats.float32) :=
  Floats.Float32.of_int.

Definition eqn_f32_of_intu : (Integers.Int.int -> Floats.float32) :=
  Floats.Float32.of_intu.

Definition eqn_f32_of_longu : (Integers.Int64.int -> Floats.float32) :=
  Floats.Float32.of_longu.

Definition eqn_f32_to_int : (Floats.float32 -> (option Integers.Int.int)) :=
  Floats.Float32.to_int.

Definition eqn_f32_to_longu : (Floats.float32 -> (option Integers.Int64.int)) :=
  Floats.Float32.to_longu.

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
          (@Values.Vint x) (@Values.Vint y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_add_d : (forall (x : Floats.float) (y : Floats.float),
    (binop_ok Cop.Oadd (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
      (@Values.Vfloat y) (@Values.Vfloat (@Floats.Float.add x y))))
  | bo_sub_d : (forall (x : Floats.float) (y : Floats.float),
    (binop_ok Cop.Osub (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
      (@Values.Vfloat y) (@Values.Vfloat (@Floats.Float.sub x y))))
  | bo_mul_d : (forall (x : Floats.float) (y : Floats.float),
    (binop_ok Cop.Omul (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
      (@Values.Vfloat y) (@Values.Vfloat (@Floats.Float.mul x y))))
  | bo_div_d : (forall (x : Floats.float) (y : Floats.float),
    (binop_ok Cop.Odiv (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
      (@Values.Vfloat y) (@Values.Vfloat (@Floats.Float.div x y))))
  | bo_eq_d_1 : (forall (x : Floats.float) (y : Floats.float),
    ((@eq _ (@Floats.Float.cmp Integers.Ceq x y) true)
      -> (binop_ok Cop.Oeq (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
          (@Values.Vfloat y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_eq_d_0 : (forall (x : Floats.float) (y : Floats.float),
    ((@eq _ (@Floats.Float.cmp Integers.Ceq x y) false)
      -> (binop_ok Cop.Oeq (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
          (@Values.Vfloat y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_ne_d_1 : (forall (x : Floats.float) (y : Floats.float),
    ((@eq _ (@Floats.Float.cmp Integers.Cne x y) true)
      -> (binop_ok Cop.One (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
          (@Values.Vfloat y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_ne_d_0 : (forall (x : Floats.float) (y : Floats.float),
    ((@eq _ (@Floats.Float.cmp Integers.Cne x y) false)
      -> (binop_ok Cop.One (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
          (@Values.Vfloat y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_lt_d_1 : (forall (x : Floats.float) (y : Floats.float),
    ((@eq _ (@Floats.Float.cmp Integers.Clt x y) true)
      -> (binop_ok Cop.Olt (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
          (@Values.Vfloat y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_lt_d_0 : (forall (x : Floats.float) (y : Floats.float),
    ((@eq _ (@Floats.Float.cmp Integers.Clt x y) false)
      -> (binop_ok Cop.Olt (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
          (@Values.Vfloat y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_le_d_1 : (forall (x : Floats.float) (y : Floats.float),
    ((@eq _ (@Floats.Float.cmp Integers.Cle x y) true)
      -> (binop_ok Cop.Ole (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
          (@Values.Vfloat y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_le_d_0 : (forall (x : Floats.float) (y : Floats.float),
    ((@eq _ (@Floats.Float.cmp Integers.Cle x y) false)
      -> (binop_ok Cop.Ole (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
          (@Values.Vfloat y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_ge_d_1 : (forall (x : Floats.float) (y : Floats.float),
    ((@eq _ (@Floats.Float.cmp Integers.Cge x y) true)
      -> (binop_ok Cop.Oge (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
          (@Values.Vfloat y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_ge_d_0 : (forall (x : Floats.float) (y : Floats.float),
    ((@eq _ (@Floats.Float.cmp Integers.Cge x y) false)
      -> (binop_ok Cop.Oge (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
          (@Values.Vfloat y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_add_f : (forall (x : Floats.float32) (y : Floats.float32),
    (binop_ok Cop.Oadd (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
      (@Values.Vsingle y) (@Values.Vsingle (@Floats.Float32.add x y))))
  | bo_sub_f : (forall (x : Floats.float32) (y : Floats.float32),
    (binop_ok Cop.Osub (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
      (@Values.Vsingle y) (@Values.Vsingle (@Floats.Float32.sub x y))))
  | bo_mul_f : (forall (x : Floats.float32) (y : Floats.float32),
    (binop_ok Cop.Omul (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
      (@Values.Vsingle y) (@Values.Vsingle (@Floats.Float32.mul x y))))
  | bo_div_f : (forall (x : Floats.float32) (y : Floats.float32),
    (binop_ok Cop.Odiv (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
      (@Values.Vsingle y) (@Values.Vsingle (@Floats.Float32.div x y))))
  | bo_eq_f_1 : (forall (x : Floats.float32) (y : Floats.float32),
    ((@eq _ (@Floats.Float32.cmp Integers.Ceq x y) true)
      -> (binop_ok Cop.Oeq (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
          (@Values.Vsingle y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_eq_f_0 : (forall (x : Floats.float32) (y : Floats.float32),
    ((@eq _ (@Floats.Float32.cmp Integers.Ceq x y) false)
      -> (binop_ok Cop.Oeq (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
          (@Values.Vsingle y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_ne_f_1 : (forall (x : Floats.float32) (y : Floats.float32),
    ((@eq _ (@Floats.Float32.cmp Integers.Cne x y) true)
      -> (binop_ok Cop.One (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
          (@Values.Vsingle y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_ne_f_0 : (forall (x : Floats.float32) (y : Floats.float32),
    ((@eq _ (@Floats.Float32.cmp Integers.Cne x y) false)
      -> (binop_ok Cop.One (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
          (@Values.Vsingle y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_lt_f_1 : (forall (x : Floats.float32) (y : Floats.float32),
    ((@eq _ (@Floats.Float32.cmp Integers.Clt x y) true)
      -> (binop_ok Cop.Olt (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
          (@Values.Vsingle y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_lt_f_0 : (forall (x : Floats.float32) (y : Floats.float32),
    ((@eq _ (@Floats.Float32.cmp Integers.Clt x y) false)
      -> (binop_ok Cop.Olt (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
          (@Values.Vsingle y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_le_f_1 : (forall (x : Floats.float32) (y : Floats.float32),
    ((@eq _ (@Floats.Float32.cmp Integers.Cle x y) true)
      -> (binop_ok Cop.Ole (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
          (@Values.Vsingle y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_le_f_0 : (forall (x : Floats.float32) (y : Floats.float32),
    ((@eq _ (@Floats.Float32.cmp Integers.Cle x y) false)
      -> (binop_ok Cop.Ole (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
          (@Values.Vsingle y) (@Values.Vint (@NBase.r32 (0)%Z)))))
  | bo_ge_f_1 : (forall (x : Floats.float32) (y : Floats.float32),
    ((@eq _ (@Floats.Float32.cmp Integers.Cge x y) true)
      -> (binop_ok Cop.Oge (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
          (@Values.Vsingle y) (@Values.Vint (@NBase.r32 (1)%Z)))))
  | bo_ge_f_0 : (forall (x : Floats.float32) (y : Floats.float32),
    ((@eq _ (@Floats.Float32.cmp Integers.Cge x y) false)
      -> (binop_ok Cop.Oge (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
          (@Values.Vsingle y) (@Values.Vint (@NBase.r32 (0)%Z))))).

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
      (@Values.Vint x)))
  | co_d_d : (forall (x : Floats.float),
    (cast_ok (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
      (@Values.Vfloat x)))
  | co_f_f : (forall (x : Floats.float32),
    (cast_ok (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
      (@Values.Vsingle x)))
  | co_ul_d : (forall (x : Integers.Int64.int),
    (cast_ok (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
      (@Values.Vfloat (@Floats.Float.of_longu x))))
  | co_d_ul : (forall (x : Floats.float) (y : Integers.Int64.int),
    ((@eq _ (@Floats.Float.to_longu x) (@Some _ y))
      -> (cast_ok (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
          (@Values.Vlong y))))
  | co_f_d : (forall (x : Floats.float32),
    (cast_ok (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
      (@Values.Vfloat (@Floats.Float.of_single x))))
  | co_d_f : (forall (x : Floats.float),
    (cast_ok (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat x)
      (@Values.Vsingle (@Floats.Float.to_single x))))
  | co_si_f : (forall (x : Integers.Int.int),
    (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vint x)
      (@Values.Vsingle (@Floats.Float32.of_int x))))
  | co_ui_f : (forall (x : Integers.Int.int),
    (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vint x)
      (@Values.Vsingle (@Floats.Float32.of_intu x))))
  | co_ul_f : (forall (x : Integers.Int64.int),
    (cast_ok (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)
      (@Values.Vsingle (@Floats.Float32.of_longu x))))
  | co_f_si : (forall (x : Floats.float32) (y : Integers.Int.int),
    ((@eq _ (@Floats.Float32.to_int x) (@Some _ y))
      -> (cast_ok (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Values.Vsingle x) (@Values.Vint y))))
  | co_f_ul : (forall (x : Floats.float32) (y : Integers.Int64.int),
    ((@eq _ (@Floats.Float32.to_longu x) (@Some _ y))
      -> (cast_ok (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle x)
          (@Values.Vlong y)))).

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

Inductive unop_ok : Cop.unary_operation -> Ctypes.type -> Values.val -> Values.val -> Prop :=
  | uo_neg_d : (forall (x : Floats.float),
    (unop_ok Cop.Oneg (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
      (@Values.Vfloat x) (@Values.Vfloat (@Floats.Float.neg x))))
  | uo_abs_d : (forall (x : Floats.float),
    (unop_ok Cop.Oabsfloat (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
      (@Values.Vfloat x) (@Values.Vfloat (@Floats.Float.abs x))))
  | uo_neg_f : (forall (x : Floats.float32),
    (unop_ok Cop.Oneg (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
      (@Values.Vsingle x) (@Values.Vsingle (@Floats.Float32.neg x)))).

Inductive in_defs : (list (AST.ident * (@AST.globdef Clight.fundef Ctypes.type))) -> AST.ident ->
    (@AST.globdef Clight.fundef Ctypes.type) -> Prop :=
  | in_here : (forall (x : AST.ident) (g : (@AST.globdef Clight.fundef Ctypes.type))
      (rest : (list (AST.ident * (@AST.globdef Clight.fundef Ctypes.type)))),
    (in_defs (@cons _ (@pair _ _ x g) rest) x g))
  | in_there : (forall (d : (AST.ident * (@AST.globdef Clight.fundef Ctypes.type)))
      (rest : (list (AST.ident * (@AST.globdef Clight.fundef Ctypes.type)))) (x : AST.ident)
      (g : (@AST.globdef Clight.fundef Ctypes.type)),
    ((in_defs rest x g) -> (in_defs (@cons _ d rest) x g))).

Inductive out_defs : AST.ident -> (list (AST.ident * (@AST.globdef Clight.fundef Ctypes.type))) ->
    Prop :=
  | od_nil : (forall (x : AST.ident), (out_defs x (@nil _)))
  | od_cons : (forall (x : AST.ident) (y : AST.ident) (g : (@AST.globdef Clight.fundef Ctypes.type))
      (rest : (list (AST.ident * (@AST.globdef Clight.fundef Ctypes.type)))),
    ((~ (@eq _ x y)) -> ((out_defs x rest) -> (out_defs x (@cons _ (@pair _ _ y g) rest))))).

Inductive norepet_defs : (list (AST.ident * (@AST.globdef Clight.fundef Ctypes.type))) -> Prop :=
  | nd_nil : (norepet_defs (@nil _))
  | nd_cons : (forall (x : AST.ident) (g : (@AST.globdef Clight.fundef Ctypes.type))
      (rest : (list (AST.ident * (@AST.globdef Clight.fundef Ctypes.type)))),
    ((out_defs x rest) -> ((norepet_defs rest) -> (norepet_defs (@cons _ (@pair _ _ x g) rest))))).

Inductive out_names : AST.ident -> (list (AST.ident * Ctypes.type)) -> Prop :=
  | on_nil : (forall (x : AST.ident), (out_names x (@nil _)))
  | on_cons : (forall (x : AST.ident) (y : AST.ident) (ty : Ctypes.type)
      (rest : (list (AST.ident * Ctypes.type))),
    ((~ (@eq _ x y)) -> ((out_names x rest) -> (out_names x (@cons _ (@pair _ _ y ty) rest))))).

Inductive norepet_names : (list (AST.ident * Ctypes.type)) -> Prop :=
  | nn_nil : (norepet_names (@nil _))
  | nn_cons : (forall (x : AST.ident) (ty : Ctypes.type) (rest : (list (AST.ident * Ctypes.type))),
    ((out_names x rest)
      -> ((norepet_names rest) -> (norepet_names (@cons _ (@pair _ _ x ty) rest))))).

Inductive disjoint_names : (list (AST.ident * Ctypes.type)) -> (list (AST.ident * Ctypes.type)) ->
    Prop :=
  | dn_nil : (forall (l : (list (AST.ident * Ctypes.type))), (disjoint_names (@nil _) l))
  | dn_cons : (forall (x : AST.ident) (ty : Ctypes.type) (rest : (list (AST.ident * Ctypes.type)))
      (l : (list (AST.ident * Ctypes.type))),
    ((out_names x l)
      -> ((disjoint_names rest l) -> (disjoint_names (@cons _ (@pair _ _ x ty) rest) l)))).

Inductive params_types : (list (AST.ident * Ctypes.type)) -> (list Ctypes.type) -> Prop :=
  | pt_nil : (params_types (@nil _) (@nil _))
  | pt_cons : (forall (x : AST.ident) (ty : Ctypes.type) (rest : (list (AST.ident * Ctypes.type)))
      (tys : (list Ctypes.type)),
    ((params_types rest tys) -> (params_types (@cons _ (@pair _ _ x ty) rest) (@cons _ ty tys)))).

Inductive undef_temps : (list (AST.ident * Ctypes.type)) -> (AST.ident -> (option Values.val)) ->
    Prop :=
  | ut_nil : (forall (le : (AST.ident -> (option Values.val))),
    ((forall (x : AST.ident), (@eq _ (le x) (@None _))) -> (undef_temps (@nil _) le)))
  | ut_cons : (forall (x : AST.ident) (ty : Ctypes.type) (rest : (list (AST.ident * Ctypes.type)))
      (le0 : (AST.ident -> (option Values.val))) (le : (AST.ident -> (option Values.val))),
    ((undef_temps rest le0)
      -> ((forall (x_upd : AST.ident),
            (((@eq _ x_upd x) -> (@eq _ (le x_upd) (@Some _ Values.Vundef)))
              /\ ((~ (@eq _ x_upd x)) -> (@eq _ (le x_upd) (le0 x_upd)))))
          -> (undef_temps (@cons _ (@pair _ _ x ty) rest) le)))).

Inductive bind_params : (list (AST.ident * Ctypes.type)) -> (list Values.val) ->
    (AST.ident -> (option Values.val)) -> (AST.ident -> (option Values.val)) -> Prop :=
  | bp_nil : (forall (le : (AST.ident -> (option Values.val))),
    (bind_params (@nil _) (@nil _) le le))
  | bp_cons : (forall (x : AST.ident) (ty : Ctypes.type) (rest : (list (AST.ident * Ctypes.type)))
      (v : Values.val) (vs : (list Values.val)) (le : (AST.ident -> (option Values.val)))
      (le1 : (AST.ident -> (option Values.val))) (le2 : (AST.ident -> (option Values.val))),
    ((forall (x_upd : AST.ident),
        (((@eq _ x_upd x) -> (@eq _ (le1 x_upd) (@Some _ v)))
          /\ ((~ (@eq _ x_upd x)) -> (@eq _ (le1 x_upd) (le x_upd)))))
      -> ((bind_params rest vs le1 le2)
          -> (bind_params (@cons _ (@pair _ _ x ty) rest) (@cons _ v vs) le le2)))).

Inductive set_opt : (option AST.ident) -> Values.val -> (AST.ident -> (option Values.val)) ->
    (AST.ident -> (option Values.val)) -> Prop :=
  | so_none : (forall (v : Values.val) (le : (AST.ident -> (option Values.val))),
    (set_opt (@None _) v le le))
  | so_some : (forall (x : AST.ident) (v : Values.val) (le : (AST.ident -> (option Values.val)))
      (le2 : (AST.ident -> (option Values.val))),
    ((forall (x_upd : AST.ident),
        (((@eq _ x_upd x) -> (@eq _ (le2 x_upd) (@Some _ v)))
          /\ ((~ (@eq _ x_upd x)) -> (@eq _ (le2 x_upd) (le x_upd)))))
      -> (set_opt (@Some _ x) v le le2))).

Inductive has_type : Clight.expr -> Ctypes.type -> Prop :=
  | ht_int : (forall (i : Integers.Int.int) (ty : Ctypes.type),
    (has_type (@Clight.Econst_int i ty) ty))
  | ht_long : (forall (i : Integers.Int64.int) (ty : Ctypes.type),
    (has_type (@Clight.Econst_long i ty) ty))
  | ht_float : (forall (f : Floats.float) (ty : Ctypes.type),
    (has_type (@Clight.Econst_float f ty) ty))
  | ht_single : (forall (f : Floats.float32) (ty : Ctypes.type),
    (has_type (@Clight.Econst_single f ty) ty))
  | ht_temp : (forall (x : AST.ident) (ty : Ctypes.type), (has_type (@Clight.Etempvar x ty) ty))
  | ht_var : (forall (x : AST.ident) (ty : Ctypes.type), (has_type (@Clight.Evar x ty) ty))
  | ht_deref : (forall (a : Clight.expr) (ty : Ctypes.type), (has_type (@Clight.Ederef a ty) ty))
  | ht_binop : (forall (op : Cop.binary_operation) (a1 : Clight.expr) (a2 : Clight.expr)
      (ty : Ctypes.type), (has_type (@Clight.Ebinop op a1 a2 ty) ty))
  | ht_cast : (forall (a : Clight.expr) (ty : Ctypes.type), (has_type (@Clight.Ecast a ty) ty))
  | ht_unop : (forall (op : Cop.unary_operation) (a : Clight.expr) (ty : Ctypes.type),
    (has_type (@Clight.Eunop op a ty) ty)).

Inductive scalar : Ctypes.type -> Prop :=
  | sc_ui : (scalar (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))))
  | sc_ul : (scalar (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))))
  | sc_d : (scalar (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))))
  | sc_f : (scalar (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))).

Inductive gval : Ctypes.type -> Values.val -> Prop :=
  | gv_ui : (forall (x : Integers.Int.int),
    (gval (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@Values.Vint x)))
  | gv_ul : (forall (x : Integers.Int64.int),
    (gval (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) (@Values.Vlong x)))
  | gv_d : (forall (f : Floats.float),
    (gval (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@Values.Vfloat f)))
  | gv_f : (forall (f : Floats.float32),
    (gval (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) (@Values.Vsingle f))).

Inductive ginit : Ctypes.type -> (list AST.init_data) -> Values.val -> Prop :=
  | gi_ui : (forall (x : Integers.Int.int),
    (ginit (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@cons _ (@AST.Init_int32 x) (@nil _)) (@Values.Vint x)))
  | gi_ul : (forall (x : Integers.Int64.int),
    (ginit (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
      (@cons _ (@AST.Init_int64 x) (@nil _)) (@Values.Vlong x)))
  | gi_d : (ginit (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
    (@cons _ (@AST.Init_space (8)%Z) (@nil _))
    (@Values.Vfloat (@NBase.f64_of_bits (@NBase.r64 (0)%Z))))
  | gi_f : (ginit (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
    (@cons _ (@AST.Init_space (4)%Z) (@nil _))
    (@Values.Vsingle (@NBase.f32_of_bits (@NBase.r32 (0)%Z)))).

Inductive init_ok : (list AST.init_data) -> Prop :=
  | io_nil : (init_ok (@nil _))
  | io_int32 : (forall (x : Integers.Int.int), (init_ok (@cons _ (@AST.Init_int32 x) (@nil _))))
  | io_int64 : (forall (x : Integers.Int64.int), (init_ok (@cons _ (@AST.Init_int64 x) (@nil _))))
  | io_space : (forall (n : BinNums.Z), (init_ok (@cons _ (@AST.Init_space n) (@nil _)))).

Inductive vload_ok : AST.memory_chunk -> Ctypes.type -> BinNums.Z -> Integers.Int.int ->
    Values.val -> Prop :=
  | vl_uchar : (forall (j : Integers.Int.int),
    (vload_ok AST.Mint8unsigned
      (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr true (@None _))) (1)%Z j
      (@Values.Vint (@NBase.r32 (@NBase.zmod (@NBase.u32 j) (256)%Z)))))
  | vl_uint : (forall (j : Integers.Int.int),
    (vload_ok AST.Mint32 (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr true (@None _)))
      (4)%Z j (@Values.Vint j))).

Inductive result_ok : ClightBigstep.outcome -> Ctypes.type -> Values.val -> Prop :=
  | rs_normal : (result_ok ClightBigstep.Out_normal Ctypes.Tvoid Values.Vundef)
  | rs_none : (result_ok (@ClightBigstep.Out_return (@None _)) Ctypes.Tvoid Values.Vundef)
  | rs_some : (forall (v : Values.val) (t : Ctypes.type) (ty : Ctypes.type) (v2 : Values.val),
    ((~ (@eq _ ty Ctypes.Tvoid))
      -> ((cast_ok t ty v v2)
          -> (result_ok (@ClightBigstep.Out_return (@Some _ (@pair _ _ v t))) ty v2)))).

Inductive neval (defs : (list (AST.ident * (@AST.globdef Clight.fundef Ctypes.type))))
    (le : (AST.ident -> (option Values.val))) (gv : (AST.ident -> (option Values.val)))
    (mb : (AST.ident -> (BinNums.Z -> BinNums.Z))) : Clight.expr -> Values.val -> Prop :=
  | nv_int : (forall (i : Integers.Int.int) (ty : Ctypes.type),
    (neval defs le gv mb (@Clight.Econst_int i ty) (@Values.Vint i)))
  | nv_long : (forall (i : Integers.Int64.int) (ty : Ctypes.type),
    (neval defs le gv mb (@Clight.Econst_long i ty) (@Values.Vlong i)))
  | nv_float : (forall (f : Floats.float) (ty : Ctypes.type),
    (neval defs le gv mb (@Clight.Econst_float f ty) (@Values.Vfloat f)))
  | nv_single : (forall (f : Floats.float32) (ty : Ctypes.type),
    (neval defs le gv mb (@Clight.Econst_single f ty) (@Values.Vsingle f)))
  | nv_temp : (forall (x : AST.ident) (ty : Ctypes.type) (v : Values.val),
    ((@eq _ (le x) (@Some _ v)) -> (neval defs le gv mb (@Clight.Etempvar x ty) v)))
  | nv_global : (forall (x : AST.ident) (ty : Ctypes.type) (init : (list AST.init_data))
      (v : Values.val),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type (@AST.mkglobvar Ctypes.type ty init false false)))
      -> ((scalar ty)
          -> ((@eq _ (gv x) (@Some _ v)) -> (neval defs le gv mb (@Clight.Evar x ty) v)))))
  | nv_word : (forall (x : AST.ident) (n : BinNums.Z) (i : Clight.expr) (k : Integers.Int64.int),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type
          (@AST.mkglobvar Ctypes.type
            (@Ctypes.Tarray (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
              (@Ctypes.mk_attr false (@None _)))
            (@cons _ (@AST.Init_space (@BinInt.Z.mul (8)%Z n)) (@nil _)) false false)))
      -> ((neval defs le gv mb i (@Values.Vlong k))
          -> ((has_type i (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))))
              -> ((@BinInt.Z.le
                    (@BinInt.Z.add
                      (@NBase.zmod (@BinInt.Z.mul (8)%Z (@NBase.u64 k)) (18446744073709551616)%Z)
                      (8)%Z) (@BinInt.Z.mul (8)%Z n))
                  -> (neval defs le gv mb
                      (@Clight.Ederef
                        (@Clight.Ebinop Cop.Oadd
                          (@Clight.Evar x
                            (@Ctypes.Tarray
                              (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
                              (@Ctypes.mk_attr false (@None _)))) i
                          (@Ctypes.Tpointer
                            (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
                            (@Ctypes.mk_attr false (@None _))))
                        (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))))
                      (@Values.Vlong
                        (@NBase.r64
                          (@BinInt.Z.add
                            (@BinInt.Z.add
                              (mb x
                                (@NBase.zmod (@BinInt.Z.mul (8)%Z (@NBase.u64 k))
                                  (18446744073709551616)%Z))
                              (@BinInt.Z.add
                                (@BinInt.Z.mul (256)%Z
                                  (mb x
                                    (@BinInt.Z.add
                                      (@NBase.zmod (@BinInt.Z.mul (8)%Z (@NBase.u64 k))
                                        (18446744073709551616)%Z) (1)%Z)))
                                (@BinInt.Z.add
                                  (@BinInt.Z.mul (65536)%Z
                                    (mb x
                                      (@BinInt.Z.add
                                        (@NBase.zmod (@BinInt.Z.mul (8)%Z (@NBase.u64 k))
                                        (18446744073709551616)%Z) (2)%Z)))
                                  (@BinInt.Z.mul (16777216)%Z
                                    (mb x
                                      (@BinInt.Z.add
                                        (@NBase.zmod (@BinInt.Z.mul (8)%Z (@NBase.u64 k))
                                        (18446744073709551616)%Z) (3)%Z))))))
                            (@BinInt.Z.mul (4294967296)%Z
                              (@BinInt.Z.add
                                (mb x
                                  (@BinInt.Z.add
                                    (@NBase.zmod (@BinInt.Z.mul (8)%Z (@NBase.u64 k))
                                      (18446744073709551616)%Z) (4)%Z))
                                (@BinInt.Z.add
                                  (@BinInt.Z.mul (256)%Z
                                    (mb x
                                      (@BinInt.Z.add
                                        (@BinInt.Z.add
                                        (@NBase.zmod (@BinInt.Z.mul (8)%Z (@NBase.u64 k))
                                        (18446744073709551616)%Z) (4)%Z) (1)%Z)))
                                  (@BinInt.Z.add
                                    (@BinInt.Z.mul (65536)%Z
                                      (mb x
                                        (@BinInt.Z.add
                                        (@BinInt.Z.add
                                        (@NBase.zmod (@BinInt.Z.mul (8)%Z (@NBase.u64 k))
                                        (18446744073709551616)%Z) (4)%Z) (2)%Z)))
                                    (@BinInt.Z.mul (16777216)%Z
                                      (mb x
                                        (@BinInt.Z.add
                                        (@BinInt.Z.add
                                        (@NBase.zmod (@BinInt.Z.mul (8)%Z (@NBase.u64 k))
                                        (18446744073709551616)%Z) (4)%Z) (3)%Z))))))))))))))))
  | nv_byte : (forall (x : AST.ident) (n : BinNums.Z) (i : Clight.expr) (k : Integers.Int64.int),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type
          (@AST.mkglobvar Ctypes.type
            (@Ctypes.Tarray (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
              (@Ctypes.mk_attr false (@None _)))
            (@cons _ (@AST.Init_space (@BinInt.Z.mul (8)%Z n)) (@nil _)) false false)))
      -> ((neval defs le gv mb i (@Values.Vlong k))
          -> ((has_type i (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))))
              -> ((@BinInt.Z.lt (@NBase.u64 k) (@BinInt.Z.mul (8)%Z n))
                  -> (neval defs le gv mb
                      (@Clight.Ederef
                        (@Clight.Ebinop Cop.Oadd
                          (@Clight.Ecast
                            (@Clight.Evar x
                              (@Ctypes.Tarray
                                (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
                                (@Ctypes.mk_attr false (@None _))))
                            (@Ctypes.Tpointer
                              (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned
                                (@Ctypes.mk_attr false (@None _)))
                              (@Ctypes.mk_attr false (@None _)))) i
                          (@Ctypes.Tpointer
                            (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned
                              (@Ctypes.mk_attr false (@None _))) (@Ctypes.mk_attr false (@None _))))
                        (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))))
                      (@Values.Vint (@NBase.r32 (mb x (@NBase.u64 k))))))))))
  | nv_cell64 : (forall (x : AST.ident) (n : BinNums.Z),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type
          (@AST.mkglobvar Ctypes.type
            (@Ctypes.Tarray (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
              (@Ctypes.mk_attr false (@None _)))
            (@cons _ (@AST.Init_space (@BinInt.Z.mul (8)%Z n)) (@nil _)) false false)))
      -> ((@BinInt.Z.le (1)%Z n)
          -> (neval defs le gv mb
              (@Clight.Ederef
                (@Clight.Ecast
                  (@Clight.Evar x
                    (@Ctypes.Tarray
                      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
                      (@Ctypes.mk_attr false (@None _))))
                  (@Ctypes.Tpointer
                    (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
                    (@Ctypes.mk_attr false (@None _))))
                (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))))
              (@Values.Vlong
                (@NBase.r64
                  (@BinInt.Z.add
                    (@BinInt.Z.add (mb x (0)%Z)
                      (@BinInt.Z.add (@BinInt.Z.mul (256)%Z (mb x (@BinInt.Z.add (0)%Z (1)%Z)))
                        (@BinInt.Z.add (@BinInt.Z.mul (65536)%Z (mb x (@BinInt.Z.add (0)%Z (2)%Z)))
                          (@BinInt.Z.mul (16777216)%Z (mb x (@BinInt.Z.add (0)%Z (3)%Z))))))
                    (@BinInt.Z.mul (4294967296)%Z
                      (@BinInt.Z.add (mb x (@BinInt.Z.add (0)%Z (4)%Z))
                        (@BinInt.Z.add
                          (@BinInt.Z.mul (256)%Z
                            (mb x (@BinInt.Z.add (@BinInt.Z.add (0)%Z (4)%Z) (1)%Z)))
                          (@BinInt.Z.add
                            (@BinInt.Z.mul (65536)%Z
                              (mb x (@BinInt.Z.add (@BinInt.Z.add (0)%Z (4)%Z) (2)%Z)))
                            (@BinInt.Z.mul (16777216)%Z
                              (mb x (@BinInt.Z.add (@BinInt.Z.add (0)%Z (4)%Z) (3)%Z))))))))))))))
  | nv_cell32 : (forall (x : AST.ident) (n : BinNums.Z),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type
          (@AST.mkglobvar Ctypes.type
            (@Ctypes.Tarray (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
              (@Ctypes.mk_attr false (@None _)))
            (@cons _ (@AST.Init_space (@BinInt.Z.mul (8)%Z n)) (@nil _)) false false)))
      -> ((@BinInt.Z.le (1)%Z n)
          -> (neval defs le gv mb
              (@Clight.Ederef
                (@Clight.Ecast
                  (@Clight.Evar x
                    (@Ctypes.Tarray
                      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
                      (@Ctypes.mk_attr false (@None _))))
                  (@Ctypes.Tpointer
                    (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
                    (@Ctypes.mk_attr false (@None _))))
                (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))))
              (@Values.Vint
                (@NBase.r32
                  (@BinInt.Z.add (mb x (0)%Z)
                    (@BinInt.Z.add (@BinInt.Z.mul (256)%Z (mb x (@BinInt.Z.add (0)%Z (1)%Z)))
                      (@BinInt.Z.add (@BinInt.Z.mul (65536)%Z (mb x (@BinInt.Z.add (0)%Z (2)%Z)))
                        (@BinInt.Z.mul (16777216)%Z (mb x (@BinInt.Z.add (0)%Z (3)%Z))))))))))))
  | nv_cellf64 : (forall (x : AST.ident) (n : BinNums.Z),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type
          (@AST.mkglobvar Ctypes.type
            (@Ctypes.Tarray (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
              (@Ctypes.mk_attr false (@None _)))
            (@cons _ (@AST.Init_space (@BinInt.Z.mul (8)%Z n)) (@nil _)) false false)))
      -> ((@BinInt.Z.le (1)%Z n)
          -> (neval defs le gv mb
              (@Clight.Ederef
                (@Clight.Ecast
                  (@Clight.Evar x
                    (@Ctypes.Tarray
                      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
                      (@Ctypes.mk_attr false (@None _))))
                  (@Ctypes.Tpointer (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
                    (@Ctypes.mk_attr false (@None _))))
                (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))))
              (@Values.Vfloat
                (@NBase.f64_of_bits
                  (@NBase.r64
                    (@BinInt.Z.add
                      (@BinInt.Z.add (mb x (0)%Z)
                        (@BinInt.Z.add (@BinInt.Z.mul (256)%Z (mb x (@BinInt.Z.add (0)%Z (1)%Z)))
                          (@BinInt.Z.add
                            (@BinInt.Z.mul (65536)%Z (mb x (@BinInt.Z.add (0)%Z (2)%Z)))
                            (@BinInt.Z.mul (16777216)%Z (mb x (@BinInt.Z.add (0)%Z (3)%Z))))))
                      (@BinInt.Z.mul (4294967296)%Z
                        (@BinInt.Z.add (mb x (@BinInt.Z.add (0)%Z (4)%Z))
                          (@BinInt.Z.add
                            (@BinInt.Z.mul (256)%Z
                              (mb x (@BinInt.Z.add (@BinInt.Z.add (0)%Z (4)%Z) (1)%Z)))
                            (@BinInt.Z.add
                              (@BinInt.Z.mul (65536)%Z
                                (mb x (@BinInt.Z.add (@BinInt.Z.add (0)%Z (4)%Z) (2)%Z)))
                              (@BinInt.Z.mul (16777216)%Z
                                (mb x
                                  (@BinInt.Z.add (@BinInt.Z.add (0)%Z (4)%Z) (3)%Z)))))))))))))))
  | nv_cellf32 : (forall (x : AST.ident) (n : BinNums.Z),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type
          (@AST.mkglobvar Ctypes.type
            (@Ctypes.Tarray (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
              (@Ctypes.mk_attr false (@None _)))
            (@cons _ (@AST.Init_space (@BinInt.Z.mul (8)%Z n)) (@nil _)) false false)))
      -> ((@BinInt.Z.le (1)%Z n)
          -> (neval defs le gv mb
              (@Clight.Ederef
                (@Clight.Ecast
                  (@Clight.Evar x
                    (@Ctypes.Tarray
                      (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
                      (@Ctypes.mk_attr false (@None _))))
                  (@Ctypes.Tpointer (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
                    (@Ctypes.mk_attr false (@None _))))
                (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))))
              (@Values.Vsingle
                (@NBase.f32_of_bits
                  (@NBase.r32
                    (@BinInt.Z.add (mb x (0)%Z)
                      (@BinInt.Z.add (@BinInt.Z.mul (256)%Z (mb x (@BinInt.Z.add (0)%Z (1)%Z)))
                        (@BinInt.Z.add (@BinInt.Z.mul (65536)%Z (mb x (@BinInt.Z.add (0)%Z (2)%Z)))
                          (@BinInt.Z.mul (16777216)%Z (mb x (@BinInt.Z.add (0)%Z (3)%Z)))))))))))))
  | nv_binop : (forall (op : Cop.binary_operation) (a1 : Clight.expr) (a2 : Clight.expr)
      (ty : Ctypes.type) (t1 : Ctypes.type) (t2 : Ctypes.type) (v1 : Values.val) (v2 : Values.val)
      (v : Values.val),
    ((neval defs le gv mb a1 v1)
      -> ((has_type a1 t1)
          -> ((neval defs le gv mb a2 v2)
              -> ((has_type a2 t2)
                  -> ((binop_ok op t1 t2 v1 v2 v)
                      -> (neval defs le gv mb (@Clight.Ebinop op a1 a2 ty) v)))))))
  | nv_cast : (forall (a : Clight.expr) (ty : Ctypes.type) (t1 : Ctypes.type) (v1 : Values.val)
      (v : Values.val),
    ((neval defs le gv mb a v1)
      -> ((has_type a t1)
          -> ((cast_ok t1 ty v1 v) -> (neval defs le gv mb (@Clight.Ecast a ty) v)))))
  | nv_unop : (forall (op : Cop.unary_operation) (a : Clight.expr) (ty : Ctypes.type)
      (t1 : Ctypes.type) (v1 : Values.val) (v : Values.val),
    ((neval defs le gv mb a v1)
      -> ((has_type a t1)
          -> ((unop_ok op t1 v1 v) -> (neval defs le gv mb (@Clight.Eunop op a ty) v))))).

Inductive neval_list (defs : (list (AST.ident * (@AST.globdef Clight.fundef Ctypes.type))))
    (le : (AST.ident -> (option Values.val))) (gv : (AST.ident -> (option Values.val)))
    (mb : (AST.ident -> (BinNums.Z -> BinNums.Z))) : (list Clight.expr) -> (list Ctypes.type) ->
    (list Values.val) -> Prop :=
  | nl_nil : (neval_list defs le gv mb (@nil _) (@nil _) (@nil _))
  | nl_cons : (forall (a : Clight.expr) (al : (list Clight.expr)) (ty : Ctypes.type)
      (tys : (list Ctypes.type)) (t1 : Ctypes.type) (v1 : Values.val) (v : Values.val)
      (vs : (list Values.val)),
    ((neval defs le gv mb a v1)
      -> ((has_type a t1)
          -> ((cast_ok t1 ty v1 v)
              -> ((neval_list defs le gv mb al tys vs)
                  -> (neval_list defs le gv mb (@cons _ a al) (@cons _ ty tys) (@cons _ v vs))))))).

Inductive nexec (defs : (list (AST.ident * (@AST.globdef Clight.fundef Ctypes.type)))) :
    (AST.ident -> (option Values.val)) -> (AST.ident -> (option Values.val)) ->
    (AST.ident -> (BinNums.Z -> BinNums.Z)) -> Clight.statement -> (list Events.event) ->
    (AST.ident -> (option Values.val)) -> (AST.ident -> (option Values.val)) ->
    (AST.ident -> (BinNums.Z -> BinNums.Z)) -> ClightBigstep.outcome -> Prop :=
  | nx_skip : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z))),
    (nexec defs le gv mb Clight.Sskip (@nil _) le gv mb ClightBigstep.Out_normal))
  | nx_set : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (x : AST.ident) (a : Clight.expr) (v : Values.val) (le2 : (AST.ident -> (option Values.val))),
    ((neval defs le gv mb a v)
      -> ((forall (x_upd : AST.ident),
            (((@eq _ x_upd x) -> (@eq _ (le2 x_upd) (@Some _ v)))
              /\ ((~ (@eq _ x_upd x)) -> (@eq _ (le2 x_upd) (le x_upd)))))
          -> (nexec defs le gv mb (@Clight.Sset x a) (@nil _) le2 gv mb ClightBigstep.Out_normal))))
  | nx_store : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (x : AST.ident) (ty : Ctypes.type) (init : (list AST.init_data)) (a : Clight.expr)
      (t1 : Ctypes.type) (v1 : Values.val) (v : Values.val)
      (gv2 : (AST.ident -> (option Values.val))),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type (@AST.mkglobvar Ctypes.type ty init false false)))
      -> ((scalar ty)
          -> ((neval defs le gv mb a v1)
              -> ((has_type a t1)
                  -> ((cast_ok t1 ty v1 v)
                      -> ((gval ty v)
                          -> ((forall (x_upd : AST.ident),
                                (((@eq _ x_upd x) -> (@eq _ (gv2 x_upd) (@Some _ v)))
                                  /\ ((~ (@eq _ x_upd x)) -> (@eq _ (gv2 x_upd) (gv x_upd)))))
                              -> (nexec defs le gv mb (@Clight.Sassign (@Clight.Evar x ty) a)
                                  (@nil _) le gv2 mb ClightBigstep.Out_normal)))))))))
  | nx_store_word : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (x : AST.ident) (n : BinNums.Z) (i : Clight.expr) (k : Integers.Int64.int) (a : Clight.expr)
      (t1 : Ctypes.type) (v1 : Values.val) (w : Integers.Int64.int)
      (mb2 : (AST.ident -> (BinNums.Z -> BinNums.Z))),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type
          (@AST.mkglobvar Ctypes.type
            (@Ctypes.Tarray (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
              (@Ctypes.mk_attr false (@None _)))
            (@cons _ (@AST.Init_space (@BinInt.Z.mul (8)%Z n)) (@nil _)) false false)))
      -> ((neval defs le gv mb i (@Values.Vlong k))
          -> ((has_type i (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))))
              -> ((@BinInt.Z.le
                    (@BinInt.Z.add
                      (@NBase.zmod (@BinInt.Z.mul (8)%Z (@NBase.u64 k)) (18446744073709551616)%Z)
                      (8)%Z) (@BinInt.Z.mul (8)%Z n))
                  -> ((neval defs le gv mb a v1)
                      -> ((has_type a t1)
                          -> ((cast_ok t1
                                (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1
                                (@Values.Vlong w))
                              -> ((forall (y_sb : AST.ident) (j_sb : BinNums.Z),
                                    ((((@eq _ y_sb x)
                                        /\ ((@BinInt.Z.le
                                        (@NBase.zmod (@BinInt.Z.mul (8)%Z (@NBase.u64 k))
                                        (18446744073709551616)%Z) j_sb)
                                        /\ (@BinInt.Z.lt j_sb
                                        (@BinInt.Z.add
                                        (@NBase.zmod (@BinInt.Z.mul (8)%Z (@NBase.u64 k))
                                        (18446744073709551616)%Z) (8)%Z))))
                                        -> (@eq _ (mb2 y_sb j_sb)
                                        (@NBase.zmod
                                        (@NBase.zdiv (@NBase.u64 w)
                                        (@NBase.pow2
                                        (@BinInt.Z.mul (8)%Z
                                        (@BinInt.Z.sub j_sb
                                        (@NBase.zmod (@BinInt.Z.mul (8)%Z (@NBase.u64 k))
                                        (18446744073709551616)%Z))))) (256)%Z)))
                                      /\ ((~ ((@eq _ y_sb x)
                                        /\ ((@BinInt.Z.le
                                        (@NBase.zmod (@BinInt.Z.mul (8)%Z (@NBase.u64 k))
                                        (18446744073709551616)%Z) j_sb)
                                        /\ (@BinInt.Z.lt j_sb
                                        (@BinInt.Z.add
                                        (@NBase.zmod (@BinInt.Z.mul (8)%Z (@NBase.u64 k))
                                        (18446744073709551616)%Z) (8)%Z)))))
                                        -> (@eq _ (mb2 y_sb j_sb) (mb y_sb j_sb)))))
                                  -> (nexec defs le gv mb
                                      (@Clight.Sassign
                                        (@Clight.Ederef
                                        (@Clight.Ebinop Cop.Oadd
                                        (@Clight.Evar x
                                        (@Ctypes.Tarray
                                        (@Ctypes.Tlong Ctypes.Unsigned
                                        (@Ctypes.mk_attr false (@None _))) n
                                        (@Ctypes.mk_attr false (@None _)))) i
                                        (@Ctypes.Tpointer
                                        (@Ctypes.Tlong Ctypes.Unsigned
                                        (@Ctypes.mk_attr false (@None _)))
                                        (@Ctypes.mk_attr false (@None _))))
                                        (@Ctypes.Tlong Ctypes.Unsigned
                                        (@Ctypes.mk_attr false (@None _)))) a) (@nil _) le gv mb2
                                      ClightBigstep.Out_normal))))))))))
  | nx_store_byte : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (x : AST.ident) (n : BinNums.Z) (i : Clight.expr) (k : Integers.Int64.int) (a : Clight.expr)
      (t1 : Ctypes.type) (v1 : Values.val) (c : Integers.Int.int)
      (mb2 : (AST.ident -> (BinNums.Z -> BinNums.Z))),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type
          (@AST.mkglobvar Ctypes.type
            (@Ctypes.Tarray (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
              (@Ctypes.mk_attr false (@None _)))
            (@cons _ (@AST.Init_space (@BinInt.Z.mul (8)%Z n)) (@nil _)) false false)))
      -> ((neval defs le gv mb i (@Values.Vlong k))
          -> ((has_type i (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))))
              -> ((@BinInt.Z.lt (@NBase.u64 k) (@BinInt.Z.mul (8)%Z n))
                  -> ((neval defs le gv mb a v1)
                      -> ((has_type a t1)
                          -> ((cast_ok t1
                                (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned
                                  (@Ctypes.mk_attr false (@None _))) v1 (@Values.Vint c))
                              -> ((forall (y_sb : AST.ident) (j_sb : BinNums.Z),
                                    ((((@eq _ y_sb x)
                                        /\ ((@BinInt.Z.le (@NBase.u64 k) j_sb)
                                        /\ (@BinInt.Z.lt j_sb
                                        (@BinInt.Z.add (@NBase.u64 k) (1)%Z))))
                                        -> (@eq _ (mb2 y_sb j_sb)
                                        (@NBase.zmod
                                        (@NBase.zdiv (@NBase.u32 c)
                                        (@NBase.pow2
                                        (@BinInt.Z.mul (8)%Z (@BinInt.Z.sub j_sb (@NBase.u64 k)))))
                                        (256)%Z)))
                                      /\ ((~ ((@eq _ y_sb x)
                                        /\ ((@BinInt.Z.le (@NBase.u64 k) j_sb)
                                        /\ (@BinInt.Z.lt j_sb
                                        (@BinInt.Z.add (@NBase.u64 k) (1)%Z)))))
                                        -> (@eq _ (mb2 y_sb j_sb) (mb y_sb j_sb)))))
                                  -> (nexec defs le gv mb
                                      (@Clight.Sassign
                                        (@Clight.Ederef
                                        (@Clight.Ebinop Cop.Oadd
                                        (@Clight.Ecast
                                        (@Clight.Evar x
                                        (@Ctypes.Tarray
                                        (@Ctypes.Tlong Ctypes.Unsigned
                                        (@Ctypes.mk_attr false (@None _))) n
                                        (@Ctypes.mk_attr false (@None _))))
                                        (@Ctypes.Tpointer
                                        (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned
                                        (@Ctypes.mk_attr false (@None _)))
                                        (@Ctypes.mk_attr false (@None _)))) i
                                        (@Ctypes.Tpointer
                                        (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned
                                        (@Ctypes.mk_attr false (@None _)))
                                        (@Ctypes.mk_attr false (@None _))))
                                        (@Ctypes.Tint Ctypes.I8 Ctypes.Unsigned
                                        (@Ctypes.mk_attr false (@None _)))) a) (@nil _) le gv mb2
                                      ClightBigstep.Out_normal))))))))))
  | nx_store_cell64 : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (x : AST.ident) (n : BinNums.Z) (a : Clight.expr) (t1 : Ctypes.type) (v1 : Values.val)
      (w : Integers.Int64.int) (mb2 : (AST.ident -> (BinNums.Z -> BinNums.Z))),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type
          (@AST.mkglobvar Ctypes.type
            (@Ctypes.Tarray (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
              (@Ctypes.mk_attr false (@None _)))
            (@cons _ (@AST.Init_space (@BinInt.Z.mul (8)%Z n)) (@nil _)) false false)))
      -> ((@BinInt.Z.le (1)%Z n)
          -> ((neval defs le gv mb a v1)
              -> ((has_type a t1)
                  -> ((cast_ok t1 (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
                        v1 (@Values.Vlong w))
                      -> ((forall (y_sb : AST.ident) (j_sb : BinNums.Z),
                            ((((@eq _ y_sb x)
                                  /\ ((@BinInt.Z.le (0)%Z j_sb)
                                      /\ (@BinInt.Z.lt j_sb (@BinInt.Z.add (0)%Z (8)%Z))))
                                -> (@eq _ (mb2 y_sb j_sb)
                                    (@NBase.zmod
                                      (@NBase.zdiv (@NBase.u64 w)
                                        (@NBase.pow2
                                        (@BinInt.Z.mul (8)%Z (@BinInt.Z.sub j_sb (0)%Z))))
                                      (256)%Z)))
                              /\ ((~ ((@eq _ y_sb x)
                                        /\ ((@BinInt.Z.le (0)%Z j_sb)
                                        /\ (@BinInt.Z.lt j_sb (@BinInt.Z.add (0)%Z (8)%Z)))))
                                  -> (@eq _ (mb2 y_sb j_sb) (mb y_sb j_sb)))))
                          -> (nexec defs le gv mb
                              (@Clight.Sassign
                                (@Clight.Ederef
                                  (@Clight.Ecast
                                    (@Clight.Evar x
                                      (@Ctypes.Tarray
                                        (@Ctypes.Tlong Ctypes.Unsigned
                                        (@Ctypes.mk_attr false (@None _))) n
                                        (@Ctypes.mk_attr false (@None _))))
                                    (@Ctypes.Tpointer
                                      (@Ctypes.Tlong Ctypes.Unsigned
                                        (@Ctypes.mk_attr false (@None _)))
                                      (@Ctypes.mk_attr false (@None _))))
                                  (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))))
                                a) (@nil _) le gv mb2 ClightBigstep.Out_normal))))))))
  | nx_store_cell32 : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (x : AST.ident) (n : BinNums.Z) (a : Clight.expr) (t1 : Ctypes.type) (v1 : Values.val)
      (c : Integers.Int.int) (mb2 : (AST.ident -> (BinNums.Z -> BinNums.Z))),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type
          (@AST.mkglobvar Ctypes.type
            (@Ctypes.Tarray (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
              (@Ctypes.mk_attr false (@None _)))
            (@cons _ (@AST.Init_space (@BinInt.Z.mul (8)%Z n)) (@nil _)) false false)))
      -> ((@BinInt.Z.le (1)%Z n)
          -> ((neval defs le gv mb a v1)
              -> ((has_type a t1)
                  -> ((cast_ok t1
                        (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
                        v1 (@Values.Vint c))
                      -> ((forall (y_sb : AST.ident) (j_sb : BinNums.Z),
                            ((((@eq _ y_sb x)
                                  /\ ((@BinInt.Z.le (0)%Z j_sb)
                                      /\ (@BinInt.Z.lt j_sb (@BinInt.Z.add (0)%Z (4)%Z))))
                                -> (@eq _ (mb2 y_sb j_sb)
                                    (@NBase.zmod
                                      (@NBase.zdiv (@NBase.u32 c)
                                        (@NBase.pow2
                                        (@BinInt.Z.mul (8)%Z (@BinInt.Z.sub j_sb (0)%Z))))
                                      (256)%Z)))
                              /\ ((~ ((@eq _ y_sb x)
                                        /\ ((@BinInt.Z.le (0)%Z j_sb)
                                        /\ (@BinInt.Z.lt j_sb (@BinInt.Z.add (0)%Z (4)%Z)))))
                                  -> (@eq _ (mb2 y_sb j_sb) (mb y_sb j_sb)))))
                          -> (nexec defs le gv mb
                              (@Clight.Sassign
                                (@Clight.Ederef
                                  (@Clight.Ecast
                                    (@Clight.Evar x
                                      (@Ctypes.Tarray
                                        (@Ctypes.Tlong Ctypes.Unsigned
                                        (@Ctypes.mk_attr false (@None _))) n
                                        (@Ctypes.mk_attr false (@None _))))
                                    (@Ctypes.Tpointer
                                      (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned
                                        (@Ctypes.mk_attr false (@None _)))
                                      (@Ctypes.mk_attr false (@None _))))
                                  (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned
                                    (@Ctypes.mk_attr false (@None _)))) a) (@nil _) le gv mb2
                              ClightBigstep.Out_normal))))))))
  | nx_store_cellf64 : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (x : AST.ident) (n : BinNums.Z) (a : Clight.expr) (t1 : Ctypes.type) (v1 : Values.val)
      (f : Floats.float) (mb2 : (AST.ident -> (BinNums.Z -> BinNums.Z))),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type
          (@AST.mkglobvar Ctypes.type
            (@Ctypes.Tarray (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
              (@Ctypes.mk_attr false (@None _)))
            (@cons _ (@AST.Init_space (@BinInt.Z.mul (8)%Z n)) (@nil _)) false false)))
      -> ((@BinInt.Z.le (1)%Z n)
          -> ((neval defs le gv mb a v1)
              -> ((has_type a t1)
                  -> ((cast_ok t1 (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v1
                        (@Values.Vfloat f))
                      -> ((forall (y_sb : AST.ident) (j_sb : BinNums.Z),
                            ((((@eq _ y_sb x)
                                  /\ ((@BinInt.Z.le (0)%Z j_sb)
                                      /\ (@BinInt.Z.lt j_sb (@BinInt.Z.add (0)%Z (8)%Z))))
                                -> (@eq _ (mb2 y_sb j_sb)
                                    (@NBase.zmod
                                      (@NBase.zdiv (@NBase.u64 (@NBase.f64_bits f))
                                        (@NBase.pow2
                                        (@BinInt.Z.mul (8)%Z (@BinInt.Z.sub j_sb (0)%Z))))
                                      (256)%Z)))
                              /\ ((~ ((@eq _ y_sb x)
                                        /\ ((@BinInt.Z.le (0)%Z j_sb)
                                        /\ (@BinInt.Z.lt j_sb (@BinInt.Z.add (0)%Z (8)%Z)))))
                                  -> (@eq _ (mb2 y_sb j_sb) (mb y_sb j_sb)))))
                          -> (nexec defs le gv mb
                              (@Clight.Sassign
                                (@Clight.Ederef
                                  (@Clight.Ecast
                                    (@Clight.Evar x
                                      (@Ctypes.Tarray
                                        (@Ctypes.Tlong Ctypes.Unsigned
                                        (@Ctypes.mk_attr false (@None _))) n
                                        (@Ctypes.mk_attr false (@None _))))
                                    (@Ctypes.Tpointer
                                      (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
                                      (@Ctypes.mk_attr false (@None _))))
                                  (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))) a)
                              (@nil _) le gv mb2 ClightBigstep.Out_normal))))))))
  | nx_store_cellf32 : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (x : AST.ident) (n : BinNums.Z) (a : Clight.expr) (t1 : Ctypes.type) (v1 : Values.val)
      (f : Floats.float32) (mb2 : (AST.ident -> (BinNums.Z -> BinNums.Z))),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type
          (@AST.mkglobvar Ctypes.type
            (@Ctypes.Tarray (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
              (@Ctypes.mk_attr false (@None _)))
            (@cons _ (@AST.Init_space (@BinInt.Z.mul (8)%Z n)) (@nil _)) false false)))
      -> ((@BinInt.Z.le (1)%Z n)
          -> ((neval defs le gv mb a v1)
              -> ((has_type a t1)
                  -> ((cast_ok t1 (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v1
                        (@Values.Vsingle f))
                      -> ((forall (y_sb : AST.ident) (j_sb : BinNums.Z),
                            ((((@eq _ y_sb x)
                                  /\ ((@BinInt.Z.le (0)%Z j_sb)
                                      /\ (@BinInt.Z.lt j_sb (@BinInt.Z.add (0)%Z (4)%Z))))
                                -> (@eq _ (mb2 y_sb j_sb)
                                    (@NBase.zmod
                                      (@NBase.zdiv (@NBase.u32 (@NBase.f32_bits f))
                                        (@NBase.pow2
                                        (@BinInt.Z.mul (8)%Z (@BinInt.Z.sub j_sb (0)%Z))))
                                      (256)%Z)))
                              /\ ((~ ((@eq _ y_sb x)
                                        /\ ((@BinInt.Z.le (0)%Z j_sb)
                                        /\ (@BinInt.Z.lt j_sb (@BinInt.Z.add (0)%Z (4)%Z)))))
                                  -> (@eq _ (mb2 y_sb j_sb) (mb y_sb j_sb)))))
                          -> (nexec defs le gv mb
                              (@Clight.Sassign
                                (@Clight.Ederef
                                  (@Clight.Ecast
                                    (@Clight.Evar x
                                      (@Ctypes.Tarray
                                        (@Ctypes.Tlong Ctypes.Unsigned
                                        (@Ctypes.mk_attr false (@None _))) n
                                        (@Ctypes.mk_attr false (@None _))))
                                    (@Ctypes.Tpointer
                                      (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
                                      (@Ctypes.mk_attr false (@None _))))
                                  (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))) a)
                              (@nil _) le gv mb2 ClightBigstep.Out_normal))))))))
  | nx_out : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (x : AST.ident) (init : (list AST.init_data)) (a : Clight.expr) (t1 : Ctypes.type)
      (v1 : Values.val) (i : Integers.Int.int),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type
          (@AST.mkglobvar Ctypes.type
            (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr true (@None _))) init false
            true)))
      -> ((neval defs le gv mb a v1)
          -> ((has_type a t1)
              -> ((cast_ok t1
                    (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr true (@None _))) v1
                    (@Values.Vint i))
                  -> (nexec defs le gv mb
                      (@Clight.Sbuiltin (@None _) (@AST.EF_vstore AST.Mint32)
                        (@cons _
                          (@Ctypes.Tpointer
                            (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned
                              (@Ctypes.mk_attr true (@None _))) (@Ctypes.mk_attr false (@None _)))
                          (@cons _
                            (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned
                              (@Ctypes.mk_attr true (@None _))) (@nil _)))
                        (@cons _
                          (@Clight.Eaddrof
                            (@Clight.Evar x
                              (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned
                                (@Ctypes.mk_attr true (@None _))))
                            (@Ctypes.Tpointer
                              (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned
                                (@Ctypes.mk_attr true (@None _)))
                              (@Ctypes.mk_attr false (@None _)))) (@cons _ a (@nil _))))
                      (@cons _
                        (@Events.Event_vstore AST.Mint32 x (@NBase.rptr (0)%Z) (@Events.EVint i))
                        (@nil _)) le gv mb ClightBigstep.Out_normal))))))
  | nx_vload : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (t : AST.ident) (x : AST.ident) (ty : Ctypes.type) (n : BinNums.Z)
      (init : (list AST.init_data)) (ch : AST.memory_chunk) (sz : BinNums.Z) (i : Clight.expr)
      (k : Integers.Int64.int) (j : Integers.Int.int) (v : Values.val)
      (le2 : (AST.ident -> (option Values.val))),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type
          (@AST.mkglobvar Ctypes.type (@Ctypes.Tarray ty n (@Ctypes.mk_attr false (@None _))) init
            false true)))
      -> ((neval defs le gv mb i (@Values.Vlong k))
          -> ((has_type i (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))))
              -> ((vload_ok ch ty sz j v)
                  -> ((forall (x_upd : AST.ident),
                        (((@eq _ x_upd t) -> (@eq _ (le2 x_upd) (@Some _ v)))
                          /\ ((~ (@eq _ x_upd t)) -> (@eq _ (le2 x_upd) (le x_upd)))))
                      -> (nexec defs le gv mb
                          (@Clight.Sbuiltin (@Some _ t) (@AST.EF_vload ch)
                            (@cons _ (@Ctypes.Tpointer ty (@Ctypes.mk_attr false (@None _)))
                              (@nil _))
                            (@cons _
                              (@Clight.Eaddrof
                                (@Clight.Ederef
                                  (@Clight.Ebinop Cop.Oadd
                                    (@Clight.Evar x
                                      (@Ctypes.Tarray ty n (@Ctypes.mk_attr false (@None _)))) i
                                    (@Ctypes.Tpointer ty (@Ctypes.mk_attr false (@None _)))) ty)
                                (@Ctypes.Tpointer ty (@Ctypes.mk_attr false (@None _)))) (@nil _)))
                          (@cons _
                            (@Events.Event_vload ch x
                              (@NBase.rptr (@BinInt.Z.mul sz (@NBase.u64 k))) (@Events.EVint j))
                            (@nil _)) le2 gv mb ClightBigstep.Out_normal)))))))
  | nx_vstore : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (x : AST.ident) (n : BinNums.Z) (init : (list AST.init_data)) (i : Clight.expr)
      (k : Integers.Int64.int) (a : Clight.expr) (t1 : Ctypes.type) (v1 : Values.val)
      (c : Integers.Int.int),
    ((in_defs defs x
        (@AST.Gvar Clight.fundef Ctypes.type
          (@AST.mkglobvar Ctypes.type
            (@Ctypes.Tarray
              (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr true (@None _))) n
              (@Ctypes.mk_attr false (@None _))) init false true)))
      -> ((neval defs le gv mb i (@Values.Vlong k))
          -> ((has_type i (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))))
              -> ((neval defs le gv mb a v1)
                  -> ((has_type a t1)
                      -> ((cast_ok t1
                            (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned
                              (@Ctypes.mk_attr true (@None _))) v1 (@Values.Vint c))
                          -> (nexec defs le gv mb
                              (@Clight.Sbuiltin (@None _) (@AST.EF_vstore AST.Mint32)
                                (@cons _
                                  (@Ctypes.Tpointer
                                    (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned
                                      (@Ctypes.mk_attr true (@None _)))
                                    (@Ctypes.mk_attr false (@None _)))
                                  (@cons _
                                    (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned
                                      (@Ctypes.mk_attr true (@None _))) (@nil _)))
                                (@cons _
                                  (@Clight.Eaddrof
                                    (@Clight.Ederef
                                      (@Clight.Ebinop Cop.Oadd
                                        (@Clight.Evar x
                                        (@Ctypes.Tarray
                                        (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned
                                        (@Ctypes.mk_attr true (@None _))) n
                                        (@Ctypes.mk_attr false (@None _)))) i
                                        (@Ctypes.Tpointer
                                        (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned
                                        (@Ctypes.mk_attr true (@None _)))
                                        (@Ctypes.mk_attr false (@None _))))
                                      (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned
                                        (@Ctypes.mk_attr true (@None _))))
                                    (@Ctypes.Tpointer
                                      (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned
                                        (@Ctypes.mk_attr true (@None _)))
                                      (@Ctypes.mk_attr false (@None _)))) (@cons _ a (@nil _))))
                              (@cons _
                                (@Events.Event_vstore AST.Mint32 x
                                  (@NBase.rptr (@BinInt.Z.mul (4)%Z (@NBase.u64 k)))
                                  (@Events.EVint c)) (@nil _)) le gv mb
                              ClightBigstep.Out_normal))))))))
  | nx_call : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (optid : (option AST.ident)) (x : AST.ident) (tys : (list Ctypes.type)) (ret : Ctypes.type)
      (cc : AST.calling_convention) (al : (list Clight.expr)) (vs : (list Values.val))
      (params : (list (AST.ident * Ctypes.type))) (temps : (list (AST.ident * Ctypes.type)))
      (body : Clight.statement) (le0 : (AST.ident -> (option Values.val)))
      (le1 : (AST.ident -> (option Values.val))) (t : (list Events.event))
      (le2 : (AST.ident -> (option Values.val))) (gv2 : (AST.ident -> (option Values.val)))
      (mb2 : (AST.ident -> (BinNums.Z -> BinNums.Z))) (out : ClightBigstep.outcome) (v : Values.val)
      (le3 : (AST.ident -> (option Values.val))),
    ((in_defs defs x
        (@AST.Gfun Clight.fundef Ctypes.type
          (@Ctypes.Internal Clight.function
            (@Clight.mkfunction ret cc params (@nil _) temps body))))
      -> ((params_types params tys)
          -> ((neval_list defs le gv mb al tys vs)
              -> ((norepet_names params)
                  -> ((disjoint_names params temps)
                      -> ((undef_temps temps le0)
                          -> ((bind_params params vs le0 le1)
                              -> ((nexec defs le1 gv mb body t le2 gv2 mb2 out)
                                  -> ((result_ok out ret v)
                                      -> ((set_opt optid v le le3)
                                        -> (nexec defs le gv mb
                                        (@Clight.Scall optid
                                        (@Clight.Evar x (@Ctypes.Tfunction tys ret cc)) al) t le3
                                        gv2 mb2 ClightBigstep.Out_normal))))))))))))
  | nx_sqrt : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (optid : (option AST.ident)) (x : AST.ident) (al : (list Clight.expr)) (f : Floats.float)
      (le2 : (AST.ident -> (option Values.val))),
    ((in_defs defs x
        (@AST.Gfun Clight.fundef Ctypes.type
          (@Ctypes.External Clight.function
            (@AST.EF_builtin ("__builtin_fsqrt"%string)
              (@AST.mksignature (@cons _ AST.Xfloat (@nil _)) AST.Xfloat
                (@AST.mkcallconv (@None _) false false)))
            (@cons _ (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@nil _))
            (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
            (@AST.mkcallconv (@None _) false false))))
      -> ((neval_list defs le gv mb al
            (@cons _ (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) (@nil _))
            (@cons _ (@Values.Vfloat f) (@nil _)))
          -> ((set_opt optid (@Values.Vfloat (@Floats.Float.sqrt f)) le le2)
              -> (nexec defs le gv mb
                  (@Clight.Scall optid
                    (@Clight.Evar x
                      (@Ctypes.Tfunction
                        (@cons _ (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
                          (@nil _)) (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
                        (@AST.mkcallconv (@None _) false false))) al) (@nil _) le2 gv mb
                  ClightBigstep.Out_normal)))))
  | nx_seq1 : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (s1 : Clight.statement) (s2 : Clight.statement) (t1 : (list Events.event))
      (le1 : (AST.ident -> (option Values.val))) (gv1 : (AST.ident -> (option Values.val)))
      (mb1 : (AST.ident -> (BinNums.Z -> BinNums.Z))) (t2 : (list Events.event))
      (le2 : (AST.ident -> (option Values.val))) (gv2 : (AST.ident -> (option Values.val)))
      (mb2 : (AST.ident -> (BinNums.Z -> BinNums.Z))) (out : ClightBigstep.outcome),
    ((nexec defs le gv mb s1 t1 le1 gv1 mb1 ClightBigstep.Out_normal)
      -> ((nexec defs le1 gv1 mb1 s2 t2 le2 gv2 mb2 out)
          -> (nexec defs le gv mb (@Clight.Ssequence s1 s2) (@NBase.app t1 t2) le2 gv2 mb2 out))))
  | nx_seq2 : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (s1 : Clight.statement) (s2 : Clight.statement) (t1 : (list Events.event))
      (le1 : (AST.ident -> (option Values.val))) (gv1 : (AST.ident -> (option Values.val)))
      (mb1 : (AST.ident -> (BinNums.Z -> BinNums.Z))) (out : ClightBigstep.outcome),
    ((nexec defs le gv mb s1 t1 le1 gv1 mb1 out)
      -> ((~ (@eq _ out ClightBigstep.Out_normal))
          -> (nexec defs le gv mb (@Clight.Ssequence s1 s2) t1 le1 gv1 mb1 out))))
  | nx_if_true : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (a : Clight.expr) (s1 : Clight.statement) (s2 : Clight.statement) (v : Values.val)
      (ta : Ctypes.type) (t : (list Events.event)) (le2 : (AST.ident -> (option Values.val)))
      (gv2 : (AST.ident -> (option Values.val))) (mb2 : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (out : ClightBigstep.outcome),
    ((neval defs le gv mb a v)
      -> ((has_type a ta)
          -> ((bool_ok ta v true)
              -> ((nexec defs le gv mb s1 t le2 gv2 mb2 out)
                  -> (nexec defs le gv mb (@Clight.Sifthenelse a s1 s2) t le2 gv2 mb2 out))))))
  | nx_if_false : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (a : Clight.expr) (s1 : Clight.statement) (s2 : Clight.statement) (v : Values.val)
      (ta : Ctypes.type) (t : (list Events.event)) (le2 : (AST.ident -> (option Values.val)))
      (gv2 : (AST.ident -> (option Values.val))) (mb2 : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (out : ClightBigstep.outcome),
    ((neval defs le gv mb a v)
      -> ((has_type a ta)
          -> ((bool_ok ta v false)
              -> ((nexec defs le gv mb s2 t le2 gv2 mb2 out)
                  -> (nexec defs le gv mb (@Clight.Sifthenelse a s1 s2) t le2 gv2 mb2 out))))))
  | nx_return_none : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z))),
    (nexec defs le gv mb (@Clight.Sreturn (@None _)) (@nil _) le gv mb
      (@ClightBigstep.Out_return (@None _))))
  | nx_return_some : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (a : Clight.expr) (v : Values.val) (ta : Ctypes.type),
    ((neval defs le gv mb a v)
      -> ((has_type a ta)
          -> (nexec defs le gv mb (@Clight.Sreturn (@Some _ a)) (@nil _) le gv mb
              (@ClightBigstep.Out_return (@Some _ (@pair _ _ v ta)))))))
  | nx_break : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z))),
    (nexec defs le gv mb Clight.Sbreak (@nil _) le gv mb ClightBigstep.Out_break))
  | nx_continue : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z))),
    (nexec defs le gv mb Clight.Scontinue (@nil _) le gv mb ClightBigstep.Out_continue))
  | nx_loop_stop1 : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (s1 : Clight.statement) (s2 : Clight.statement) (t : (list Events.event))
      (le1 : (AST.ident -> (option Values.val))) (gv1 : (AST.ident -> (option Values.val)))
      (mb1 : (AST.ident -> (BinNums.Z -> BinNums.Z))) (out1 : ClightBigstep.outcome)
      (out : ClightBigstep.outcome),
    ((nexec defs le gv mb s1 t le1 gv1 mb1 out1)
      -> ((((@eq _ out1 ClightBigstep.Out_break) /\ (@eq _ out ClightBigstep.Out_normal))
            \/ (exists (r : (option (Values.val * Ctypes.type))),
                ((@eq _ out1 (@ClightBigstep.Out_return r))
                  /\ (@eq _ out (@ClightBigstep.Out_return r)))))
          -> (nexec defs le gv mb (@Clight.Sloop s1 s2) t le1 gv1 mb1 out))))
  | nx_loop_stop2 : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (s1 : Clight.statement) (s2 : Clight.statement) (t1 : (list Events.event))
      (le1 : (AST.ident -> (option Values.val))) (gv1 : (AST.ident -> (option Values.val)))
      (mb1 : (AST.ident -> (BinNums.Z -> BinNums.Z))) (out1 : ClightBigstep.outcome)
      (t2 : (list Events.event)) (le2 : (AST.ident -> (option Values.val)))
      (gv2 : (AST.ident -> (option Values.val))) (mb2 : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (out2 : ClightBigstep.outcome) (out : ClightBigstep.outcome),
    ((nexec defs le gv mb s1 t1 le1 gv1 mb1 out1)
      -> (((@eq _ out1 ClightBigstep.Out_normal) \/ (@eq _ out1 ClightBigstep.Out_continue))
          -> ((nexec defs le1 gv1 mb1 s2 t2 le2 gv2 mb2 out2)
              -> ((((@eq _ out2 ClightBigstep.Out_break) /\ (@eq _ out ClightBigstep.Out_normal))
                    \/ (exists (r : (option (Values.val * Ctypes.type))),
                        ((@eq _ out2 (@ClightBigstep.Out_return r))
                          /\ (@eq _ out (@ClightBigstep.Out_return r)))))
                  -> (nexec defs le gv mb (@Clight.Sloop s1 s2) (@NBase.app t1 t2) le2 gv2 mb2
                      out))))))
  | nx_loop : (forall (le : (AST.ident -> (option Values.val)))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (s1 : Clight.statement) (s2 : Clight.statement) (t1 : (list Events.event))
      (le1 : (AST.ident -> (option Values.val))) (gv1 : (AST.ident -> (option Values.val)))
      (mb1 : (AST.ident -> (BinNums.Z -> BinNums.Z))) (out1 : ClightBigstep.outcome)
      (t2 : (list Events.event)) (le2 : (AST.ident -> (option Values.val)))
      (gv2 : (AST.ident -> (option Values.val))) (mb2 : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (t3 : (list Events.event)) (le3 : (AST.ident -> (option Values.val)))
      (gv3 : (AST.ident -> (option Values.val))) (mb3 : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (out : ClightBigstep.outcome),
    ((nexec defs le gv mb s1 t1 le1 gv1 mb1 out1)
      -> (((@eq _ out1 ClightBigstep.Out_normal) \/ (@eq _ out1 ClightBigstep.Out_continue))
          -> ((nexec defs le1 gv1 mb1 s2 t2 le2 gv2 mb2 ClightBigstep.Out_normal)
              -> ((nexec defs le2 gv2 mb2 (@Clight.Sloop s1 s2) t3 le3 gv3 mb3 out)
                  -> (nexec defs le gv mb (@Clight.Sloop s1 s2) (@NBase.app t1 (@NBase.app t2 t3))
                      le3 gv3 mb3 out)))))).

Inductive ninit : (list (AST.ident * (@AST.globdef Clight.fundef Ctypes.type))) ->
    (AST.ident -> (option Values.val)) -> (AST.ident -> (BinNums.Z -> BinNums.Z)) -> Prop :=
  | ni_intro : (forall (defs : (list (AST.ident * (@AST.globdef Clight.fundef Ctypes.type))))
      (gv : (AST.ident -> (option Values.val))) (mb : (AST.ident -> (BinNums.Z -> BinNums.Z))),
    ((norepet_defs defs)
      -> ((forall (x : AST.ident) (ty : Ctypes.type) (init : (list AST.init_data)) (ro : bool)
              (vol : bool),
            ((in_defs defs x
                (@AST.Gvar Clight.fundef Ctypes.type (@AST.mkglobvar Ctypes.type ty init ro vol)))
              -> (init_ok init)))
          -> ((forall (x : AST.ident) (ty : Ctypes.type) (init : (list AST.init_data)),
                ((in_defs defs x
                    (@AST.Gvar Clight.fundef Ctypes.type
                      (@AST.mkglobvar Ctypes.type ty init false false)))
                  -> ((scalar ty)
                      -> (exists (v : Values.val),
                          ((ginit ty init v) /\ (@eq _ (gv x) (@Some _ v)))))))
              -> ((forall (x : AST.ident) (n : BinNums.Z) (j : BinNums.Z),
                    ((in_defs defs x
                        (@AST.Gvar Clight.fundef Ctypes.type
                          (@AST.mkglobvar Ctypes.type
                            (@Ctypes.Tarray
                              (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) n
                              (@Ctypes.mk_attr false (@None _)))
                            (@cons _ (@AST.Init_space (@BinInt.Z.mul (8)%Z n)) (@nil _)) false
                            false)))
                      -> ((@BinInt.Z.le (0)%Z j)
                          -> ((@BinInt.Z.lt j (@BinInt.Z.mul (8)%Z n)) -> (@eq _ (mb x j) (0)%Z)))))
                  -> (ninit defs gv mb)))))).

Inductive nprog : (list (AST.ident * (@AST.globdef Clight.fundef Ctypes.type))) -> AST.ident ->
    (list Events.event) -> Integers.Int.int -> Prop :=
  | np_intro : (forall (defs : (list (AST.ident * (@AST.globdef Clight.fundef Ctypes.type))))
      (main : AST.ident) (temps : (list (AST.ident * Ctypes.type))) (body : Clight.statement)
      (gv0 : (AST.ident -> (option Values.val))) (mb0 : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (le0 : (AST.ident -> (option Values.val))) (t : (list Events.event))
      (le2 : (AST.ident -> (option Values.val))) (gv2 : (AST.ident -> (option Values.val)))
      (mb2 : (AST.ident -> (BinNums.Z -> BinNums.Z))) (out : ClightBigstep.outcome)
      (r : Integers.Int.int),
    ((ninit defs gv0 mb0)
      -> ((in_defs defs main
            (@AST.Gfun Clight.fundef Ctypes.type
              (@Ctypes.Internal Clight.function
                (@Clight.mkfunction
                  (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
                  (@AST.mkcallconv (@None _) false false) (@nil _) (@nil _) temps body))))
          -> ((undef_temps temps le0)
              -> ((nexec defs le0 gv0 mb0 body t le2 gv2 mb2 out)
                  -> ((result_ok out
                        (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
                        (@Values.Vint r)) -> (nprog defs main t r))))))).

Inductive loop_in : Clight.statement -> Clight.statement -> Clight.statement -> Clight.statement ->
    Prop :=
  | li_loop : (forall (body : Clight.statement) (post : Clight.statement),
    (loop_in (@Clight.Sloop body post) Clight.Sskip body post))
  | li_after : (forall (s : Clight.statement) (init : Clight.statement) (body : Clight.statement)
      (post : Clight.statement) (rest : Clight.statement),
    ((loop_in s init body post) -> (loop_in (@Clight.Ssequence s rest) init body post)))
  | li_before : (forall (s : Clight.statement) (init : Clight.statement) (body : Clight.statement)
      (post : Clight.statement) (pre : Clight.statement),
    ((loop_in s init body post)
      -> (loop_in (@Clight.Ssequence pre s) (@Clight.Ssequence pre init) body post))).

Inductive nreacts : (list (AST.ident * (@AST.globdef Clight.fundef Ctypes.type))) -> AST.ident ->
    (list Events.event) -> (nat -> (list Events.event)) -> Prop :=
  | nr_intro : (forall (defs : (list (AST.ident * (@AST.globdef Clight.fundef Ctypes.type))))
      (main : AST.ident) (temps : (list (AST.ident * Ctypes.type))) (body : Clight.statement)
      (gv0 : (AST.ident -> (option Values.val))) (mb0 : (AST.ident -> (BinNums.Z -> BinNums.Z)))
      (le0 : (AST.ident -> (option Values.val))) (init : Clight.statement)
      (lbody : Clight.statement) (lpost : Clight.statement) (t0 : (list Events.event))
      (W : (nat -> (list Events.event)))
      (Inv :
        (nat
          -> ((AST.ident -> (option Values.val))
              -> ((AST.ident -> (option Values.val))
                  -> ((AST.ident -> (BinNums.Z -> BinNums.Z)) -> Prop))))),
    ((forall (n : nat), (~ (@eq _ (W n) (@nil _))))
      -> ((ninit defs gv0 mb0)
          -> ((in_defs defs main
                (@AST.Gfun Clight.fundef Ctypes.type
                  (@Ctypes.Internal Clight.function
                    (@Clight.mkfunction
                      (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
                      (@AST.mkcallconv (@None _) false false) (@nil _) (@nil _) temps body))))
              -> ((undef_temps temps le0)
                  -> ((loop_in body init lbody lpost)
                      -> ((exists (le : (AST.ident -> (option Values.val)))
                              (gv : (AST.ident -> (option Values.val)))
                              (mb : (AST.ident -> (BinNums.Z -> BinNums.Z))),
                            ((nexec defs le0 gv0 mb0 init t0 le gv mb ClightBigstep.Out_normal)
                              /\ (Inv O le gv mb)))
                          -> ((forall (n : nat) (le : (AST.ident -> (option Values.val)))
                                  (gv : (AST.ident -> (option Values.val)))
                                  (mb : (AST.ident -> (BinNums.Z -> BinNums.Z))),
                                ((Inv n le gv mb)
                                  -> (exists (le2 : (AST.ident -> (option Values.val)))
                                        (gv2 : (AST.ident -> (option Values.val)))
                                        (mb2 : (AST.ident -> (BinNums.Z -> BinNums.Z))),
                                      ((nexec defs le gv mb (@Clight.Ssequence lbody lpost) (W n)
                                        le2 gv2 mb2 ClightBigstep.Out_normal)
                                        /\ (Inv (@S n) le2 gv2 mb2)))))
                              -> (nreacts defs main t0 W))))))))).

Inductive nreads : (nat -> Integers.Int.int) -> nat -> (list Events.event) -> Prop :=
  | nr_nil : (forall (s : (nat -> Integers.Int.int)) (c : nat), (nreads s c (@nil _)))
  | nr_load : (forall (s : (nat -> Integers.Int.int)) (c : nat) (ch : AST.memory_chunk)
      (x : AST.ident) (o : Integers.Ptrofs.int) (t : (list Events.event)),
    ((nreads s (@S c) t)
      -> (nreads s c (@cons _ (@Events.Event_vload ch x o (@Events.EVint (s c))) t))))
  | nr_store : (forall (s : (nat -> Integers.Int.int)) (c : nat) (ch : AST.memory_chunk)
      (x : AST.ident) (o : Integers.Ptrofs.int) (ev : Events.eventval) (t : (list Events.event)),
    ((nreads s c t) -> (nreads s c (@cons _ (@Events.Event_vstore ch x o ev) t)))).

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

Definition stmt_add_d_d : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oadd v1
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Oadd (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_sub_d_d : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Osub v1
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Osub (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_mul_d_d : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Omul v1
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Omul (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_div_d_d : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Odiv v1
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Odiv (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_eq_d_d : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oeq v1
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Oeq (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_ne_d_d : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.One v1
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.One (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_lt_d_d : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Olt v1
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Olt (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_le_d_d : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Ole v1
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Ole (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_ge_d_d : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oge v1
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Oge (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_add_f_f : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oadd v1
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Oadd (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_sub_f_f : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Osub v1
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Osub (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_mul_f_f : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Omul v1
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Omul (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_div_f_f : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Odiv v1
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Odiv (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_eq_f_f : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oeq v1
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Oeq (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_ne_f_f : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.One v1
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.One (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_lt_f_f : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Olt v1
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Olt (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_le_f_f : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Ole v1
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Ole (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

Definition stmt_ge_f_f : Prop :=
  (forall (ce : Ctypes.composite_env) (v1 : Values.val) (v2 : Values.val) (v : Values.val)
      (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_binop ce Cop.Oge v1
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v2
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (binop_ok Cop.Oge (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v1 v2 v))).

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

Definition stmt_cast_d_d : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1 (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_f_f : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1 (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_ul_d : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1 (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_d_ul : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1 (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_f_d : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1 (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_d_f : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1 (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_si_f : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_ui_f : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1
          (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_ul_f : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1 (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_f_si : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1 (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tint Ctypes.I32 Ctypes.Signed (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_cast_f_ul : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_cast v1 (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (cast_ok (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          (@Ctypes.Tlong Ctypes.Unsigned (@Ctypes.mk_attr false (@None _))) v1 v))).

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

Definition stmt_neg_d : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_unop Cop.Oneg v1 (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _)))
          m) (@Some _ v))
      <-> (unop_ok Cop.Oneg (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v1 v))).

Definition stmt_abs_d : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_unop Cop.Oabsfloat v1
          (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) m) (@Some _ v))
      <-> (unop_ok Cop.Oabsfloat (@Ctypes.Tfloat Ctypes.F64 (@Ctypes.mk_attr false (@None _))) v1
          v))).

Definition stmt_neg_f : Prop :=
  (forall (v1 : Values.val) (v : Values.val) (m : Memory.Mem.mem),
    ((@eq _
        (@NBase.sem_unop Cop.Oneg v1 (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _)))
          m) (@Some _ v))
      <-> (unop_ok Cop.Oneg (@Ctypes.Tfloat Ctypes.F32 (@Ctypes.mk_attr false (@None _))) v1 v))).

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

Definition stmt_uptr_range : Prop :=
  (forall (x : Integers.Ptrofs.int),
    ((@BinInt.Z.le (0)%Z (@NBase.uptr x))
      /\ (@BinInt.Z.lt (@NBase.uptr x) (18446744073709551616)%Z))).

Definition stmt_uptr_rptr : Prop :=
  (forall (z : BinNums.Z),
    (@eq _ (@NBase.uptr (@NBase.rptr z)) (@NBase.zmod z (18446744073709551616)%Z))).

Definition stmt_rptr_uptr : Prop :=
  (forall (x : Integers.Ptrofs.int), (@eq _ (@NBase.rptr (@NBase.uptr x)) x)).

Definition stmt_app_nil : Prop :=
  (forall (t : (list Events.event)), (@eq _ (@NBase.app (@nil _) t) t)).

Definition stmt_app_cons : Prop :=
  (forall (e : Events.event) (t1 : (list Events.event)) (t2 : (list Events.event)),
    (@eq _ (@NBase.app (@cons _ e t1) t2) (@cons _ e (@NBase.app t1 t2)))).

Definition stmt_f64_bits_of_bits : Prop :=
  (forall (x : Integers.Int64.int), (@eq _ (@NBase.f64_bits (@NBase.f64_of_bits x)) x)).

Definition stmt_f64_of_bits_bits : Prop :=
  (forall (f : Floats.float), (@eq _ (@NBase.f64_of_bits (@NBase.f64_bits f)) f)).

Definition stmt_f32_bits_of_bits : Prop :=
  (forall (x : Integers.Int.int), (@eq _ (@NBase.f32_bits (@NBase.f32_of_bits x)) x)).

Definition stmt_f32_of_bits_bits : Prop :=
  (forall (f : Floats.float32), (@eq _ (@NBase.f32_of_bits (@NBase.f32_bits f)) f)).
