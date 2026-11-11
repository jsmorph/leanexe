(* The statements of clightn/N.nsx, proved of CompCert 3.18's definitions: the laws of the base
   symbols of NBase.v, and the leaf forms of the operators, casts, truth values, and constants
   that the C translator emits.  Each leaf form first computes CompCert's definition on every
   shape of value (the lemmas eq_*, proved by computation after case analysis), then relates the
   result to the rules of the leaf relation.  The proofs need Archi.ptr64 = true, which holds on
   AArch64.  Lean proves the same statements of the Lean copy of Clight
   (LeanExe/Native/ClightN/Laws.lean and Leaf.lean). *)
From Coq Require Import ZArith Lia Znumtheory.
Require Import Coqlib Integers Floats Values Memory Ctypes Cop Clight.
Require Import NBase NSpec.

Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

(** * Laws of the base symbols *)

Theorem u32_range : stmt_u32_range.
Proof.
  intros x. pose proof (Int.unsigned_range x). unfold u32.
  change Int.modulus with 4294967296 in H. lia.
Qed.

Theorem u32_r32 : stmt_u32_r32.
Proof. intros z. unfold u32, r32, zmod. rewrite Int.unsigned_repr_eq. reflexivity. Qed.

Theorem r32_u32 : stmt_r32_u32.
Proof. intros x. apply Int.repr_unsigned. Qed.

Theorem u64_range : stmt_u64_range.
Proof.
  intros x. pose proof (Int64.unsigned_range x). unfold u64.
  change Int64.modulus with 18446744073709551616 in H. lia.
Qed.

Theorem u64_r64 : stmt_u64_r64.
Proof. intros z. unfold u64, r64, zmod. rewrite Int64.unsigned_repr_eq. reflexivity. Qed.

Theorem r64_u64 : stmt_r64_u64.
Proof. intros x. apply Int64.repr_unsigned. Qed.

Theorem s64_low : stmt_s64_low.
Proof.
  intros x H. unfold s64, u64 in *. unfold Int64.signed.
  destruct (zlt (Int64.unsigned x) Int64.half_modulus) as [L|L]; auto.
  change Int64.half_modulus with 9223372036854775808 in L. lia.
Qed.

Theorem s64_high : stmt_s64_high.
Proof.
  intros x H. unfold s64, u64 in *. unfold Int64.signed.
  destruct (zlt (Int64.unsigned x) Int64.half_modulus) as [L|L].
  - change Int64.half_modulus with 9223372036854775808 in L. lia.
  - reflexivity.
Qed.

Theorem zdiv_zmod : stmt_zdiv_zmod.
Proof.
  intros a b H. unfold zdiv, zmod. split.
  - apply Z.div_mod. lia.
  - apply Z.mod_pos_bound. lia.
Qed.

Theorem pow2_zero : stmt_pow2_zero.
Proof. reflexivity. Qed.

Theorem pow2_succ : stmt_pow2_succ.
Proof. intros k H. unfold pow2. rewrite Z.pow_add_r by lia. ring. Qed.

Ltac bits :=
  intros a b k Ha Hb Hk; unfold zmod, zdiv, pow2, land, lor, lxor;
  rewrite <- !Z.testbit_spec' by lia;
  rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec;
  destruct (Z.testbit a k), (Z.testbit b k); reflexivity.

Theorem land_bits : stmt_land_bits.
Proof. bits. Qed.

Theorem lor_bits : stmt_lor_bits.
Proof. bits. Qed.

Theorem lxor_bits : stmt_lxor_bits.
Proof. bits. Qed.

Theorem land_nonneg : stmt_land_nonneg.
Proof. intros a b Ha Hb. apply Z.land_nonneg. auto. Qed.

Theorem lor_nonneg : stmt_lor_nonneg.
Proof. intros a b Ha Hb. apply Z.lor_nonneg. auto. Qed.

Theorem lxor_nonneg : stmt_lxor_nonneg.
Proof. intros a b Ha Hb. apply Z.lxor_nonneg. tauto. Qed.

(** * Shapes of values *)

Notation tulong := (Tlong Unsigned (mk_attr false None)).
Notation tlong := (Tlong Signed (mk_attr false None)).
Notation tuint := (Tint I32 Unsigned (mk_attr false None)).
Notation tint := (Tint I32 Signed (mk_attr false None)).
Notation tuchar := (Tint I8 Unsigned (mk_attr false None)).
Notation tvuint := (Tint I32 Unsigned (mk_attr true None)).
Notation tvuchar := (Tint I8 Unsigned (mk_attr true None)).

Definition on_longs (f: int64 -> int64 -> option val) (v1 v2: val) : option val :=
  match v1, v2 with Vlong x, Vlong y => f x y | _, _ => None end.

Definition on_ints (f: int -> int -> option val) (v1 v2: val) : option val :=
  match v1, v2 with Vint x, Vint y => f x y | _, _ => None end.

Definition on_long {A: Type} (f: int64 -> option A) (v: val) : option A :=
  match v with Vlong x => f x | _ => None end.

Definition on_int {A: Type} (f: int -> option A) (v: val) : option A :=
  match v with Vint x => f x | _ => None end.

Definition pass_long (v: val) : option val :=
  match v with Vlong x => Some (Vlong x) | Vptr b o => Some (Vptr b o) | _ => None end.

Lemma on_longs_some : forall f v1 v2 v,
  on_longs f v1 v2 = Some v <-> exists x y, v1 = Vlong x /\ v2 = Vlong y /\ f x y = Some v.
Proof.
  intros. destruct v1, v2; simpl; split; intros H;
  try discriminate; try (destruct H as (x & y & A & B & C); discriminate); eauto.
  destruct H as (x & y & A & B & C). inv A. inv B. auto.
Qed.

Lemma on_ints_some : forall f v1 v2 v,
  on_ints f v1 v2 = Some v <-> exists x y, v1 = Vint x /\ v2 = Vint y /\ f x y = Some v.
Proof.
  intros. destruct v1, v2; simpl; split; intros H;
  try discriminate; try (destruct H as (x & y & A & B & C); discriminate); eauto.
  destruct H as (x & y & A & B & C). inv A. inv B. auto.
Qed.

Lemma on_long_some : forall A (f: int64 -> option A) v r,
  on_long f v = Some r <-> exists x, v = Vlong x /\ f x = Some r.
Proof.
  intros. destruct v; simpl; split; intros H;
  try discriminate; try (destruct H as (x & B & C); discriminate); eauto.
  destruct H as (x & B & C). inv B. auto.
Qed.

Lemma on_int_some : forall A (f: int -> option A) v r,
  on_int f v = Some r <-> exists x, v = Vint x /\ f x = Some r.
Proof.
  intros. destruct v; simpl; split; intros H;
  try discriminate; try (destruct H as (x & B & C); discriminate); eauto.
  destruct H as (x & B & C). inv B. auto.
Qed.

(** * Words *)

Lemma long_eq_zero : forall y, Int64.eq y Int64.zero = true <-> u64 y = 0.
Proof.
  intros. unfold Int64.eq, u64. rewrite Int64.unsigned_zero.
  destruct (zeq (Int64.unsigned y) 0); split; congruence.
Qed.

Lemma long_ltu_64 : forall y, Int64.ltu y Int64.iwordsize = true <-> u64 y < 64.
Proof.
  intros. unfold Int64.ltu, u64. change (Int64.unsigned Int64.iwordsize) with 64.
  destruct (zlt (Int64.unsigned y) 64); split; congruence || lia.
Qed.

Lemma int_ltu_32 : forall y, Int.ltu y Int.iwordsize = true <-> u32 y < 32.
Proof.
  intros. unfold Int.ltu, u32. change (Int.unsigned Int.iwordsize) with 32.
  destruct (zlt (Int.unsigned y) 32); split; congruence || lia.
Qed.

Lemma int_eq_zero : forall y, Int.eq y Int.zero = true <-> u32 y = 0.
Proof.
  intros. unfold Int.eq, u32. rewrite Int.unsigned_zero.
  destruct (zeq (Int.unsigned y) 0); split; congruence.
Qed.

Lemma long_shl : forall x y,
  Int64.shl x y = r64 (u64 x * pow2 (u64 y)).
Proof.
  intros. unfold Int64.shl, r64, u64, pow2.
  rewrite Z.shiftl_mul_pow2 by (apply Int64.unsigned_range). reflexivity.
Qed.

Lemma long_shru : forall x y,
  Int64.shru x y = r64 (zdiv (u64 x) (pow2 (u64 y))).
Proof.
  intros. unfold Int64.shru, r64, u64, pow2, zdiv.
  rewrite Z.shiftr_div_pow2 by (apply Int64.unsigned_range). reflexivity.
Qed.

Lemma long_shr : forall x y,
  Int64.shr x y = r64 (zdiv (s64 x) (pow2 (u64 y))).
Proof.
  intros. unfold Int64.shr, r64, s64, u64, pow2, zdiv.
  rewrite Z.shiftr_div_pow2 by (apply Int64.unsigned_range). reflexivity.
Qed.

Lemma int_shl : forall x y, Int.shl x y = r32 (u32 x * pow2 (u32 y)).
Proof.
  intros. unfold Int.shl, r32, u32, pow2.
  rewrite Z.shiftl_mul_pow2 by (apply Int.unsigned_range). reflexivity.
Qed.

Lemma int_shru : forall x y, Int.shru x y = r32 (zdiv (u32 x) (pow2 (u32 y))).
Proof.
  intros. unfold Int.shru, r32, u32, pow2, zdiv.
  rewrite Z.shiftr_div_pow2 by (apply Int.unsigned_range). reflexivity.
Qed.

Lemma zero_ext8 : forall x, Int.zero_ext 8 x = r32 (zmod (u32 x) 256).
Proof.
  intros. unfold Int.zero_ext, r32, zmod, u32.
  rewrite Zbits.Zzero_ext_mod by lia. reflexivity.
Qed.

Lemma zero_ext8_long : forall x,
  Int.zero_ext 8 (Int.repr (Int64.unsigned x)) = r32 (zmod (u64 x) 256).
Proof.
  intros. rewrite zero_ext8. unfold r32, zmod, u32, u64. f_equal.
  rewrite Int.unsigned_repr_eq. symmetry. apply Zmod_div_mod; try lia.
  - reflexivity.
  - exists 16777216. reflexivity.
Qed.

(** * Comparisons *)

Ltac compare :=
  unfold Int64.cmpu, Int64.cmp, Int.cmpu, Int64.ltu, Int64.lt, Int64.eq, Int.ltu, Int.eq,
    u64, u32, s64 in *;
  repeat match goal with
    | H: context [zlt ?a ?b] |- _ => destruct (zlt a b)
    | H: context [zeq ?a ?b] |- _ => destruct (zeq a b)
    | |- context [zlt ?a ?b] => destruct (zlt a b)
    | |- context [zeq ?a ?b] => destruct (zeq a b)
    end;
  simpl in *; first [reflexivity | discriminate | lia | exfalso; lia].

(** * Operators on unsigned long *)

Lemma eq_add_ul_ul : forall ce v1 v2 m,
  sem_binop ce Oadd v1 tulong v2 tulong m =
  on_longs (fun x y => Some (Vlong (Int64.add x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem add_ul_ul : stmt_add_ul_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_add_ul_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    inv H. apply bo_add_ul.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity.
Qed.

Lemma eq_sub_ul_ul : forall ce v1 v2 m,
  sem_binop ce Osub v1 tulong v2 tulong m =
  on_longs (fun x y => Some (Vlong (Int64.sub x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem sub_ul_ul : stmt_sub_ul_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_sub_ul_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    inv H. apply bo_sub_ul.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity.
Qed.

Lemma eq_mul_ul_ul : forall ce v1 v2 m,
  sem_binop ce Omul v1 tulong v2 tulong m =
  on_longs (fun x y => Some (Vlong (Int64.mul x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem mul_ul_ul : stmt_mul_ul_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_mul_ul_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    inv H. apply bo_mul_ul.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity.
Qed.

Lemma eq_and_ul_ul : forall ce v1 v2 m,
  sem_binop ce Oand v1 tulong v2 tulong m =
  on_longs (fun x y => Some (Vlong (Int64.and x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem and_ul_ul : stmt_and_ul_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_and_ul_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    inv H. apply bo_and_ul.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity.
Qed.

Lemma eq_or_ul_ul : forall ce v1 v2 m,
  sem_binop ce Oor v1 tulong v2 tulong m =
  on_longs (fun x y => Some (Vlong (Int64.or x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem or_ul_ul : stmt_or_ul_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_or_ul_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    inv H. apply bo_or_ul.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity.
Qed.

Lemma eq_xor_ul_ul : forall ce v1 v2 m,
  sem_binop ce Oxor v1 tulong v2 tulong m =
  on_longs (fun x y => Some (Vlong (Int64.xor x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem xor_ul_ul : stmt_xor_ul_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_xor_ul_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    inv H. apply bo_xor_ul.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity.
Qed.

Lemma eq_div_ul_ul : forall ce v1 v2 m,
  sem_binop ce Odiv v1 tulong v2 tulong m =
  on_longs (fun x y => if Int64.eq y Int64.zero then None else Some (Vlong (Int64.divu x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem div_ul_ul : stmt_div_ul_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_div_ul_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    destruct (Int64.eq y Int64.zero) eqn:E; inv H.
    apply bo_div_ul. rewrite <- long_eq_zero. congruence.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity.
    destruct (Int64.eq _ Int64.zero) eqn:E; [apply long_eq_zero in E; contradiction | reflexivity].
Qed.

Lemma eq_mod_ul_ul : forall ce v1 v2 m,
  sem_binop ce Omod v1 tulong v2 tulong m =
  on_longs (fun x y => if Int64.eq y Int64.zero then None else Some (Vlong (Int64.modu x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem mod_ul_ul : stmt_mod_ul_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_mod_ul_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    destruct (Int64.eq y Int64.zero) eqn:E; inv H.
    apply bo_mod_ul. rewrite <- long_eq_zero. congruence.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity.
    destruct (Int64.eq _ Int64.zero) eqn:E; [apply long_eq_zero in E; contradiction | reflexivity].
Qed.

Lemma eq_shl_ul_ul : forall ce v1 v2 m,
  sem_binop ce Oshl v1 tulong v2 tulong m =
  on_longs (fun x y => if Int64.ltu y Int64.iwordsize then Some (Vlong (Int64.shl x y)) else None) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem shl_ul_ul : stmt_shl_ul_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_shl_ul_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    destruct (Int64.ltu y Int64.iwordsize) eqn:E; inv H.
    rewrite long_shl. apply bo_shl_ul. apply long_ltu_64; auto.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity.
    rewrite (proj2 (long_ltu_64 _)) by auto. rewrite long_shl. reflexivity.
Qed.

Lemma eq_shr_ul_ul : forall ce v1 v2 m,
  sem_binop ce Oshr v1 tulong v2 tulong m =
  on_longs (fun x y => if Int64.ltu y Int64.iwordsize then Some (Vlong (Int64.shru x y)) else None) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem shr_ul_ul : stmt_shr_ul_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_shr_ul_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    destruct (Int64.ltu y Int64.iwordsize) eqn:E; inv H.
    rewrite long_shru. apply bo_shr_ul. apply long_ltu_64; auto.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity.
    rewrite (proj2 (long_ltu_64 _)) by auto. rewrite long_shru. reflexivity.
Qed.

Lemma eq_eq_ul_ul : forall ce v1 v2 m,
  sem_binop ce Oeq v1 tulong v2 tulong m =
  on_longs (fun x y => Some (Val.of_bool (Int64.cmpu Ceq x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem eq_ul_ul : stmt_eq_ul_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_eq_ul_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    inv H. match goal with |- context [Val.of_bool ?b] => destruct b eqn:E end;
      [apply bo_eq_ul_1 | apply bo_eq_ul_0]; compare.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity; compare.
Qed.

Lemma eq_ne_ul_ul : forall ce v1 v2 m,
  sem_binop ce One v1 tulong v2 tulong m =
  on_longs (fun x y => Some (Val.of_bool (Int64.cmpu Cne x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem ne_ul_ul : stmt_ne_ul_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_ne_ul_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    inv H. match goal with |- context [Val.of_bool ?b] => destruct b eqn:E end;
      [apply bo_ne_ul_1 | apply bo_ne_ul_0]; compare.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity; compare.
Qed.

Lemma eq_lt_ul_ul : forall ce v1 v2 m,
  sem_binop ce Olt v1 tulong v2 tulong m =
  on_longs (fun x y => Some (Val.of_bool (Int64.cmpu Clt x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem lt_ul_ul : stmt_lt_ul_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_lt_ul_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    inv H. match goal with |- context [Val.of_bool ?b] => destruct b eqn:E end;
      [apply bo_lt_ul_1 | apply bo_lt_ul_0]; compare.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity; compare.
Qed.

Lemma eq_le_ul_ul : forall ce v1 v2 m,
  sem_binop ce Ole v1 tulong v2 tulong m =
  on_longs (fun x y => Some (Val.of_bool (Int64.cmpu Cle x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem le_ul_ul : stmt_le_ul_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_le_ul_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    inv H. match goal with |- context [Val.of_bool ?b] => destruct b eqn:E end;
      [apply bo_le_ul_1 | apply bo_le_ul_0]; compare.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity; compare.
Qed.

Lemma eq_gt_ul_ul : forall ce v1 v2 m,
  sem_binop ce Ogt v1 tulong v2 tulong m =
  on_longs (fun x y => Some (Val.of_bool (Int64.cmpu Cgt x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem gt_ul_ul : stmt_gt_ul_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_gt_ul_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    inv H. match goal with |- context [Val.of_bool ?b] => destruct b eqn:E end;
      [apply bo_gt_ul_1 | apply bo_gt_ul_0]; compare.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity; compare.
Qed.

Lemma eq_ge_ul_ul : forall ce v1 v2 m,
  sem_binop ce Oge v1 tulong v2 tulong m =
  on_longs (fun x y => Some (Val.of_bool (Int64.cmpu Cge x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem ge_ul_ul : stmt_ge_ul_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_ge_ul_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    inv H. match goal with |- context [Val.of_bool ?b] => destruct b eqn:E end;
      [apply bo_ge_ul_1 | apply bo_ge_ul_0]; compare.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity; compare.
Qed.

(** * Operators on long *)

Lemma eq_lt_sl_sl : forall ce v1 v2 m,
  sem_binop ce Olt v1 tlong v2 tlong m =
  on_longs (fun x y => Some (Val.of_bool (Int64.cmp Clt x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem lt_sl_sl : stmt_lt_sl_sl.
Proof.
  intros ce v1 v2 v m. rewrite eq_lt_sl_sl, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    inv H. match goal with |- context [Val.of_bool ?b] => destruct b eqn:E end;
      [apply bo_lt_sl_1 | apply bo_lt_sl_0]; compare.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity; compare.
Qed.

Lemma eq_le_sl_sl : forall ce v1 v2 m,
  sem_binop ce Ole v1 tlong v2 tlong m =
  on_longs (fun x y => Some (Val.of_bool (Int64.cmp Cle x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem le_sl_sl : stmt_le_sl_sl.
Proof.
  intros ce v1 v2 v m. rewrite eq_le_sl_sl, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    inv H. match goal with |- context [Val.of_bool ?b] => destruct b eqn:E end;
      [apply bo_le_sl_1 | apply bo_le_sl_0]; compare.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity; compare.
Qed.

Lemma eq_shr_sl_ul : forall ce v1 v2 m,
  sem_binop ce Oshr v1 tlong v2 tulong m =
  on_longs (fun x y => if Int64.ltu y Int64.iwordsize then Some (Vlong (Int64.shr x y)) else None) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem shr_sl_ul : stmt_shr_sl_ul.
Proof.
  intros ce v1 v2 v m. rewrite eq_shr_sl_ul, on_longs_some. split.
  - intros (x & y & -> & -> & H).
    destruct (Int64.ltu y Int64.iwordsize) eqn:E; inv H.
    rewrite long_shr. apply bo_shr_sl_ul. apply long_ltu_64; auto.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity.
    rewrite (proj2 (long_ltu_64 _)) by auto. rewrite long_shr. reflexivity.
Qed.

(** * Operators on unsigned int *)

Lemma eq_add_ui_ui : forall ce v1 v2 m,
  sem_binop ce Oadd v1 tuint v2 tuint m =
  on_ints (fun x y => Some (Vint (Int.add x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem add_ui_ui : stmt_add_ui_ui.
Proof.
  intros ce v1 v2 v m. rewrite eq_add_ui_ui, on_ints_some. split.
  - intros (x & y & -> & -> & H).
    inv H. apply bo_add_ui.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity.
Qed.

Lemma eq_sub_ui_ui : forall ce v1 v2 m,
  sem_binop ce Osub v1 tuint v2 tuint m =
  on_ints (fun x y => Some (Vint (Int.sub x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem sub_ui_ui : stmt_sub_ui_ui.
Proof.
  intros ce v1 v2 v m. rewrite eq_sub_ui_ui, on_ints_some. split.
  - intros (x & y & -> & -> & H).
    inv H. apply bo_sub_ui.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity.
Qed.

Lemma eq_and_ui_ui : forall ce v1 v2 m,
  sem_binop ce Oand v1 tuint v2 tuint m =
  on_ints (fun x y => Some (Vint (Int.and x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem and_ui_ui : stmt_and_ui_ui.
Proof.
  intros ce v1 v2 v m. rewrite eq_and_ui_ui, on_ints_some. split.
  - intros (x & y & -> & -> & H).
    inv H. apply bo_and_ui.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity.
Qed.

Lemma eq_shl_ui_ui : forall ce v1 v2 m,
  sem_binop ce Oshl v1 tuint v2 tuint m =
  on_ints (fun x y => if Int.ltu y Int.iwordsize then Some (Vint (Int.shl x y)) else None) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem shl_ui_ui : stmt_shl_ui_ui.
Proof.
  intros ce v1 v2 v m. rewrite eq_shl_ui_ui, on_ints_some. split.
  - intros (x & y & -> & -> & H).
    destruct (Int.ltu y Int.iwordsize) eqn:E; inv H.
    rewrite int_shl. apply bo_shl_ui. apply int_ltu_32; auto.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity.
    rewrite (proj2 (int_ltu_32 _)) by auto. rewrite int_shl. reflexivity.
Qed.

Lemma eq_shr_ui_ui : forall ce v1 v2 m,
  sem_binop ce Oshr v1 tuint v2 tuint m =
  on_ints (fun x y => if Int.ltu y Int.iwordsize then Some (Vint (Int.shru x y)) else None) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem shr_ui_ui : stmt_shr_ui_ui.
Proof.
  intros ce v1 v2 v m. rewrite eq_shr_ui_ui, on_ints_some. split.
  - intros (x & y & -> & -> & H).
    destruct (Int.ltu y Int.iwordsize) eqn:E; inv H.
    rewrite int_shru. apply bo_shr_ui. apply int_ltu_32; auto.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity.
    rewrite (proj2 (int_ltu_32 _)) by auto. rewrite int_shru. reflexivity.
Qed.

Lemma eq_eq_ui_ui : forall ce v1 v2 m,
  sem_binop ce Oeq v1 tuint v2 tuint m =
  on_ints (fun x y => Some (Val.of_bool (Int.cmpu Ceq x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem eq_ui_ui : stmt_eq_ui_ui.
Proof.
  intros ce v1 v2 v m. rewrite eq_eq_ui_ui, on_ints_some. split.
  - intros (x & y & -> & -> & H).
    inv H. match goal with |- context [Val.of_bool ?b] => destruct b eqn:E end;
      [apply bo_eq_ui_1 | apply bo_eq_ui_0]; compare.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity; compare.
Qed.

Lemma eq_ne_ui_ui : forall ce v1 v2 m,
  sem_binop ce One v1 tuint v2 tuint m =
  on_ints (fun x y => Some (Val.of_bool (Int.cmpu Cne x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem ne_ui_ui : stmt_ne_ui_ui.
Proof.
  intros ce v1 v2 v m. rewrite eq_ne_ui_ui, on_ints_some. split.
  - intros (x & y & -> & -> & H).
    inv H. match goal with |- context [Val.of_bool ?b] => destruct b eqn:E end;
      [apply bo_ne_ui_1 | apply bo_ne_ui_0]; compare.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity; compare.
Qed.

Lemma eq_lt_ui_ui : forall ce v1 v2 m,
  sem_binop ce Olt v1 tuint v2 tuint m =
  on_ints (fun x y => Some (Val.of_bool (Int.cmpu Clt x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem lt_ui_ui : stmt_lt_ui_ui.
Proof.
  intros ce v1 v2 v m. rewrite eq_lt_ui_ui, on_ints_some. split.
  - intros (x & y & -> & -> & H).
    inv H. match goal with |- context [Val.of_bool ?b] => destruct b eqn:E end;
      [apply bo_lt_ui_1 | apply bo_lt_ui_0]; compare.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity; compare.
Qed.

Lemma eq_gt_ui_ui : forall ce v1 v2 m,
  sem_binop ce Ogt v1 tuint v2 tuint m =
  on_ints (fun x y => Some (Val.of_bool (Int.cmpu Cgt x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem gt_ui_ui : stmt_gt_ui_ui.
Proof.
  intros ce v1 v2 v m. rewrite eq_gt_ui_ui, on_ints_some. split.
  - intros (x & y & -> & -> & H).
    inv H. match goal with |- context [Val.of_bool ?b] => destruct b eqn:E end;
      [apply bo_gt_ui_1 | apply bo_gt_ui_0]; compare.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity; compare.
Qed.

Lemma eq_ge_ui_ui : forall ce v1 v2 m,
  sem_binop ce Oge v1 tuint v2 tuint m =
  on_ints (fun x y => Some (Val.of_bool (Int.cmpu Cge x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem ge_ui_ui : stmt_ge_ui_ui.
Proof.
  intros ce v1 v2 v m. rewrite eq_ge_ui_ui, on_ints_some. split.
  - intros (x & y & -> & -> & H).
    inv H. match goal with |- context [Val.of_bool ?b] => destruct b eqn:E end;
      [apply bo_ge_ui_1 | apply bo_ge_ui_0]; compare.
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity; compare.
Qed.

(** * Casts *)

Lemma eq_cast_si_ui : forall v1 m,
  sem_cast v1 tint tuint m = on_int (fun x => Some (Vint x)) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_si_ui : stmt_cast_si_ui.
Proof.
  intros v1 v m. rewrite eq_cast_si_ui, on_int_some. split.
  - intros (x & -> & H). inv H. apply co_si_ui.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_ui_si : forall v1 m,
  sem_cast v1 tuint tint m = on_int (fun x => Some (Vint x)) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_ui_si : stmt_cast_ui_si.
Proof.
  intros v1 v m. rewrite eq_cast_ui_si, on_int_some. split.
  - intros (x & -> & H). inv H. apply co_ui_si.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_ul_ui : forall v1 m,
  sem_cast v1 tulong tuint m = on_long (fun x => Some (Vint (r32 (u64 x)))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_ul_ui : stmt_cast_ul_ui.
Proof.
  intros v1 v m. rewrite eq_cast_ul_ui, on_long_some. split.
  - intros (x & -> & H). inv H. apply co_ul_ui.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_ui_ul : forall v1 m,
  sem_cast v1 tuint tulong m = on_int (fun x => Some (Vlong (r64 (u32 x)))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_ui_ul : stmt_cast_ui_ul.
Proof.
  intros v1 v m. rewrite eq_cast_ui_ul, on_int_some. split.
  - intros (x & -> & H). inv H. apply co_ui_ul.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_ul_sl : forall v1 m,
  sem_cast v1 tulong tlong m = pass_long v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_ul_sl : stmt_cast_ul_sl.
Proof.
  intros v1 v m. rewrite eq_cast_ul_sl. split.
  - intros H. destruct v1; inv H; [apply co_ul_sl | apply co_ul_sl_ptr].
  - intros H. inv H; reflexivity.
Qed.

Lemma eq_cast_sl_ul : forall v1 m,
  sem_cast v1 tlong tulong m = pass_long v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_sl_ul : stmt_cast_sl_ul.
Proof.
  intros v1 v m. rewrite eq_cast_sl_ul. split.
  - intros H. destruct v1; inv H; [apply co_sl_ul | apply co_sl_ul_ptr].
  - intros H. inv H; reflexivity.
Qed.

Lemma eq_cast_uc_ul : forall v1 m,
  sem_cast v1 tuchar tulong m = on_int (fun x => Some (Vlong (r64 (u32 x)))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_uc_ul : stmt_cast_uc_ul.
Proof.
  intros v1 v m. rewrite eq_cast_uc_ul, on_int_some. split.
  - intros (x & -> & H). inv H. apply co_uc_ul.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_uc_ui : forall v1 m,
  sem_cast v1 tuchar tuint m = on_int (fun x => Some (Vint x)) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_uc_ui : stmt_cast_uc_ui.
Proof.
  intros v1 v m. rewrite eq_cast_uc_ui, on_int_some. split.
  - intros (x & -> & H). inv H. apply co_uc_ui.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_ul_uc : forall v1 m,
  sem_cast v1 tulong tuchar m = on_long (fun x => Some (Vint (Int.zero_ext 8 (Int.repr (Int64.unsigned x))))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_ul_uc : stmt_cast_ul_uc.
Proof.
  intros v1 v m. rewrite eq_cast_ul_uc, on_long_some. split.
  - intros (x & -> & H). inv H. rewrite zero_ext8_long. apply co_ul_uc.
  - intros H. inv H. eexists. split; [reflexivity|]. rewrite zero_ext8_long. reflexivity.
Qed.

Lemma eq_cast_ui_uc : forall v1 m,
  sem_cast v1 tuint tuchar m = on_int (fun x => Some (Vint (Int.zero_ext 8 x))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_ui_uc : stmt_cast_ui_uc.
Proof.
  intros v1 v m. rewrite eq_cast_ui_uc, on_int_some. split.
  - intros (x & -> & H). inv H. rewrite zero_ext8. apply co_ui_uc.
  - intros H. inv H. eexists. split; [reflexivity|]. rewrite zero_ext8. reflexivity.
Qed.

Lemma eq_cast_vuc_ul : forall v1 m,
  sem_cast v1 tvuchar tulong m = on_int (fun x => Some (Vlong (r64 (u32 x)))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_vuc_ul : stmt_cast_vuc_ul.
Proof.
  intros v1 v m. rewrite eq_cast_vuc_ul, on_int_some. split.
  - intros (x & -> & H). inv H. apply co_vuc_ul.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_vui_ul : forall v1 m,
  sem_cast v1 tvuint tulong m = on_int (fun x => Some (Vlong (r64 (u32 x)))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_vui_ul : stmt_cast_vui_ul.
Proof.
  intros v1 v m. rewrite eq_cast_vui_ul, on_int_some. split.
  - intros (x & -> & H). inv H. apply co_vui_ul.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_ui_vui : forall v1 m,
  sem_cast v1 tuint tvuint m = on_int (fun x => Some (Vint x)) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_ui_vui : stmt_cast_ui_vui.
Proof.
  intros v1 v m. rewrite eq_cast_ui_vui, on_int_some. split.
  - intros (x & -> & H). inv H. apply co_ui_vui.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_ul_ul : forall v1 m,
  sem_cast v1 tulong tulong m = pass_long v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_ul_ul : stmt_cast_ul_ul.
Proof.
  intros v1 v m. rewrite eq_cast_ul_ul. split.
  - intros H. destruct v1; inv H; [apply co_ul_ul | apply co_ul_ul_ptr].
  - intros H. inv H; reflexivity.
Qed.

Lemma eq_cast_ui_ui : forall v1 m,
  sem_cast v1 tuint tuint m = on_int (fun x => Some (Vint x)) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_ui_ui : stmt_cast_ui_ui.
Proof.
  intros v1 v m. rewrite eq_cast_ui_ui, on_int_some. split.
  - intros (x & -> & H). inv H. apply co_ui_ui.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_uc_uc : forall v1 m,
  sem_cast v1 tuchar tuchar m = on_int (fun x => Some (Vint (Int.zero_ext 8 x))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_uc_uc : stmt_cast_uc_uc.
Proof.
  intros v1 v m. rewrite eq_cast_uc_uc, on_int_some. split.
  - intros (x & -> & H). inv H. rewrite zero_ext8. apply co_uc_uc.
  - intros H. inv H. eexists. split; [reflexivity|]. rewrite zero_ext8. reflexivity.
Qed.

Lemma eq_cast_si_si : forall v1 m,
  sem_cast v1 tint tint m = on_int (fun x => Some (Vint x)) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_si_si : stmt_cast_si_si.
Proof.
  intros v1 v m. rewrite eq_cast_si_si, on_int_some. split.
  - intros (x & -> & H). inv H. apply co_si_si.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

(** * Floating-point numbers *)

Notation tdbl := (Tfloat F64 (mk_attr false None)).
Notation tflt := (Tfloat F32 (mk_attr false None)).

Definition on_floats (f: float -> float -> option val) (v1 v2: val) : option val :=
  match v1, v2 with Vfloat x, Vfloat y => f x y | _, _ => None end.

Definition on_singles (f: float32 -> float32 -> option val) (v1 v2: val) : option val :=
  match v1, v2 with Vsingle x, Vsingle y => f x y | _, _ => None end.

Definition on_float (f: float -> option val) (v: val) : option val :=
  match v with Vfloat x => f x | _ => None end.

Definition on_single (f: float32 -> option val) (v: val) : option val :=
  match v with Vsingle x => f x | _ => None end.

Lemma on_floats_some : forall f v1 v2 v,
  on_floats f v1 v2 = Some v <-> exists x y, v1 = Vfloat x /\ v2 = Vfloat y /\ f x y = Some v.
Proof.
  intros. destruct v1, v2; simpl; split; intros H;
  try discriminate; try (destruct H as (x & y & A & B & C); discriminate); eauto.
  destruct H as (x & y & A & B & C). inv A. inv B. auto.
Qed.

Lemma on_singles_some : forall f v1 v2 v,
  on_singles f v1 v2 = Some v <->
  exists x y, v1 = Vsingle x /\ v2 = Vsingle y /\ f x y = Some v.
Proof.
  intros. destruct v1, v2; simpl; split; intros H;
  try discriminate; try (destruct H as (x & y & A & B & C); discriminate); eauto.
  destruct H as (x & y & A & B & C). inv A. inv B. auto.
Qed.

Lemma on_float_some : forall f v r,
  on_float f v = Some r <-> exists x, v = Vfloat x /\ f x = Some r.
Proof.
  intros. destruct v; simpl; split; intros H;
  try discriminate; try (destruct H as (x & B & C); discriminate); eauto.
  destruct H as (x & B & C). inv B. auto.
Qed.

Lemma on_single_some : forall f v r,
  on_single f v = Some r <-> exists x, v = Vsingle x /\ f x = Some r.
Proof.
  intros. destruct v; simpl; split; intros H;
  try discriminate; try (destruct H as (x & B & C); discriminate); eauto.
  destruct H as (x & B & C). inv B. auto.
Qed.

(** A partial conversion's value, as [sem_cast] gives it. *)
Lemma conv_some : forall A (o: option A) (mk: A -> val) v,
  match o with Some i => Some (mk i) | None => None end = Some v <->
  exists y, o = Some y /\ v = mk y.
Proof.
  intros. destruct o; split; intros H.
  - inv H. eauto.
  - destruct H as (y & E & ->). inv E. reflexivity.
  - discriminate.
  - destruct H as (y & E & _). discriminate.
Qed.

(** ** Operators on double *)

Lemma eq_add_d_d : forall ce v1 v2 m,
  sem_binop ce Oadd v1 tdbl v2 tdbl m = on_floats (fun x y => Some (Vfloat (Float.add x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem add_d_d : stmt_add_d_d.
Proof.
  intros ce v1 v2 v m. rewrite eq_add_d_d, on_floats_some. split.
  - intros (x & y & -> & -> & H). inv H. apply bo_add_d.
  - intros H. inv H. do 2 eexists. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma eq_sub_d_d : forall ce v1 v2 m,
  sem_binop ce Osub v1 tdbl v2 tdbl m = on_floats (fun x y => Some (Vfloat (Float.sub x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem sub_d_d : stmt_sub_d_d.
Proof.
  intros ce v1 v2 v m. rewrite eq_sub_d_d, on_floats_some. split.
  - intros (x & y & -> & -> & H). inv H. apply bo_sub_d.
  - intros H. inv H. do 2 eexists. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma eq_mul_d_d : forall ce v1 v2 m,
  sem_binop ce Omul v1 tdbl v2 tdbl m = on_floats (fun x y => Some (Vfloat (Float.mul x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem mul_d_d : stmt_mul_d_d.
Proof.
  intros ce v1 v2 v m. rewrite eq_mul_d_d, on_floats_some. split.
  - intros (x & y & -> & -> & H). inv H. apply bo_mul_d.
  - intros H. inv H. do 2 eexists. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma eq_div_d_d : forall ce v1 v2 m,
  sem_binop ce Odiv v1 tdbl v2 tdbl m = on_floats (fun x y => Some (Vfloat (Float.div x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem div_d_d : stmt_div_d_d.
Proof.
  intros ce v1 v2 v m. rewrite eq_div_d_d, on_floats_some. split.
  - intros (x & y & -> & -> & H). inv H. apply bo_div_d.
  - intros H. inv H. do 2 eexists. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma eq_eq_d_d : forall ce v1 v2 m,
  sem_binop ce Oeq v1 tdbl v2 tdbl m =
  on_floats (fun x y => Some (Val.of_bool (Float.cmp Ceq x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem eq_d_d : stmt_eq_d_d.
Proof.
  intros ce v1 v2 v m. rewrite eq_eq_d_d, on_floats_some. split.
  - intros (x & y & -> & -> & H). inv H.
    destruct (Float.cmp Ceq x y) eqn:E; [exact (bo_eq_d_1 x y E) | exact (bo_eq_d_0 x y E)].
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity;
    match goal with E: Float.cmp _ _ _ = _ |- _ => rewrite E end; reflexivity.
Qed.

Lemma eq_ne_d_d : forall ce v1 v2 m,
  sem_binop ce One v1 tdbl v2 tdbl m =
  on_floats (fun x y => Some (Val.of_bool (Float.cmp Cne x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem ne_d_d : stmt_ne_d_d.
Proof.
  intros ce v1 v2 v m. rewrite eq_ne_d_d, on_floats_some. split.
  - intros (x & y & -> & -> & H). inv H.
    destruct (Float.cmp Cne x y) eqn:E; [exact (bo_ne_d_1 x y E) | exact (bo_ne_d_0 x y E)].
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity;
    match goal with E: Float.cmp _ _ _ = _ |- _ => rewrite E end; reflexivity.
Qed.

Lemma eq_lt_d_d : forall ce v1 v2 m,
  sem_binop ce Olt v1 tdbl v2 tdbl m =
  on_floats (fun x y => Some (Val.of_bool (Float.cmp Clt x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem lt_d_d : stmt_lt_d_d.
Proof.
  intros ce v1 v2 v m. rewrite eq_lt_d_d, on_floats_some. split.
  - intros (x & y & -> & -> & H). inv H.
    destruct (Float.cmp Clt x y) eqn:E; [exact (bo_lt_d_1 x y E) | exact (bo_lt_d_0 x y E)].
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity;
    match goal with E: Float.cmp _ _ _ = _ |- _ => rewrite E end; reflexivity.
Qed.

Lemma eq_le_d_d : forall ce v1 v2 m,
  sem_binop ce Ole v1 tdbl v2 tdbl m =
  on_floats (fun x y => Some (Val.of_bool (Float.cmp Cle x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem le_d_d : stmt_le_d_d.
Proof.
  intros ce v1 v2 v m. rewrite eq_le_d_d, on_floats_some. split.
  - intros (x & y & -> & -> & H). inv H.
    destruct (Float.cmp Cle x y) eqn:E; [exact (bo_le_d_1 x y E) | exact (bo_le_d_0 x y E)].
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity;
    match goal with E: Float.cmp _ _ _ = _ |- _ => rewrite E end; reflexivity.
Qed.

Lemma eq_ge_d_d : forall ce v1 v2 m,
  sem_binop ce Oge v1 tdbl v2 tdbl m =
  on_floats (fun x y => Some (Val.of_bool (Float.cmp Cge x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem ge_d_d : stmt_ge_d_d.
Proof.
  intros ce v1 v2 v m. rewrite eq_ge_d_d, on_floats_some. split.
  - intros (x & y & -> & -> & H). inv H.
    destruct (Float.cmp Cge x y) eqn:E; [exact (bo_ge_d_1 x y E) | exact (bo_ge_d_0 x y E)].
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity;
    match goal with E: Float.cmp _ _ _ = _ |- _ => rewrite E end; reflexivity.
Qed.

(** ** Operators on float *)

Lemma eq_add_f_f : forall ce v1 v2 m,
  sem_binop ce Oadd v1 tflt v2 tflt m =
  on_singles (fun x y => Some (Vsingle (Float32.add x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem add_f_f : stmt_add_f_f.
Proof.
  intros ce v1 v2 v m. rewrite eq_add_f_f, on_singles_some. split.
  - intros (x & y & -> & -> & H). inv H. apply bo_add_f.
  - intros H. inv H. do 2 eexists. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma eq_sub_f_f : forall ce v1 v2 m,
  sem_binop ce Osub v1 tflt v2 tflt m =
  on_singles (fun x y => Some (Vsingle (Float32.sub x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem sub_f_f : stmt_sub_f_f.
Proof.
  intros ce v1 v2 v m. rewrite eq_sub_f_f, on_singles_some. split.
  - intros (x & y & -> & -> & H). inv H. apply bo_sub_f.
  - intros H. inv H. do 2 eexists. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma eq_mul_f_f : forall ce v1 v2 m,
  sem_binop ce Omul v1 tflt v2 tflt m =
  on_singles (fun x y => Some (Vsingle (Float32.mul x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem mul_f_f : stmt_mul_f_f.
Proof.
  intros ce v1 v2 v m. rewrite eq_mul_f_f, on_singles_some. split.
  - intros (x & y & -> & -> & H). inv H. apply bo_mul_f.
  - intros H. inv H. do 2 eexists. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma eq_div_f_f : forall ce v1 v2 m,
  sem_binop ce Odiv v1 tflt v2 tflt m =
  on_singles (fun x y => Some (Vsingle (Float32.div x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem div_f_f : stmt_div_f_f.
Proof.
  intros ce v1 v2 v m. rewrite eq_div_f_f, on_singles_some. split.
  - intros (x & y & -> & -> & H). inv H. apply bo_div_f.
  - intros H. inv H. do 2 eexists. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma eq_eq_f_f : forall ce v1 v2 m,
  sem_binop ce Oeq v1 tflt v2 tflt m =
  on_singles (fun x y => Some (Val.of_bool (Float32.cmp Ceq x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem eq_f_f : stmt_eq_f_f.
Proof.
  intros ce v1 v2 v m. rewrite eq_eq_f_f, on_singles_some. split.
  - intros (x & y & -> & -> & H). inv H.
    destruct (Float32.cmp Ceq x y) eqn:E;
      [exact (bo_eq_f_1 x y E) | exact (bo_eq_f_0 x y E)].
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity;
    match goal with E: Float32.cmp _ _ _ = _ |- _ => rewrite E end; reflexivity.
Qed.

Lemma eq_ne_f_f : forall ce v1 v2 m,
  sem_binop ce One v1 tflt v2 tflt m =
  on_singles (fun x y => Some (Val.of_bool (Float32.cmp Cne x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem ne_f_f : stmt_ne_f_f.
Proof.
  intros ce v1 v2 v m. rewrite eq_ne_f_f, on_singles_some. split.
  - intros (x & y & -> & -> & H). inv H.
    destruct (Float32.cmp Cne x y) eqn:E;
      [exact (bo_ne_f_1 x y E) | exact (bo_ne_f_0 x y E)].
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity;
    match goal with E: Float32.cmp _ _ _ = _ |- _ => rewrite E end; reflexivity.
Qed.

Lemma eq_lt_f_f : forall ce v1 v2 m,
  sem_binop ce Olt v1 tflt v2 tflt m =
  on_singles (fun x y => Some (Val.of_bool (Float32.cmp Clt x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem lt_f_f : stmt_lt_f_f.
Proof.
  intros ce v1 v2 v m. rewrite eq_lt_f_f, on_singles_some. split.
  - intros (x & y & -> & -> & H). inv H.
    destruct (Float32.cmp Clt x y) eqn:E;
      [exact (bo_lt_f_1 x y E) | exact (bo_lt_f_0 x y E)].
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity;
    match goal with E: Float32.cmp _ _ _ = _ |- _ => rewrite E end; reflexivity.
Qed.

Lemma eq_le_f_f : forall ce v1 v2 m,
  sem_binop ce Ole v1 tflt v2 tflt m =
  on_singles (fun x y => Some (Val.of_bool (Float32.cmp Cle x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem le_f_f : stmt_le_f_f.
Proof.
  intros ce v1 v2 v m. rewrite eq_le_f_f, on_singles_some. split.
  - intros (x & y & -> & -> & H). inv H.
    destruct (Float32.cmp Cle x y) eqn:E;
      [exact (bo_le_f_1 x y E) | exact (bo_le_f_0 x y E)].
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity;
    match goal with E: Float32.cmp _ _ _ = _ |- _ => rewrite E end; reflexivity.
Qed.

Lemma eq_ge_f_f : forall ce v1 v2 m,
  sem_binop ce Oge v1 tflt v2 tflt m =
  on_singles (fun x y => Some (Val.of_bool (Float32.cmp Cge x y))) v1 v2.
Proof. intros. destruct v1, v2; reflexivity. Qed.

Theorem ge_f_f : stmt_ge_f_f.
Proof.
  intros ce v1 v2 v m. rewrite eq_ge_f_f, on_singles_some. split.
  - intros (x & y & -> & -> & H). inv H.
    destruct (Float32.cmp Cge x y) eqn:E;
      [exact (bo_ge_f_1 x y E) | exact (bo_ge_f_0 x y E)].
  - intros H. inv H; do 2 eexists; split; try reflexivity; split; try reflexivity;
    match goal with E: Float32.cmp _ _ _ = _ |- _ => rewrite E end; reflexivity.
Qed.

(** ** Casts of floating-point numbers *)

Lemma eq_cast_d_d : forall v1 m,
  sem_cast v1 tdbl tdbl m =
  on_float (fun x => Some (Vfloat x)) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_d_d : stmt_cast_d_d.
Proof.
  intros v1 v m. rewrite eq_cast_d_d, on_float_some. split.
  - intros (x & -> & H). inv H. apply co_d_d.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_f_f : forall v1 m,
  sem_cast v1 tflt tflt m =
  on_single (fun x => Some (Vsingle x)) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_f_f : stmt_cast_f_f.
Proof.
  intros v1 v m. rewrite eq_cast_f_f, on_single_some. split.
  - intros (x & -> & H). inv H. apply co_f_f.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_ul_d : forall v1 m,
  sem_cast v1 tulong tdbl m =
  on_long (fun x => Some (Vfloat (Float.of_longu x))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_ul_d : stmt_cast_ul_d.
Proof.
  intros v1 v m. rewrite eq_cast_ul_d, on_long_some. split.
  - intros (x & -> & H). inv H. apply co_ul_d.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_f_d : forall v1 m,
  sem_cast v1 tflt tdbl m =
  on_single (fun x => Some (Vfloat (Float.of_single x))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_f_d : stmt_cast_f_d.
Proof.
  intros v1 v m. rewrite eq_cast_f_d, on_single_some. split.
  - intros (x & -> & H). inv H. apply co_f_d.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_d_f : forall v1 m,
  sem_cast v1 tdbl tflt m =
  on_float (fun x => Some (Vsingle (Float.to_single x))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_d_f : stmt_cast_d_f.
Proof.
  intros v1 v m. rewrite eq_cast_d_f, on_float_some. split.
  - intros (x & -> & H). inv H. apply co_d_f.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_si_f : forall v1 m,
  sem_cast v1 tint tflt m =
  on_int (fun x => Some (Vsingle (Float32.of_int x))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_si_f : stmt_cast_si_f.
Proof.
  intros v1 v m. rewrite eq_cast_si_f, on_int_some. split.
  - intros (x & -> & H). inv H. apply co_si_f.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_ui_f : forall v1 m,
  sem_cast v1 tuint tflt m =
  on_int (fun x => Some (Vsingle (Float32.of_intu x))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_ui_f : stmt_cast_ui_f.
Proof.
  intros v1 v m. rewrite eq_cast_ui_f, on_int_some. split.
  - intros (x & -> & H). inv H. apply co_ui_f.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_ul_f : forall v1 m,
  sem_cast v1 tulong tflt m =
  on_long (fun x => Some (Vsingle (Float32.of_longu x))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_ul_f : stmt_cast_ul_f.
Proof.
  intros v1 v m. rewrite eq_cast_ul_f, on_long_some. split.
  - intros (x & -> & H). inv H. apply co_ul_f.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_cast_d_ul : forall v1 m,
  sem_cast v1 tdbl tulong m =
  on_float (fun x => match Float.to_longu x with Some i => Some (Vlong i) | None => None end) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_d_ul : stmt_cast_d_ul.
Proof.
  intros v1 v m. rewrite eq_cast_d_ul, on_float_some. split.
  - intros (x & -> & H). apply conv_some in H. destruct H as (y & E & ->).
    apply co_d_ul; auto.
  - intros H. inv H. eexists. split; [reflexivity|]. apply conv_some. eauto.
Qed.

Lemma eq_cast_f_si : forall v1 m,
  sem_cast v1 tflt tint m =
  on_single (fun x => match Float32.to_int x with Some i => Some (Vint i) | None => None end) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_f_si : stmt_cast_f_si.
Proof.
  intros v1 v m. rewrite eq_cast_f_si, on_single_some. split.
  - intros (x & -> & H). apply conv_some in H. destruct H as (y & E & ->).
    apply co_f_si; auto.
  - intros H. inv H. eexists. split; [reflexivity|]. apply conv_some. eauto.
Qed.

Lemma eq_cast_f_ul : forall v1 m,
  sem_cast v1 tflt tulong m =
  on_single (fun x => match Float32.to_longu x with Some i => Some (Vlong i) | None => None end) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem cast_f_ul : stmt_cast_f_ul.
Proof.
  intros v1 v m. rewrite eq_cast_f_ul, on_single_some. split.
  - intros (x & -> & H). apply conv_some in H. destruct H as (y & E & ->).
    apply co_f_ul; auto.
  - intros H. inv H. eexists. split; [reflexivity|]. apply conv_some. eauto.
Qed.

(** ** Unary operators *)

Lemma eq_neg_d : forall v1 m,
  sem_unop Oneg v1 tdbl m = on_float (fun x => Some (Vfloat (Float.neg x))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem neg_d : stmt_neg_d.
Proof.
  intros v1 v m. rewrite eq_neg_d, on_float_some. split.
  - intros (x & -> & H). inv H. apply uo_neg_d.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_abs_d : forall v1 m,
  sem_unop Oabsfloat v1 tdbl m = on_float (fun x => Some (Vfloat (Float.abs x))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem abs_d : stmt_abs_d.
Proof.
  intros v1 v m. rewrite eq_abs_d, on_float_some. split.
  - intros (x & -> & H). inv H. apply uo_abs_d.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

Lemma eq_neg_f : forall v1 m,
  sem_unop Oneg v1 tflt m = on_single (fun x => Some (Vsingle (Float32.neg x))) v1.
Proof. intros. destruct v1; reflexivity. Qed.

Theorem neg_f : stmt_neg_f.
Proof.
  intros v1 v m. rewrite eq_neg_f, on_single_some. split.
  - intros (x & -> & H). inv H. apply uo_neg_f.
  - intros H. inv H. eexists. split; [reflexivity|]. reflexivity.
Qed.

(** * Conditions *)

Lemma eq_bool_si : forall v m,
  bool_val v tint m = on_int (fun x => Some (negb (Int.eq x Int.zero))) v.
Proof. intros. destruct v; reflexivity. Qed.

Theorem bool_si : stmt_bool_si.
Proof.
  intros v b m. rewrite eq_bool_si, on_int_some. split.
  - intros (x & -> & H). inv H. destruct (Int.eq x Int.zero) eqn:E; simpl.
    + apply bv_si_false. apply int_eq_zero; auto.
    + apply bv_si_true. intros Z. apply int_eq_zero in Z. congruence.
  - intros H. inv H; eexists; split; try reflexivity.
    + destruct (Int.eq _ Int.zero) eqn:E; [apply int_eq_zero in E; contradiction | reflexivity].
    + rewrite (proj2 (int_eq_zero _)) by auto. reflexivity.
Qed.

Lemma eq_bool_ui : forall v m,
  bool_val v tuint m = on_int (fun x => Some (negb (Int.eq x Int.zero))) v.
Proof. intros. destruct v; reflexivity. Qed.

Theorem bool_ui : stmt_bool_ui.
Proof.
  intros v b m. rewrite eq_bool_ui, on_int_some. split.
  - intros (x & -> & H). inv H. destruct (Int.eq x Int.zero) eqn:E; simpl.
    + apply bv_ui_false. apply int_eq_zero; auto.
    + apply bv_ui_true. intros Z. apply int_eq_zero in Z. congruence.
  - intros H. inv H; eexists; split; try reflexivity.
    + destruct (Int.eq _ Int.zero) eqn:E; [apply int_eq_zero in E; contradiction | reflexivity].
    + rewrite (proj2 (int_eq_zero _)) by auto. reflexivity.
Qed.

(** * Constants *)

Theorem const_int : stmt_const_int.
Proof.
  intros ge e le m i ty v. unfold eval_expr. split.
  - intros H. inv H; [reflexivity |].
    match goal with H: Clight.eval_lvalue _ _ _ _ _ _ _ _ |- _ => inv H end.
  - intros ->. constructor.
Qed.

Theorem const_long : stmt_const_long.
Proof.
  intros ge e le m i ty v. unfold eval_expr. split.
  - intros H. inv H; [reflexivity |].
    match goal with H: Clight.eval_lvalue _ _ _ _ _ _ _ _ |- _ => inv H end.
  - intros ->. constructor.
Qed.


(** * Laws of pointer offsets, traces, and floating-point bits *)

Theorem uptr_range : stmt_uptr_range.
Proof.
  intros x. pose proof (Ptrofs.unsigned_range x). unfold uptr.
  change Ptrofs.modulus with 18446744073709551616 in H. lia.
Qed.

Theorem uptr_rptr : stmt_uptr_rptr.
Proof.
  intros z. unfold uptr, rptr, zmod. rewrite Ptrofs.unsigned_repr_eq. reflexivity.
Qed.

Theorem rptr_uptr : stmt_rptr_uptr.
Proof. intros x. apply Ptrofs.repr_unsigned. Qed.

Theorem app_nil : stmt_app_nil.
Proof. intros t. reflexivity. Qed.

Theorem app_cons : stmt_app_cons.
Proof. intros e t1 t2. reflexivity. Qed.

Theorem f64_bits_of_bits : stmt_f64_bits_of_bits.
Proof. intros x. apply Float.to_of_bits. Qed.

Theorem f64_of_bits_bits : stmt_f64_of_bits_bits.
Proof. intros f. apply Float.of_to_bits. Qed.

Theorem f32_bits_of_bits : stmt_f32_bits_of_bits.
Proof. intros x. apply Float32.to_of_bits. Qed.

Theorem f32_of_bits_bits : stmt_f32_of_bits_bits.
Proof. intros f. apply Float32.of_to_bits. Qed.
