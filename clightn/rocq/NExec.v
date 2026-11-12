(* The soundness of the reference semantics N (clightn/N.nsx) for CompCert 3.18's Clight with
   parameters as temporaries: every derivation of N's statement relation, from temporaries and
   a memory related to N's, is a derivation of Clight2.exec_stmt.  nprog_sound carries N's
   program judgment to Clight2.bigstep_program_terminates, nreacts_sound carries N's judgment of
   a main that runs forever to loop_reacts of Clight2Asm.v, and nreads_reads carries N's reads
   to reads of Clight2Asm.v.  N's scalar globals are related to the memory by their values at
   offset 0, and N's bytes of an array to the bytes of its block.  The leaf relations are sound
   by the statements of NProof.v.  The proofs need Archi.ptr64 = true, which holds on AArch64. *)
From Coq Require Import ZArith Lia.
Require Import Coqlib Maps Integers Floats Values AST Memdata Memory Events Globalenvs.
Require Import Ctypes Cop Clight ClightBigstep.
Require Builtins0 Builtins NBase Clight2Asm.
Require Import NSpec NProof.

Local Open Scope Z_scope.
Local Transparent Archi.ptr64 Archi.big_endian Mem.load Mem.loadbytes.

(** * Leaf relations *)

Ltac binop_leaf H ce m :=
  first [ exact (proj2 (add_ul_ul ce _ _ _ m) H) | exact (proj2 (sub_ul_ul ce _ _ _ m) H)
        | exact (proj2 (mul_ul_ul ce _ _ _ m) H) | exact (proj2 (div_ul_ul ce _ _ _ m) H)
        | exact (proj2 (mod_ul_ul ce _ _ _ m) H) | exact (proj2 (and_ul_ul ce _ _ _ m) H)
        | exact (proj2 (or_ul_ul ce _ _ _ m) H) | exact (proj2 (xor_ul_ul ce _ _ _ m) H)
        | exact (proj2 (shl_ul_ul ce _ _ _ m) H) | exact (proj2 (shr_ul_ul ce _ _ _ m) H)
        | exact (proj2 (eq_ul_ul ce _ _ _ m) H) | exact (proj2 (ne_ul_ul ce _ _ _ m) H)
        | exact (proj2 (lt_ul_ul ce _ _ _ m) H) | exact (proj2 (le_ul_ul ce _ _ _ m) H)
        | exact (proj2 (gt_ul_ul ce _ _ _ m) H) | exact (proj2 (ge_ul_ul ce _ _ _ m) H)
        | exact (proj2 (lt_sl_sl ce _ _ _ m) H) | exact (proj2 (le_sl_sl ce _ _ _ m) H)
        | exact (proj2 (shr_sl_ul ce _ _ _ m) H) | exact (proj2 (add_ui_ui ce _ _ _ m) H)
        | exact (proj2 (sub_ui_ui ce _ _ _ m) H) | exact (proj2 (and_ui_ui ce _ _ _ m) H)
        | exact (proj2 (shl_ui_ui ce _ _ _ m) H) | exact (proj2 (shr_ui_ui ce _ _ _ m) H)
        | exact (proj2 (eq_ui_ui ce _ _ _ m) H) | exact (proj2 (ne_ui_ui ce _ _ _ m) H)
        | exact (proj2 (lt_ui_ui ce _ _ _ m) H) | exact (proj2 (gt_ui_ui ce _ _ _ m) H)
        | exact (proj2 (ge_ui_ui ce _ _ _ m) H)
        | exact (proj2 (add_d_d ce _ _ _ m) H) | exact (proj2 (sub_d_d ce _ _ _ m) H)
        | exact (proj2 (mul_d_d ce _ _ _ m) H) | exact (proj2 (div_d_d ce _ _ _ m) H)
        | exact (proj2 (eq_d_d ce _ _ _ m) H) | exact (proj2 (ne_d_d ce _ _ _ m) H)
        | exact (proj2 (lt_d_d ce _ _ _ m) H) | exact (proj2 (le_d_d ce _ _ _ m) H)
        | exact (proj2 (ge_d_d ce _ _ _ m) H) | exact (proj2 (add_f_f ce _ _ _ m) H)
        | exact (proj2 (sub_f_f ce _ _ _ m) H) | exact (proj2 (mul_f_f ce _ _ _ m) H)
        | exact (proj2 (div_f_f ce _ _ _ m) H) | exact (proj2 (eq_f_f ce _ _ _ m) H)
        | exact (proj2 (ne_f_f ce _ _ _ m) H) | exact (proj2 (lt_f_f ce _ _ _ m) H)
        | exact (proj2 (le_f_f ce _ _ _ m) H) | exact (proj2 (ge_f_f ce _ _ _ m) H) ].

Lemma binop_ok_sound : forall op t1 t2 v1 v2 v, binop_ok op t1 t2 v1 v2 v ->
  forall ce m, sem_binary_operation ce op v1 t1 v2 t2 m = Some v.
Proof.
  intros op t1 t2 v1 v2 v H ce m. pose proof H as H0. revert H0.
  destruct H; intros H0; binop_leaf H0 ce m.
Qed.

Ltac cast_leaf H m :=
  first [ exact (proj2 (cast_si_ui _ _ m) H) | exact (proj2 (cast_ui_si _ _ m) H)
        | exact (proj2 (cast_ul_ui _ _ m) H) | exact (proj2 (cast_ui_ul _ _ m) H)
        | exact (proj2 (cast_ul_sl _ _ m) H) | exact (proj2 (cast_sl_ul _ _ m) H)
        | exact (proj2 (cast_uc_ul _ _ m) H) | exact (proj2 (cast_uc_ui _ _ m) H)
        | exact (proj2 (cast_ul_uc _ _ m) H) | exact (proj2 (cast_ui_uc _ _ m) H)
        | exact (proj2 (cast_vuc_ul _ _ m) H) | exact (proj2 (cast_vui_ul _ _ m) H)
        | exact (proj2 (cast_ui_vui _ _ m) H) | exact (proj2 (cast_ul_ul _ _ m) H)
        | exact (proj2 (cast_ui_ui _ _ m) H) | exact (proj2 (cast_uc_uc _ _ m) H)
        | exact (proj2 (cast_si_si _ _ m) H)
        | exact (proj2 (cast_d_d _ _ m) H) | exact (proj2 (cast_f_f _ _ m) H)
        | exact (proj2 (cast_ul_d _ _ m) H) | exact (proj2 (cast_d_ul _ _ m) H)
        | exact (proj2 (cast_f_d _ _ m) H) | exact (proj2 (cast_d_f _ _ m) H)
        | exact (proj2 (cast_si_f _ _ m) H) | exact (proj2 (cast_ui_f _ _ m) H)
        | exact (proj2 (cast_ul_f _ _ m) H) | exact (proj2 (cast_f_si _ _ m) H)
        | exact (proj2 (cast_f_ul _ _ m) H) ].

Lemma cast_ok_sound : forall t1 t2 v1 v, cast_ok t1 t2 v1 v ->
  forall m, sem_cast v1 t1 t2 m = Some v.
Proof.
  intros t1 t2 v1 v H m. pose proof H as H0. revert H0. destruct H; intros H0; cast_leaf H0 m.
Qed.

Lemma bool_ok_sound : forall t v b, bool_ok t v b -> forall m, bool_val v t m = Some b.
Proof.
  intros t v b H m. pose proof H as H0. revert H0.
  destruct H; intros H0;
  first [ exact (proj2 (bool_si _ _ m) H0) | exact (proj2 (bool_ui _ _ m) H0) ].
Qed.

Lemma unop_ok_sound : forall op t v1 v, unop_ok op t v1 v ->
  forall m, sem_unary_operation op v1 t m = Some v.
Proof.
  intros op t v1 v H m. pose proof H as H0. revert H0.
  destruct H; intros H0;
  first [ exact (proj2 (neg_d _ _ m) H0) | exact (proj2 (abs_d _ _ m) H0)
        | exact (proj2 (neg_f _ _ m) H0) ].
Qed.

Lemma has_type_typeof : forall a t, has_type a t -> typeof a = t.
Proof. destruct 1; reflexivity. Qed.

(** * Lists *)

Lemma in_defs_In : forall defs x g, in_defs defs x g -> In (x, g) defs.
Proof. induction 1; simpl; auto. Qed.

Lemma In_in_defs : forall defs x g, In (x, g) defs -> in_defs defs x g.
Proof.
  induction defs as [|d defs IH]; simpl; intros x g H; [contradiction|].
  destruct H as [-> | H]; [apply in_here | apply in_there; auto].
Qed.

Lemma out_defs_notin : forall x defs, out_defs x defs -> ~ In x (map fst defs).
Proof. induction 1; simpl; intuition. Qed.

Lemma norepet_defs_sound : forall defs, norepet_defs defs -> list_norepet (map fst defs).
Proof.
  induction 1; simpl; constructor; auto. apply out_defs_notin; auto.
Qed.

Lemma out_names_notin : forall x l, out_names x l -> ~ In x (var_names l).
Proof. induction 1; unfold var_names in *; simpl; intuition. Qed.

Lemma norepet_names_sound : forall l, norepet_names l -> list_norepet (var_names l).
Proof.
  induction 1; unfold var_names in *; simpl; constructor; auto.
  apply (out_names_notin x rest); auto.
Qed.

Lemma disjoint_names_sound : forall l1 l2, disjoint_names l1 l2 ->
  list_disjoint (var_names l1) (var_names l2).
Proof.
  induction 1; unfold var_names in *; simpl; red; intros a b A B; [contradiction|].
  destruct A as [<- | A].
  - intros <-. apply (out_names_notin x l); auto.
  - apply IHdisjoint_names; auto.
Qed.

Lemma params_types_sound : forall l tys, params_types l tys -> type_of_params l = tys.
Proof. induction 1; simpl; congruence. Qed.

(** * Temporaries *)

Definition temps_rel (le: temp_env) (ln: ident -> option val) : Prop :=
  forall id, le ! id = ln id.

Lemma upd_temps : forall le ln ln2 x v, temps_rel le ln ->
  (forall y, (y = x -> ln2 y = Some v) /\ (y <> x -> ln2 y = ln y)) ->
  temps_rel (PTree.set x v le) ln2.
Proof.
  intros le ln ln2 x v R U y. rewrite PTree.gsspec. destruct (peq y x).
  - symmetry. apply (proj1 (U y)); auto.
  - rewrite (proj2 (U y)); auto.
Qed.

Lemma undef_temps_sound : forall temps ln, undef_temps temps ln ->
  temps_rel (create_undef_temps temps) ln.
Proof.
  induction 1; simpl.
  - intros y. rewrite PTree.gempty. auto.
  - eapply upd_temps; eauto.
Qed.

Lemma bind_params_sound : forall params vs ln ln2, bind_params params vs ln ln2 ->
  forall le, temps_rel le ln ->
  exists le2, bind_parameter_temps params vs le = Some le2 /\ temps_rel le2 ln2.
Proof.
  induction 1; intros le0 R; simpl.
  - eauto.
  - apply IHbind_params. eapply upd_temps; eauto.
Qed.

Lemma set_opt_sound : forall optid v ln ln2, set_opt optid v ln ln2 ->
  forall le, temps_rel le ln -> temps_rel (set_opttemp optid v le) ln2.
Proof.
  destruct 1; intros le0 R; simpl; auto. eapply upd_temps; eauto.
Qed.

Lemma result_ok_sound : forall out ty v, result_ok out ty v ->
  forall m, outcome_result_value out ty v m.
Proof.
  destruct 1; intros m; simpl; auto. split; auto. eapply cast_ok_sound; eauto.
Qed.

(** * Offsets and accesses *)

Lemma modulus_eq : Ptrofs.modulus = 18446744073709551616.
Proof. reflexivity. Qed.

Lemma chunk_in_range : forall chunk, 0 + size_chunk chunk <= Ptrofs.modulus.
Proof.
  intros. assert (size_chunk chunk <= 8) by (destruct chunk; simpl; lia).
  rewrite modulus_eq. lia.
Qed.

Lemma loadv_zero : forall chunk m b,
  Mem.loadv chunk m (Vptr b Ptrofs.zero) = Mem.load chunk m b 0.
Proof.
  intros. unfold Mem.loadv. rewrite Ptrofs.unsigned_zero, zle_true; auto.
  apply chunk_in_range.
Qed.

Lemma storev_zero : forall chunk m b v,
  Mem.storev chunk m (Vptr b Ptrofs.zero) v = Mem.store chunk m b 0 v.
Proof.
  intros. unfold Mem.storev. rewrite Ptrofs.unsigned_zero, zle_true; auto.
  apply chunk_in_range.
Qed.

(** The offset that CompCert's pointer arithmetic gives the element [k] of size [sz]. *)
Lemma ptr_off : forall sz k,
  Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.of_int64 k)) =
  Ptrofs.repr (sz * Int64.unsigned k).
Proof.
  intros. rewrite Ptrofs.add_zero_l. unfold Ptrofs.mul, Ptrofs.of_int64.
  apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_mult; apply Ptrofs.eqm_sym;
  apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma add_ptr : forall ge b ty pty k m, classify_add pty (Tlong Unsigned noattr) = add_case_pl ty ->
  sem_binary_operation ge Oadd (Vptr b Ptrofs.zero) pty (Vlong k) (Tlong Unsigned noattr) m =
  Some (Vptr b (Ptrofs.repr (sizeof ge ty * Int64.unsigned k))).
Proof.
  intros. unfold sem_binary_operation, sem_add. rewrite H. unfold sem_add_ptr_long.
  rewrite ptr_off. reflexivity.
Qed.

Definition woff (k: int64) : Z := NBase.zmod (8 * NBase.u64 k) 18446744073709551616.

Lemma woff_spec : forall k, woff k = 8 * (Int64.unsigned k mod 2305843009213693952).
Proof.
  intros. unfold woff, NBase.zmod, NBase.u64.
  change 18446744073709551616 with (8 * 2305843009213693952).
  apply Z.mul_mod_distr_l; lia.
Qed.

Lemma woff_unsigned : forall k, Ptrofs.unsigned (Ptrofs.repr (8 * Int64.unsigned k)) = woff k.
Proof. intros. rewrite Ptrofs.unsigned_repr_eq, modulus_eq. reflexivity. Qed.

Lemma woff_range : forall k, 0 <= woff k /\ (8 | woff k).
Proof.
  intros. rewrite woff_spec. split.
  - pose proof (Z.mod_pos_bound (Int64.unsigned k) 2305843009213693952). lia.
  - exists (Int64.unsigned k mod 2305843009213693952). lia.
Qed.

Lemma uk_unsigned : forall sz k, 0 <= sz ->
  sz * Int64.unsigned k < Ptrofs.modulus ->
  Ptrofs.unsigned (Ptrofs.repr (sz * Int64.unsigned k)) = sz * Int64.unsigned k.
Proof.
  intros. pose proof (Int64.unsigned_range k).
  apply Ptrofs.unsigned_repr. unfold Ptrofs.max_unsigned. nia.
Qed.

(** The bytes of an array: [f j] is the byte of the block [b] at offset [j], for [0 <= j < hi],
    and the memory allows its store. *)
Definition bytes_at (m: mem) (b: block) (f: Z -> Z) (hi: Z) : Prop :=
  forall j, 0 <= j < hi ->
    0 <= f j < 256 /\ ZMap.get j (Mem.mem_contents m) !! b = Byte (Byte.repr (f j)) /\
    Mem.perm m b j Cur Writable.

Definition le4 (f: Z -> Z) (o: Z) : Z :=
  f o + (256 * f (o + 1) + (65536 * f (o + 2) + 16777216 * f (o + 3))).

Definition le8 (f: Z -> Z) (o: Z) : Z := le4 f o + 4294967296 * le4 f (o + 4).

Ltac contents B :=
  repeat match goal with |- context [ZMap.get ?X ((Mem.mem_contents ?m) !! ?b)] =>
    rewrite (proj1 (proj2 (B X ltac:(lia)))) end;
  unfold decode_val; cbn [proj_bytes]; unfold decode_int, rev_if_be, Archi.big_endian;
  cbn [int_of_bytes];
  repeat match goal with |- context [Byte.unsigned (Byte.repr ?Y)] =>
    rewrite (Byte.unsigned_repr Y) by
      (match Y with ?F ?X => pose proof (proj1 (B X ltac:(lia))) end;
       unfold Byte.max_unsigned; simpl; lia) end.

Lemma valid_bytes : forall m b f hi o chunk,
  bytes_at m b f hi -> 0 <= o -> o + size_chunk chunk <= hi -> (align_chunk chunk | o) ->
  Mem.valid_access m chunk b o Writable.
Proof.
  intros m b f hi o chunk B O0 OH A. split; auto.
  intros j J. apply (B j). lia.
Qed.

Lemma load_le8 : forall m b f hi ofs o,
  bytes_at m b f hi -> Ptrofs.unsigned ofs = o -> 0 <= o -> o + 8 <= hi -> (8 | o) ->
  Mem.loadv Mint64 m (Vptr b ofs) = Some (Vlong (Int64.repr (le8 f o))).
Proof.
  intros m b f hi ofs o B U O0 OH [q Q].
  pose proof (Ptrofs.unsigned_range ofs) as R. rewrite modulus_eq in R.
  unfold Mem.loadv. rewrite U, zle_true by (simpl; rewrite modulus_eq; lia).
  unfold Mem.load. rewrite pred_dec_true.
  2: { apply Mem.valid_access_implies with Writable; [| constructor].
       eapply valid_bytes; [exact B | exact O0 | simpl; lia | exists q; auto]. }
  f_equal. change (size_chunk_nat Mint64) with 8%nat. cbn [Mem.getN].
  contents B.
  unfold le8, le4. do 2 f_equal.
  replace (o + 1 + 1) with (o + 2) by lia. replace (o + 2 + 1) with (o + 3) by lia.
  replace (o + 3 + 1) with (o + 4) by lia. replace (o + 4 + 1) with (o + 5) by lia.
  replace (o + 5 + 1) with (o + 6) by lia. replace (o + 6 + 1) with (o + 7) by lia.
  replace (o + 4 + 2) with (o + 6) by lia. replace (o + 4 + 3) with (o + 7) by lia.
  ring.
Qed.

Lemma load_le4 : forall m b f hi ofs o,
  bytes_at m b f hi -> Ptrofs.unsigned ofs = o -> 0 <= o -> o + 4 <= hi -> (4 | o) ->
  Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint (Int.repr (le4 f o))).
Proof.
  intros m b f hi ofs o B U O0 OH [q Q].
  pose proof (Ptrofs.unsigned_range ofs) as R. rewrite modulus_eq in R.
  unfold Mem.loadv. rewrite U, zle_true by (simpl; rewrite modulus_eq; lia).
  unfold Mem.load. rewrite pred_dec_true.
  2: { apply Mem.valid_access_implies with Writable; [| constructor].
       eapply valid_bytes; [exact B | exact O0 | simpl; lia | exists q; auto]. }
  f_equal. change (size_chunk_nat Mint32) with 4%nat. cbn [Mem.getN].
  contents B.
  unfold le4. do 2 f_equal.
  replace (o + 1 + 1) with (o + 2) by lia. replace (o + 2 + 1) with (o + 3) by lia.
  ring.
Qed.

Lemma load_f64 : forall m b f hi ofs o,
  bytes_at m b f hi -> Ptrofs.unsigned ofs = o -> 0 <= o -> o + 8 <= hi -> (8 | o) ->
  Mem.loadv Mfloat64 m (Vptr b ofs) = Some (Vfloat (Float.of_bits (Int64.repr (le8 f o)))).
Proof.
  intros m b f hi ofs o B U O0 OH [q Q].
  pose proof (Ptrofs.unsigned_range ofs) as R. rewrite modulus_eq in R.
  unfold Mem.loadv. rewrite U, zle_true by (simpl; rewrite modulus_eq; lia).
  unfold Mem.load. rewrite pred_dec_true.
  2: { apply Mem.valid_access_implies with Writable; [| constructor].
       eapply valid_bytes; [exact B | exact O0 | simpl; lia | exists q; auto]. }
  f_equal. change (size_chunk_nat Mfloat64) with 8%nat. cbn [Mem.getN].
  contents B.
  unfold le8, le4. do 3 f_equal.
  replace (o + 1 + 1) with (o + 2) by lia. replace (o + 2 + 1) with (o + 3) by lia.
  replace (o + 3 + 1) with (o + 4) by lia. replace (o + 4 + 1) with (o + 5) by lia.
  replace (o + 5 + 1) with (o + 6) by lia. replace (o + 6 + 1) with (o + 7) by lia.
  replace (o + 4 + 2) with (o + 6) by lia. replace (o + 4 + 3) with (o + 7) by lia.
  ring.
Qed.

Lemma load_f32 : forall m b f hi ofs o,
  bytes_at m b f hi -> Ptrofs.unsigned ofs = o -> 0 <= o -> o + 4 <= hi -> (4 | o) ->
  Mem.loadv Mfloat32 m (Vptr b ofs) = Some (Vsingle (Float32.of_bits (Int.repr (le4 f o)))).
Proof.
  intros m b f hi ofs o B U O0 OH [q Q].
  pose proof (Ptrofs.unsigned_range ofs) as R. rewrite modulus_eq in R.
  unfold Mem.loadv. rewrite U, zle_true by (simpl; rewrite modulus_eq; lia).
  unfold Mem.load. rewrite pred_dec_true.
  2: { apply Mem.valid_access_implies with Writable; [| constructor].
       eapply valid_bytes; [exact B | exact O0 | simpl; lia | exists q; auto]. }
  f_equal. change (size_chunk_nat Mfloat32) with 4%nat. cbn [Mem.getN].
  contents B.
  unfold le4. do 3 f_equal.
  replace (o + 1 + 1) with (o + 2) by lia. replace (o + 2 + 1) with (o + 3) by lia.
  ring.
Qed.

Lemma load_byte : forall m b f hi ofs o,
  bytes_at m b f hi -> Ptrofs.unsigned ofs = o -> 0 <= o -> o + 1 <= hi ->
  Mem.loadv Mint8unsigned m (Vptr b ofs) = Some (Vint (Int.repr (f o))).
Proof.
  intros m b f hi ofs o B U O0 OH.
  pose proof (Ptrofs.unsigned_range ofs) as R. rewrite modulus_eq in R.
  unfold Mem.loadv. rewrite U, zle_true by (simpl; rewrite modulus_eq; lia).
  unfold Mem.load. rewrite pred_dec_true.
  2: { apply Mem.valid_access_implies with Writable; [| constructor].
       eapply valid_bytes; [exact B | exact O0 | simpl; lia | apply Z.divide_1_l]. }
  f_equal. change (size_chunk_nat Mint8unsigned) with 1%nat. cbn [Mem.getN].
  contents B.
  rewrite Z.mul_0_l, Z.add_0_r. f_equal. pose proof (proj1 (B o ltac:(lia))).
  unfold Int.zero_ext. rewrite Int.unsigned_repr by (unfold Int.max_unsigned; simpl; lia).
  rewrite Zbits.Zzero_ext_mod by lia. f_equal. apply Z.mod_small. change (two_p 8) with 256. lia.
Qed.

Lemma setN_bytes_of_int : forall n x p c j, 0 <= x -> 0 <= j < Z.of_nat n ->
  ZMap.get (p + j) (Mem.setN (inj_bytes (bytes_of_int n x)) p c) =
  Byte (Byte.repr (x / two_p (8 * j))).
Proof.
  induction n; intros x p c j X J. simpl in J; lia.
  rewrite Nat2Z.inj_succ in J. simpl bytes_of_int. unfold inj_bytes. simpl map. simpl Mem.setN.
  destruct (zeq j 0).
  - subst j. rewrite Mem.setN_outside by lia. rewrite Z.add_0_r, ZMap.gss.
    change (two_p (8 * 0)) with 1. rewrite Z.div_1_r. reflexivity.
  - replace (p + j) with ((p + 1) + (j - 1)) by lia. unfold inj_bytes in IHn.
    rewrite IHn by (try apply Z.div_pos; lia).
    assert (two_p (8 * (j - 1)) > 0) by (apply two_p_gt_ZERO; lia).
    rewrite Zdiv.Zdiv_Zdiv by lia.
    replace (8 * j) with (8 + 8 * (j - 1)) by lia. rewrite two_p_is_exp by lia. reflexivity.
Qed.

(** The store of a value whose bytes are those of the number [w], from the lowest, at offset
    [o] of the array's block. *)
Lemma store_le : forall m b f hi o chunk v w f2,
  bytes_at m b f hi -> 0 <= o -> o + size_chunk chunk <= hi -> (align_chunk chunk | o) ->
  o + size_chunk chunk <= Ptrofs.modulus -> 0 <= w ->
  encode_val chunk v = inj_bytes (bytes_of_int (size_chunk_nat chunk) w) ->
  (forall j, (o <= j < o + size_chunk chunk ->
               f2 j = NBase.zmod (NBase.zdiv w (NBase.pow2 (8 * (j - o)))) 256) /\
             (~ (o <= j < o + size_chunk chunk) -> f2 j = f j)) ->
  exists m', Mem.storev chunk m (Vptr b (Ptrofs.repr o)) v = Some m' /\
    Mem.store chunk m b o v = Some m' /\ bytes_at m' b f2 hi.
Proof.
  intros m b f hi o chunk v w f2 B O0 OH A OM W EV F2.
  destruct (Mem.valid_access_store m chunk b o v) as [m' ST]. eapply valid_bytes; eauto.
  exists m'. unfold Mem.storev.
  rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; pose proof (size_chunk_pos chunk);
    lia).
  rewrite zle_true by lia. split; auto. split; auto.
  intros j J. rewrite (Mem.store_mem_contents _ _ _ _ _ _ ST), PMap.gss.
  assert (LEN: Z.of_nat (length (encode_val chunk v)) = size_chunk chunk)
    by (rewrite encode_val_length, <- size_chunk_conv; auto).
  destruct (zlt j o) as [LT|GE]; [|destruct (zlt j (o + size_chunk chunk)) as [LT|GE2]].
  - rewrite Mem.setN_outside by lia. rewrite (proj2 (F2 j)) by lia.
    destruct (B j J) as (R & C & P). split; auto. split; auto. eapply Mem.perm_store_1; eauto.
  - rewrite (proj1 (F2 j)) by lia. unfold NBase.zmod, NBase.zdiv, NBase.pow2.
    split; [apply Z.mod_pos_bound; lia|]. split.
    + rewrite EV. replace j with (o + (j - o)) at 1 by lia.
      rewrite setN_bytes_of_int by (try rewrite <- size_chunk_conv; lia).
      f_equal. rewrite two_p_equiv. apply Byte.eqm_samerepr.
      change 256 with Byte.modulus. apply Zbits.eqmod_mod. reflexivity.
    + eapply Mem.perm_store_1; eauto. apply (B j). auto.
  - rewrite Mem.setN_outside by lia. rewrite (proj2 (F2 j)) by lia.
    destruct (B j J) as (R & C & P). split; auto. split; auto. eapply Mem.perm_store_1; eauto.
Qed.

(** * Expressions and statements of one program *)

Section PROGRAM.

Variable p: Clight.program.
Let ge := globalenv p.
Hypothesis NOREP: list_norepet (map fst (prog_defs p)).

Lemma def_of : forall x g, in_defs (prog_defs p) x g ->
  exists b, Genv.find_symbol ge x = Some b /\ Genv.find_def ge b = Some g.
Proof.
  intros x g H. apply (Genv.find_def_symbol (program_of_program p)).
  apply prog_defmap_norepet; auto. apply in_defs_In; auto.
Qed.

Lemma in_defs_unique : forall x g1 g2,
  in_defs (prog_defs p) x g1 -> in_defs (prog_defs p) x g2 -> g1 = g2.
Proof.
  intros x g1 g2 H1 H2.
  destruct (def_of x g1 H1) as (b1 & S1 & D1). destruct (def_of x g2 H2) as (b2 & S2 & D2).
  congruence.
Qed.

Lemma distinct_blocks : forall x y g1 g2 b1 b2,
  in_defs (prog_defs p) x g1 -> in_defs (prog_defs p) y g2 -> g1 <> g2 ->
  Genv.find_symbol ge x = Some b1 -> Genv.find_symbol ge y = Some b2 -> b1 <> b2.
Proof.
  intros x y g1 g2 b1 b2 D1 D2 NE S1 S2.
  eapply Genv.global_addresses_distinct; eauto.
  intros <-. apply NE. eapply in_defs_unique; eauto.
Qed.

Lemma volatile_block : forall x ty init b,
  in_defs (prog_defs p) x (Gvar (mkglobvar ty init false true)) ->
  Genv.find_symbol ge x = Some b -> Genv.block_is_volatile ge b = true.
Proof.
  intros x ty init b D S. destruct (def_of _ _ D) as (b' & S' & F).
  assert (b' = b) by congruence. subst b'.
  unfold Genv.block_is_volatile. rewrite (proj2 (Genv.find_var_info_iff _ _ _) F). reflexivity.
Qed.

(** The scalar globals of N are in memory: each holds its value of N, which a load of its
    type's chunk at offset 0 reads, and the memory allows the store of that chunk. *)
Definition globs_rel (m: mem) (gv: ident -> option val) : Prop :=
  forall x ty init, in_defs (prog_defs p) x (Gvar (mkglobvar ty init false false)) -> scalar ty ->
  exists b chunk v, Genv.find_symbol ge x = Some b /\ access_mode ty = By_value chunk /\
    gv x = Some v /\ gval ty v /\ Mem.load chunk m b 0 = Some v /\
    Mem.valid_access m chunk b 0 Writable.

(** The arrays of N are in memory: byte [j] of the array [x] of [n] words is the byte at offset
    [j] of its block. *)
Definition arr_def (n: Z) : globdef fundef type :=
  Gvar (mkglobvar (Tarray (Tlong Unsigned noattr) n noattr) (Init_space (8 * n) :: nil)
    false false).

Definition arrays_rel (m: mem) (mb: ident -> Z -> Z) : Prop :=
  forall x n, in_defs (prog_defs p) x (arr_def n) ->
  exists b, Genv.find_symbol ge x = Some b /\ bytes_at m b (mb x) (8 * n).

Lemma scalar_not_arr : forall ty init n, scalar ty ->
  Gvar (mkglobvar ty init false false) <> arr_def n.
Proof. intros ty init n S E. inv E. inv S. Qed.

Lemma arr_def_inj : forall n1 n2, arr_def n1 = arr_def n2 -> n1 = n2.
Proof. intros n1 n2 E. inv E. auto. Qed.

Lemma gval_load_result : forall ty v chunk, gval ty v -> access_mode ty = By_value chunk ->
  Val.load_result chunk v = v.
Proof. destruct 1; simpl; intros A; inv A; reflexivity. Qed.

Lemma global_lvalue : forall x ty le m b,
  Genv.find_symbol ge x = Some b ->
  eval_lvalue ge empty_env le m (Evar x ty) b Ptrofs.zero Full.
Proof. intros. apply eval_Evar_global; auto. Qed.

Lemma eval_base : forall le m x b ty n a,
  Genv.find_symbol ge x = Some b ->
  eval_expr ge empty_env le m (Evar x (Tarray ty n a)) (Vptr b Ptrofs.zero).
Proof.
  intros. eapply eval_Elvalue; [apply global_lvalue; exact H | apply deref_loc_reference].
  reflexivity.
Qed.

Lemma eval_base_cast : forall le m x b n ty,
  Genv.find_symbol ge x = Some b ->
  eval_expr ge empty_env le m
    (Ecast (Evar x (Tarray (Tlong Unsigned noattr) n noattr)) (Tpointer ty noattr))
    (Vptr b Ptrofs.zero).
Proof. intros. eapply eval_Ecast; [apply eval_base; exact H | reflexivity]. Qed.

Lemma eval_elem : forall le m x b ty n i k,
  Genv.find_symbol ge x = Some b ->
  eval_expr ge empty_env le m i (Vlong k) -> typeof i = Tlong Unsigned noattr ->
  eval_expr ge empty_env le m (Ebinop Oadd (Evar x (Tarray ty n noattr)) i (Tpointer ty noattr))
    (Vptr b (Ptrofs.repr (sizeof ge ty * Int64.unsigned k))).
Proof.
  intros. eapply eval_Ebinop; [apply eval_base; exact H | exact H0 |]. rewrite H1.
  apply add_ptr. reflexivity.
Qed.

Lemma eval_byte_elem : forall le m x b n i k,
  Genv.find_symbol ge x = Some b ->
  eval_expr ge empty_env le m i (Vlong k) -> typeof i = Tlong Unsigned noattr ->
  eval_expr ge empty_env le m
    (Ebinop Oadd (Ecast (Evar x (Tarray (Tlong Unsigned noattr) n noattr))
                   (Tpointer (Tint I8 Unsigned noattr) noattr)) i
      (Tpointer (Tint I8 Unsigned noattr) noattr))
    (Vptr b (Ptrofs.repr (1 * Int64.unsigned k))).
Proof.
  intros. eapply eval_Ebinop; [apply eval_base_cast; exact H | exact H0 |]. rewrite H1.
  apply (add_ptr ge b (Tint I8 Unsigned noattr)). reflexivity.
Qed.

Lemma neval_sound : forall ln gv mb a v, neval (prog_defs p) ln gv mb a v ->
  forall le m, temps_rel le ln -> globs_rel m gv -> arrays_rel m mb ->
  eval_expr ge empty_env le m a v.
Proof.
  induction 1; intros le0 m R G AR.
  - apply eval_Econst_int.
  - apply eval_Econst_long.
  - apply eval_Econst_float.
  - apply eval_Econst_single.
  - apply eval_Etempvar. rewrite R. auto.
  - destruct (G x ty init H H0) as (b & chunk & v' & S & A & E & _ & L & _).
    assert (v' = v) by congruence. subst v'.
    eapply eval_Elvalue. apply global_lvalue; eauto.
    eapply deref_loc_value; [exact A | rewrite loadv_zero; exact L].
  - (* word *)
    destruct (AR x n H) as (b & S & B). destruct (woff_range k) as [W0 WA].
    eapply eval_Elvalue.
    + apply eval_Ederef. apply eval_elem; eauto. apply has_type_typeof; auto.
    + eapply deref_loc_value. reflexivity.
      eapply load_le8; [exact B | apply woff_unsigned | exact W0 | exact H2 | exact WA].
  - (* byte *)
    destruct (AR x n H) as (b & S & B). pose proof (Int64.unsigned_range k) as RK.
    change Int64.modulus with 18446744073709551616 in RK.
    eapply eval_Elvalue.
    + apply eval_Ederef. apply eval_byte_elem; eauto. apply has_type_typeof; auto.
    + eapply deref_loc_value. reflexivity.
      unfold NBase.u64 in *. eapply load_byte; [exact B | | lia | lia].
      rewrite uk_unsigned; rewrite ?modulus_eq; lia.
  - (* cell of a word *)
    destruct (AR x n H) as (b & S & B).
    eapply eval_Elvalue.
    + apply eval_Ederef. apply eval_base_cast; exact S.
    + eapply deref_loc_value. reflexivity.
      eapply load_le8; [exact B | apply Ptrofs.unsigned_zero | lia | lia | apply Z.divide_0_r].
  - (* cell of an int *)
    destruct (AR x n H) as (b & S & B).
    eapply eval_Elvalue.
    + apply eval_Ederef. apply eval_base_cast; exact S.
    + eapply deref_loc_value. reflexivity.
      eapply load_le4; [exact B | apply Ptrofs.unsigned_zero | lia | lia | apply Z.divide_0_r].
  - (* cell of a double *)
    destruct (AR x n H) as (b & S & B).
    eapply eval_Elvalue.
    + apply eval_Ederef. apply eval_base_cast; exact S.
    + eapply deref_loc_value. reflexivity.
      eapply load_f64; [exact B | apply Ptrofs.unsigned_zero | lia | lia | apply Z.divide_0_r].
  - (* cell of a float *)
    destruct (AR x n H) as (b & S & B).
    eapply eval_Elvalue.
    + apply eval_Ederef. apply eval_base_cast; exact S.
    + eapply deref_loc_value. reflexivity.
      eapply load_f32; [exact B | apply Ptrofs.unsigned_zero | lia | lia | apply Z.divide_0_r].
  - eapply eval_Ebinop; eauto.
    rewrite (has_type_typeof _ _ H0), (has_type_typeof _ _ H2). eapply binop_ok_sound; eauto.
  - eapply eval_Ecast; eauto. rewrite (has_type_typeof _ _ H0). eapply cast_ok_sound; eauto.
  - eapply eval_Eunop; eauto. rewrite (has_type_typeof _ _ H0). eapply unop_ok_sound; eauto.
Qed.

Lemma neval_list_sound : forall ln gv mb al tys vs,
  neval_list (prog_defs p) ln gv mb al tys vs ->
  forall le m, temps_rel le ln -> globs_rel m gv -> arrays_rel m mb ->
  eval_exprlist ge empty_env le m al tys vs.
Proof.
  induction 1; intros le0 m R G AR; econstructor; eauto.
  - eapply neval_sound; eauto.
  - rewrite (has_type_typeof _ _ H0). eapply cast_ok_sound; eauto.
Qed.

(** A store to a block that holds no scalar global keeps the scalar globals, and a store to a
    block that holds no array keeps the arrays. *)
Lemma globs_store_other : forall m m' gv chunk b o v,
  globs_rel m gv -> Mem.store chunk m b o v = Some m' ->
  (forall x ty init b', in_defs (prog_defs p) x (Gvar (mkglobvar ty init false false)) ->
     scalar ty -> Genv.find_symbol ge x = Some b' -> b' <> b) ->
  globs_rel m' gv.
Proof.
  intros m m' gv chunk b o v G ST D x ty init Dx Sx.
  destruct (G x ty init Dx Sx) as (b' & chunk' & v' & S' & A' & E' & V' & L' & VA').
  exists b', chunk', v'. do 4 (split; [assumption |]). split.
  - rewrite (Mem.load_store_other _ _ _ _ _ _ ST); auto. left. eapply D; eauto.
  - eapply Mem.store_valid_access_1; eauto.
Qed.

Lemma arrays_store_other : forall m m' mb chunk b o v,
  arrays_rel m mb -> Mem.store chunk m b o v = Some m' ->
  (forall x n b', in_defs (prog_defs p) x (arr_def n) -> Genv.find_symbol ge x = Some b' ->
     b' <> b) ->
  arrays_rel m' mb.
Proof.
  intros m m' mb chunk b o v AR ST D x n Dx.
  destruct (AR x n Dx) as (b' & S' & B'). exists b'. split; auto.
  intros j J. destruct (B' j J) as (R & C & P). split; auto. split.
  - rewrite (Mem.store_mem_contents _ _ _ _ _ _ ST), PMap.gso; eauto.
  - eapply Mem.perm_store_1; eauto.
Qed.

Lemma arrays_store_same : forall m m' mb mb2 chunk x n b o v,
  arrays_rel m mb -> in_defs (prog_defs p) x (arr_def n) -> Genv.find_symbol ge x = Some b ->
  Mem.store chunk m b o v = Some m' -> bytes_at m' b (mb2 x) (8 * n) ->
  (forall y j, y <> x -> mb2 y j = mb y j) ->
  arrays_rel m' mb2.
Proof.
  intros m m' mb mb2 chunk x n b o v AR Dx Sx ST B2 OTHER y n' Dy.
  destruct (AR y n' Dy) as (b' & S' & B'). exists b'. split; auto.
  destruct (peq y x) as [<- | NE].
  - assert (n' = n) by (apply arr_def_inj; eapply in_defs_unique; eauto). subst n'.
    assert (b' = b) by congruence. subst b'. auto.
  - assert (b' <> b).
    { eapply Genv.global_addresses_distinct; eauto. }
    intros j J. rewrite OTHER by auto. destruct (B' j J) as (R & C & P). split; auto. split.
    + rewrite (Mem.store_mem_contents _ _ _ _ _ _ ST), PMap.gso; auto.
    + eapply Mem.perm_store_1; eauto.
Qed.

Lemma array_not_scalar : forall x n b,
  in_defs (prog_defs p) x (arr_def n) -> Genv.find_symbol ge x = Some b ->
  forall y ty init b', in_defs (prog_defs p) y (Gvar (mkglobvar ty init false false)) ->
  scalar ty -> Genv.find_symbol ge y = Some b' -> b' <> b.
Proof.
  intros x n b Dx Sx y ty init b' Dy Sy Sy'.
  eapply (distinct_blocks y x); [exact Dy | exact Dx | apply scalar_not_arr; auto | exact Sy' |
    exact Sx].
Qed.

Lemma store_global : forall m gv mb x ty init v gv2,
  globs_rel m gv -> arrays_rel m mb ->
  in_defs (prog_defs p) x (Gvar (mkglobvar ty init false false)) ->
  scalar ty -> gval ty v ->
  (forall y, (y = x -> gv2 y = Some v) /\ (y <> x -> gv2 y = gv y)) ->
  exists b chunk m', Genv.find_symbol ge x = Some b /\ access_mode ty = By_value chunk /\
    Mem.storev chunk m (Vptr b Ptrofs.zero) v = Some m' /\ globs_rel m' gv2 /\
    arrays_rel m' mb.
Proof.
  intros m gv mb x ty init v gv2 G AR D S V U.
  destruct (G x ty init D S) as (b & chunk & v0 & SY & A & _ & _ & _ & VA).
  destruct (Mem.valid_access_store m chunk b 0 v VA) as [m' ST].
  exists b, chunk, m'. split; auto. split; auto. split; [rewrite storev_zero; exact ST|].
  split.
  - intros y tyy inity Dy Sy.
    destruct (G y tyy inity Dy Sy) as (b' & chunk' & v' & SY' & A' & E' & V' & L' & VA').
    exists b', chunk'. destruct (peq y x).
    + subst y. assert (mkglobvar tyy inity false false = mkglobvar ty init false false).
      { assert (Gvar (mkglobvar tyy inity false false) =
                @Gvar fundef type (mkglobvar ty init false false))
          by (eapply in_defs_unique; eauto). congruence. }
      inv H. assert (b' = b) by congruence. subst b'. rewrite A in A'. inv A'.
      exists v. split; auto. split; auto. split; [apply (proj1 (U x)); auto|]. split; auto.
      split.
      * rewrite (Mem.load_store_same _ _ _ _ _ _ ST). f_equal. eapply gval_load_result; eauto.
      * eapply Mem.store_valid_access_1; eauto.
    + exists v'. split; auto. split; auto. split; [rewrite (proj2 (U y)); auto|]. split; auto.
      split.
      * rewrite (Mem.load_store_other _ _ _ _ _ _ ST); auto. left.
        eapply Genv.global_addresses_distinct; eauto.
      * eapply Mem.store_valid_access_1; eauto.
  - eapply arrays_store_other; [exact AR | exact ST |]. intros y n b' Dy Sy.
    apply not_eq_sym. exact (array_not_scalar y n b' Dy Sy x ty init b D S SY).
Qed.

Lemma ptr_cast : forall b ofs t a m,
  sem_cast (Vptr b ofs) (Tpointer t a) (Tpointer t a) m = Some (Vptr b ofs).
Proof. reflexivity. Qed.

Lemma out_store : forall x init i m,
  in_defs (prog_defs p) x
    (Gvar (mkglobvar (Tint I32 Unsigned (mk_attr true None)) init false true)) ->
  exists b, Genv.find_symbol ge x = Some b /\
    external_call (EF_vstore Mint32) ge (Vptr b Ptrofs.zero :: Vint i :: nil) m
      (Event_vstore Mint32 x Ptrofs.zero (EVint i) :: nil) Vundef m.
Proof.
  intros x init i m D. destruct (def_of _ _ D) as (b & S & F).
  exists b. split; auto. constructor. apply volatile_store_vol.
  - eapply volatile_block; eauto.
  - exact S.
  - constructor.
Qed.

Lemma vstore_elem : forall x b ofs i m,
  Genv.find_symbol ge x = Some b -> Genv.block_is_volatile ge b = true ->
  external_call (EF_vstore Mint32) ge (Vptr b ofs :: Vint i :: nil) m
    (Event_vstore Mint32 x ofs (EVint i) :: nil) Vundef m.
Proof.
  intros. constructor. apply volatile_store_vol; auto. constructor.
Qed.

Lemma vload_elem : forall ch ty sz j v x b ofs m,
  vload_ok ch ty sz j v -> Genv.find_symbol ge x = Some b ->
  Genv.block_is_volatile ge b = true ->
  external_call (EF_vload ch) ge (Vptr b ofs :: nil) m (Event_vload ch x ofs (EVint j) :: nil)
    v m.
Proof.
  intros ch ty sz j v x b ofs m VL S V. destruct VL.
  - replace (Vint (NBase.r32 (NBase.zmod (NBase.u32 j) 256)))
      with (Val.load_result Mint8unsigned (Vint j)).
    + constructor. apply volatile_load_vol; auto. constructor.
    + simpl. unfold Int.zero_ext, NBase.r32, NBase.zmod, NBase.u32. do 2 f_equal.
      apply Zbits.Zzero_ext_mod. lia.
  - change (Vint j) with (Val.load_result Mint32 (Vint j)).
    constructor. apply volatile_load_vol; auto. constructor.
Qed.

Lemma vload_size : forall ch ty sz j v, vload_ok ch ty sz j v -> sizeof ge ty = sz.
Proof. destruct 1; reflexivity. Qed.

(** The built-in [__builtin_fsqrt] of CompCert's table gives the square root, with no event. *)
Lemma sqrt_call : forall f m,
  external_call (EF_builtin "__builtin_fsqrt" (mksignature (Xfloat :: nil) Xfloat cc_default))
    ge (Vfloat f :: nil) m E0 (Vfloat (Float.sqrt f)) m.
Proof.
  intros f m. simpl. unfold builtin_or_external_sem.
  assert (L: Builtins.lookup_builtin_function "__builtin_fsqrt"
               (mksignature (Xfloat :: nil) Xfloat cc_default) =
             Some (Builtins.BI_standard Builtins0.BI_fsqrt)) by reflexivity.
  rewrite L. constructor. reflexivity.
Qed.

Lemma internal_funct : forall x f, in_defs (prog_defs p) x (Gfun (Internal f)) ->
  exists b, Genv.find_symbol ge x = Some b /\ Genv.find_funct_ptr ge b = Some (Internal f).
Proof.
  intros x f D. destruct (def_of _ _ D) as (b & S & F).
  exists b. split; auto. apply Genv.find_funct_ptr_iff; auto.
Qed.

Ltac outcomes :=
  repeat match goal with
  | H: (_ = Out_break /\ _ = Out_normal) \/ _ |- _ => destruct H as [[-> ->] | [? [-> ->]]]
  | H: _ = Out_normal \/ _ = Out_continue |- _ => destruct H as [-> | ->]
  end; constructor.

(** The new bytes of N's store rules, for the stored array and for the others. *)
Lemma setbytes_same : forall (mb mb2: ident -> Z -> Z) x o c w,
  (forall y j, (y = x /\ (o <= j /\ j < o + c) ->
                mb2 y j = NBase.zmod (NBase.zdiv w (NBase.pow2 (8 * (j - o)))) 256) /\
               (~ (y = x /\ (o <= j /\ j < o + c)) -> mb2 y j = mb y j)) ->
  forall j, (o <= j < o + c ->
             mb2 x j = NBase.zmod (NBase.zdiv w (NBase.pow2 (8 * (j - o)))) 256) /\
            (~ (o <= j < o + c) -> mb2 x j = mb x j).
Proof.
  intros mb mb2 x o c w SB j. split; intros J.
  - apply (proj1 (SB x j)). auto.
  - apply (proj2 (SB x j)). intros [_ J']. auto.
Qed.

Lemma setbytes_other : forall (mb mb2: ident -> Z -> Z) x o c w,
  (forall y j, (y = x /\ (o <= j /\ j < o + c) ->
                mb2 y j = NBase.zmod (NBase.zdiv w (NBase.pow2 (8 * (j - o)))) 256) /\
               (~ (y = x /\ (o <= j /\ j < o + c)) -> mb2 y j = mb y j)) ->
  forall y j, y <> x -> mb2 y j = mb y j.
Proof.
  intros mb mb2 x o c w SB y j NE. apply (proj2 (SB y j)). intros [E _]. auto.
Qed.

(** The store to an array: N's new bytes and the memory after CompCert's store are related, and
    the scalar globals keep their values. *)
Lemma store_array : forall m gv mb mb2 x n b o chunk v w c,
  globs_rel m gv -> arrays_rel m mb -> in_defs (prog_defs p) x (arr_def n) ->
  Genv.find_symbol ge x = Some b -> size_chunk chunk = c ->
  0 <= o -> o + c <= 8 * n -> (align_chunk chunk | o) -> o + c <= Ptrofs.modulus -> 0 <= w ->
  encode_val chunk v = inj_bytes (bytes_of_int (size_chunk_nat chunk) w) ->
  (forall y j, (y = x /\ (o <= j /\ j < o + c) ->
                mb2 y j = NBase.zmod (NBase.zdiv w (NBase.pow2 (8 * (j - o)))) 256) /\
               (~ (y = x /\ (o <= j /\ j < o + c)) -> mb2 y j = mb y j)) ->
  exists m', Mem.storev chunk m (Vptr b (Ptrofs.repr o)) v = Some m' /\
    globs_rel m' gv /\ arrays_rel m' mb2.
Proof.
  intros m gv mb mb2 x n b o chunk v w c G AR D S C O0 OH A OM W EV SB. subst c.
  destruct (AR x n D) as (b' & S' & B). assert (b' = b) by congruence. subst b'.
  destruct (store_le m b (mb x) (8 * n) o chunk v w (mb2 x) B O0 OH A OM W EV
              (setbytes_same mb mb2 x o _ w SB)) as (m' & SV & ST & B2).
  exists m'. split; auto. split.
  - eapply globs_store_other; [exact G | exact ST |]. intros y ty init b' Dy Sy Sy'.
    exact (array_not_scalar x n b D S y ty init b' Dy Sy Sy').
  - eapply arrays_store_same; [exact AR | exact D | exact S | exact ST | exact B2 |].
    intros y j NE. eapply setbytes_other; eauto.
Qed.

Lemma nexec_sound : forall ln gv mb s t ln' gv' mb' out,
  nexec (prog_defs p) ln gv mb s t ln' gv' mb' out ->
  forall le m, temps_rel le ln -> globs_rel m gv -> arrays_rel m mb ->
  exists le' m', Clight2.exec_stmt ge empty_env le m s t le' m' out /\
    temps_rel le' ln' /\ globs_rel m' gv' /\ arrays_rel m' mb'.
Proof.
  unfold Clight2.exec_stmt.
  induction 1; intros tle m0 R G AR.
  - (* skip *)
    exists tle, m0. split; [constructor | auto].
  - (* set *)
    exists (PTree.set x v tle), m0. split; [| split; auto; eapply upd_temps; eauto].
    apply exec_Sset. eapply neval_sound; eauto.
  - (* store to a scalar global *)
    destruct (store_global m0 gv mb x ty init v gv2 G AR H H0 H4 H5)
      as (b & chunk & m' & S & A & ST & G' & AR').
    exists tle, m'. split; [| auto].
    eapply exec_Sassign.
    + apply global_lvalue; eauto.
    + eapply neval_sound; eauto.
    + simpl. rewrite (has_type_typeof _ _ H2). eapply cast_ok_sound; eauto.
    + eapply assign_loc_value; eauto.
  - (* store of a word *)
    destruct (AR x n H) as (b & S & _). destruct (woff_range k) as [W0 [q Q]].
    destruct (store_array m0 gv mb mb2 x n b (woff k) Mint64 (Vlong w) (NBase.u64 w) 8
                G AR H S eq_refl W0 H2 ltac:(exists q; auto)
                ltac:(rewrite modulus_eq; rewrite woff_spec in *;
                      pose proof (Z.mod_pos_bound (Int64.unsigned k) 2305843009213693952);
                      lia)
                (proj1 (Int64.unsigned_range w)) eq_refl H6)
      as (m' & ST & G' & AR').
    exists tle, m'. split; [| auto].
    eapply exec_Sassign.
    + apply eval_Ederef. apply eval_elem; eauto. eapply neval_sound; eauto.
      apply has_type_typeof; auto.
    + eapply neval_sound; eauto.
    + simpl. rewrite (has_type_typeof _ _ H4). eapply cast_ok_sound; eauto.
    + eapply assign_loc_value. reflexivity.
      rewrite <- (Ptrofs.repr_unsigned (Ptrofs.repr _)). change (sizeof ge _) with 8.
      rewrite woff_unsigned. exact ST.
  - (* store of a byte *)
    destruct (AR x n H) as (b & S & _). pose proof (Int64.unsigned_range k) as RK.
    change Int64.modulus with 18446744073709551616 in RK.
    destruct (store_array m0 gv mb mb2 x n b (NBase.u64 k) Mint8unsigned (Vint c) (NBase.u32 c) 1
                G AR H S eq_refl ltac:(unfold NBase.u64; lia) ltac:(lia)
                (Z.divide_1_l _) ltac:(rewrite modulus_eq; unfold NBase.u64; lia)
                (proj1 (Int.unsigned_range c)) eq_refl H6)
      as (m' & ST & G' & AR').
    exists tle, m'. split; [| auto].
    eapply exec_Sassign.
    + apply eval_Ederef. apply eval_byte_elem; eauto. eapply neval_sound; eauto.
      apply has_type_typeof; auto.
    + eapply neval_sound; eauto.
    + simpl. rewrite (has_type_typeof _ _ H4). eapply cast_ok_sound; eauto.
    + eapply assign_loc_value. reflexivity. rewrite Z.mul_1_l. exact ST.
  - (* store to the cell of a word *)
    destruct (AR x n H) as (b & S & _).
    destruct (store_array m0 gv mb mb2 x n b 0 Mint64 (Vlong w) (NBase.u64 w) 8
                G AR H S eq_refl (Z.le_refl 0) ltac:(lia) (Z.divide_0_r _)
                ltac:(rewrite modulus_eq; lia) (proj1 (Int64.unsigned_range w)) eq_refl H4)
      as (m' & ST & G' & AR').
    exists tle, m'. split; [| auto].
    eapply exec_Sassign.
    + apply eval_Ederef. apply eval_base_cast; exact S.
    + eapply neval_sound; eauto.
    + simpl. rewrite (has_type_typeof _ _ H2). eapply cast_ok_sound; eauto.
    + eapply assign_loc_value. reflexivity. exact ST.
  - (* store to the cell of an int *)
    destruct (AR x n H) as (b & S & _).
    destruct (store_array m0 gv mb mb2 x n b 0 Mint32 (Vint c) (NBase.u32 c) 4
                G AR H S eq_refl (Z.le_refl 0) ltac:(lia) (Z.divide_0_r _)
                ltac:(rewrite modulus_eq; lia) (proj1 (Int.unsigned_range c)) eq_refl H4)
      as (m' & ST & G' & AR').
    exists tle, m'. split; [| auto].
    eapply exec_Sassign.
    + apply eval_Ederef. apply eval_base_cast; exact S.
    + eapply neval_sound; eauto.
    + simpl. rewrite (has_type_typeof _ _ H2). eapply cast_ok_sound; eauto.
    + eapply assign_loc_value. reflexivity. exact ST.
  - (* store to the cell of a double *)
    destruct (AR x n H) as (b & S & _).
    destruct (store_array m0 gv mb mb2 x n b 0 Mfloat64 (Vfloat f) (NBase.u64 (NBase.f64_bits f))
                8 G AR H S eq_refl (Z.le_refl 0) ltac:(lia) (Z.divide_0_r _)
                ltac:(rewrite modulus_eq; lia) (proj1 (Int64.unsigned_range _)) eq_refl H4)
      as (m' & ST & G' & AR').
    exists tle, m'. split; [| auto].
    eapply exec_Sassign.
    + apply eval_Ederef. apply eval_base_cast; exact S.
    + eapply neval_sound; eauto.
    + simpl. rewrite (has_type_typeof _ _ H2). eapply cast_ok_sound; eauto.
    + eapply assign_loc_value. reflexivity. exact ST.
  - (* store to the cell of a float *)
    destruct (AR x n H) as (b & S & _).
    destruct (store_array m0 gv mb mb2 x n b 0 Mfloat32 (Vsingle f)
                (NBase.u32 (NBase.f32_bits f)) 4 G AR H S eq_refl (Z.le_refl 0) ltac:(lia)
                (Z.divide_0_r _) ltac:(rewrite modulus_eq; lia) (proj1 (Int.unsigned_range _))
                eq_refl H4)
      as (m' & ST & G' & AR').
    exists tle, m'. split; [| auto].
    eapply exec_Sassign.
    + apply eval_Ederef. apply eval_base_cast; exact S.
    + eapply neval_sound; eauto.
    + simpl. rewrite (has_type_typeof _ _ H2). eapply cast_ok_sound; eauto.
    + eapply assign_loc_value. reflexivity. exact ST.
  - (* volatile store *)
    destruct (out_store x init i m0 H) as (b & S & EC).
    exists tle, m0. split; [| auto].
    change (Event_vstore Mint32 x (NBase.rptr 0) (EVint i) :: nil)
      with (Event_vstore Mint32 x Ptrofs.zero (EVint i) :: nil).
    change tle with (set_opttemp None Vundef tle).
    eapply exec_Sbuiltin; [| exact EC].
    econstructor.
    + apply eval_Eaddrof. apply global_lvalue; eauto.
    + apply ptr_cast.
    + econstructor; [eapply neval_sound; eauto | | constructor].
      rewrite (has_type_typeof _ _ H1). eapply cast_ok_sound; eauto.
  - (* volatile load of an element *)
    destruct (def_of _ _ H) as (b & S & _).
    pose proof (volatile_block _ _ _ _ H S) as V.
    exists (PTree.set t v tle), m0. split; [| split; [eapply upd_temps; eauto | auto]].
    change (PTree.set t v tle) with (set_opttemp (Some t) v tle).
    eapply exec_Sbuiltin; [| eapply vload_elem; eauto].
    econstructor; [| apply ptr_cast | constructor].
    apply eval_Eaddrof. apply eval_Ederef.
    rewrite <- (vload_size _ _ _ _ _ H2). apply eval_elem; auto.
    + eapply neval_sound; eauto.
    + apply has_type_typeof; auto.
  - (* volatile store to an element *)
    destruct (def_of _ _ H) as (b & S & _).
    pose proof (volatile_block _ _ _ _ H S) as V.
    exists tle, m0. split; [| auto].
    change tle with (set_opttemp None Vundef tle).
    eapply exec_Sbuiltin; [| eapply vstore_elem; eauto].
    econstructor; [| apply ptr_cast |].
    + apply eval_Eaddrof. apply eval_Ederef.
      change 4 with (sizeof ge (Tint I32 Unsigned (mk_attr true None))). apply eval_elem; auto.
      * eapply neval_sound; eauto.
      * apply has_type_typeof; auto.
    + econstructor; [eapply neval_sound; eauto | | constructor].
      rewrite (has_type_typeof _ _ H3). eapply cast_ok_sound; eauto.
  - (* call *)
    destruct (internal_funct _ _ H) as (b & S & F).
    destruct (bind_params_sound _ _ _ _ H5 _ (undef_temps_sound _ _ H4)) as (le1' & B & R1).
    destruct (IHnexec le1' m0 R1 G AR) as (le2' & m2 & E & R2 & G2 & AR2).
    exists (set_opttemp optid v tle), m2.
    split; [| split; [eapply set_opt_sound; eauto | auto]].
    eapply exec_Scall with (vf := Vptr b Ptrofs.zero).
    + reflexivity.
    + eapply eval_Elvalue. apply global_lvalue; eauto. apply deref_loc_reference; reflexivity.
    + eapply neval_list_sound; eauto.
    + simpl. rewrite dec_eq_true. exact F.
    + simpl. unfold type_of_function; simpl. rewrite (params_types_sound _ _ H0). reflexivity.
    + eapply eval_funcall_internal with (e := empty_env) (m1 := m0).
      * constructor; simpl.
        -- constructor.
        -- apply norepet_names_sound; auto.
        -- apply disjoint_names_sound; auto.
        -- constructor.
        -- exact B.
      * exact E.
      * apply result_ok_sound; auto.
      * reflexivity.
  - (* call of __builtin_fsqrt *)
    destruct (def_of _ _ H) as (b & S & F).
    exists (set_opttemp optid (Vfloat (Float.sqrt f)) tle), m0.
    split; [| split; [eapply set_opt_sound; eauto | auto]].
    eapply exec_Scall with (vf := Vptr b Ptrofs.zero).
    + reflexivity.
    + eapply eval_Elvalue. apply global_lvalue; eauto. apply deref_loc_reference; reflexivity.
    + eapply neval_list_sound; eauto.
    + simpl. rewrite dec_eq_true. apply Genv.find_funct_ptr_iff. exact F.
    + reflexivity.
    + apply eval_funcall_external. apply sqrt_call.
  - (* sequence, normal *)
    destruct (IHnexec1 tle m0 R G AR) as (le1' & m1 & E1 & R1 & G1 & AR1).
    destruct (IHnexec2 le1' m1 R1 G1 AR1) as (le2' & m2 & E2 & R2 & G2 & AR2).
    exists le2', m2. split; auto. eapply exec_Sseq_1; eauto.
  - (* sequence, abrupt *)
    destruct (IHnexec tle m0 R G AR) as (le1' & m1 & E1 & R1 & G1 & AR1).
    exists le1', m1. split; auto. eapply exec_Sseq_2; eauto.
  - (* if, true *)
    destruct (IHnexec tle m0 R G AR) as (le' & m' & E & R' & G' & AR').
    exists le', m'. split; auto. eapply exec_Sifthenelse with (b := true); eauto.
    + eapply neval_sound; eauto.
    + rewrite (has_type_typeof _ _ H0). eapply bool_ok_sound; eauto.
  - (* if, false *)
    destruct (IHnexec tle m0 R G AR) as (le' & m' & E & R' & G' & AR').
    exists le', m'. split; auto. eapply exec_Sifthenelse with (b := false); eauto.
    + eapply neval_sound; eauto.
    + rewrite (has_type_typeof _ _ H0). eapply bool_ok_sound; eauto.
  - (* return without a value *)
    exists tle, m0. split; [constructor | auto].
  - (* return with a value *)
    exists tle, m0. split; auto. rewrite <- (has_type_typeof _ _ H0).
    apply exec_Sreturn_some. eapply neval_sound; eauto.
  - exists tle, m0. split; [constructor | auto].
  - exists tle, m0. split; [constructor | auto].
  - (* loop, first part leaves *)
    destruct (IHnexec tle m0 R G AR) as (le1' & m1 & E1 & R1 & G1 & AR1).
    exists le1', m1. split; auto. eapply exec_Sloop_stop1; eauto. outcomes.
  - (* loop, second part leaves *)
    destruct (IHnexec1 tle m0 R G AR) as (le1' & m1 & E1 & R1 & G1 & AR1).
    destruct (IHnexec2 le1' m1 R1 G1 AR1) as (le2' & m2 & E2 & R2 & G2 & AR2).
    exists le2', m2. split; auto. eapply exec_Sloop_stop2; eauto; outcomes.
  - (* loop, next iteration *)
    destruct (IHnexec1 tle m0 R G AR) as (le1' & m1 & E1 & R1 & G1 & AR1).
    destruct (IHnexec2 le1' m1 R1 G1 AR1) as (le2' & m2 & E2 & R2 & G2 & AR2).
    destruct (IHnexec3 le2' m2 R2 G2 AR2) as (le3' & m3 & E3 & R3 & G3 & AR3).
    exists le3', m3. split; auto. eapply exec_Sloop_loop; eauto. outcomes.
Qed.

End PROGRAM.

(** * Programs *)

Lemma init_ok_aligned : forall init, init_ok init ->
  Genv.init_data_list_aligned 0 init /\ forall i o, ~ In (Init_addrof i o) init.
Proof.
  destruct 1; simpl; repeat split; try (intros i o H; intuition discriminate);
  try apply Z.divide_0_r.
Qed.

(** The bytes that [loadbytes] reads are the contents of the block. *)
Lemma loadbytes_get : forall m b o len bytes j,
  Mem.loadbytes m b o len = Some bytes -> o <= j < o + len ->
  In (ZMap.get j (Mem.mem_contents m) !! b) bytes.
Proof.
  intros m b o len bytes j L J. unfold Mem.loadbytes in L.
  destruct (Mem.range_perm_dec m b o (o + len) Cur Readable); inv L.
  apply Mem.getN_in. rewrite Z2Nat.id; lia.
Qed.

Lemma init_space_bytes : forall F V (ge: Genv.t F V) z mv,
  In mv (Genv.bytes_of_init_data_list ge (Init_space z :: nil)) -> mv = Byte Byte.zero.
Proof.
  intros F V ge z mv IN. simpl in IN. apply in_app_or in IN.
  destruct IN as [IN | []]. eapply repeat_spec; eauto.
Qed.

(** The initial memory of a program that [ninit] describes holds N's initial state. *)
Lemma init_state : forall p gv0 mb0, ninit (prog_defs p) gv0 mb0 ->
  list_norepet (map fst (prog_defs p)) /\
  exists m0, Genv.init_mem p = Some m0 /\ globs_rel p m0 gv0 /\ arrays_rel p m0 mb0.
Proof.
  intros p gv0 mb0 H. inversion H as [defs gv mb ND INIT GLOB ARR]; subst.
  pose proof (norepet_defs_sound _ ND) as NOREP. split; auto.
  destruct (Genv.init_mem_exists p) as [m0 IM].
  { intros id v Hin. destruct v as [ty init ro vol].
    destruct (init_ok_aligned init (INIT id ty init ro vol (In_in_defs _ _ _ Hin))) as [A N].
    split; auto. intros i o Hi. exfalso. eapply N; eauto. }
  exists m0. split; auto. split.
  - intros x ty init D S.
    destruct (GLOB x ty init D S) as (v & GI & E).
    destruct (def_of p NOREP _ _ D) as (b & SY & F).
    assert (FV : Genv.find_var_info (Genv.globalenv p) b = Some (mkglobvar ty init false false))
      by (apply Genv.find_var_info_iff; auto).
    exploit Genv.init_mem_characterization. eexact FV. eexact IM. intros (RP & _ & LS & LB).
    simpl in RP, LS. specialize (LS eq_refl). specialize (LB eq_refl).
    destruct GI.
    + simpl in RP, LS. destruct LS as [L _].
      exists b, Mint32, (Vint x0). do 4 (split; [first [exact SY | reflexivity | exact E |
        constructor] |]). split; [exact L |]. split; [| apply Z.divide_0_r].
      intros o O. apply RP. simpl in O. lia.
    + simpl in RP, LS. destruct LS as [L _].
      exists b, Mint64, (Vlong x0). do 4 (split; [first [exact SY | reflexivity | exact E |
        constructor] |]). split; [exact L |]. split; [| apply Z.divide_0_r].
      intros o O. apply RP. simpl in O. lia.
    + exists b, Mfloat64, (Vfloat (NBase.f64_of_bits (NBase.r64 0))).
      do 4 (split; [first [exact SY | reflexivity | exact E | constructor] |]).
      split.
      * rewrite (Mem.loadbytes_load Mfloat64 _ _ _ _ LB (Z.divide_0_r _)). reflexivity.
      * split; [| apply Z.divide_0_r]. intros o O. apply RP. simpl in O |- *. lia.
    + exists b, Mfloat32, (Vsingle (NBase.f32_of_bits (NBase.r32 0))).
      do 4 (split; [first [exact SY | reflexivity | exact E | constructor] |]).
      split.
      * rewrite (Mem.loadbytes_load Mfloat32 _ _ _ _ LB (Z.divide_0_r _)). reflexivity.
      * split; [| apply Z.divide_0_r]. intros o O. apply RP. simpl in O |- *. lia.
  - intros x n D.
    destruct (def_of p NOREP _ _ D) as (b & SY & F).
    assert (FV : Genv.find_var_info (Genv.globalenv p) b =
                 Some (mkglobvar (Tarray (Tlong Unsigned noattr) n noattr)
                         (Init_space (8 * n) :: nil) false false))
      by (apply Genv.find_var_info_iff; auto).
    exploit Genv.init_mem_characterization. eexact FV. eexact IM. intros (RP & _ & _ & LB).
    specialize (LB eq_refl).
    exists b. split; auto. intros j J.
    assert (SZ: 0 <= j < 0 + init_data_list_size (Init_space (8 * n) :: nil)).
    { change (init_data_list_size (Init_space (8 * n) :: nil)) with (Z.max (8 * n) 0 + 0).
      lia. }
    assert (Z0: mb0 x j = 0) by (apply (ARR x n j D); lia).
    rewrite Z0. split; [lia|]. split.
    + rewrite (init_space_bytes _ _ _ _ _ (loadbytes_get _ _ _ _ _ j LB SZ)). reflexivity.
    + apply RP. rewrite Z.add_0_l in SZ. exact SZ.
Qed.

Theorem nprog_sound : forall (p : Clight.program) t r,
  NSpec.nprog (prog_defs p) (prog_main p) t r ->
  ClightBigstep.Clight2.bigstep_program_terminates p t r.
Proof.
  intros p t r H. inversion H as [defs main temps body gv0 mb0 le0 t' le2 gv2 mb2 out r'
    INI MAIN UT EX RES]; subst.
  destruct (init_state p gv0 mb0 INI) as (NOREP & m0 & IM & G0 & A0).
  destruct (internal_funct p NOREP _ _ MAIN) as (b & S & F).
  destruct (nexec_sound p NOREP _ _ _ _ _ _ _ _ _ EX (create_undef_temps temps) m0
              (undef_temps_sound _ _ UT) G0 A0) as (le2' & m2 & E & _ & _).
  unfold Clight2.bigstep_program_terminates.
  apply bigstep_program_terminates_intro with b (Internal (mkfunction tint cc_default nil nil
    temps body)) m0 m2; auto.
  eapply eval_funcall_internal with (e := empty_env) (m1 := m0).
  - constructor; simpl; try constructor.
    red; simpl; intros; contradiction.
  - exact E.
  - apply result_ok_sound; auto.
  - reflexivity.
Qed.

(** * A main that runs forever *)

Lemma loop_in_entry : forall s init body post, loop_in s init body post ->
  Clight2Asm.loop_entry s init body post.
Proof.
  induction 1; [apply Clight2Asm.loop_entry_loop | apply Clight2Asm.loop_entry_seq_after; auto |
    apply Clight2Asm.loop_entry_seq_before; auto].
Qed.

Theorem nreacts_sound : forall (p : Clight.program) t0 W,
  NSpec.nreacts (prog_defs p) (prog_main p) t0 W -> Clight2Asm.loop_reacts p t0 W.
Proof.
  intros p t0 W H. inversion H as [defs main temps body gv0 mb0 le0 init lbody lpost t0' W' Inv
    NE INI MAIN UT LI [le1 [gv1 [mb1 [EX0 I0]]]] STEP]; subst.
  destruct (init_state p gv0 mb0 INI) as (NOREP & m0 & IM & G0 & A0).
  destruct (internal_funct p NOREP _ _ MAIN) as (b & S & F).
  split; [exact NE |].
  exists b, (mkfunction tint cc_default nil nil temps body), m0, m0, empty_env,
    (create_undef_temps temps), init, lbody, lpost,
    (fun n le m => exists ln gv mb, Inv n ln gv mb /\ temps_rel le ln /\ globs_rel p m gv /\
                                    arrays_rel p m mb).
  split; [exact IM |]. split; [exact S |]. split; [exact F |]. split; [reflexivity |].
  split; [apply loop_in_entry; exact LI |].
  split.
  { constructor; simpl; try constructor. red; simpl; intros; contradiction. }
  split.
  - destruct (nexec_sound p NOREP _ _ _ _ _ _ _ _ _ EX0 (create_undef_temps temps) m0
                (undef_temps_sound _ _ UT) G0 A0) as (le' & m' & E & R & G & A).
    exists le', m'. split; [exact E |]. exists le1, gv1, mb1. auto.
  - intros n le m (ln & gv & mb & IN & R & G & A).
    destruct (STEP n ln gv mb IN) as (le2 & gv2 & mb2 & EX & IN2).
    destruct (nexec_sound p NOREP _ _ _ _ _ _ _ _ _ EX le m R G A)
      as (le' & m' & E & R' & G' & A').
    exists le', m'. split; [exact E |]. rewrite Nat.add_1_r. exists le2, gv2, mb2. auto.
Qed.

(** * Values read *)

Lemma nreads_from : forall s c t, NSpec.nreads s c t ->
  forall tp ev u, t = tp ++ ev :: u ->
  match ev with
  | Event_syscall _ _ _ => False
  | Event_vload _ _ _ v => v = EVint (s (c + Clight2Asm.count_vloads tp)%nat)
  | _ => True
  end.
Proof.
  induction 1; intros tp evt u E.
  - destruct tp; discriminate.
  - destruct tp as [| e tp]; simpl in E; inv E.
    + rewrite Nat.add_0_r. reflexivity.
    + specialize (IHnreads tp evt u eq_refl).
      replace (c + Clight2Asm.count_vloads (Event_vload ch x o (EVint (s c)) :: tp))%nat
        with (S c + Clight2Asm.count_vloads tp)%nat; [exact IHnreads |].
      unfold Clight2Asm.count_vloads. simpl. lia.
  - destruct tp as [| e tp]; simpl in E; inv E.
    + exact I.
    + specialize (IHnreads tp evt u eq_refl).
      replace (c + Clight2Asm.count_vloads (Event_vstore ch x o ev :: tp))%nat
        with (c + Clight2Asm.count_vloads tp)%nat; [exact IHnreads | reflexivity].
Qed.

Theorem nreads_reads : forall sigma t, NSpec.nreads sigma O t -> Clight2Asm.reads sigma t.
Proof.
  intros sigma t H tp ev u E. exact (nreads_from _ _ _ H tp ev u E).
Qed.
