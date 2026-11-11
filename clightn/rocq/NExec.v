(* The soundness of the reference semantics N (clightn/N.nsx) for CompCert 3.18's Clight with
   parameters as temporaries: every derivation of N's statement relation, from temporaries and
   a memory related to N's, is a derivation of Clight2.exec_stmt, and nprog_sound carries N's
   program judgment to Clight2.bigstep_program_terminates.  The leaf relations are sound by the
   statements of NProof.v.  The proofs need Archi.ptr64 = true, which holds on AArch64. *)
From Coq Require Import ZArith Lia.
Require Import Coqlib Maps Integers Floats Values AST Memory Events Globalenvs.
Require Import Ctypes Cop Clight ClightBigstep.
Require NBase.
Require Import NSpec NProof.

Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

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
        | exact (proj2 (ge_ui_ui ce _ _ _ m) H) ].

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
        | exact (proj2 (cast_si_si _ _ m) H) ].

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

(** * Accesses at offset 0 *)

Lemma chunk_in_range : forall chunk, 0 + size_chunk chunk <= Ptrofs.modulus.
Proof.
  intros. assert (size_chunk chunk <= 8) by (destruct chunk; simpl; lia).
  change Ptrofs.modulus with 18446744073709551616. lia.
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

(** The scalar globals of N are in memory: each holds its value of N, which a load of its
    type's chunk at offset 0 reads, and the memory allows the store of that chunk. *)
Definition globs_rel (m: mem) (gv: ident -> option val) : Prop :=
  forall x ty init, in_defs (prog_defs p) x (Gvar (mkglobvar ty init false false)) -> scalar ty ->
  exists b chunk v, Genv.find_symbol ge x = Some b /\ access_mode ty = By_value chunk /\
    gv x = Some v /\ gval ty v /\ Mem.load chunk m b 0 = Some v /\
    Mem.valid_access m chunk b 0 Writable.

Lemma gval_load_result : forall ty v chunk, gval ty v -> access_mode ty = By_value chunk ->
  Val.load_result chunk v = v.
Proof. destruct 1; simpl; intros A; inv A; reflexivity. Qed.

Lemma global_lvalue : forall x ty le m b,
  Genv.find_symbol ge x = Some b ->
  eval_lvalue ge empty_env le m (Evar x ty) b Ptrofs.zero Full.
Proof. intros. apply eval_Evar_global; auto. Qed.

Lemma neval_sound : forall ln gv a v, neval (prog_defs p) ln gv a v ->
  forall le m, temps_rel le ln -> globs_rel m gv -> eval_expr ge empty_env le m a v.
Proof.
  induction 1; intros le0 m R G.
  - apply eval_Econst_int.
  - apply eval_Econst_long.
  - apply eval_Econst_float.
  - apply eval_Econst_single.
  - apply eval_Etempvar. rewrite R. auto.
  - destruct (G x ty init H H0) as (b & chunk & v' & S & A & E & _ & L & _).
    assert (v' = v) by congruence. subst v'.
    eapply eval_Elvalue. apply global_lvalue; eauto.
    eapply deref_loc_value; [exact A | rewrite loadv_zero; exact L].
  - eapply eval_Ebinop; eauto.
    rewrite (has_type_typeof _ _ H0), (has_type_typeof _ _ H2). eapply binop_ok_sound; eauto.
  - eapply eval_Ecast; eauto. rewrite (has_type_typeof _ _ H0). eapply cast_ok_sound; eauto.
Qed.

Lemma neval_list_sound : forall ln gv al tys vs, neval_list (prog_defs p) ln gv al tys vs ->
  forall le m, temps_rel le ln -> globs_rel m gv -> eval_exprlist ge empty_env le m al tys vs.
Proof.
  induction 1; intros le0 m R G; econstructor; eauto.
  - eapply neval_sound; eauto.
  - rewrite (has_type_typeof _ _ H0). eapply cast_ok_sound; eauto.
Qed.

Lemma store_global : forall m gv x ty init v gv2,
  globs_rel m gv -> in_defs (prog_defs p) x (Gvar (mkglobvar ty init false false)) ->
  scalar ty -> gval ty v ->
  (forall y, (y = x -> gv2 y = Some v) /\ (y <> x -> gv2 y = gv y)) ->
  exists b chunk m', Genv.find_symbol ge x = Some b /\ access_mode ty = By_value chunk /\
    Mem.storev chunk m (Vptr b Ptrofs.zero) v = Some m' /\ globs_rel m' gv2.
Proof.
  intros m gv x ty init v gv2 G D S V U.
  destruct (G x ty init D S) as (b & chunk & v0 & SY & A & _ & _ & _ & VA).
  destruct (Mem.valid_access_store m chunk b 0 v VA) as [m' ST].
  exists b, chunk, m'. split; auto. split; auto. split; [rewrite storev_zero; exact ST|].
  intros y tyy inity Dy Sy.
  destruct (G y tyy inity Dy Sy) as (b' & chunk' & v' & SY' & A' & E' & V' & L' & VA').
  exists b', chunk'. destruct (peq y x).
  - subst y. assert (mkglobvar tyy inity false false = mkglobvar ty init false false).
    { assert (Gvar (mkglobvar tyy inity false false) =
              @Gvar fundef type (mkglobvar ty init false false))
        by (eapply in_defs_unique; eauto). congruence. }
    inv H. assert (b' = b) by congruence. subst b'. rewrite A in A'. inv A'.
    exists v. split; auto. split; auto. split; [apply (proj1 (U x)); auto|]. split; auto.
    split.
    + rewrite (Mem.load_store_same _ _ _ _ _ _ ST). f_equal. eapply gval_load_result; eauto.
    + eapply Mem.store_valid_access_1; eauto.
  - exists v'. split; auto. split; auto. split; [rewrite (proj2 (U y)); auto|]. split; auto.
    split.
    + rewrite (Mem.load_store_other _ _ _ _ _ _ ST); auto. left.
      eapply Genv.global_addresses_distinct; eauto.
    + eapply Mem.store_valid_access_1; eauto.
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
  - change (Genv.block_is_volatile ge b = true). unfold Genv.block_is_volatile.
    rewrite (proj2 (Genv.find_var_info_iff _ _ _) F). reflexivity.
  - exact S.
  - constructor.
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

Lemma nexec_sound : forall ln gv s t ln' gv' out, nexec (prog_defs p) ln gv s t ln' gv' out ->
  forall le m, temps_rel le ln -> globs_rel m gv ->
  exists le' m', Clight2.exec_stmt ge empty_env le m s t le' m' out /\
                 temps_rel le' ln' /\ globs_rel m' gv'.
Proof.
  unfold Clight2.exec_stmt.
  induction 1; intros tle m0 R G.
  - (* skip *)
    exists tle, m0. split; [constructor | auto].
  - (* set *)
    exists (PTree.set x v tle), m0. split; [| split; auto; eapply upd_temps; eauto].
    apply exec_Sset. eapply neval_sound; eauto.
  - (* store to a scalar global *)
    destruct (store_global m0 gv x ty init v gv2 G H H0 H4 H5)
      as (b & chunk & m' & S & A & ST & G').
    exists tle, m'. split; [| auto].
    eapply exec_Sassign.
    + apply global_lvalue; eauto.
    + eapply neval_sound; eauto.
    + simpl. rewrite (has_type_typeof _ _ H2). eapply cast_ok_sound; eauto.
    + eapply assign_loc_value; eauto.
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
  - (* call *)
    destruct (internal_funct _ _ H) as (b & S & F).
    destruct (bind_params_sound _ _ _ _ H5 _ (undef_temps_sound _ _ H4)) as (le1' & B & R1).
    destruct (IHnexec le1' m0 R1 G) as (le2' & m2 & E & R2 & G2).
    exists (set_opttemp optid v tle), m2. split; [| split; [eapply set_opt_sound; eauto | auto]].
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
  - (* sequence, normal *)
    destruct (IHnexec1 tle m0 R G) as (le1' & m1 & E1 & R1 & G1).
    destruct (IHnexec2 le1' m1 R1 G1) as (le2' & m2 & E2 & R2 & G2).
    exists le2', m2. split; auto. eapply exec_Sseq_1; eauto.
  - (* sequence, abrupt *)
    destruct (IHnexec tle m0 R G) as (le1' & m1 & E1 & R1 & G1).
    exists le1', m1. split; auto. eapply exec_Sseq_2; eauto.
  - (* if, true *)
    destruct (IHnexec tle m0 R G) as (le' & m' & E & R' & G').
    exists le', m'. split; auto. eapply exec_Sifthenelse with (b := true); eauto.
    + eapply neval_sound; eauto.
    + rewrite (has_type_typeof _ _ H0). eapply bool_ok_sound; eauto.
  - (* if, false *)
    destruct (IHnexec tle m0 R G) as (le' & m' & E & R' & G').
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
    destruct (IHnexec tle m0 R G) as (le1' & m1 & E1 & R1 & G1).
    exists le1', m1. split; auto. eapply exec_Sloop_stop1; eauto. outcomes.
  - (* loop, second part leaves *)
    destruct (IHnexec1 tle m0 R G) as (le1' & m1 & E1 & R1 & G1).
    destruct (IHnexec2 le1' m1 R1 G1) as (le2' & m2 & E2 & R2 & G2).
    exists le2', m2. split; auto. eapply exec_Sloop_stop2; eauto; outcomes.
  - (* loop, next iteration *)
    destruct (IHnexec1 tle m0 R G) as (le1' & m1 & E1 & R1 & G1).
    destruct (IHnexec2 le1' m1 R1 G1) as (le2' & m2 & E2 & R2 & G2).
    destruct (IHnexec3 le2' m2 R2 G2) as (le3' & m3 & E3 & R3 & G3).
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

Theorem nprog_sound : forall (p : Clight.program) t r,
  NSpec.nprog (prog_defs p) (prog_main p) t r ->
  ClightBigstep.Clight2.bigstep_program_terminates p t r.
Proof.
  intros p t r H. inversion H as [defs main temps body gv0 le0 t' le2 gv2 out r'
    ND INIT GLOB MAIN UT EX RES]; subst.
  pose proof (norepet_defs_sound _ ND) as NOREP.
  destruct (Genv.init_mem_exists p) as [m0 IM].
  { intros id v Hin. destruct v as [ty init ro vol].
    destruct (init_ok_aligned init (INIT id ty init ro vol (In_in_defs _ _ _ Hin))) as [A N].
    split; auto. intros i o Hi. exfalso. eapply N; eauto. }
  assert (G0 : globs_rel p m0 gv0).
  { intros x ty init D S.
    destruct (GLOB x ty init D S) as (v & GI & E).
    destruct (def_of p NOREP _ _ D) as (b & SY & F).
    assert (FV : Genv.find_var_info (Genv.globalenv p) b = Some (mkglobvar ty init false false))
      by (apply Genv.find_var_info_iff; auto).
    exploit Genv.init_mem_characterization. eexact FV. eexact IM. intros (RP & _ & LS & _).
    simpl in RP, LS. specialize (LS eq_refl).
    destruct GI; simpl in RP, LS; destruct LS as [L _].
    - exists b, Mint32, (Vint x0). do 4 (split; [first [exact SY | reflexivity | exact E |
        constructor] |]). split; [exact L |]. split; [| apply Z.divide_0_r].
      intros o O. apply RP. simpl in O. lia.
    - exists b, Mint64, (Vlong x0). do 4 (split; [first [exact SY | reflexivity | exact E |
        constructor] |]). split; [exact L |]. split; [| apply Z.divide_0_r].
      intros o O. apply RP. simpl in O. lia. }
  destruct (internal_funct p NOREP _ _ MAIN) as (b & S & F).
  destruct (nexec_sound p NOREP _ _ _ _ _ _ _ EX (create_undef_temps temps) m0
              (undef_temps_sound _ _ UT) G0) as (le2' & m2 & E & _ & _).
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
