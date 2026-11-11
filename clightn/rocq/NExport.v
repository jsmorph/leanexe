(* The program of the Coq file that clightgen writes and the program inside clightgen, in
   CompCert 3.18's Clight with parameters as temporaries.  clightgen prints a statement with
   stmt of export/ExportClight.ml (lines 88 to 136), which drops a Sskip on either side of a
   sequence and prints two forms of loop as Swhile, whose definition (cfrontend/Clight.v,
   line 119) the file reads back.  export_stmt transcribes stmt, its cases on sequences as tests
   of Sskip, and export_terminates shows that
   a terminating run of the file's program is a run of the program inside clightgen with the same
   trace and result.  export_rel relates a printed statement to the statement it was printed
   from, each step a core relation wrapped in sequences with Sskip.  The model is
   LeanExe/Native/Proof/Export.lean, which proves the same of the Lean copy of Clight. *)
From Coq Require Import ZArith Lia.
Require Import Coqlib Maps Integers Values AST Memory Events Globalenvs Linking.
Require Import Ctypes Cop Clight ClightBigstep.

Definition is_skip (s: statement) : bool :=
  match s with Sskip => true | _ => false end.

Fixpoint export_stmt (s: statement) : statement :=
  match s with
  | Ssequence s1 s2 =>
      if is_skip s1 then export_stmt s2
      else if is_skip s2 then export_stmt s1
      else Ssequence (export_stmt s1) (export_stmt s2)
  | Sifthenelse e s1 s2 => Sifthenelse e (export_stmt s1) (export_stmt s2)
  | Sloop s1 s2 =>
      match s1, s2 with
      | Ssequence x s3, Sskip =>
          match x with
          | Sifthenelse e Sskip Sbreak => Swhile e (export_stmt s3)
          | Ssequence Sskip (Sifthenelse e Sskip Sbreak) => Swhile e (export_stmt s3)
          | _ => Sloop (export_stmt s1) (export_stmt s2)
          end
      | _, _ => Sloop (export_stmt s1) (export_stmt s2)
      end
  | Sswitch e ls => Sswitch e (export_lbl ls)
  | Slabel l s1 => Slabel l (export_stmt s1)
  | _ => s
  end
with export_lbl (ls: labeled_statements) : labeled_statements :=
  match ls with
  | LSnil => LSnil
  | LScons c s ls' => LScons c (export_stmt s) (export_lbl ls')
  end.

Definition export_function (f: function) : function :=
  mkfunction f.(fn_return) f.(fn_callconv) f.(fn_params) f.(fn_vars) f.(fn_temps)
    (export_stmt f.(fn_body)).

Definition export_fundef (fd: fundef) : fundef :=
  match fd with
  | Internal f => Internal (export_function f)
  | External ef targs tres cc => External ef targs tres cc
  end.

Definition export_defs (defs: list (ident * globdef fundef type)) :
    list (ident * globdef fundef type) :=
  map (transform_program_globdef export_fundef) defs.

(** * The relation of printed statements *)

Definition atomic (s: statement) : Prop :=
  match s with
  | Ssequence _ _ | Sifthenelse _ _ _ | Sloop _ _ | Sswitch _ _ | Slabel _ _ => False
  | _ => True
  end.

Inductive wrap (c: statement) : statement -> Prop :=
  | wrap_refl : wrap c c
  | wrap_left : forall s, wrap c s -> wrap c (Ssequence Sskip s)
  | wrap_right : forall s, wrap c s -> wrap c (Ssequence s Sskip).

Inductive export_rel : statement -> statement -> Prop :=
  | er_atom : forall c s, atomic c -> wrap c s -> export_rel c s
  | er_seq : forall a b s1 s2 s, export_rel a s1 -> export_rel b s2 ->
      wrap (Ssequence s1 s2) s -> export_rel (Ssequence a b) s
  | er_ite : forall e a b s1 s2 s, export_rel a s1 -> export_rel b s2 ->
      wrap (Sifthenelse e s1 s2) s -> export_rel (Sifthenelse e a b) s
  | er_loop : forall a b s1 s2 s, export_rel a s1 -> export_rel b s2 ->
      wrap (Sloop s1 s2) s -> export_rel (Sloop a b) s
  | er_switch : forall e la ls s, export_lrel la ls -> wrap (Sswitch e ls) s ->
      export_rel (Sswitch e la) s
  | er_label : forall l a s1 s, export_rel a s1 -> wrap (Slabel l s1) s ->
      export_rel (Slabel l a) s
with export_lrel : labeled_statements -> labeled_statements -> Prop :=
  | el_nil : export_lrel LSnil LSnil
  | el_cons : forall c a s la ls, export_rel a s -> export_lrel la ls ->
      export_lrel (LScons c a la) (LScons c s ls).

Lemma wrap_trans : forall c s, wrap c s -> forall s', wrap s s' -> wrap c s'.
Proof. intros c s W s' W'. induction W'; auto; constructor; auto. Qed.

Lemma export_rel_wrap : forall a s, export_rel a s -> forall s', wrap s s' -> export_rel a s'.
Proof.
  intros a s R s' W. destruct R; [apply er_atom | eapply er_seq | eapply er_ite | eapply er_loop
    | eapply er_switch | eapply er_label]; eauto using wrap_trans.
Qed.

Lemma export_rel_left : forall a s, export_rel a s -> export_rel a (Ssequence Sskip s).
Proof. intros. eapply export_rel_wrap; eauto. repeat constructor. Qed.

Lemma export_rel_right : forall a s, export_rel a s -> export_rel a (Ssequence s Sskip).
Proof. intros. eapply export_rel_wrap; eauto. repeat constructor. Qed.

Lemma export_rel_atom : forall s, atomic s -> export_rel s s.
Proof. intros. apply er_atom; auto. constructor. Qed.

Fixpoint ssize (s: statement) : nat :=
  match s with
  | Ssequence a b | Sloop a b | Sifthenelse _ a b => S (ssize a + ssize b)
  | Slabel _ a => S (ssize a)
  | Sswitch _ ls => S (lssize ls)
  | _ => O
  end
with lssize (ls: labeled_statements) : nat :=
  match ls with
  | LSnil => O
  | LScons _ s ls' => S (ssize s + lssize ls')
  end.

Lemma is_skip_true : forall s, is_skip s = true -> s = Sskip.
Proof. destruct s; simpl; congruence. Qed.

Lemma seq_rel : forall s1 s2, export_rel (export_stmt s1) s1 -> export_rel (export_stmt s2) s2 ->
  export_rel (export_stmt (Ssequence s1 s2)) (Ssequence s1 s2).
Proof.
  intros s1 s2 H1 H2. simpl.
  destruct (is_skip s1) eqn:A; [apply is_skip_true in A; subst; apply export_rel_left; auto |].
  destruct (is_skip s2) eqn:B; [apply is_skip_true in B; subst; apply export_rel_right; auto |].
  eapply er_seq; eauto. constructor.
Qed.

Lemma while_rel : forall e s, export_rel (export_stmt s) s ->
  export_rel (Ssequence (Sifthenelse e Sskip Sbreak) (export_stmt s))
             (Ssequence (Sifthenelse e Sskip Sbreak) s).
Proof.
  intros. eapply er_seq; [| eauto | constructor].
  eapply er_ite; [apply export_rel_atom; exact I | apply export_rel_atom; exact I | constructor].
Qed.

Lemma loop_rel : forall s1 s2, export_rel (export_stmt s1) s1 -> export_rel (export_stmt s2) s2 ->
  (forall s, (ssize s < ssize s1)%nat -> export_rel (export_stmt s) s) ->
  export_rel (export_stmt (Sloop s1 s2)) (Sloop s1 s2).
Proof.
  intros s1 s2 H1 H2 IH.
  assert (GEN: export_stmt (Sloop s1 s2) = Sloop (export_stmt s1) (export_stmt s2) ->
               export_rel (export_stmt (Sloop s1 s2)) (Sloop s1 s2)).
  { intros E. rewrite E. eapply er_loop; eauto. constructor. }
  destruct s1 as [| | | | | x s | | | | | | | |]; try (apply GEN; reflexivity).
  destruct s2; try (apply GEN; reflexivity).
  destruct x as [| | | | | u w | e c d | | | | | | |]; try (apply GEN; reflexivity).
  - destruct u; try (apply GEN; reflexivity).
    destruct w as [| | | | | | e c d | | | | | | |]; try (apply GEN; reflexivity).
    destruct c; try (apply GEN; reflexivity). destruct d; try (apply GEN; reflexivity).
    eapply er_loop; [| apply export_rel_atom; exact I | constructor].
    eapply er_seq; [| apply IH; simpl; lia | constructor].
    apply export_rel_left. eapply er_ite;
      [apply export_rel_atom; exact I | apply export_rel_atom; exact I | constructor].
  - destruct c; try (apply GEN; reflexivity). destruct d; try (apply GEN; reflexivity).
    eapply er_loop; [| apply export_rel_atom; exact I | constructor].
    apply while_rel. apply IH. simpl. lia.
Qed.

Lemma export_rel_size : forall n s, (ssize s < n)%nat -> export_rel (export_stmt s) s.
Proof.
  induction n; intros s L; [lia |].
  destruct s; try (apply export_rel_atom; exact I); simpl in L.
  - apply seq_rel; apply IHn; lia.
  - eapply er_ite; [apply IHn; lia | apply IHn; lia | constructor].
  - apply loop_rel; [apply IHn; lia | apply IHn; lia | intros; apply IHn; lia].
  - eapply er_switch; [| constructor].
    revert L; induction l; simpl; intros L; constructor; [apply IHn; lia | apply IHl; lia].
  - eapply er_label; [apply IHn; lia | constructor].
Qed.

Lemma export_stmt_rel : forall s, export_rel (export_stmt s) s.
Proof. intros. apply (export_rel_size (S (ssize s))). lia. Qed.

(** * Runs of printed statements *)

Section EXEC.

Variables ge ge': genv.
Hypothesis CENV: genv_cenv ge' = genv_cenv ge.
Hypothesis SENV: Senv.equiv ge' ge.
Hypothesis FUNCT: forall v fd', Genv.find_funct ge' v = Some fd' ->
  exists fd, Genv.find_funct ge v = Some fd /\ fd' = export_fundef fd.

Lemma symb : forall id, Genv.find_symbol ge' id = Genv.find_symbol ge id.
Proof. intros. destruct SENV as (A & _ & _). symmetry. apply A. Qed.

Lemma eval_export : forall e le m,
  (forall a v, eval_expr ge' e le m a v -> eval_expr ge e le m a v) /\
  (forall a b ofs bf, eval_lvalue ge' e le m a b ofs bf -> eval_lvalue ge e le m a b ofs bf).
Proof.
  intros e le m. apply eval_expr_lvalue_ind; intros; try rewrite CENV in *;
  try rewrite symb in *;
  first [ solve [econstructor; eauto] | solve [eapply eval_Evar_global; eauto]
        | solve [eapply eval_Efield_union; eauto] ].
Qed.

Lemma eval_exprlist_export : forall e le m al tys vs,
  eval_exprlist ge' e le m al tys vs -> eval_exprlist ge e le m al tys vs.
Proof.
  induction 1; econstructor; eauto. apply (proj1 (eval_export e le m)); auto.
Qed.

Lemma wrap_exec : forall c s, wrap c s -> forall e le m t le' m' out,
  exec_stmt function_entry2 ge e le m c t le' m' out ->
  exec_stmt function_entry2 ge e le m s t le' m' out.
Proof.
  induction 1; intros e le m t le' m' out E; auto.
  - change t with (E0 ** t). eapply exec_Sseq_1; eauto. constructor.
  - assert (O: out = Out_normal \/ out <> Out_normal)
      by (destruct out; first [left; reflexivity | right; discriminate]).
    destruct O as [-> | N].
    + rewrite <- (E0_right t). eapply exec_Sseq_1; eauto. constructor.
    + eapply exec_Sseq_2; eauto.
Qed.

Lemma select_case_export : forall n la ls, export_lrel la ls ->
  match select_switch_case n la, select_switch_case n ls with
  | Some la', Some ls' => export_lrel la' ls'
  | None, None => True
  | _, _ => False
  end.
Proof.
  induction 1; simpl; auto. destruct c as [c|]; auto.
  destruct (zeq c n); auto. constructor; auto.
Qed.

Lemma select_default_export : forall la ls, export_lrel la ls ->
  export_lrel (select_switch_default la) (select_switch_default ls).
Proof. induction 1; simpl; [constructor|]. destruct c; auto. constructor; auto. Qed.

Lemma seq_of_export : forall la ls, export_lrel la ls ->
  export_rel (seq_of_labeled_statement la) (seq_of_labeled_statement ls).
Proof.
  induction 1; simpl. apply export_rel_atom; exact I.
  eapply er_seq; eauto. constructor.
Qed.

Lemma select_export : forall n la ls, export_lrel la ls ->
  export_rel (seq_of_labeled_statement (select_switch n la))
             (seq_of_labeled_statement (select_switch n ls)).
Proof.
  intros n la ls R. apply seq_of_export. unfold select_switch.
  pose proof (select_case_export n la ls R) as C.
  destruct (select_switch_case n la), (select_switch_case n ls); try contradiction; auto.
  apply select_default_export; auto.
Qed.

Lemma export_type : forall fd, type_of_fundef (export_fundef fd) = type_of_fundef fd.
Proof. destruct fd; reflexivity. Qed.

Lemma alloc_variables_export : forall e m vars e' m',
  alloc_variables ge' e m vars e' m' -> alloc_variables ge e m vars e' m'.
Proof. induction 1; econstructor; eauto. rewrite <- CENV; auto. Qed.

Lemma blocks_export : forall e, blocks_of_env ge' e = blocks_of_env ge e.
Proof.
  intros. unfold blocks_of_env. apply map_ext. intros [id [b ty]].
  unfold block_of_binding. rewrite CENV. reflexivity.
Qed.

Ltac transfer :=
  repeat match goal with
  | H: eval_expr ge' ?e ?le ?m _ _ |- _ => apply (proj1 (eval_export e le m)) in H
  | H: eval_lvalue ge' ?e ?le ?m _ _ _ _ |- _ => apply (proj2 (eval_export e le m)) in H
  | H: eval_exprlist ge' _ _ _ _ _ _ |- _ => apply eval_exprlist_export in H
  | H: assign_loc (genv_cenv ge') _ _ _ _ _ _ _ |- _ => rewrite CENV in H
  | H: alloc_variables ge' _ _ _ _ _ |- _ => apply alloc_variables_export in H
  end.

Lemma exec_export :
  (forall e le m s' t le' m' out, exec_stmt function_entry2 ge' e le m s' t le' m' out ->
     forall s, export_rel s' s -> exec_stmt function_entry2 ge e le m s t le' m' out) /\
  (forall m fd' vargs t m' vres, eval_funcall function_entry2 ge' m fd' vargs t m' vres ->
     forall fd, fd' = export_fundef fd -> eval_funcall function_entry2 ge m fd vargs t m' vres).
Proof.
  apply exec_stmt_funcall_ind; intros;
  try (match goal with R: export_rel _ _ |- _ =>
         inversion R; subst; try contradiction; eapply wrap_exec; [eassumption |] end);
  transfer.
  all: first
    [ solve [econstructor; eauto]
    | solve [eapply exec_Sloop_stop1; eauto]
    | solve [eapply exec_Sloop_stop2; eauto]
    | solve [eapply exec_Sloop_loop; eauto using er_loop, wrap_refl]
    | idtac ].
  - destruct (FUNCT _ _ H2) as (fd & F & ->).
    eapply exec_Scall; eauto. rewrite <- export_type. auto.
  - eapply exec_Sbuiltin; eauto. eapply external_call_symbols_preserved; eauto.
  - eapply exec_Sifthenelse; [eauto | eauto | destruct b; eauto].
  - eapply exec_Sswitch; eauto. apply H2. apply select_export; auto.
  - destruct fd as [f0 |]; simpl in H4; inv H4. inv H. transfer.
    eapply eval_funcall_internal; eauto.
    + econstructor; eauto.
    + apply H1. apply export_stmt_rel.
    + rewrite <- blocks_export. auto.
  - destruct fd; simpl in H0; inv H0.
    apply eval_funcall_external. eapply external_call_symbols_preserved; eauto.
Qed.

End EXEC.

(** * Programs *)

Lemma funct_export : forall (p p': Clight.program),
  match_program (fun _ f tf => tf = export_fundef f) eq (program_of_program p)
    (program_of_program p') ->
  forall b fd', Genv.find_funct_ptr (globalenv p') b = Some fd' ->
  exists fd, Genv.find_funct_ptr (globalenv p) b = Some fd /\ fd' = export_fundef fd.
Proof.
  intros p p' M b fd' F.
  pose proof (Genv.find_def_match_2 M b) as O.
  apply Genv.find_funct_ptr_iff in F.
  change (@Genv.find_def fundef type (@Genv.globalenv fundef type (program_of_program p')) b =
          Some (Gfun fd')) in F.
  rewrite F in O.
  destruct (@Genv.find_def fundef type (@Genv.globalenv fundef type (program_of_program p)) b)
    as [g|] eqn:D; inv O.
  inv H1. exists f1. split; auto.
  apply Genv.find_funct_ptr_iff. exact D.
Qed.

Theorem export_terminates : forall (p p': Clight.program) t r,
  prog_defs p' = export_defs (prog_defs p) ->
  prog_main p' = prog_main p ->
  prog_public p' = prog_public p ->
  prog_types p' = prog_types p ->
  ClightBigstep.Clight2.bigstep_program_terminates p' t r ->
  ClightBigstep.Clight2.bigstep_program_terminates p t r.
Proof.
  intros p p' t r DEFS MAIN PUB TYPES BT.
  assert (TP: program_of_program p' = transform_program export_fundef (program_of_program p)).
  { unfold program_of_program, transform_program; simpl. rewrite DEFS, MAIN, PUB. reflexivity. }
  assert (M: match_program (fun _ f tf => tf = export_fundef f) eq
               (program_of_program p) (program_of_program p')).
  { rewrite TP. apply match_transform_program. }
  assert (CENV: genv_cenv (globalenv p') = genv_cenv (globalenv p)).
  { simpl. pose proof (prog_comp_env_eq p) as E. pose proof (prog_comp_env_eq p') as E'.
    rewrite TYPES in E'. congruence. }
  assert (SENV: Senv.equiv (globalenv p') (globalenv p)).
  { pose proof (Genv.senv_transf M) as (A & P & C). split; [|split]; intros;
    [rewrite A | rewrite P | rewrite C]; reflexivity. }
  assert (FUNCT: forall v fd', Genv.find_funct (globalenv p') v = Some fd' ->
            exists fd, Genv.find_funct (globalenv p) v = Some fd /\ fd' = export_fundef fd).
  { intros v fd' F. destruct v; try discriminate. simpl in *.
    destruct (Ptrofs.eq_dec i Ptrofs.zero); try discriminate.
    destruct (funct_export p p' M b fd' F) as (fd & F1 & ->). exists fd. split; auto. }
  unfold Clight2.bigstep_program_terminates in *. inv BT.
  destruct (Genv.init_mem_exists p) as [m0' IM'].
  { intros id v Hin. assert (IN: In (id, Gvar v) (prog_defs p')).
    { rewrite DEFS. unfold export_defs. change (id, Gvar v) with
        (transform_program_globdef export_fundef (id, @Gvar fundef type v)).
      apply in_map; auto. }
    exploit Genv.init_mem_inversion; [eassumption | exact IN |]. intros (A & Bs). split; auto.
    intros i o Hi. destruct (Bs i o Hi) as (b' & S). exists b'.
    rewrite <- (Genv.find_symbol_transf M). exact S. }
  assert (m0' = m0).
  { pose proof (Genv.init_mem_transf M IM') as X. change (Genv.init_mem p' = Some m0') in X.
    congruence. }
  subst m0'.
  destruct (funct_export p p' M b f H1) as (fd & F1 & ->).
  apply bigstep_program_terminates_intro with b fd m0 m1; auto.
  - rewrite <- (Genv.find_symbol_transf M). rewrite <- MAIN. exact H0.
  - rewrite <- export_type. auto.
  - eapply (proj2 (exec_export (globalenv p) (globalenv p') CENV SENV FUNCT)); eauto.
Qed.
