(* An evaluator for CompCert 3.18's big-step semantics of Clight with function_entry2, the
   module Clight2 of cfrontend/ClightBigstep.v, and its soundness: a result of the evaluator is
   an execution of that semantics.  Clight2Asm.v carries a termination of the semantics to the
   assembly program that CompCert produces.

   MemExec restates the operations of common/Memory.v and common/Globalenvs.v whose definitions
   do not reduce under vm_compute: those that decide permissions over a range with
   Mem.range_perm_dec, which recurs on an opaque proof of well-foundedness, and store_zeros,
   defined by well-founded recursion.  Each restatement is proved equal to CompCert's operation,
   and init_mem_eq states it of the initial memory.

   Expressions evaluate by structural recursion.  exec_fn and call_fn execute statements and
   calls with fuel, which each statement and each call consumes; OutOfFuel reports that the fuel
   ran out, and Stuck that the evaluator applied no rule at the point it reached.  The evaluator
   omits rules of the semantics: bit-field accesses (deref_loc_bitfield, assign_loc_bitfield),
   assignment of structs and unions (assign_loc_copy), volatile accesses whose event is a
   pointer (ev_match_ptr), and external calls other than built-in functions, EF_vload, and
   EF_vstore.  A program that reaches one of them is Stuck, so Stuck does not show that the
   semantics has no execution.

   The semantics lets a volatile load return any value of its type.  The evaluator takes the
   event value of a load of a chunk at an offset of a volatile global from the parameter vload,
   as CompCert's reference interpreter takes it from its world (cfrontend/Cexec.v,
   do_volatile_load).  run and run_program pass world_vload, which reads the value from the
   initial memory of world_program, where the interpreter's world starts (driver/Interp.ml,
   world_vload and world_program).

   exec_call_sound states soundness for every vload, run_sound for a call from the initial
   memory, and run_program_sound concludes bigstep_program_terminates.  rocq/check.sh checks
   the file against a CompCert 3.18 tree whose proofs are built. *)

From Coq Require Import String List ZArith FunInd.
Require Import Coqlib Maps Errors Integers Floats Values AST Memdata Memory Events Globalenvs.
Require Import Ctypes Cop Clight ClightBigstep.
Require Builtins0 Builtins.

Module MemExec.

Local Transparent Mem.load Mem.store Mem.free.

Fixpoint perm_range (m: mem) (b: block) (lo: Z) (n: nat) (k: perm_kind) (p: permission)
    : bool :=
  match n with
  | O => true
  | S n' => proj_sumbool (Mem.perm_dec m b lo k p) && perm_range m b (lo + 1) n' k p
  end.

Lemma perm_range_spec:
  forall m b k p n lo,
  perm_range m b lo n k p = true <->
  (forall ofs, lo <= ofs < lo + Z.of_nat n -> Mem.perm m b ofs k p).
Proof.
  induction n; intros lo; simpl.
  - split; intros; auto. lia.
  - rewrite andb_true_iff, IHn. split.
    + intros [A B] ofs R. destruct (zeq ofs lo).
      * subst. destruct (Mem.perm_dec m b lo k p); auto. discriminate.
      * apply B. lia.
    + intros H. split.
      * destruct (Mem.perm_dec m b lo k p); auto. elim n0. apply H. lia.
      * intros. apply H. lia.
Qed.

Lemma to_nat_range:
  forall lo hi ofs, lo <= ofs < lo + Z.of_nat (Z.to_nat (hi - lo)) <-> lo <= ofs < hi.
Proof.
  intros. destruct (zle 0 (hi - lo)).
  - rewrite Z2Nat.id by auto. lia.
  - rewrite Z_to_nat_neg by lia. simpl. lia.
Qed.

Definition range_perm_dec (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) :
  {Mem.range_perm m b lo hi k p} + {~ Mem.range_perm m b lo hi k p}.
Proof.
  destruct (perm_range m b lo (Z.to_nat (hi - lo)) k p) eqn:E; [left | right];
  unfold Mem.range_perm.
  - intros ofs R. apply (proj1 (perm_range_spec _ _ _ _ _ _) E). apply to_nat_range; auto.
  - intro H. rewrite (proj2 (perm_range_spec m b k p (Z.to_nat (hi - lo)) lo)) in E.
    + discriminate.
    + intros ofs R. apply H. apply to_nat_range; auto.
Defined.

Definition align_dec (chunk: memory_chunk) (ofs: Z) :
  {(align_chunk chunk | ofs)} + {~ (align_chunk chunk | ofs)}.
Proof.
  assert (align_chunk chunk <> 0) by (generalize (align_chunk_pos chunk); lia).
  destruct (zeq (ofs mod align_chunk chunk) 0) as [E|E]; [left | right].
  - apply Z.mod_divide; auto.
  - intro D. apply E. apply Z.mod_divide; auto.
Defined.

Definition valid_access_dec (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z)
    (p: permission) :
  {Mem.valid_access m chunk b ofs p} + {~ Mem.valid_access m chunk b ofs p}.
Proof.
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Cur p).
  - destruct (align_dec chunk ofs).
    + left; split; auto.
    + right; intros [_ A]; contradiction.
  - right; intros [R _]; contradiction.
Defined.

Definition load (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) : option val :=
  if valid_access_dec m chunk b ofs Readable
  then Some (decode_val chunk
               (Mem.getN (size_chunk_nat chunk) ofs (PMap.get b (Mem.mem_contents m))))
  else None.

Lemma load_eq: forall chunk m b ofs, load chunk m b ofs = Mem.load chunk m b ofs.
Proof.
  intros. unfold load, Mem.load.
  destruct (valid_access_dec m chunk b ofs Readable);
  destruct (Mem.valid_access_dec m chunk b ofs Readable); auto; contradiction.
Qed.

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match addr with
  | Vptr b ofs =>
      if zle (Ptrofs.unsigned ofs + size_chunk chunk) Ptrofs.modulus
      then load chunk m b (Ptrofs.unsigned ofs)
      else None
  | _ => None
  end.

Lemma loadv_eq: forall chunk m addr, loadv chunk m addr = Mem.loadv chunk m addr.
Proof.
  intros. unfold loadv, Mem.loadv. destruct addr; auto. rewrite load_eq; auto.
Qed.

Program Definition store (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val)
    : option mem :=
  if valid_access_dec m chunk b ofs Writable then
    Some (Mem.mkmem (PMap.set b (Mem.setN (encode_val chunk v) ofs
                                   (PMap.get b (Mem.mem_contents m)))
                              (Mem.mem_contents m))
                    (Mem.mem_access m) (Mem.nextblock m) _ _ _)
  else None.
Next Obligation. apply Mem.access_max. Qed.
Next Obligation. apply Mem.nextblock_noaccess; auto. Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b0 b).
  - rewrite Mem.setN_default. apply Mem.contents_default.
  - apply Mem.contents_default.
Qed.

Lemma store_eq: forall chunk m b ofs v, store chunk m b ofs v = Mem.store chunk m b ofs v.
Proof.
  intros. unfold store, Mem.store.
  destruct (valid_access_dec m chunk b ofs Writable);
  destruct (Mem.valid_access_dec m chunk b ofs Writable); try contradiction; auto.
  f_equal. apply Mem.mkmem_ext; auto.
Qed.

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs =>
      if zle (Ptrofs.unsigned ofs + size_chunk chunk) Ptrofs.modulus
      then store chunk m b (Ptrofs.unsigned ofs) v
      else None
  | _ => None
  end.

Lemma storev_eq: forall chunk m addr v, storev chunk m addr v = Mem.storev chunk m addr v.
Proof.
  intros. unfold storev, Mem.storev. destruct addr; auto. rewrite store_eq; auto.
Qed.

Definition free (m: mem) (b: block) (lo hi: Z) : option mem :=
  if range_perm_dec m b lo hi Cur Freeable
  then Some (Mem.unchecked_free m b lo hi)
  else None.

Lemma free_eq: forall m b lo hi, free m b lo hi = Mem.free m b lo hi.
Proof.
  intros. unfold free, Mem.free.
  destruct (range_perm_dec m b lo hi Cur Freeable);
  destruct (Mem.range_perm_dec m b lo hi Cur Freeable); auto; contradiction.
Qed.

Fixpoint free_list (m: mem) (l: list (block * Z * Z)) : option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

Lemma free_list_eq: forall l m, free_list m l = Mem.free_list m l.
Proof.
  induction l as [|[[b lo] hi] l IH]; intros; simpl; auto.
  rewrite free_eq. destruct (Mem.free m b lo hi); auto.
Qed.

Program Definition drop_perm (m: mem) (b: block) (lo hi: Z) (p: permission) : option mem :=
  if range_perm_dec m b lo hi Cur Freeable then
    Some (Mem.mkmem (Mem.mem_contents m)
                    (PMap.set b
                       (fun ofs k => if zle lo ofs && zlt ofs hi then Some p
                                     else PMap.get b (Mem.mem_access m) ofs k)
                       (Mem.mem_access m))
                    (Mem.nextblock m) _ _ _)
  else None.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b).
  - subst b0. destruct (zle lo ofs && zlt ofs hi).
    + simpl. constructor.
    + apply Mem.access_max.
  - apply Mem.access_max.
Qed.
Next Obligation.
  match goal with
  | R: Mem.range_perm _ _ _ _ _ _, N: ~ Plt _ _ |- _ =>
      rename R into RP; specialize (Mem.nextblock_noaccess m _ ofs k N); intros NOACC
  end.
  rewrite PMap.gsspec. destruct (peq b0 b); auto. subst b0.
  destruct (zle lo ofs); destruct (zlt ofs hi); simpl; auto.
  assert (P: Mem.perm m b ofs k Freeable).
  { apply Mem.perm_cur. apply RP. lia. }
  unfold Mem.perm in P. rewrite NOACC in P. contradiction.
Qed.
Next Obligation. apply Mem.contents_default. Qed.

Lemma drop_perm_eq: forall m b lo hi p, drop_perm m b lo hi p = Mem.drop_perm m b lo hi p.
Proof.
  intros. unfold drop_perm, Mem.drop_perm.
  destruct (range_perm_dec m b lo hi Cur Freeable);
  destruct (Mem.range_perm_dec m b lo hi Cur Freeable); try contradiction; auto.
  f_equal. apply Mem.mkmem_ext; auto.
Qed.

Fixpoint store_zeros_n (m: mem) (b: block) (p: Z) (n: nat) : option mem :=
  match n with
  | O => Some m
  | S n' =>
      match store Mint8unsigned m b p Vzero with
      | Some m' => store_zeros_n m' b (p + 1) n'
      | None => None
      end
  end.

Definition store_zeros (m: mem) (b: block) (p n: Z) : option mem :=
  store_zeros_n m b p (Z.to_nat n).

Lemma store_zeros_eq: forall m b p n, store_zeros m b p n = Globalenvs.store_zeros m b p n.
Proof.
  intros. functional induction (Globalenvs.store_zeros m b p n); unfold store_zeros.
  - rewrite Z_to_nat_neg by lia. auto.
  - replace (Z.to_nat n) with (S (Z.to_nat (n - 1))).
    + simpl. rewrite store_eq, e0. exact IHo.
    + rewrite <- Z2Nat.inj_succ by lia. f_equal. lia.
  - replace (Z.to_nat n) with (S (Z.to_nat (n - 1))).
    + simpl. rewrite store_eq, e0. auto.
    + rewrite <- Z2Nat.inj_succ by lia. f_equal. lia.
Qed.

Section INITMEM.

Context {F V: Type}.
Variable ge: Genv.t F V.

Definition store_init_data (m: mem) (b: block) (p: Z) (id: init_data) : option mem :=
  match id with
  | Init_int8 n => store Mint8unsigned m b p (Vint n)
  | Init_int16 n => store Mint16unsigned m b p (Vint n)
  | Init_int32 n => store Mint32 m b p (Vint n)
  | Init_int64 n => store Mint64 m b p (Vlong n)
  | Init_float32 n => store Mfloat32 m b p (Vsingle n)
  | Init_float64 n => store Mfloat64 m b p (Vfloat n)
  | Init_addrof symb ofs =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b' => store Mptr m b p (Vptr b' ofs)
      end
  | Init_space n => Some m
  end.

Lemma store_init_data_eq:
  forall m b p id, store_init_data m b p id = Genv.store_init_data ge m b p id.
Proof.
  intros. destruct id; simpl; try apply store_eq; auto.
  destruct (Genv.find_symbol ge i); auto. apply store_eq.
Qed.

Fixpoint store_init_data_list (m: mem) (b: block) (p: Z) (idl: list init_data)
    : option mem :=
  match idl with
  | nil => Some m
  | id :: idl' =>
      match store_init_data m b p id with
      | None => None
      | Some m' => store_init_data_list m' b (p + init_data_size id) idl'
      end
  end.

Lemma store_init_data_list_eq:
  forall idl m b p, store_init_data_list m b p idl = Genv.store_init_data_list ge m b p idl.
Proof.
  induction idl; intros; simpl; auto.
  rewrite store_init_data_eq. destruct (Genv.store_init_data ge m b p a); auto.
Qed.

Definition alloc_global (m: mem) (idg: ident * globdef F V) : option mem :=
  match idg with
  | (id, Gfun f) =>
      let (m1, b) := Mem.alloc m 0 1 in
      drop_perm m1 b 0 1 Nonempty
  | (id, Gvar v) =>
      let init := v.(gvar_init) in
      let sz := init_data_list_size init in
      let (m1, b) := Mem.alloc m 0 sz in
      match store_zeros m1 b 0 sz with
      | None => None
      | Some m2 =>
          match store_init_data_list m2 b 0 init with
          | None => None
          | Some m3 => drop_perm m3 b 0 sz (Genv.perm_globvar v)
          end
      end
  end.

Lemma alloc_global_eq: forall m idg, alloc_global m idg = Genv.alloc_global ge m idg.
Proof.
  intros m [id [f|v]]; simpl; destruct (Mem.alloc _ _ _) as [m1 b].
  - apply drop_perm_eq.
  - rewrite store_zeros_eq. destruct (Globalenvs.store_zeros m1 b 0 _); auto.
    rewrite store_init_data_list_eq. destruct (Genv.store_init_data_list ge _ b 0 _); auto.
    apply drop_perm_eq.
Qed.

Fixpoint alloc_globals (m: mem) (gl: list (ident * globdef F V)) : option mem :=
  match gl with
  | nil => Some m
  | g :: gl' =>
      match alloc_global m g with
      | None => None
      | Some m' => alloc_globals m' gl'
      end
  end.

Lemma alloc_globals_eq: forall gl m, alloc_globals m gl = Genv.alloc_globals ge m gl.
Proof.
  induction gl; intros; simpl; auto.
  rewrite alloc_global_eq. destruct (Genv.alloc_global ge m a); auto.
Qed.

End INITMEM.

Definition init_mem {F V: Type} (p: AST.program F V) : option mem :=
  alloc_globals (Genv.globalenv p) Mem.empty p.(AST.prog_defs).

Lemma init_mem_eq: forall F V (p: AST.program F V), init_mem p = Genv.init_mem p.
Proof.
  intros. apply alloc_globals_eq.
Qed.

End MemExec.

Inductive result (A: Type) : Type :=
  | Done (a: A)
  | Stuck
  | OutOfFuel.

Arguments Done {A}.
Arguments Stuck {A}.
Arguments OutOfFuel {A}.

Section EVAL.

Variable ge: genv.
Variable vload: memory_chunk -> ident -> ptrofs -> option eventval.

(** Expressions *)

Section EXPR.

Variable e: env.
Variable le: temp_env.
Variable m: mem.

Definition var_loc (id: ident) (ty: type) : option block :=
  match e ! id with
  | Some (l, ty') => if type_eq ty ty' then Some l else None
  | None => Genv.find_symbol ge id
  end.

Definition field_loc (ta: type) (i: ident) (l: block) (ofs: ptrofs)
    : option (block * ptrofs * bitfield) :=
  match ta with
  | Tstruct id _ =>
      match (genv_cenv ge) ! id with
      | Some co =>
          match field_offset ge i (co_members co) with
          | OK (delta, bf) => Some (l, Ptrofs.add ofs (Ptrofs.repr delta), bf)
          | Error _ => None
          end
      | None => None
      end
  | Tunion id _ =>
      match (genv_cenv ge) ! id with
      | Some co =>
          match union_field_offset ge i (co_members co) with
          | OK (delta, bf) => Some (l, Ptrofs.add ofs (Ptrofs.repr delta), bf)
          | Error _ => None
          end
      | None => None
      end
  | _ => None
  end.

Definition deref_loc_fn (ty: type) (l: block) (ofs: ptrofs) (bf: bitfield) : option val :=
  match bf with
  | Full =>
      match access_mode ty with
      | By_value chunk => MemExec.loadv chunk m (Vptr l ofs)
      | By_reference => Some (Vptr l ofs)
      | By_copy => Some (Vptr l ofs)
      | By_nothing => None
      end
  | Bits _ _ _ _ => None
  end.

Fixpoint eval_expr_fn (a: expr) : option val :=
  match a with
  | Econst_int i _ => Some (Vint i)
  | Econst_float f _ => Some (Vfloat f)
  | Econst_single f _ => Some (Vsingle f)
  | Econst_long i _ => Some (Vlong i)
  | Etempvar id _ => le ! id
  | Eaddrof a1 _ =>
      match a1 with
      | Evar id ty =>
          match var_loc id ty with
          | Some l => Some (Vptr l Ptrofs.zero)
          | None => None
          end
      | Ederef a2 _ =>
          match eval_expr_fn a2 with
          | Some (Vptr l ofs) => Some (Vptr l ofs)
          | _ => None
          end
      | Efield a2 i _ =>
          match eval_expr_fn a2 with
          | Some (Vptr l ofs) =>
              match field_loc (typeof a2) i l ofs with
              | Some (l', ofs', Full) => Some (Vptr l' ofs')
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  | Eunop op a1 _ =>
      match eval_expr_fn a1 with
      | Some v1 => sem_unary_operation op v1 (typeof a1) m
      | None => None
      end
  | Ebinop op a1 a2 _ =>
      match eval_expr_fn a1, eval_expr_fn a2 with
      | Some v1, Some v2 => sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m
      | _, _ => None
      end
  | Ecast a1 ty =>
      match eval_expr_fn a1 with
      | Some v1 => sem_cast v1 (typeof a1) ty m
      | None => None
      end
  | Esizeof ty1 _ => Some (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
  | Ealignof ty1 _ => Some (Vptrofs (Ptrofs.repr (alignof ge ty1)))
  | Evar id ty =>
      match var_loc id ty with
      | Some l => deref_loc_fn ty l Ptrofs.zero Full
      | None => None
      end
  | Ederef a1 ty =>
      match eval_expr_fn a1 with
      | Some (Vptr l ofs) => deref_loc_fn ty l ofs Full
      | _ => None
      end
  | Efield a1 i ty =>
      match eval_expr_fn a1 with
      | Some (Vptr l ofs) =>
          match field_loc (typeof a1) i l ofs with
          | Some (l', ofs', bf) => deref_loc_fn ty l' ofs' bf
          | None => None
          end
      | _ => None
      end
  end.

Definition eval_lvalue_fn (a: expr) : option (block * ptrofs * bitfield) :=
  match a with
  | Evar id ty =>
      match var_loc id ty with
      | Some l => Some (l, Ptrofs.zero, Full)
      | None => None
      end
  | Ederef a1 _ =>
      match eval_expr_fn a1 with
      | Some (Vptr l ofs) => Some (l, ofs, Full)
      | _ => None
      end
  | Efield a1 i _ =>
      match eval_expr_fn a1 with
      | Some (Vptr l ofs) => field_loc (typeof a1) i l ofs
      | _ => None
      end
  | _ => None
  end.

Fixpoint eval_exprlist_fn (al: list expr) (tyl: list type) : option (list val) :=
  match al, tyl with
  | nil, nil => Some nil
  | a :: bl, ty :: tyl' =>
      match eval_expr_fn a with
      | Some v1 =>
          match sem_cast v1 (typeof a) ty m with
          | Some v2 =>
              match eval_exprlist_fn bl tyl' with
              | Some vl => Some (v2 :: vl)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | _, _ => None
  end.

Lemma var_loc_sound:
  forall id ty l, var_loc id ty = Some l -> eval_lvalue ge e le m (Evar id ty) l Ptrofs.zero Full.
Proof.
  unfold var_loc; intros. destruct (e ! id) as [[l' ty']|] eqn:E.
  - destruct (type_eq ty ty'); inv H. apply eval_Evar_local; auto.
  - apply eval_Evar_global; auto.
Qed.

Lemma field_loc_sound:
  forall a i ty l ofs l' ofs' bf,
  eval_expr ge e le m a (Vptr l ofs) ->
  field_loc (typeof a) i l ofs = Some (l', ofs', bf) ->
  eval_lvalue ge e le m (Efield a i ty) l' ofs' bf.
Proof.
  unfold field_loc; intros.
  destruct (typeof a) eqn:T; try discriminate;
  destruct ((genv_cenv ge) ! i0) as [co|] eqn:C; try discriminate.
  - destruct (field_offset ge i (co_members co)) as [[delta bf']|] eqn:F; inv H0.
    eapply eval_Efield_struct; eauto.
  - destruct (union_field_offset ge i (co_members co)) as [[delta bf']|] eqn:F; inv H0.
    eapply eval_Efield_union; eauto.
Qed.

Lemma deref_loc_fn_sound:
  forall ty l ofs bf v, deref_loc_fn ty l ofs bf = Some v -> deref_loc ty m l ofs bf v.
Proof.
  unfold deref_loc_fn; intros. destruct bf; try discriminate.
  destruct (access_mode ty) eqn:A; inv H.
  - eapply deref_loc_value; eauto. rewrite <- MemExec.loadv_eq; auto.
  - apply deref_loc_reference; auto.
  - apply deref_loc_copy; auto.
Qed.

Lemma eval_expr_lvalue_fn_sound:
  forall a,
  (forall v, eval_expr_fn a = Some v -> eval_expr ge e le m a v) /\
  (forall l ofs bf, eval_lvalue_fn a = Some (l, ofs, bf) -> eval_lvalue ge e le m a l ofs bf).
Proof.
  induction a as [i ty|f ty|f ty|i ty|id ty|id ty|a IHa ty|a IHa ty|op a IHa ty
                 |op a1 IHa1 a2 IHa2 ty|a IHa ty|a IHa fid ty|t1 ty|t1 ty];
  split; intros; simpl in H; try discriminate.
  - inv H. constructor.
  - inv H. constructor.
  - inv H. constructor.
  - inv H. constructor.
  - destruct (var_loc id ty) as [l|] eqn:L; try discriminate.
    eapply eval_Elvalue. apply var_loc_sound; eauto. apply deref_loc_fn_sound; auto.
  - destruct (var_loc id ty) as [l'|] eqn:L; inv H. apply var_loc_sound; auto.
  - constructor; auto.
  - destruct (eval_expr_fn a) as [[| | | | |l ofs]|] eqn:A; try discriminate.
    eapply eval_Elvalue. apply eval_Ederef. apply IHa; eauto.
    apply deref_loc_fn_sound; auto.
  - destruct (eval_expr_fn a) as [[| | | | |l' ofs']|] eqn:A; inv H.
    apply eval_Ederef. apply IHa; auto.
  - destruct IHa as [_ IHl].
    destruct a as [| | | |id ty'|id ty'|a2 ty2|a2 ty2|op a2 ty2|op a2 a3 ty2|a2 ty2
                  |a2 fid ty2| |]; try discriminate.
    + destruct (var_loc id ty') as [l|] eqn:L; inv H. constructor. apply var_loc_sound; auto.
    + destruct (eval_expr_fn a2) as [[| | | | |l ofs]|] eqn:A; inv H.
      constructor. apply IHl. simpl. rewrite A. auto.
    + destruct (eval_expr_fn a2) as [[| | | | |l ofs]|] eqn:A; try discriminate.
      destruct (field_loc (typeof a2) fid l ofs) as [[[l' ofs'] []]|] eqn:F; inv H.
      constructor. apply IHl. simpl. rewrite A. auto.
  - destruct (eval_expr_fn a) as [v1|] eqn:A; try discriminate.
    econstructor; eauto. apply IHa; auto.
  - destruct (eval_expr_fn a1) as [v1|] eqn:A1; try discriminate.
    destruct (eval_expr_fn a2) as [v2|] eqn:A2; try discriminate.
    econstructor; eauto. apply IHa1; auto. apply IHa2; auto.
  - destruct (eval_expr_fn a) as [v1|] eqn:A; try discriminate.
    econstructor; eauto. apply IHa; auto.
  - destruct (eval_expr_fn a) as [[| | | | |l ofs]|] eqn:A; try discriminate.
    destruct (field_loc (typeof a) fid l ofs) as [[[l' ofs'] bf']|] eqn:F; try discriminate.
    eapply eval_Elvalue. eapply field_loc_sound; eauto. apply IHa; auto.
    apply deref_loc_fn_sound; auto.
  - destruct (eval_expr_fn a) as [[| | | | |l' ofs']|] eqn:A; try discriminate.
    eapply field_loc_sound; eauto. apply IHa; auto.
  - inv H. constructor.
  - inv H. constructor.
Qed.

Lemma eval_expr_fn_sound:
  forall a v, eval_expr_fn a = Some v -> eval_expr ge e le m a v.
Proof.
  intros. apply (eval_expr_lvalue_fn_sound a); auto.
Qed.

Lemma eval_lvalue_fn_sound:
  forall a l ofs bf, eval_lvalue_fn a = Some (l, ofs, bf) -> eval_lvalue ge e le m a l ofs bf.
Proof.
  intros. apply (eval_expr_lvalue_fn_sound a); auto.
Qed.

Lemma eval_exprlist_fn_sound:
  forall al tyl vl, eval_exprlist_fn al tyl = Some vl -> eval_exprlist ge e le m al tyl vl.
Proof.
  induction al as [|a al IH]; destruct tyl as [|ty tyl]; simpl; intros; try discriminate.
  - inv H. constructor.
  - destruct (eval_expr_fn a) as [v1|] eqn:A; try discriminate.
    destruct (sem_cast v1 (typeof a) ty m) as [v2|] eqn:C; try discriminate.
    destruct (eval_exprlist_fn al tyl) as [vl'|] eqn:L; inv H.
    econstructor; eauto. apply eval_expr_fn_sound; auto.
Qed.

End EXPR.

(** External calls *)

Definition val_of_eventval_fn (ev: eventval) (t: typ) : option val :=
  match ev, t with
  | EVint i, AST.Tint => Some (Vint i)
  | EVlong i, AST.Tlong => Some (Vlong i)
  | EVfloat f, AST.Tfloat => Some (Vfloat f)
  | EVsingle f, AST.Tsingle => Some (Vsingle f)
  | _, _ => None
  end.

Definition eventval_of_val_fn (v: val) (t: typ) : option eventval :=
  match v, t with
  | Vint i, AST.Tint => Some (EVint i)
  | Vlong i, AST.Tlong => Some (EVlong i)
  | Vfloat f, AST.Tfloat => Some (EVfloat f)
  | Vsingle f, AST.Tsingle => Some (EVsingle f)
  | _, _ => None
  end.

Lemma val_of_eventval_fn_sound:
  forall ev t v, val_of_eventval_fn ev t = Some v -> eventval_match ge ev t v.
Proof.
  intros. destruct ev, t; inv H; constructor.
Qed.

Lemma eventval_of_val_fn_sound:
  forall v t ev, eventval_of_val_fn v t = Some ev -> eventval_match ge ev t v.
Proof.
  intros. destruct v, t; inv H; constructor.
Qed.

Definition volatile_load_fn (chunk: memory_chunk) (m: mem) (b: block) (ofs: ptrofs)
    : option (trace * val) :=
  if Genv.block_is_volatile ge b then
    match Genv.invert_symbol ge b with
    | Some id =>
        match vload chunk id ofs with
        | Some ev =>
            match val_of_eventval_fn ev (type_of_chunk chunk) with
            | Some v => Some (Event_vload chunk id ofs ev :: nil, Val.load_result chunk v)
            | None => None
            end
        | None => None
        end
    | None => None
    end
  else
    match MemExec.loadv chunk m (Vptr b ofs) with
    | Some v => Some (E0, v)
    | None => None
    end.

Definition volatile_store_fn (chunk: memory_chunk) (m: mem) (b: block) (ofs: ptrofs)
    (v: val) : option (trace * mem) :=
  if Genv.block_is_volatile ge b then
    match Genv.invert_symbol ge b with
    | Some id =>
        match eventval_of_val_fn (Val.load_result chunk v) (type_of_chunk chunk) with
        | Some ev => Some (Event_vstore chunk id ofs ev :: nil, m)
        | None => None
        end
    | None => None
    end
  else
    match MemExec.storev chunk m (Vptr b ofs) v with
    | Some m' => Some (E0, m')
    | None => None
    end.

Definition builtin_fn (name: string) (sg: signature) (vargs: list val) (m: mem)
    : option (trace * val * mem) :=
  match Builtins.lookup_builtin_function name sg with
  | Some bf =>
      match Builtins0.bs_sem _ (Builtins.builtin_function_sem bf) vargs with
      | Some vres => Some (E0, vres, m)
      | None => None
      end
  | None => None
  end.

Definition external_call_fn (ef: external_function) (vargs: list val) (m: mem)
    : option (trace * val * mem) :=
  match ef with
  | EF_builtin name sg => builtin_fn name sg vargs m
  | EF_runtime name sg => builtin_fn name sg vargs m
  | EF_vload chunk =>
      match vargs with
      | Vptr b ofs :: nil =>
          match volatile_load_fn chunk m b ofs with
          | Some (t, v) => Some (t, v, m)
          | None => None
          end
      | _ => None
      end
  | EF_vstore chunk =>
      match vargs with
      | Vptr b ofs :: v :: nil =>
          match volatile_store_fn chunk m b ofs v with
          | Some (t, m') => Some (t, Vundef, m')
          | None => None
          end
      | _ => None
      end
  | _ => None
  end.

Lemma builtin_fn_sound:
  forall name sg vargs m t vres m',
  builtin_fn name sg vargs m = Some (t, vres, m') ->
  builtin_or_external_sem name sg ge vargs m t vres m'.
Proof.
  unfold builtin_fn, builtin_or_external_sem; intros.
  destruct (Builtins.lookup_builtin_function name sg) as [bf|]; try discriminate.
  destruct (Builtins0.bs_sem _ (Builtins.builtin_function_sem bf) vargs) as [v|] eqn:S; inv H.
  constructor; auto.
Qed.

Lemma volatile_load_fn_sound:
  forall chunk m b ofs t v,
  volatile_load_fn chunk m b ofs = Some (t, v) -> volatile_load ge chunk m b ofs t v.
Proof.
  unfold volatile_load_fn; intros.
  destruct (Genv.block_is_volatile ge b) eqn:VOL.
  - destruct (Genv.invert_symbol ge b) as [id|] eqn:INV; try discriminate.
    destruct (vload chunk id ofs) as [ev|]; try discriminate.
    destruct (val_of_eventval_fn ev (type_of_chunk chunk)) as [v'|] eqn:EV; inv H.
    apply volatile_load_vol; auto.
    + apply Genv.invert_find_symbol; auto.
    + apply val_of_eventval_fn_sound; auto.
  - destruct (MemExec.loadv chunk m (Vptr b ofs)) as [v'|] eqn:LD; inv H.
    apply volatile_load_nonvol; auto. rewrite <- MemExec.loadv_eq; auto.
Qed.

Lemma volatile_store_fn_sound:
  forall chunk m b ofs v t m',
  volatile_store_fn chunk m b ofs v = Some (t, m') -> volatile_store ge chunk m b ofs v t m'.
Proof.
  unfold volatile_store_fn; intros.
  destruct (Genv.block_is_volatile ge b) eqn:VOL.
  - destruct (Genv.invert_symbol ge b) as [id|] eqn:INV; try discriminate.
    destruct (eventval_of_val_fn (Val.load_result chunk v) (type_of_chunk chunk))
      as [ev|] eqn:EV; inv H.
    apply volatile_store_vol; auto.
    + apply Genv.invert_find_symbol; auto.
    + apply eventval_of_val_fn_sound; auto.
  - destruct (MemExec.storev chunk m (Vptr b ofs) v) as [m''|] eqn:ST; inv H.
    apply volatile_store_nonvol; auto. rewrite <- MemExec.storev_eq; auto.
Qed.

Lemma external_call_fn_sound:
  forall ef vargs m t vres m',
  external_call_fn ef vargs m = Some (t, vres, m') -> external_call ef ge vargs m t vres m'.
Proof.
  intros. destruct ef; simpl in H; try discriminate.
  - apply builtin_fn_sound; auto.
  - apply builtin_fn_sound; auto.
  - destruct vargs as [|[| | | | |b ofs] [|]]; try discriminate.
    destruct (volatile_load_fn chunk m b ofs) as [[t' v]|] eqn:L; inv H.
    constructor. apply volatile_load_fn_sound; auto.
  - destruct vargs as [|[| | | | |b ofs] [|v [|]]]; try discriminate.
    destruct (volatile_store_fn chunk m b ofs v) as [[t' m'']|] eqn:S; inv H.
    constructor. apply volatile_store_fn_sound; auto.
Qed.

(** Statements and calls *)

Definition assign_loc_fn (ty: type) (m: mem) (b: block) (ofs: ptrofs) (bf: bitfield)
    (v: val) : option mem :=
  match bf with
  | Full =>
      match access_mode ty with
      | By_value chunk => MemExec.storev chunk m (Vptr b ofs) v
      | _ => None
      end
  | Bits _ _ _ _ => None
  end.

Lemma assign_loc_fn_sound:
  forall ty m b ofs bf v m',
  assign_loc_fn ty m b ofs bf v = Some m' -> assign_loc ge ty m b ofs bf v m'.
Proof.
  unfold assign_loc_fn; intros. destruct bf; try discriminate.
  destruct (access_mode ty) eqn:A; try discriminate.
  eapply assign_loc_value; eauto. rewrite <- MemExec.storev_eq; auto.
Qed.

Fixpoint alloc_variables_fn (e: env) (m: mem) (vars: list (ident * type)) : env * mem :=
  match vars with
  | nil => (e, m)
  | (id, ty) :: vars' =>
      let (m1, b1) := Mem.alloc m 0 (sizeof ge ty) in
      alloc_variables_fn (PTree.set id (b1, ty) e) m1 vars'
  end.

Lemma alloc_variables_fn_sound:
  forall vars e m e' m',
  alloc_variables_fn e m vars = (e', m') -> alloc_variables ge e m vars e' m'.
Proof.
  induction vars as [|[id ty] vars IH]; simpl; intros.
  - inv H. constructor.
  - destruct (Mem.alloc m 0 (sizeof ge ty)) as [m1 b1] eqn:A. econstructor; eauto.
Qed.

Definition function_entry2_fn (f: function) (vargs: list val) (m: mem)
    : option (env * temp_env * mem) :=
  if list_norepet_dec ident_eq (var_names f.(fn_vars)) then
    if list_norepet_dec ident_eq (var_names f.(fn_params)) then
      if list_disjoint_dec ident_eq (var_names f.(fn_params)) (var_names f.(fn_temps)) then
        let (e, m') := alloc_variables_fn empty_env m f.(fn_vars) in
        match bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) with
        | Some le => Some (e, le, m')
        | None => None
        end
      else None
    else None
  else None.

Lemma function_entry2_fn_sound:
  forall f vargs m e le m',
  function_entry2_fn f vargs m = Some (e, le, m') -> function_entry2 ge f vargs m e le m'.
Proof.
  unfold function_entry2_fn; intros.
  destruct (list_norepet_dec ident_eq (var_names f.(fn_vars))); try discriminate.
  destruct (list_norepet_dec ident_eq (var_names f.(fn_params))); try discriminate.
  destruct (list_disjoint_dec ident_eq (var_names f.(fn_params)) (var_names f.(fn_temps)));
    try discriminate.
  destruct (alloc_variables_fn empty_env m f.(fn_vars)) as [e1 m1] eqn:A.
  destruct (bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)))
    as [le1|] eqn:B; inv H.
  constructor; auto. apply alloc_variables_fn_sound; auto.
Qed.

Definition outcome_result_value_fn (out: outcome) (t: type) (m: mem) : option val :=
  match out, t with
  | Out_normal, Tvoid => Some Vundef
  | Out_return None, Tvoid => Some Vundef
  | Out_return (Some (v', t')), ty => if type_eq ty Tvoid then None else sem_cast v' t' ty m
  | _, _ => None
  end.

Lemma outcome_result_value_fn_sound:
  forall out t m v, outcome_result_value_fn out t m = Some v -> outcome_result_value out t v m.
Proof.
  intros. destruct out as [| | |[[v' t']|]]; destruct t; simpl in *; try discriminate;
  try (inv H; auto; fail);
  (destruct (type_eq _ Tvoid); [discriminate | split; auto; congruence]).
Qed.

Fixpoint exec_fn (fuel: nat) (e: env) (le: temp_env) (m: mem) (s: statement) {struct fuel}
    : result (trace * temp_env * mem * outcome) :=
  match fuel with
  | O => OutOfFuel
  | S fuel =>
  match s with
  | Sskip => Done (E0, le, m, Out_normal)
  | Sassign a1 a2 =>
      match eval_lvalue_fn e le m a1, eval_expr_fn e le m a2 with
      | Some (loc, ofs, bf), Some v2 =>
          match sem_cast v2 (typeof a2) (typeof a1) m with
          | Some v =>
              match assign_loc_fn (typeof a1) m loc ofs bf v with
              | Some m' => Done (E0, le, m', Out_normal)
              | None => Stuck
              end
          | None => Stuck
          end
      | _, _ => Stuck
      end
  | Sset id a =>
      match eval_expr_fn e le m a with
      | Some v => Done (E0, PTree.set id v le, m, Out_normal)
      | None => Stuck
      end
  | Scall optid a al =>
      match classify_fun (typeof a) with
      | fun_case_f tyargs tyres cconv =>
          match eval_expr_fn e le m a, eval_exprlist_fn e le m al tyargs with
          | Some vf, Some vargs =>
              match Genv.find_funct ge vf with
              | Some f =>
                  if type_eq (type_of_fundef f) (Tfunction tyargs tyres cconv) then
                    match call_fn fuel m f vargs with
                    | Done (t, m', vres) => Done (t, set_opttemp optid vres le, m', Out_normal)
                    | Stuck => Stuck
                    | OutOfFuel => OutOfFuel
                    end
                  else Stuck
              | None => Stuck
              end
          | _, _ => Stuck
          end
      | fun_default => Stuck
      end
  | Sbuiltin optid ef tyargs al =>
      match eval_exprlist_fn e le m al tyargs with
      | Some vargs =>
          match external_call_fn ef vargs m with
          | Some (t, vres, m') => Done (t, set_opttemp optid vres le, m', Out_normal)
          | None => Stuck
          end
      | None => Stuck
      end
  | Ssequence s1 s2 =>
      match exec_fn fuel e le m s1 with
      | Done (t1, le1, m1, Out_normal) =>
          match exec_fn fuel e le1 m1 s2 with
          | Done (t2, le2, m2, out) => Done (t1 ** t2, le2, m2, out)
          | Stuck => Stuck
          | OutOfFuel => OutOfFuel
          end
      | Done r => Done r
      | Stuck => Stuck
      | OutOfFuel => OutOfFuel
      end
  | Sifthenelse a s1 s2 =>
      match eval_expr_fn e le m a with
      | Some v1 =>
          match bool_val v1 (typeof a) m with
          | Some b => exec_fn fuel e le m (if b then s1 else s2)
          | None => Stuck
          end
      | None => Stuck
      end
  | Sloop s1 s2 =>
      match exec_fn fuel e le m s1 with
      | Done (t1, le1, m1, Out_break) => Done (t1, le1, m1, Out_normal)
      | Done (t1, le1, m1, Out_return ov) => Done (t1, le1, m1, Out_return ov)
      | Done (t1, le1, m1, _) =>
          match exec_fn fuel e le1 m1 s2 with
          | Done (t2, le2, m2, Out_normal) =>
              match exec_fn fuel e le2 m2 (Sloop s1 s2) with
              | Done (t3, le3, m3, out) => Done (t1 ** t2 ** t3, le3, m3, out)
              | Stuck => Stuck
              | OutOfFuel => OutOfFuel
              end
          | Done (t2, le2, m2, Out_break) => Done (t1 ** t2, le2, m2, Out_normal)
          | Done (t2, le2, m2, Out_return ov) => Done (t1 ** t2, le2, m2, Out_return ov)
          | Done (_, _, _, Out_continue) => Stuck
          | Stuck => Stuck
          | OutOfFuel => OutOfFuel
          end
      | Stuck => Stuck
      | OutOfFuel => OutOfFuel
      end
  | Sbreak => Done (E0, le, m, Out_break)
  | Scontinue => Done (E0, le, m, Out_continue)
  | Sreturn None => Done (E0, le, m, Out_return None)
  | Sreturn (Some a) =>
      match eval_expr_fn e le m a with
      | Some v => Done (E0, le, m, Out_return (Some (v, typeof a)))
      | None => Stuck
      end
  | Sswitch a sl =>
      match eval_expr_fn e le m a with
      | Some v =>
          match sem_switch_arg v (typeof a) with
          | Some n =>
              match exec_fn fuel e le m (seq_of_labeled_statement (select_switch n sl)) with
              | Done (t, le1, m1, out) => Done (t, le1, m1, outcome_switch out)
              | Stuck => Stuck
              | OutOfFuel => OutOfFuel
              end
          | None => Stuck
          end
      | None => Stuck
      end
  | Slabel _ _ => Stuck
  | Sgoto _ => Stuck
  end
  end

with call_fn (fuel: nat) (m: mem) (fd: fundef) (vargs: list val) {struct fuel}
    : result (trace * mem * val) :=
  match fuel with
  | O => OutOfFuel
  | S fuel =>
  match fd with
  | Internal f =>
      match function_entry2_fn f vargs m with
      | Some (e, le1, m1) =>
          match exec_fn fuel e le1 m1 f.(fn_body) with
          | Done (t, le2, m2, out) =>
              match outcome_result_value_fn out f.(fn_return) m2 with
              | Some vres =>
                  match MemExec.free_list m2 (blocks_of_env ge e) with
                  | Some m3 => Done (t, m3, vres)
                  | None => Stuck
                  end
              | None => Stuck
              end
          | Stuck => Stuck
          | OutOfFuel => OutOfFuel
          end
      | None => Stuck
      end
  | External ef targs tres cconv =>
      match external_call_fn ef vargs m with
      | Some (t, vres, m') => Done (t, m', vres)
      | None => Stuck
      end
  end
  end.

(* Case analysis on the scrutinee of the outermost match of H, an equation whose right side is
   a constructor, until H is an equation between constructors. *)
Ltac split_match H :=
  match type of H with
  | (match ?x with _ => _ end) = _ =>
      first [is_var x; destruct x | destruct x eqn:?];
      cbv beta iota in H; try discriminate H; split_match H
  | _ => idtac
  end.

Theorem exec_call_sound:
  forall fuel,
  (forall e le m s t le' m' out,
     exec_fn fuel e le m s = Done (t, le', m', out) ->
     Clight2.exec_stmt ge e le m s t le' m' out) /\
  (forall m fd vargs t m' vres,
     call_fn fuel m fd vargs = Done (t, m', vres) ->
     Clight2.eval_funcall ge m fd vargs t m' vres).
Proof.
  unfold Clight2.exec_stmt, Clight2.eval_funcall.
  induction fuel as [|fuel [IHe IHc]]; split; intros; simpl in H; try discriminate.
  - destruct s; split_match H; inv H;
    solve [ constructor; eauto using eval_expr_fn_sound
          | eapply exec_Sassign;
            eauto using eval_lvalue_fn_sound, eval_expr_fn_sound, assign_loc_fn_sound
          | eapply exec_Scall; eauto using eval_expr_fn_sound, eval_exprlist_fn_sound
          | eapply exec_Sbuiltin; eauto using eval_exprlist_fn_sound, external_call_fn_sound
          | eapply exec_Sseq_1; eauto
          | eapply exec_Sseq_2; eauto; congruence
          | eapply exec_Sifthenelse; eauto using eval_expr_fn_sound
          | eapply exec_Sloop_stop1; eauto; constructor
          | eapply exec_Sloop_stop2; eauto; constructor
          | eapply exec_Sloop_loop; eauto; constructor
          | eapply exec_Sswitch; eauto using eval_expr_fn_sound ].
  - destruct fd; split_match H; inv H.
    + econstructor; eauto using function_entry2_fn_sound, outcome_result_value_fn_sound.
      rewrite <- MemExec.free_list_eq; auto.
    + constructor. apply external_call_fn_sound; auto.
Qed.

End EVAL.

(** Whole programs *)

Definition world_def {F V: Type} (idg: ident * globdef F V) : ident * globdef F V :=
  match idg with
  | (id, Gvar v) =>
      (id, Gvar (if v.(gvar_volatile)
                 then {| gvar_info := v.(gvar_info); gvar_init := v.(gvar_init);
                         gvar_readonly := false; gvar_volatile := false |}
                 else {| gvar_info := v.(gvar_info); gvar_init := nil;
                         gvar_readonly := v.(gvar_readonly);
                         gvar_volatile := v.(gvar_volatile) |}))
  | (id, Gfun f) => (id, Gfun f)
  end.

(* The program whose initial memory is the reference interpreter's first world: each volatile
   global becomes an ordinary global that can be written, and every other global loses its
   initialization data. *)
Definition world_program {F V: Type} (p: AST.program F V) : AST.program F V :=
  {| AST.prog_defs := map world_def p.(AST.prog_defs);
     AST.prog_public := p.(AST.prog_public);
     AST.prog_main := p.(AST.prog_main) |}.

Definition world_vload (p: program) : memory_chunk -> ident -> ptrofs -> option eventval :=
  let wp := world_program (program_of_program p) in
  match MemExec.init_mem wp with
  | None => fun _ _ _ => None
  | Some wm => fun chunk id ofs =>
      match Genv.find_symbol (Genv.globalenv wp) id with
      | None => None
      | Some b =>
          match MemExec.load chunk wm b (Ptrofs.unsigned ofs) with
          | Some v => eventval_of_val_fn v (type_of_chunk chunk)
          | None => None
          end
      end
  end.

Definition run (p: program) (name: ident) (args: list val) (fuel: nat)
    : result (trace * mem * val) :=
  let ge := globalenv p in
  match MemExec.init_mem p with
  | None => Stuck
  | Some m0 =>
      match Genv.find_symbol ge name with
      | None => Stuck
      | Some b =>
          match Genv.find_funct_ptr ge b with
          | None => Stuck
          | Some fd => call_fn ge (world_vload p) fuel m0 fd args
          end
      end
  end.

Theorem run_sound:
  forall p name args fuel t m v,
  run p name args fuel = Done (t, m, v) ->
  exists m0 b fd,
    Genv.init_mem p = Some m0 /\
    Genv.find_symbol (globalenv p) name = Some b /\
    Genv.find_funct_ptr (globalenv p) b = Some fd /\
    Clight2.eval_funcall (globalenv p) m0 fd args t m v.
Proof.
  unfold run; intros.
  destruct (MemExec.init_mem p) as [m0|] eqn:I; try discriminate.
  destruct (Genv.find_symbol (globalenv p) name) as [b|] eqn:S; try discriminate.
  destruct (Genv.find_funct_ptr (globalenv p) b) as [fd|] eqn:F; try discriminate.
  exists m0, b, fd. rewrite <- MemExec.init_mem_eq. split; auto. split; auto. split; auto.
  eapply exec_call_sound; eauto.
Qed.

Definition run_program (p: program) (fuel: nat) : result (trace * int) :=
  let ge := globalenv p in
  match MemExec.init_mem p with
  | None => Stuck
  | Some m0 =>
      match Genv.find_symbol ge p.(prog_main) with
      | None => Stuck
      | Some b =>
          match Genv.find_funct_ptr ge b with
          | None => Stuck
          | Some fd =>
              if type_eq (type_of_fundef fd) (Tfunction nil type_int32s cc_default) then
                match call_fn ge (world_vload p) fuel m0 fd nil with
                | Done (t, _, Vint r) => Done (t, r)
                | Done _ => Stuck
                | Stuck => Stuck
                | OutOfFuel => OutOfFuel
                end
              else Stuck
          end
      end
  end.

Theorem run_program_sound:
  forall p fuel t r,
  run_program p fuel = Done (t, r) -> Clight2.bigstep_program_terminates p t r.
Proof.
  unfold run_program; intros.
  destruct (MemExec.init_mem p) as [m0|] eqn:I; try discriminate.
  destruct (Genv.find_symbol (globalenv p) (prog_main p)) as [b|] eqn:S; try discriminate.
  destruct (Genv.find_funct_ptr (globalenv p) b) as [fd|] eqn:F; try discriminate.
  destruct (type_eq (type_of_fundef fd) (Tfunction nil type_int32s cc_default)) as [T|];
    try discriminate.
  destruct (call_fn (globalenv p) (world_vload p) fuel m0 fd nil) as [[[t' m1] v]| |] eqn:C;
    try discriminate.
  destruct v; inv H.
  econstructor; eauto.
  - rewrite <- MemExec.init_mem_eq; eauto.
  - eapply exec_call_sound; eauto.
Qed.
