import LeanExe.Native.Proof.Genv

/-!
Renaming of identifiers in Clight programs, and the theorem `bigstep_program_terminates_rename`:
the whole-program judgment survives every injective renaming.  `clightgen` numbers identifiers
by a canonical encoding of their names and `ccomp` numbers them in the order it meets them, so
the program that the per-build check reads and the program that `ccomp` compiles differ from
the translation by renamings (`docs/native-bare-metal.md`).

A renaming has two parts.  `g` renames the identifiers of globals: the definitions of a program,
the variables of expressions, the local variables of functions, `Init_addrof`, `prog_main`, and
the identifiers of events.  `τ` renames temporaries, for each function separately, under the
identifier of its definition, since `clightgen` numbers the temporaries of calls anew in each
function.  Both must be injective.  Labels, field names, and types are not renamed: the copy
gives `Slabel`, `Sgoto`, and `Efield` no rule and has no composite types.  `prog_public` is not
compared, since the semantics does not read it.

The semantics of an external function is a parameter, and nothing makes it invariant under
renaming.  `ExtRen g X X'` states that `X'` does on renamed symbols what `X` does, and
`ExtSem.none`, which relates nothing, meets it with every `X'`: a run that calls no external
function holds for `ExtSem.none`, and its renaming then holds for every semantics.

A compiler numbers the identifiers of the program alone, so its renaming is injective on them
and undefined elsewhere.  `exists_injective_extension` extends such a map to an injective map on
all identifiers, and renaming depends only on the identifiers that occur.
`bigstep_program_terminates_rename_on` therefore asks for injectivity only on those identifiers.
-/

namespace LClight

/-! ## Renamings -/

section Ren

variable (g t : ident → ident)

def renExpr : expr → expr
  | .Econst_int i ty => .Econst_int i ty
  | .Econst_float f ty => .Econst_float f ty
  | .Econst_single f ty => .Econst_single f ty
  | .Econst_long i ty => .Econst_long i ty
  | .Evar id ty => .Evar (g id) ty
  | .Etempvar id ty => .Etempvar (t id) ty
  | .Ederef a ty => .Ederef (renExpr a) ty
  | .Eaddrof a ty => .Eaddrof (renExpr a) ty
  | .Eunop op a ty => .Eunop op (renExpr a) ty
  | .Ebinop op a1 a2 ty => .Ebinop op (renExpr a1) (renExpr a2) ty
  | .Ecast a ty => .Ecast (renExpr a) ty
  | .Efield a f ty => .Efield (renExpr a) f ty
  | .Esizeof ty1 ty => .Esizeof ty1 ty
  | .Ealignof ty1 ty => .Ealignof ty1 ty

mutual
  def renStmt : statement → statement
    | .Sskip => .Sskip
    | .Sassign a1 a2 => .Sassign (renExpr g t a1) (renExpr g t a2)
    | .Sset id a => .Sset (t id) (renExpr g t a)
    | .Scall optid a al => .Scall (optid.map t) (renExpr g t a) (al.map (renExpr g t))
    | .Sbuiltin optid ef tys al => .Sbuiltin (optid.map t) ef tys (al.map (renExpr g t))
    | .Ssequence s1 s2 => .Ssequence (renStmt s1) (renStmt s2)
    | .Sifthenelse a s1 s2 => .Sifthenelse (renExpr g t a) (renStmt s1) (renStmt s2)
    | .Sloop s1 s2 => .Sloop (renStmt s1) (renStmt s2)
    | .Sbreak => .Sbreak
    | .Scontinue => .Scontinue
    | .Sreturn oa => .Sreturn (oa.map (renExpr g t))
    | .Sswitch a sl => .Sswitch (renExpr g t a) (renLabeled sl)
    | .Slabel lbl s => .Slabel lbl (renStmt s)
    | .Sgoto lbl => .Sgoto lbl

  def renLabeled : labeled_statements → labeled_statements
    | .LSnil => .LSnil
    | .LScons c s sl => .LScons c (renStmt s) (renLabeled sl)
end

def renBindings (r : ident → ident) (l : List (ident × type)) : List (ident × type) :=
  l.map fun p => (r p.1, p.2)

def renFunction (f : function) : function :=
  { fn_return := f.fn_return, fn_callconv := f.fn_callconv,
    fn_params := renBindings t f.fn_params, fn_vars := renBindings g f.fn_vars,
    fn_temps := renBindings t f.fn_temps, fn_body := renStmt g t f.fn_body }

def renFundef : fundef function → fundef function
  | .Internal f => .Internal (renFunction g t f)
  | .External ef targs tres cc => .External ef targs tres cc

end Ren

def renInit (g : ident → ident) : init_data → init_data
  | .Init_addrof id ofs => .Init_addrof (g id) ofs
  | d => d

def renGlobdef (g t : ident → ident) : globdef (fundef function) type → globdef (fundef function) type
  | .Gfun f => .Gfun (renFundef g t f)
  | .Gvar v => .Gvar { v with gvar_init := v.gvar_init.map (renInit g) }

/-- The definitions of a program, the temporaries of each function renamed by `τ` at the
identifier of its definition. -/
def renDefs (g : ident → ident) (τ : ident → ident → ident)
    (l : List (ident × globdef (fundef function) type)) :
    List (ident × globdef (fundef function) type) :=
  l.map fun d => (g d.1, renGlobdef g (τ d.1) d.2)

def renEventval (g : ident → ident) : eventval → eventval
  | .EVptr_global id ofs => .EVptr_global (g id) ofs
  | v => v

def renEvent (g : ident → ident) : event → event
  | .Event_syscall name args res => .Event_syscall name (args.map (renEventval g)) (renEventval g res)
  | .Event_vload chunk id ofs v => .Event_vload chunk (g id) ofs (renEventval g v)
  | .Event_vstore chunk id ofs v => .Event_vstore chunk (g id) ofs (renEventval g v)
  | .Event_annot text args => .Event_annot text (args.map (renEventval g))

def renTrace (g : ident → ident) (tr : trace) : trace := tr.map (renEvent g)

theorem renTrace_append (g : ident → ident) (t1 t2 : trace) :
    renTrace g (t1 ++ t2) = renTrace g t1 ++ renTrace g t2 := List.map_append

theorem renTrace_E0 (g : ident → ident) : renTrace g E0 = E0 := rfl

theorem typeof_renExpr (g t : ident → ident) (a : expr) : typeof (renExpr g t a) = typeof a := by
  cases a <;> rfl

theorem type_of_fundef_ren (g t : ident → ident) (fd : fundef function) :
    type_of_fundef (renFundef g t fd) = type_of_fundef fd := by
  cases fd with
  | Internal f =>
      simp [renFundef, type_of_fundef, type_of_function, renFunction, type_of_params,
        renBindings, Function.comp_def]
  | External => rfl

/-! ## Temporary environments -/

/-- `le'` holds under `t x` what `le` holds under `x`. -/
def TempRen (t : ident → ident) (le le' : temp_env) : Prop := ∀ x, le'[t x]? = le[x]?

theorem TempRen.insert {t : ident → ident} (ht : Function.Injective t) {le le' : temp_env}
    (h : TempRen t le le') (x : ident) (v : val) :
    TempRen t (le.insert x v) (le'.insert (t x) v) := by
  intro y
  by_cases hxy : x = y
  · subst hxy
    rw [te_insert_same, te_insert_same]
  · rw [te_insert_ne _ hxy, te_insert_ne _ (fun e => hxy (ht e))]
    exact h y

theorem TempRen.set_opttemp {t : ident → ident} (ht : Function.Injective t) {le le' : temp_env}
    (h : TempRen t le le') (optid : Option ident) (v : val) :
    TempRen t (set_opttemp optid v le) (set_opttemp (optid.map t) v le') := by
  cases optid with
  | none => exact h
  | some x => exact h.insert ht x v

theorem TempRen.empty (t : ident → ident) : TempRen t (∅ : temp_env) ∅ := by
  intro x
  simp

theorem create_undef_temps_ren {t : ident → ident} (ht : Function.Injective t) :
    ∀ temps : List (ident × type),
      TempRen t (create_undef_temps temps) (create_undef_temps (renBindings t temps))
  | [] => TempRen.empty t
  | (id, _) :: rest => (create_undef_temps_ren ht rest).insert ht id .Vundef

theorem bind_parameter_temps_ren {t : ident → ident} (ht : Function.Injective t) :
    ∀ (params : List (ident × type)) (vargs : List val) (le le' le2 : temp_env),
      TempRen t le le' → bind_parameter_temps params vargs le = some le2 →
      ∃ le2', bind_parameter_temps (renBindings t params) vargs le' = some le2' ∧ TempRen t le2 le2'
  | [], [], le, le', le2, h, hb => by
      simp only [bind_parameter_temps, Option.some.injEq] at hb
      subst hb
      exact ⟨le', rfl, h⟩
  | (id, ty) :: rest, v :: vs, le, le', le2, h, hb => by
      simp only [bind_parameter_temps] at hb
      exact bind_parameter_temps_ren ht rest vs _ _ le2 (h.insert ht id v) hb
  | [], _ :: _, _, _, _, _, hb => by simp [bind_parameter_temps] at hb
  | _ :: _, [], _, _, _, _, hb => by simp [bind_parameter_temps] at hb

/-! ## Global environments -/

/-- `ge'` is `ge` renamed: the same blocks, symbols renamed by `g`, and each definition renamed,
its temporaries by the renaming that `τ` gives at some identifier. -/
structure GenvRen (g : ident → ident) (τ : ident → ident → ident) (ge ge' : genv) : Prop where
  symb : ∀ id, Genv.find_symbol ge' (g id) = Genv.find_symbol ge id
  defs : ∀ b, ∃ id, Genv.find_def ge' b = (Genv.find_def ge b).map (renGlobdef g (τ id))

theorem GenvRen.symb_map {g : ident → ident} {τ : ident → ident → ident} {ge ge' : genv}
    (h : GenvRen g τ ge ge') (id : ident) : ge'.genv_symb[g id]? = ge.genv_symb[id]? :=
  h.symb id

theorem GenvRen.block_is_volatile {g : ident → ident} {τ : ident → ident → ident}
    {ge ge' : genv} (h : GenvRen g τ ge ge') (b : block) :
    Genv.block_is_volatile ge' b = Genv.block_is_volatile ge b := by
  obtain ⟨id, hd⟩ := h.defs b
  simp only [Genv.block_is_volatile, Genv.find_var_info, hd]
  cases Genv.find_def ge b with
  | none => rfl
  | some d =>
      cases d with
      | Gfun f => rfl
      | Gvar v => rfl

theorem GenvRen.find_funct {g : ident → ident} {τ : ident → ident → ident} {ge ge' : genv}
    (h : GenvRen g τ ge ge') {vf : val} {fd : fundef function}
    (hf : Genv.find_funct ge vf = some fd) :
    ∃ id, Genv.find_funct ge' vf = some (renFundef g (τ id) fd) := by
  cases vf with
  | Vptr b ofs =>
      obtain ⟨id, hd⟩ := h.defs b
      refine ⟨id, ?_⟩
      simp only [Genv.find_funct] at hf ⊢
      by_cases ho : ofs = Ptrofs.zero
      · simp only [ho, ite_true] at hf ⊢
        simp only [Genv.find_funct_ptr, hd] at hf ⊢
        cases hdef : Genv.find_def ge b with
        | none => simp [hdef] at hf
        | some d =>
            cases d with
            | Gfun f =>
                simp only [hdef, Option.some.injEq] at hf
                subst hf
                simp [renGlobdef]
            | Gvar v => simp [hdef] at hf
      · simp [ho] at hf
  | _ => simp [Genv.find_funct] at hf

/-! ## External functions -/

/-- `X'` does on renamed symbols what `X` does, with the events renamed. -/
def ExtRen (g : ident → ident) (X X' : ExtSem) : Prop :=
  ∀ name sg (symb symb' : Std.TreeMap ident block) vargs m tr vres m',
    (∀ id, symb'[g id]? = symb[id]?) →
    X.external_functions_sem name sg symb vargs m tr vres m' →
    X'.external_functions_sem name sg symb' vargs m (renTrace g tr) vres m'

/-- The semantics of external functions that relates nothing. -/
def ExtSem.none : ExtSem := ⟨fun _ _ _ _ _ _ _ _ => False⟩

theorem ExtRen.none (g : ident → ident) (X' : ExtSem) : ExtRen g ExtSem.none X' :=
  fun _ _ _ _ _ _ _ _ _ _ h => h.elim

theorem eventval_match_ren (g : ident → ident) {ev : eventval} {ty : typ} {v : val}
    (h : eventval_match ev ty v) : eventval_match (renEventval g ev) ty v := by
  cases h <;> constructor

theorem external_call_ren {A : Archi} {X X' : ExtSem} {g : ident → ident}
    {τ : ident → ident → ident} {ge ge' : genv} (hX : ExtRen g X X') (hge : GenvRen g τ ge ge')
    {ef : external_function} {vargs : List val} {m : mem} {tr : trace} {vres : val} {m' : mem}
    (h : external_call A X ef ge vargs m tr vres m') :
    external_call A X' ef ge' vargs m (renTrace g tr) vres m' := by
  cases ef with
  | EF_external name sg =>
      exact hX name sg _ _ vargs m tr vres m' hge.symb_map h
  | EF_builtin name sg =>
      simp only [external_call] at h ⊢
      cases hb : lookup_builtin_function name sg with
      | none => simp [hb] at h
      | some bf =>
          simp only [hb] at h ⊢
          obtain ⟨h1, rfl, rfl⟩ := h
          exact ⟨h1, rfl, rfl⟩
  | EF_vstore chunk =>
      simp only [external_call] at h ⊢
      cases h with
      | volatile_store_sem_intro b ofs m1 v t1 m2 hv =>
      match hv with
      | .volatile_store_vol _ _ _ _ id ev _ hvol hsym hev =>
          exact .volatile_store_sem_intro b ofs m v _ m
            (.volatile_store_vol chunk m b ofs (g id) (renEventval g ev) v
              (by rw [hge.block_is_volatile]; exact hvol) (by rw [hge.symb]; exact hsym)
              (eventval_match_ren g hev))
      | .volatile_store_nonvol _ _ _ _ _ m3 hvol hs =>
          exact .volatile_store_sem_intro b ofs m v _ m3
            (.volatile_store_nonvol chunk m b ofs v m3 (by rw [hge.block_is_volatile]; exact hvol)
              hs)
  | _ => simp [external_call] at h

/-! ## Expressions -/

section Exprs

variable {A : Archi} {g t : ident → ident} {τ : ident → ident → ident} {ge ge' : genv}
  {le le' : temp_env} {m : mem}

mutual
  theorem eval_expr_ren (hge : GenvRen g τ ge ge') (hle : TempRen t le le') {a : expr} {v : val}
      (h : eval_expr A ge empty_env le m a v) :
      eval_expr A ge' empty_env le' m (renExpr g t a) v := by
    match h with
    | .eval_Econst_int i ty => exact .eval_Econst_int i ty
    | .eval_Econst_float f ty => exact .eval_Econst_float f ty
    | .eval_Econst_single f ty => exact .eval_Econst_single f ty
    | .eval_Econst_long i ty => exact .eval_Econst_long i ty
    | .eval_Etempvar id ty v hv => exact .eval_Etempvar (t id) ty v (by rw [hle id]; exact hv)
    | .eval_Eaddrof a ty loc ofs hl => exact .eval_Eaddrof _ ty loc ofs (eval_lvalue_ren hge hle hl)
    | .eval_Eunop op a ty v1 v h1 hop =>
        exact .eval_Eunop op _ ty v1 v (eval_expr_ren hge hle h1)
          (by rw [typeof_renExpr]; exact hop)
    | .eval_Ebinop op a1 a2 ty v1 v2 v h1 h2 hop =>
        exact .eval_Ebinop op _ _ ty v1 v2 v (eval_expr_ren hge hle h1) (eval_expr_ren hge hle h2)
          (by rw [typeof_renExpr, typeof_renExpr]; exact hop)
    | .eval_Ecast a ty v1 v h1 hc =>
        exact .eval_Ecast _ ty v1 v (eval_expr_ren hge hle h1) (by rw [typeof_renExpr]; exact hc)
    | .eval_Elvalue a loc ofs bf v hl hd =>
        exact .eval_Elvalue _ loc ofs bf v (eval_lvalue_ren hge hle hl)
          (by rw [typeof_renExpr]; exact hd)

  theorem eval_lvalue_ren (hge : GenvRen g τ ge ge') (hle : TempRen t le le') {a : expr}
      {l : block} {ofs : ptrofs} {bf : bitfield}
      (h : eval_lvalue A ge empty_env le m a l ofs bf) :
      eval_lvalue A ge' empty_env le' m (renExpr g t a) l ofs bf := by
    match h with
    | .eval_Evar_local id l ty he => simp [empty_env] at he
    | .eval_Evar_global id l ty _ hs =>
        exact .eval_Evar_global (g id) l ty (by simp [empty_env]) (by rw [hge.symb]; exact hs)
    | .eval_Ederef a ty l ofs ha => exact .eval_Ederef _ ty l ofs (eval_expr_ren hge hle ha)
end

theorem eval_exprlist_ren (hge : GenvRen g τ ge ge') (hle : TempRen t le le') :
    ∀ {al : List expr} {tys : List type} {vl : List val},
      eval_exprlist A ge empty_env le m al tys vl →
      eval_exprlist A ge' empty_env le' m (al.map (renExpr g t)) tys vl
  | [], [], [], .eval_Enil => .eval_Enil
  | _ :: _, _ :: _, _ :: _, .eval_Econs a bl ty tyl v1 v2 vl h1 hc hl =>
      .eval_Econs _ _ ty tyl v1 v2 vl (eval_expr_ren hge hle h1)
        (by rw [typeof_renExpr]; exact hc) (eval_exprlist_ren hge hle hl)

end Exprs

theorem nodup_map_inj {f : ident → ident} (hf : Function.Injective f) :
    ∀ {l : List ident}, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
      rw [List.nodup_cons] at h
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, nodup_map_inj hf h.2⟩
      obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
      exact h.1 (hf he ▸ hy)

theorem function_entry2_inv {f : function} {vargs : List val} {m : mem} {e : env}
    {le : temp_env} {m1 : mem} (h : function_entry2 f vargs m e le m1) :
    e = empty_env ∧ m1 = m ∧ f.fn_vars = [] ∧ (var_names f.fn_params).Nodup ∧
      (∀ x ∈ var_names f.fn_params, ∀ y ∈ var_names f.fn_temps, x ≠ y) ∧
      bind_parameter_temps f.fn_params vargs (create_undef_temps f.fn_temps) = some le := by
  cases h with
  | intro le hv hn hd hb => exact ⟨rfl, rfl, hv, hn, hd, hb⟩

section Stmts

variable {A : Archi} {X X' : ExtSem} {g : ident → ident} {τ : ident → ident → ident}
  {ge ge' : genv}

theorem eval_expr_ren_e {t : ident → ident} {e : env} (he : e = empty_env)
    (hge : GenvRen g τ ge ge') {le le' : temp_env} (hle : TempRen t le le') {m : mem} {a : expr}
    {v : val} (h : eval_expr A ge e le m a v) : eval_expr A ge' e le' m (renExpr g t a) v := by
  subst he
  exact eval_expr_ren hge hle h

theorem eval_lvalue_ren_e {t : ident → ident} {e : env} (he : e = empty_env)
    (hge : GenvRen g τ ge ge') {le le' : temp_env} (hle : TempRen t le le') {m : mem} {a : expr}
    {l : block} {ofs : ptrofs} {bf : bitfield} (h : eval_lvalue A ge e le m a l ofs bf) :
    eval_lvalue A ge' e le' m (renExpr g t a) l ofs bf := by
  subst he
  exact eval_lvalue_ren hge hle h

theorem eval_exprlist_ren_e {t : ident → ident} {e : env} (he : e = empty_env)
    (hge : GenvRen g τ ge ge') {le le' : temp_env} (hle : TempRen t le le') {m : mem}
    {al : List expr} {tys : List type} {vl : List val}
    (h : eval_exprlist A ge e le m al tys vl) :
    eval_exprlist A ge' e le' m (al.map (renExpr g t)) tys vl := by
  subst he
  exact eval_exprlist_ren hge hle h

mutual
  theorem exec_stmt_ren (hX : ExtRen g X X') (hge : GenvRen g τ ge ge')
      (hτ : ∀ id, Function.Injective (τ id)) {t : ident → ident} (ht : Function.Injective t)
      {e : env} (he : e = empty_env) {le : temp_env} {m : mem} {s : statement} {tr : trace}
      {le2 : temp_env} {m2 : mem} {out : outcome} (h : exec_stmt A X ge e le m s tr le2 m2 out)
      {le' : temp_env} (hle : TempRen t le le') :
      ∃ le2', exec_stmt A X' ge' e le' m (renStmt g t s) (renTrace g tr) le2' m2 out ∧
        TempRen t le2 le2' := by
    match h with
    | .exec_Sskip _ _ _ => exact ⟨le', .exec_Sskip _ _ _, hle⟩
    | .exec_Sassign _ _ _ a1 a2 loc ofs bf v2 v m' hl hv hc ha =>
        refine ⟨le', ?_, hle⟩
        exact .exec_Sassign _ _ _ _ _ loc ofs bf v2 v m' (eval_lvalue_ren_e he hge hle hl)
          (eval_expr_ren_e he hge hle hv) (by rw [typeof_renExpr, typeof_renExpr]; exact hc)
          (by rw [typeof_renExpr]; exact ha)
    | .exec_Sset _ _ _ id a v hv =>
        exact ⟨le'.insert (t id) v, .exec_Sset _ _ _ (t id) _ v (eval_expr_ren_e he hge hle hv),
          hle.insert ht id v⟩
    | .exec_Scall _ _ _ optid a al tyargs tyres cconv vf vargs f tr m' vres hcl ha hal hf hty hcall =>
        obtain ⟨id, hf'⟩ := hge.find_funct hf
        refine ⟨set_opttemp (optid.map t) vres le', ?_, hle.set_opttemp ht optid vres⟩
        exact .exec_Scall _ _ _ _ _ _ tyargs tyres cconv vf vargs _ _ m' vres
          (by rw [typeof_renExpr]; exact hcl) (eval_expr_ren_e he hge hle ha)
          (eval_exprlist_ren_e he hge hle hal) hf' (by rw [type_of_fundef_ren]; exact hty)
          (eval_funcall_ren hX hge hτ (hτ id) hcall)
    | .exec_Sbuiltin _ _ _ optid ef al tyargs vargs tr m' vres hal hx =>
        refine ⟨set_opttemp (optid.map t) vres le', ?_, hle.set_opttemp ht optid vres⟩
        exact .exec_Sbuiltin _ _ _ _ ef _ tyargs vargs _ m' vres (eval_exprlist_ren_e he hge hle hal)
          (external_call_ren hX hge hx)
    | .exec_Sseq_1 _ _ _ s1 s2 t1 le1 m1 t2 le2 m2 out h1 h2 =>
        obtain ⟨le1', h1', hr1⟩ := exec_stmt_ren hX hge hτ ht he h1 hle
        obtain ⟨le2', h2', hr2⟩ := exec_stmt_ren hX hge hτ ht he h2 hr1
        refine ⟨le2', ?_, hr2⟩
        rw [renTrace_append]
        exact .exec_Sseq_1 _ _ _ _ _ _ le1' m1 _ le2' m2 out h1' h2'
    | .exec_Sseq_2 _ _ _ s1 s2 t1 le1 m1 out h1 hne =>
        obtain ⟨le1', h1', hr1⟩ := exec_stmt_ren hX hge hτ ht he h1 hle
        exact ⟨le1', .exec_Sseq_2 _ _ _ _ _ _ le1' m1 out h1' hne, hr1⟩
    | .exec_Sifthenelse _ _ _ a s1 s2 v1 b tr le2 m2 out ha hb hs =>
        obtain ⟨le2', hs', hr⟩ := exec_stmt_ren hX hge hτ ht he hs hle
        refine ⟨le2', ?_, hr⟩
        refine .exec_Sifthenelse _ _ _ _ _ _ v1 b _ le2' m2 out (eval_expr_ren_e he hge hle ha)
          (by rw [typeof_renExpr]; exact hb) ?_
        cases b <;> exact hs'
    | .exec_Sreturn_none _ _ _ => exact ⟨le', .exec_Sreturn_none _ _ _, hle⟩
    | .exec_Sreturn_some _ _ _ a v hv =>
        refine ⟨le', ?_, hle⟩
        have := exec_stmt.exec_Sreturn_some (A := A) (X := X') (ge := ge') e le' m
          (renExpr g t a) v (eval_expr_ren_e he hge hle hv)
        rw [typeof_renExpr] at this
        exact this
    | .exec_Sbreak _ _ _ => exact ⟨le', .exec_Sbreak _ _ _, hle⟩
    | .exec_Scontinue _ _ _ => exact ⟨le', .exec_Scontinue _ _ _, hle⟩
    | .exec_Sloop_stop1 _ _ _ s1 s2 tr le2 m2 out' out h1 hbr =>
        obtain ⟨le2', h1', hr⟩ := exec_stmt_ren hX hge hτ ht he h1 hle
        exact ⟨le2', .exec_Sloop_stop1 _ _ _ _ _ _ le2' m2 out' out h1' hbr, hr⟩
    | .exec_Sloop_stop2 _ _ _ s1 s2 t1 le1 m1 out1 t2 le2 m2 out2 out h1 hnc h2 hbr =>
        obtain ⟨le1', h1', hr1⟩ := exec_stmt_ren hX hge hτ ht he h1 hle
        obtain ⟨le2', h2', hr2⟩ := exec_stmt_ren hX hge hτ ht he h2 hr1
        refine ⟨le2', ?_, hr2⟩
        rw [renTrace_append]
        exact .exec_Sloop_stop2 _ _ _ _ _ _ le1' m1 out1 _ le2' m2 out2 out h1' hnc h2' hbr
    | .exec_Sloop_loop _ _ _ s1 s2 t1 le1 m1 out1 t2 le2 m2 t3 le3 m3 out h1 hnc h2 h3 =>
        obtain ⟨le1', h1', hr1⟩ := exec_stmt_ren hX hge hτ ht he h1 hle
        obtain ⟨le2', h2', hr2⟩ := exec_stmt_ren hX hge hτ ht he h2 hr1
        obtain ⟨le3', h3', hr3⟩ := exec_stmt_ren hX hge hτ ht he h3 hr2
        refine ⟨le3', ?_, hr3⟩
        rw [renTrace_append, renTrace_append]
        exact .exec_Sloop_loop _ _ _ _ _ _ le1' m1 out1 _ le2' m2 _ le3' m3 out h1' hnc h2' h3'

  theorem eval_funcall_ren (hX : ExtRen g X X') (hge : GenvRen g τ ge ge')
      (hτ : ∀ id, Function.Injective (τ id)) {t : ident → ident} (ht : Function.Injective t)
      {m : mem} {fd : fundef function} {vargs : List val} {tr : trace} {m' : mem} {vres : val}
      (h : eval_funcall A X ge m fd vargs tr m' vres) :
      eval_funcall A X' ge' m (renFundef g t fd) vargs (renTrace g tr) m' vres := by
    match h with
    | .eval_funcall_internal _ f _ tr e le1 le2 m1 m2 out _ m3 hentry hbody hres hfree =>
        obtain ⟨he, hm1, hvars, hnodup, hdisj, hbind⟩ := function_entry2_inv hentry
        obtain ⟨le1', hbind', hr1⟩ := bind_parameter_temps_ren ht f.fn_params vargs _ _ le1
          (create_undef_temps_ren ht f.fn_temps) hbind
        obtain ⟨le2', hbody', -⟩ := exec_stmt_ren hX hge hτ ht he hbody hr1
        subst he
        subst hm1
        refine .eval_funcall_internal _ (renFunction g t f) vargs _ empty_env le1' le2' m1 m2 out
          vres m3 ?_ hbody' hres hfree
        refine .intro le1' (by simp [renFunction, renBindings, hvars]) ?_ ?_ hbind'
        · have hn := nodup_map_inj ht hnodup
          simp only [var_names, List.map_map, Function.comp_def] at hn ⊢
          simpa [renFunction, renBindings, List.map_map, Function.comp_def] using hn
        · intro x hx y hy hxy
          simp only [renFunction, renBindings, var_names, List.map_map, List.mem_map,
            Function.comp_apply] at hx hy
          obtain ⟨p, hp, rfl⟩ := hx
          obtain ⟨q, hq, rfl⟩ := hy
          exact hdisj p.1 (List.mem_map_of_mem hp) q.1 (List.mem_map_of_mem hq) (ht hxy)
    | .eval_funcall_external _ ef targs tres cconv _ tr _ _ hx =>
        exact .eval_funcall_external _ ef targs tres cconv vargs _ vres m'
          (external_call_ren hX hge hx)
end

end Stmts

/-! ## Programs -/

section Programs

variable {g : ident → ident} {τ : ident → ident → ident}

theorem add_globals_ren (hg : Function.Injective g) :
    ∀ (gl : List (ident × globdef (fundef function) type)) (ge ge' : genv),
      ge'.genv_next = ge.genv_next →
      (∀ id, Genv.find_symbol ge' (g id) = Genv.find_symbol ge id) →
      (∀ b, ∃ id, Genv.find_def ge' b = (Genv.find_def ge b).map (renGlobdef g (τ id))) →
      (Genv.add_globals ge' (renDefs g τ gl)).genv_next = (Genv.add_globals ge gl).genv_next ∧
      GenvRen g τ (Genv.add_globals ge gl) (Genv.add_globals ge' (renDefs g τ gl))
  | [], ge, ge', hn, hs, hd => ⟨hn, hs, hd⟩
  | x :: gl, ge, ge', hn, hs, hd => by
      refine add_globals_ren hg gl (Genv.add_global ge x) (Genv.add_global ge' (g x.1,
        renGlobdef g (τ x.1) x.2)) (by simp [Genv.add_global, hn]) (fun id => ?_) (fun b => ?_)
      · simp only [Genv.find_symbol, Genv.add_global]
        by_cases hid : x.1 = id
        · subst hid
          rw [Std.TreeMap.getElem?_insert_self, Std.TreeMap.getElem?_insert_self, hn]
        · rw [Genv.symb_insert_ne _ (fun e => hid (hg e)), Genv.symb_insert_ne _ hid]
          exact hs id
      · simp only [Genv.find_def, Genv.add_global, hn]
        by_cases hb : ge.genv_next = b
        · subst hb
          exact ⟨x.1, by rw [Std.TreeMap.getElem?_insert_self, Std.TreeMap.getElem?_insert_self]; rfl⟩
        · rw [Genv.defs_insert_ne _ hb, Genv.defs_insert_ne _ hb]
          exact hd b

theorem globalenv_ren (hg : Function.Injective g) {p p' : program function}
    (hdefs : p'.prog_defs = renDefs g τ p.prog_defs) :
    GenvRen g τ (globalenv p) (globalenv p') := by
  unfold globalenv
  rw [hdefs]
  exact (add_globals_ren (τ := τ) hg p.prog_defs (Genv.empty_genv p.prog_public)
    (Genv.empty_genv p'.prog_public) rfl (fun id => by simp [Genv.find_symbol, Genv.empty_genv])
    (fun b => ⟨0, by simp [Genv.find_def, Genv.empty_genv]⟩)).2

theorem store_init_data_list_ren {ge ge' : genv} (hge : GenvRen g τ ge ge') (b : block) :
    ∀ (l : List init_data) (m : mem) (p : _root_.Int),
      Genv.store_init_data_list ge' m b p (l.map (renInit g)) = Genv.store_init_data_list ge m b p l
  | [], _, _ => rfl
  | d :: l, m, p => by
      have hsize : init_data_size (renInit g d) = init_data_size d := by cases d <;> rfl
      have hstore : Genv.store_init_data ge' m b p (renInit g d) = Genv.store_init_data ge m b p d := by
        cases d with
        | Init_addrof id ofs => simp [Genv.store_init_data, renInit, hge.symb]
        | _ => rfl
      simp only [List.map_cons, Genv.store_init_data_list, hstore, hsize]
      cases Genv.store_init_data ge m b p d with
      | none => rfl
      | some m' => exact store_init_data_list_ren hge b l m' _

theorem init_data_list_size_ren (l : List init_data) :
    init_data_list_size (l.map (renInit g)) = init_data_list_size l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      have hsize : init_data_size (renInit g d) = init_data_size d := by cases d <;> rfl
      simp [init_data_list_size, hsize, ih]

theorem alloc_globals_ren {ge ge' : genv} (hge : GenvRen g τ ge ge') :
    ∀ (gl : List (ident × globdef (fundef function) type)) (m : mem),
      Genv.alloc_globals ge' m (renDefs g τ gl) = Genv.alloc_globals ge m gl
  | [], _ => rfl
  | x :: gl, m => by
      have hx : Genv.alloc_global ge' m (g x.1, renGlobdef g (τ x.1) x.2) = Genv.alloc_global ge m x := by
        obtain ⟨id, d⟩ := x
        cases d with
        | Gfun f => rfl
        | Gvar v =>
            simp only [Genv.alloc_global, renGlobdef, init_data_list_size_ren,
              store_init_data_list_ren hge, Genv.perm_globvar]
      simp only [renDefs, List.map_cons, Genv.alloc_globals] at hx ⊢
      rw [hx]
      cases Genv.alloc_global ge m x with
      | none => rfl
      | some m' => exact alloc_globals_ren hge gl m'

theorem init_mem_ren (hg : Function.Injective g) {p p' : program function}
    (hdefs : p'.prog_defs = renDefs g τ p.prog_defs) : init_mem p' = init_mem p := by
  unfold init_mem
  rw [hdefs]
  exact alloc_globals_ren (globalenv_ren hg hdefs) p.prog_defs Mem.empty

end Programs

/-- The whole-program judgment survives an injective renaming `g` of globals and injective
renamings `τ` of the temporaries of each function, with the identifiers of the trace renamed by
`g`.  The semantics of external functions changes from `X` to any `X'` that does on renamed
symbols what `X` does; for `X = ExtSem.none`, every `X'` qualifies. -/
theorem bigstep_program_terminates_rename {A : Archi} {X X' : ExtSem} {g : ident → ident}
    {τ : ident → ident → ident} (hg : Function.Injective g) (hτ : ∀ id, Function.Injective (τ id))
    (hX : ExtRen g X X') {p p' : program function}
    (hdefs : p'.prog_defs = renDefs g τ p.prog_defs) (hmain : p'.prog_main = g p.prog_main)
    {tr : trace} {r : int} (h : bigstep_program_terminates A X p tr r) :
    bigstep_program_terminates A X' p' (renTrace g tr) r := by
  obtain ⟨b, fd, m0, m1, tr, r, hinit, hs, hf, hty, hcall⟩ := h
  have hge := globalenv_ren (τ := τ) hg hdefs
  obtain ⟨id, hd⟩ := hge.defs b
  have hf' : Genv.find_funct_ptr (globalenv p') b = some (renFundef g (τ id) fd) := by
    simp only [Genv.find_funct_ptr, hd] at hf ⊢
    cases hdef : Genv.find_def (globalenv p) b with
    | none => simp [hdef] at hf
    | some d =>
        cases d with
        | Gfun f =>
            simp only [hdef, Option.some.injEq] at hf
            subst hf
            simp [renGlobdef]
        | Gvar v => simp [hdef] at hf
  refine .bigstep_program_terminates_intro b _ m0 m1 _ r (by rw [init_mem_ren hg hdefs]; exact hinit)
    (by rw [hmain, hge.symb]; exact hs) hf' (by rw [type_of_fundef_ren]; exact hty)
    (eval_funcall_ren hX hge hτ (hτ id) hcall)

/-- A run of a whole program that holds for `ExtSem.none`, which calls no external function,
holds after an injective renaming for every semantics of external functions. -/
theorem bigstep_program_terminates_rename_none {A : Archi} {g : ident → ident}
    {τ : ident → ident → ident} (hg : Function.Injective g) (hτ : ∀ id, Function.Injective (τ id))
    {p p' : program function} (hdefs : p'.prog_defs = renDefs g τ p.prog_defs)
    (hmain : p'.prog_main = g p.prog_main) {tr : trace} {r : int}
    (h : bigstep_program_terminates A ExtSem.none p tr r) (X' : ExtSem) :
    bigstep_program_terminates A X' p' (renTrace g tr) r :=
  bigstep_program_terminates_rename hg hτ (ExtRen.none g X') hdefs hmain h

/-! ## Renamings of the program's own identifiers

`bigstep_program_terminates_rename` asks for renamings injective on all identifiers.  A
renaming that a compiler gives is defined, and injective, on the identifiers of the program
alone.  Every such map agrees on those identifiers with an injective map on all identifiers,
`exists_injective_extension`, and renaming depends only on the identifiers that occur, so
`bigstep_program_terminates_rename_on` needs injectivity only on the program's identifiers. -/

theorem le_sum_of_mem : ∀ {l : List Nat} {a : Nat}, a ∈ l → a ≤ l.sum
  | _ :: _, _, .head _ => by simp only [List.sum_cons]; omega
  | _ :: _, _, .tail _ h => by have := le_sum_of_mem h; simp only [List.sum_cons]; omega

theorem exists_injective_extension_nat (s : List Nat) (f : Nat → Nat)
    (hf : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) :
    ∃ g : Nat → Nat, Function.Injective g ∧ ∀ x ∈ s, g x = f x := by
  have hlt : ∀ x ∈ s, f x < (s.map f).sum + 1 := fun x hx =>
    Nat.lt_succ_of_le (le_sum_of_mem (List.mem_map_of_mem hx))
  refine ⟨fun x => if x ∈ s then f x else (s.map f).sum + 1 + x, fun x y hxy => ?_,
    fun x hx => by simp [hx]⟩
  by_cases hx : x ∈ s <;> by_cases hy : y ∈ s <;> simp only [hx, hy, ↓reduceIte] at hxy
  · exact hf x hx y hy hxy
  · have := hlt x hx; omega
  · have := hlt y hy; omega
  · omega

/-- A map injective on the finite set `s` agrees on `s` with an injective map: the map that
sends each identifier outside `s` above every value on `s`. -/
theorem exists_injective_extension (s : List ident) (f : ident → ident)
    (hf : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) :
    ∃ g : ident → ident, Function.Injective g ∧ ∀ x ∈ s, g x = f x :=
  exists_injective_extension_nat s f hf

/-! ### The identifiers that occur -/

/-- The identifiers of globals in an expression. -/
def exprG : expr → List ident
  | .Evar id _ => [id]
  | .Ederef a _ | .Eaddrof a _ | .Eunop _ a _ | .Ecast a _ | .Efield a _ _ => exprG a
  | .Ebinop _ a1 a2 _ => exprG a1 ++ exprG a2
  | _ => []

/-- The temporaries in an expression. -/
def exprT : expr → List ident
  | .Etempvar id _ => [id]
  | .Ederef a _ | .Eaddrof a _ | .Eunop _ a _ | .Ecast a _ | .Efield a _ _ => exprT a
  | .Ebinop _ a1 a2 _ => exprT a1 ++ exprT a2
  | _ => []

mutual
  /-- The identifiers of globals in a statement. -/
  def stmtG : statement → List ident
    | .Sassign a1 a2 => exprG a1 ++ exprG a2
    | .Sset _ a => exprG a
    | .Scall _ a al => exprG a ++ al.flatMap exprG
    | .Sbuiltin _ _ _ al => al.flatMap exprG
    | .Ssequence s1 s2 => stmtG s1 ++ stmtG s2
    | .Sifthenelse a s1 s2 => exprG a ++ stmtG s1 ++ stmtG s2
    | .Sloop s1 s2 => stmtG s1 ++ stmtG s2
    | .Sreturn oa => (oa.map exprG).getD []
    | .Sswitch a sl => exprG a ++ lsG sl
    | .Slabel _ s => stmtG s
    | .Sskip | .Sbreak | .Scontinue | .Sgoto _ => []

  def lsG : labeled_statements → List ident
    | .LSnil => []
    | .LScons _ s sl => stmtG s ++ lsG sl
end

mutual
  /-- The temporaries in a statement. -/
  def stmtT : statement → List ident
    | .Sassign a1 a2 => exprT a1 ++ exprT a2
    | .Sset id a => id :: exprT a
    | .Scall optid a al => optid.toList ++ exprT a ++ al.flatMap exprT
    | .Sbuiltin optid _ _ al => optid.toList ++ al.flatMap exprT
    | .Ssequence s1 s2 => stmtT s1 ++ stmtT s2
    | .Sifthenelse a s1 s2 => exprT a ++ stmtT s1 ++ stmtT s2
    | .Sloop s1 s2 => stmtT s1 ++ stmtT s2
    | .Sreturn oa => (oa.map exprT).getD []
    | .Sswitch a sl => exprT a ++ lsT sl
    | .Slabel _ s => stmtT s
    | .Sskip | .Sbreak | .Scontinue | .Sgoto _ => []

  def lsT : labeled_statements → List ident
    | .LSnil => []
    | .LScons _ s sl => stmtT s ++ lsT sl
end

/-- The identifiers of globals in a definition: the local variables and the globals of the body
of an internal function, and the targets of `Init_addrof` of a variable. -/
def globdefG : globdef (fundef function) type → List ident
  | .Gfun (.Internal f) => f.fn_vars.map (·.1) ++ stmtG f.fn_body
  | .Gfun (.External ..) => []
  | .Gvar v => v.gvar_init.flatMap fun
      | .Init_addrof id _ => [id]
      | _ => []

/-- The temporaries of a definition: the parameters, temporaries, and temporaries of the body
of an internal function. -/
def globdefT : globdef (fundef function) type → List ident
  | .Gfun (.Internal f) => f.fn_params.map (·.1) ++ f.fn_temps.map (·.1) ++ stmtT f.fn_body
  | _ => []

/-- The identifiers of globals in a program: its `main`, and the identifier and the globals of
each definition. -/
def progG (p : program function) : List ident :=
  p.prog_main :: p.prog_defs.flatMap fun d => d.1 :: globdefG d.2

/-- The temporaries of the definitions under the identifier `id`. -/
def tempsOf (defs : List (ident × globdef (fundef function) type)) (id : ident) : List ident :=
  (defs.filter fun d => d.1 == id).flatMap fun d => globdefT d.2

/-! ### Renaming depends only on the identifiers that occur -/

section Congr

variable {g g' t t' : ident → ident}

theorem renExpr_congr : ∀ (a : expr), (∀ x ∈ exprG a, g x = g' x) →
    (∀ x ∈ exprT a, t x = t' x) → renExpr g t a = renExpr g' t' a
  | .Econst_int .., _, _ | .Econst_float .., _, _ | .Econst_single .., _, _
  | .Econst_long .., _, _ | .Esizeof .., _, _ | .Ealignof .., _, _ => rfl
  | .Evar id ty, hg, _ => by simp [renExpr, hg id (by simp [exprG])]
  | .Etempvar id ty, _, ht => by simp [renExpr, ht id (by simp [exprT])]
  | .Ederef a ty, hg, ht => by
      simp only [renExpr, renExpr_congr a (fun x hx => hg x (by simpa [exprG] using hx))
        (fun x hx => ht x (by simpa [exprT] using hx))]
  | .Eaddrof a ty, hg, ht => by
      simp only [renExpr, renExpr_congr a (fun x hx => hg x (by simpa [exprG] using hx))
        (fun x hx => ht x (by simpa [exprT] using hx))]
  | .Eunop op a ty, hg, ht => by
      simp only [renExpr, renExpr_congr a (fun x hx => hg x (by simpa [exprG] using hx))
        (fun x hx => ht x (by simpa [exprT] using hx))]
  | .Ecast a ty, hg, ht => by
      simp only [renExpr, renExpr_congr a (fun x hx => hg x (by simpa [exprG] using hx))
        (fun x hx => ht x (by simpa [exprT] using hx))]
  | .Efield a f ty, hg, ht => by
      simp only [renExpr, renExpr_congr a (fun x hx => hg x (by simpa [exprG] using hx))
        (fun x hx => ht x (by simpa [exprT] using hx))]
  | .Ebinop op a1 a2 ty, hg, ht => by
      simp only [renExpr,
        renExpr_congr a1 (fun x hx => hg x (by simp [exprG, hx]))
          (fun x hx => ht x (by simp [exprT, hx])),
        renExpr_congr a2 (fun x hx => hg x (by simp [exprG, hx]))
          (fun x hx => ht x (by simp [exprT, hx]))]

theorem renExprs_congr {al : List expr} (hg : ∀ x ∈ al.flatMap exprG, g x = g' x)
    (ht : ∀ x ∈ al.flatMap exprT, t x = t' x) :
    al.map (renExpr g t) = al.map (renExpr g' t') :=
  List.map_congr_left fun a ha =>
    renExpr_congr a (fun x hx => hg x (List.mem_flatMap.mpr ⟨a, ha, hx⟩))
      (fun x hx => ht x (List.mem_flatMap.mpr ⟨a, ha, hx⟩))

theorem optmap_congr {o : Option ident} (ht : ∀ x ∈ o.toList, t x = t' x) :
    o.map t = o.map t' := by
  cases o with
  | none => rfl
  | some x => simp [ht x (by simp)]

mutual
  theorem renStmt_congr : ∀ (s : statement), (∀ x ∈ stmtG s, g x = g' x) →
      (∀ x ∈ stmtT s, t x = t' x) → renStmt g t s = renStmt g' t' s
    | .Sskip, _, _ | .Sbreak, _, _ | .Scontinue, _, _ | .Sgoto _, _, _ => rfl
    | .Sassign a1 a2, hg, ht => by
        simp only [renStmt,
          renExpr_congr a1 (fun x hx => hg x (by simp [stmtG, hx]))
            (fun x hx => ht x (by simp [stmtT, hx])),
          renExpr_congr a2 (fun x hx => hg x (by simp [stmtG, hx]))
            (fun x hx => ht x (by simp [stmtT, hx]))]
    | .Sset id a, hg, ht => by
        simp only [renStmt, ht id (by simp [stmtT]),
          renExpr_congr a (fun x hx => hg x (by simp [stmtG, hx]))
            (fun x hx => ht x (by simp [stmtT, hx]))]
    | .Scall optid a al, hg, ht => by
        simp only [renStmt,
          optmap_congr (o := optid) (fun x hx => ht x (by simp [stmtT, hx])),
          renExpr_congr a (fun x hx => hg x (by simp [stmtG, hx]))
            (fun x hx => ht x (by simp [stmtT, hx])),
          renExprs_congr (al := al)
            (fun x hx => hg x (by rw [stmtG]; exact List.mem_append_right _ hx))
            (fun x hx => ht x (by rw [stmtT]; exact List.mem_append_right _ hx))]
    | .Sbuiltin optid ef tys al, hg, ht => by
        simp only [renStmt,
          optmap_congr (o := optid) (fun x hx => ht x (by simp [stmtT, hx])),
          renExprs_congr (al := al) (fun x hx => hg x (by rw [stmtG]; exact hx))
            (fun x hx => ht x (by rw [stmtT]; exact List.mem_append_right _ hx))]
    | .Ssequence s1 s2, hg, ht => by
        simp only [renStmt,
          renStmt_congr s1 (fun x hx => hg x (by simp [stmtG, hx]))
            (fun x hx => ht x (by simp [stmtT, hx])),
          renStmt_congr s2 (fun x hx => hg x (by simp [stmtG, hx]))
            (fun x hx => ht x (by simp [stmtT, hx]))]
    | .Sifthenelse a s1 s2, hg, ht => by
        simp only [renStmt,
          renExpr_congr a (fun x hx => hg x (by simp [stmtG, hx]))
            (fun x hx => ht x (by simp [stmtT, hx])),
          renStmt_congr s1 (fun x hx => hg x (by simp [stmtG, hx]))
            (fun x hx => ht x (by simp [stmtT, hx])),
          renStmt_congr s2 (fun x hx => hg x (by simp [stmtG, hx]))
            (fun x hx => ht x (by simp [stmtT, hx]))]
    | .Sloop s1 s2, hg, ht => by
        simp only [renStmt,
          renStmt_congr s1 (fun x hx => hg x (by simp [stmtG, hx]))
            (fun x hx => ht x (by simp [stmtT, hx])),
          renStmt_congr s2 (fun x hx => hg x (by simp [stmtG, hx]))
            (fun x hx => ht x (by simp [stmtT, hx]))]
    | .Sreturn none, _, _ => rfl
    | .Sreturn (some a), hg, ht => by
        simp only [renStmt, Option.map_some,
          renExpr_congr a (fun x hx => hg x (by simp [stmtG, hx]))
            (fun x hx => ht x (by simp [stmtT, hx]))]
    | .Sswitch a sl, hg, ht => by
        simp only [renStmt,
          renExpr_congr a (fun x hx => hg x (by simp [stmtG, hx]))
            (fun x hx => ht x (by simp [stmtT, hx])),
          renLabeled_congr sl (fun x hx => hg x (by simp [stmtG, hx]))
            (fun x hx => ht x (by simp [stmtT, hx]))]
    | .Slabel lbl s, hg, ht => by
        simp only [renStmt,
          renStmt_congr s (fun x hx => hg x (by simpa [stmtG] using hx))
            (fun x hx => ht x (by simpa [stmtT] using hx))]

  theorem renLabeled_congr : ∀ (sl : labeled_statements), (∀ x ∈ lsG sl, g x = g' x) →
      (∀ x ∈ lsT sl, t x = t' x) → renLabeled g t sl = renLabeled g' t' sl
    | .LSnil, _, _ => rfl
    | .LScons c s sl, hg, ht => by
        simp only [renLabeled,
          renStmt_congr s (fun x hx => hg x (by simp [lsG, hx]))
            (fun x hx => ht x (by simp [lsT, hx])),
          renLabeled_congr sl (fun x hx => hg x (by simp [lsG, hx]))
            (fun x hx => ht x (by simp [lsT, hx]))]
end

theorem renBindings_congr {r r' : ident → ident} {l : List (ident × type)}
    (h : ∀ x ∈ l.map (·.1), r x = r' x) : renBindings r l = renBindings r' l :=
  List.map_congr_left fun p hp => by rw [h p.1 (List.mem_map_of_mem hp)]

theorem renGlobdef_congr (d : globdef (fundef function) type) (hg : ∀ x ∈ globdefG d, g x = g' x)
    (ht : ∀ x ∈ globdefT d, t x = t' x) : renGlobdef g t d = renGlobdef g' t' d := by
  cases d with
  | Gfun fd =>
      cases fd with
      | Internal f =>
          have hp : renBindings t f.fn_params = renBindings t' f.fn_params :=
            renBindings_congr fun x hx => ht x (by
              rw [globdefT]; exact List.mem_append_left _ (List.mem_append_left _ hx))
          have hv : renBindings g f.fn_vars = renBindings g' f.fn_vars :=
            renBindings_congr fun x hx => hg x (by
              rw [globdefG]; exact List.mem_append_left _ hx)
          have htm : renBindings t f.fn_temps = renBindings t' f.fn_temps :=
            renBindings_congr fun x hx => ht x (by
              rw [globdefT]; exact List.mem_append_left _ (List.mem_append_right _ hx))
          have hb : renStmt g t f.fn_body = renStmt g' t' f.fn_body :=
            renStmt_congr f.fn_body
              (fun x hx => hg x (by rw [globdefG]; exact List.mem_append_right _ hx))
              (fun x hx => ht x (by rw [globdefT]; exact List.mem_append_right _ hx))
          simp only [renGlobdef, renFundef, renFunction, hp, hv, htm, hb]
      | External => rfl
  | Gvar v =>
      have hi : v.gvar_init.map (renInit g) = v.gvar_init.map (renInit g') := by
        refine List.map_congr_left fun i hi => ?_
        cases i with
        | Init_addrof id ofs =>
            simp only [renInit, hg id (List.mem_flatMap.mpr ⟨_, hi, by simp⟩)]
        | _ => rfl
      simp only [renGlobdef, hi]

end Congr

/-- The judgment of a whole program survives every renaming that is injective on the
identifiers of globals in the program, `progG p`, and, for each identifier `id`, on the
temporaries of the definitions under `id`.  The trace is renamed by an injective map that agrees
with `g` on `progG p`. -/
theorem bigstep_program_terminates_rename_on {A : Archi} {g : ident → ident}
    {τ : ident → ident → ident} {p p' : program function}
    (hg : ∀ x ∈ progG p, ∀ y ∈ progG p, g x = g y → x = y)
    (hτ : ∀ id, ∀ x ∈ tempsOf p.prog_defs id, ∀ y ∈ tempsOf p.prog_defs id,
      τ id x = τ id y → x = y)
    (hdefs : p'.prog_defs = renDefs g τ p.prog_defs) (hmain : p'.prog_main = g p.prog_main)
    {tr : trace} {r : int} (h : bigstep_program_terminates A ExtSem.none p tr r) (X' : ExtSem) :
    ∃ g' : ident → ident, (∀ x ∈ progG p, g' x = g x) ∧
      bigstep_program_terminates A X' p' (renTrace g' tr) r := by
  obtain ⟨g', hinj, heq⟩ := exists_injective_extension (progG p) g hg
  have hext := fun id => exists_injective_extension (tempsOf p.prog_defs id) (τ id) (hτ id)
  let τ' := fun id => Classical.choose (hext id)
  have hτ' : ∀ id, Function.Injective (τ' id) := fun id => (Classical.choose_spec (hext id)).1
  have hτeq : ∀ id, ∀ x ∈ tempsOf p.prog_defs id, τ' id x = τ id x :=
    fun id => (Classical.choose_spec (hext id)).2
  have hsame : renDefs g' τ' p.prog_defs = renDefs g τ p.prog_defs := by
    refine List.map_congr_left fun d hd => ?_
    have hd1 : d.1 ∈ progG p := List.mem_cons_of_mem _
      (List.mem_flatMap.mpr ⟨d, hd, List.mem_cons_self ..⟩)
    rw [heq d.1 hd1, renGlobdef_congr d.2
      (fun x hx => heq x (List.mem_cons_of_mem _
        (List.mem_flatMap.mpr ⟨d, hd, List.mem_cons_of_mem _ hx⟩)))
      (fun x hx => hτeq d.1 x (List.mem_flatMap.mpr
        ⟨d, List.mem_filter.mpr ⟨hd, by simp⟩, hx⟩))]
  exact ⟨g', heq, bigstep_program_terminates_rename_none hinj hτ' (by rw [hdefs, hsame])
    (by rw [hmain, heq _ (List.mem_cons_self ..)]) h X'⟩

end LClight
