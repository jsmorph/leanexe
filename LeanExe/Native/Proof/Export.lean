import LeanExe.Native.Proof.Genv

/-!
The program of `clightgen`'s Coq file.  `clightgen` prints a statement with `stmt` of
`export/ExportClight.ml` (lines 88 to 136), which drops a `Sskip` on either side of a sequence
(lines 104 to 107) and prints two forms of loop as `Swhile` (lines 112 to 115), which the file
reads back by `Swhile`'s definition (`cfrontend/Clight.v`, lines 119 and 120).  `exportStmt`
transcribes `stmt` as the statement that its output denotes, so the program of the file is
`exportProgram` of the program inside `clightgen`.  `ExportRel s' s` relates a statement `s'` to
every statement `s` from which removing sequences with `Sskip` gives it, and `exportStmt_rel`
shows that it relates `exportStmt s` to `s`.
-/

namespace LClight

mutual
  /-- The statement that `stmt` of `export/ExportClight.ml` prints for `s`. -/
  def exportStmt : statement → statement
    | .Ssequence .Sskip s2 => exportStmt s2
    | .Ssequence s1 .Sskip => exportStmt s1
    | .Ssequence s1 s2 => .Ssequence (exportStmt s1) (exportStmt s2)
    | .Sifthenelse e s1 s2 => .Sifthenelse e (exportStmt s1) (exportStmt s2)
    | .Sloop (.Ssequence (.Sifthenelse e .Sskip .Sbreak) s) .Sskip =>
        .Sloop (.Ssequence (.Sifthenelse e .Sskip .Sbreak) (exportStmt s)) .Sskip
    | .Sloop (.Ssequence (.Ssequence .Sskip (.Sifthenelse e .Sskip .Sbreak)) s) .Sskip =>
        .Sloop (.Ssequence (.Sifthenelse e .Sskip .Sbreak) (exportStmt s)) .Sskip
    | .Sloop s1 s2 => .Sloop (exportStmt s1) (exportStmt s2)
    | .Sswitch e ls => .Sswitch e (exportLS ls)
    | .Slabel l s => .Slabel l (exportStmt s)
    | s => s

  /-- `lblstmts` of `export/ExportClight.ml`, lines 131 to 136. -/
  def exportLS : labeled_statements → labeled_statements
    | .LSnil => .LSnil
    | .LScons c s ls => .LScons c (exportStmt s) (exportLS ls)
end

/-- A statement other than a sequence, a conditional, or a loop. -/
def isAtom : statement → Bool
  | .Ssequence .. | .Sifthenelse .. | .Sloop .. => false
  | _ => true

/-- `s'` is `s` with sequences with `Sskip` removed. -/
inductive ExportRel : statement → statement → Prop
  | skip_left {s' s : statement} : ExportRel s' s → ExportRel s' (.Ssequence .Sskip s)
  | skip_right {s' s : statement} : ExportRel s' s → ExportRel s' (.Ssequence s .Sskip)
  | atom (s : statement) : isAtom s = true → ExportRel s s
  | seq {a b s1 s2 : statement} : ExportRel a s1 → ExportRel b s2 →
      ExportRel (.Ssequence a b) (.Ssequence s1 s2)
  | ite (e : expr) {a b s1 s2 : statement} : ExportRel a s1 → ExportRel b s2 →
      ExportRel (.Sifthenelse e a b) (.Sifthenelse e s1 s2)
  | loop {a b s1 s2 : statement} : ExportRel a s1 → ExportRel b s2 →
      ExportRel (.Sloop a b) (.Sloop s1 s2)
  | switch (e : expr) (ls ls' : labeled_statements) : ExportRel (.Sswitch e ls') (.Sswitch e ls)
  | label (l : ident) (s s' : statement) : ExportRel (.Slabel l s') (.Slabel l s)

theorem ExportRel.skip : ExportRel .Sskip .Sskip := .atom _ rfl
theorem ExportRel.brk : ExportRel .Sbreak .Sbreak := .atom _ rfl

theorem exportStmt_rel (s : statement) : ExportRel (exportStmt s) s := by
  match s with
  | .Ssequence s1 s2 =>
      have h1 := exportStmt_rel s1
      have h2 := exportStmt_rel s2
      unfold exportStmt
      split
      all_goals first
        | (rename_i heq; injection heq with e1 e2; subst e1 e2
           first | exact .skip_left h2 | exact .skip_right h1 | exact .seq h1 h2)
        | (rename_i heq; cases heq; done)
        | (exfalso; simp_all)
  | .Sifthenelse e s1 s2 =>
      unfold exportStmt
      exact .ite e (exportStmt_rel s1) (exportStmt_rel s2)
  | .Sloop s1 s2 =>
      have h1 := exportStmt_rel s1
      have h2 := exportStmt_rel s2
      unfold exportStmt
      split
      all_goals first
        | (rename_i heq; injection heq with e1 e2; subst e1 e2
           first
            | exact .loop (.seq (.ite _ .skip .brk) (exportStmt_rel _)) .skip
            | exact .loop (.seq (.skip_left (.ite _ .skip .brk)) (exportStmt_rel _)) .skip
            | exact .loop h1 h2)
        | (rename_i heq; cases heq; done)
        | (exfalso; simp_all)
  | .Sswitch e ls => unfold exportStmt; exact .switch e ls _
  | .Slabel l s => unfold exportStmt; exact .label l s _
  | .Sskip | .Sassign .. | .Sset .. | .Scall .. | .Sbuiltin .. | .Sbreak | .Scontinue
  | .Sreturn _ | .Sgoto _ => unfold exportStmt; exact .atom _ rfl
termination_by sizeOf s
decreasing_by all_goals (simp_wf; first | omega | (simp_all; omega) | (subst_vars; simp; omega))

/-! ## The relation in steps

A related statement is a core, whose last step relates its constructor, wrapped in sequences with
`Sskip`, and wrapping preserves every execution. -/

/-- `s` is `c` wrapped in sequences with `Sskip`. -/
inductive Wrap : statement → statement → Prop
  | refl (c : statement) : Wrap c c
  | left {c s : statement} : Wrap c s → Wrap c (.Ssequence .Sskip s)
  | right {c s : statement} : Wrap c s → Wrap c (.Ssequence s .Sskip)

/-- The last step of `ExportRel`, other than a wrapping. -/
inductive CoreRel : statement → statement → Prop
  | atom (s : statement) : isAtom s = true → CoreRel s s
  | seq {a b s1 s2 : statement} : ExportRel a s1 → ExportRel b s2 →
      CoreRel (.Ssequence a b) (.Ssequence s1 s2)
  | ite (e : expr) {a b s1 s2 : statement} : ExportRel a s1 → ExportRel b s2 →
      CoreRel (.Sifthenelse e a b) (.Sifthenelse e s1 s2)
  | loop {a b s1 s2 : statement} : ExportRel a s1 → ExportRel b s2 →
      CoreRel (.Sloop a b) (.Sloop s1 s2)
  | switch (e : expr) (ls ls' : labeled_statements) : CoreRel (.Sswitch e ls') (.Sswitch e ls)
  | label (l : ident) (s s' : statement) : CoreRel (.Slabel l s') (.Slabel l s)

theorem ExportRel.core {s' s : statement} (h : ExportRel s' s) : ∃ c, Wrap c s ∧ CoreRel s' c := by
  induction h with
  | skip_left _ ih => obtain ⟨c, hw, hc⟩ := ih; exact ⟨c, .left hw, hc⟩
  | skip_right _ ih => obtain ⟨c, hw, hc⟩ := ih; exact ⟨c, .right hw, hc⟩
  | atom s hs => exact ⟨s, .refl s, .atom s hs⟩
  | seq ha hb => exact ⟨_, .refl _, .seq ha hb⟩
  | ite e ha hb => exact ⟨_, .refl _, .ite e ha hb⟩
  | loop ha hb => exact ⟨_, .refl _, .loop ha hb⟩
  | switch e ls ls' => exact ⟨_, .refl _, .switch e ls ls'⟩
  | label l s s' => exact ⟨_, .refl _, .label l s s'⟩

section

variable {A : Archi} {X : ExtSem} {ge : genv}

theorem Wrap.exec {c s : statement} (hw : Wrap c s) {e : env} {le : temp_env} {m : mem}
    {t : trace} {le' : temp_env} {m' : mem} {out : outcome}
    (h : exec_stmt A X ge e le m c t le' m' out) : exec_stmt A X ge e le m s t le' m' out := by
  induction hw with
  | refl => exact h
  | left _ ih =>
      have := exec_stmt.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (.exec_Sskip e le m) ih
      simpa [E0] using this
  | right _ ih =>
      by_cases ho : out = .Out_normal
      · subst ho
        have := exec_stmt.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ ih (.exec_Sskip e le' m')
        simpa [E0] using this
      · exact .exec_Sseq_2 _ _ _ _ _ _ _ _ _ ih ho

end

/-! ## Programs -/

/-- The function whose body the exporter prints. -/
def exportFunction (f : function) : function := { f with fn_body := exportStmt f.fn_body }

def exportFundef : fundef function → fundef function
  | .Internal f => .Internal (exportFunction f)
  | fd => fd

def exportGlobdef : globdef (fundef function) type → globdef (fundef function) type
  | .Gfun fd => .Gfun (exportFundef fd)
  | g => g

/-- The program of the Coq file that `clightgen` writes for `p`: `print_function` of
`export/ExportClight.ml` (lines 140 to 149) prints a function's body with `stmt` and the rest as
it is. -/
def exportProgram (p : program function) : program function :=
  { p with prog_defs := p.prog_defs.map fun d => (d.1, exportGlobdef d.2) }

theorem type_of_exportFundef (fd : fundef function) :
    type_of_fundef (exportFundef fd) = type_of_fundef fd := by
  cases fd <;> rfl

/-- The global environment `ge'` of the file and `ge` of the program inside `clightgen`. -/
structure GenvExport (ge' ge : genv) : Prop where
  symb : ge'.genv_symb = ge.genv_symb
  defs : ∀ b, Genv.find_def ge' b = (Genv.find_def ge b).map exportGlobdef

theorem GenvExport.find_symbol {ge' ge : genv} (h : GenvExport ge' ge) (id : ident) :
    Genv.find_symbol ge' id = Genv.find_symbol ge id := by
  simp [Genv.find_symbol, h.symb]

theorem GenvExport.block_is_volatile {ge' ge : genv} (h : GenvExport ge' ge) (b : block) :
    Genv.block_is_volatile ge' b = Genv.block_is_volatile ge b := by
  simp only [Genv.block_is_volatile, Genv.find_var_info, h.defs b]
  cases Genv.find_def ge b with
  | none => rfl
  | some d => cases d <;> rfl

theorem GenvExport.find_funct {ge' ge : genv} (h : GenvExport ge' ge) {v : val}
    {fd' : fundef function} (hf : Genv.find_funct ge' v = some fd') :
    ∃ fd, Genv.find_funct ge v = some fd ∧ fd' = exportFundef fd := by
  cases v with
  | Vptr b ofs =>
      simp only [Genv.find_funct] at hf ⊢
      split at hf
      · simp only [Genv.find_funct_ptr, h.defs b] at hf
        cases hd : Genv.find_def ge b with
        | none => simp [hd] at hf
        | some d =>
            cases d with
            | Gfun fd =>
                simp only [hd, Option.map_some, exportGlobdef, Option.some.injEq] at hf
                exact ⟨fd, by simp [*, Genv.find_funct_ptr], hf.symm⟩
            | Gvar v => simp [hd, exportGlobdef] at hf
      · cases hf
  | _ => simp [Genv.find_funct] at hf

/-! ## Runs of the file's program are runs of the program inside `clightgen` -/

section

variable {A : Archi} {X : ExtSem} {ge' ge : genv}

mutual
  theorem eval_expr_export (hge : GenvExport ge' ge) {e : env} {le : temp_env} {m : mem}
      {a : expr} {v : val} (h : eval_expr A ge' e le m a v) : eval_expr A ge e le m a v := by
    match h with
    | .eval_Econst_int i ty => exact .eval_Econst_int i ty
    | .eval_Econst_float f ty => exact .eval_Econst_float f ty
    | .eval_Econst_single f ty => exact .eval_Econst_single f ty
    | .eval_Econst_long i ty => exact .eval_Econst_long i ty
    | .eval_Etempvar id ty v hv => exact .eval_Etempvar id ty v hv
    | .eval_Eaddrof a ty loc ofs hl => exact .eval_Eaddrof a ty loc ofs (eval_lvalue_export hge hl)
    | .eval_Eunop op a ty v1 v h1 hop => exact .eval_Eunop op a ty v1 v (eval_expr_export hge h1) hop
    | .eval_Ebinop op a1 a2 ty v1 v2 v h1 h2 hop =>
        exact .eval_Ebinop op a1 a2 ty v1 v2 v (eval_expr_export hge h1) (eval_expr_export hge h2) hop
    | .eval_Ecast a ty v1 v h1 hc => exact .eval_Ecast a ty v1 v (eval_expr_export hge h1) hc
    | .eval_Elvalue a loc ofs bf v hl hd =>
        exact .eval_Elvalue a loc ofs bf v (eval_lvalue_export hge hl) hd

  theorem eval_lvalue_export (hge : GenvExport ge' ge) {e : env} {le : temp_env} {m : mem}
      {a : expr} {l : block} {ofs : ptrofs} {bf : bitfield}
      (h : eval_lvalue A ge' e le m a l ofs bf) : eval_lvalue A ge e le m a l ofs bf := by
    match h with
    | .eval_Evar_local id l ty he => exact .eval_Evar_local id l ty he
    | .eval_Evar_global id l ty he hs =>
        exact .eval_Evar_global id l ty he (by rw [← hge.find_symbol]; exact hs)
    | .eval_Ederef a ty l ofs ha => exact .eval_Ederef a ty l ofs (eval_expr_export hge ha)
end

theorem eval_exprlist_export (hge : GenvExport ge' ge) {e : env} {le : temp_env} {m : mem} :
    ∀ {al : List expr} {tys : List type} {vl : List val},
      eval_exprlist A ge' e le m al tys vl → eval_exprlist A ge e le m al tys vl
  | [], [], [], .eval_Enil => .eval_Enil
  | _ :: _, _ :: _, _ :: _, .eval_Econs a bl ty tyl v1 v2 vl h1 hc hl =>
      .eval_Econs a bl ty tyl v1 v2 vl (eval_expr_export hge h1) hc (eval_exprlist_export hge hl)

theorem volatile_store_export (hge : GenvExport ge' ge) :
    ∀ {chunk : memory_chunk} {m : mem} {b : block} {ofs : ptrofs} {v : val} {t : trace} {m' : mem},
      volatile_store ge' chunk m b ofs v t m' → volatile_store ge chunk m b ofs v t m'
  | _, _, _, _, _, _, _, .volatile_store_vol chunk m b ofs id ev v hvol hs hm =>
      .volatile_store_vol chunk m b ofs id ev v (hge.block_is_volatile b ▸ hvol)
        (hge.find_symbol id ▸ hs) hm
  | _, _, _, _, _, _, _, .volatile_store_nonvol chunk m b ofs v m' hvol hst =>
      .volatile_store_nonvol chunk m b ofs v m' (hge.block_is_volatile b ▸ hvol) hst

theorem volatile_store_sem_export (hge : GenvExport ge' ge) {chunk : memory_chunk} :
    ∀ {vargs : List val} {m : mem} {t : trace} {vres : val} {m' : mem},
      volatile_store_sem chunk ge' vargs m t vres m' → volatile_store_sem chunk ge vargs m t vres m'
  | _, _, _, _, _, .volatile_store_sem_intro b ofs m1 v t m2 hv =>
      .volatile_store_sem_intro b ofs m1 v t m2 (volatile_store_export hge hv)

theorem volatile_load_export (hge : GenvExport ge' ge) :
    ∀ {chunk : memory_chunk} {m : mem} {b : block} {ofs : ptrofs} {t : trace} {v : val},
      volatile_load ge' chunk m b ofs t v → volatile_load ge chunk m b ofs t v
  | _, _, _, _, _, _, .volatile_load_vol chunk m b ofs id ev v hvol hs hm =>
      .volatile_load_vol chunk m b ofs id ev v (hge.block_is_volatile b ▸ hvol)
        (hge.find_symbol id ▸ hs) hm
  | _, _, _, _, _, _, .volatile_load_nonvol chunk m b ofs v hvol hl =>
      .volatile_load_nonvol chunk m b ofs v (hge.block_is_volatile b ▸ hvol) hl

theorem volatile_load_sem_export (hge : GenvExport ge' ge) {chunk : memory_chunk} :
    ∀ {vargs : List val} {m : mem} {t : trace} {vres : val} {m' : mem},
      volatile_load_sem chunk ge' vargs m t vres m' → volatile_load_sem chunk ge vargs m t vres m'
  | _, _, _, _, _, .volatile_load_sem_intro b ofs m t v hv =>
      .volatile_load_sem_intro b ofs m t v (volatile_load_export hge hv)

theorem external_call_export (hge : GenvExport ge' ge) {ef : external_function}
    {vargs : List val} {m : mem} {t : trace} {vres : val} {m' : mem}
    (h : external_call A X ef ge' vargs m t vres m') : external_call A X ef ge vargs m t vres m' := by
  cases ef with
  | EF_external name sg =>
      simp only [external_call] at h ⊢
      rw [← hge.symb]
      exact h
  | EF_vload chunk =>
      simp only [external_call] at h ⊢
      exact volatile_load_sem_export hge h
  | EF_vstore chunk =>
      simp only [external_call] at h ⊢
      exact volatile_store_sem_export hge h
  | _ => exact h

mutual
  /-- A run of the file's statement `s'` is a run of every core `c` of a statement related to
  it. -/
  theorem exec_export_core (hge : GenvExport ge' ge) {e : env} {le : temp_env} {m : mem}
      {s' : statement} {t : trace} {le' : temp_env} {m' : mem} {out : outcome}
      (h : exec_stmt A X ge' e le m s' t le' m' out) :
      ∀ {c : statement}, CoreRel s' c → exec_stmt A X ge e le m c t le' m' out := by
    match h with
    | .exec_Sskip .. => intro c hc; cases hc; exact .exec_Sskip _ _ _
    | .exec_Sassign _ _ _ a1 a2 loc ofs bf v2 v m2 hl hv hcast ha =>
        intro c hc
        cases hc
        exact .exec_Sassign _ _ _ a1 a2 loc ofs bf v2 v m2 (eval_lvalue_export hge hl)
          (eval_expr_export hge hv) hcast ha
    | .exec_Sset _ _ _ id a v hv =>
        intro c hc
        cases hc
        exact .exec_Sset _ _ _ id a v (eval_expr_export hge hv)
    | .exec_Scall _ _ _ optid a al tyargs tyres cconv vf vargs f tr m2 vres hcl ha hal hf hty
        hcall =>
        intro c hc
        cases hc
        obtain ⟨fd, hfd, hfe⟩ := hge.find_funct hf
        exact .exec_Scall _ _ _ optid a al tyargs tyres cconv vf vargs fd tr m2 vres hcl
          (eval_expr_export hge ha) (eval_exprlist_export hge hal) hfd
          (by rw [← type_of_exportFundef, ← hfe]; exact hty) (funcall_export hge hcall hfe)
    | .exec_Sbuiltin _ _ _ optid ef al tyargs vargs tr m2 vres hal hx =>
        intro c hc
        cases hc
        exact .exec_Sbuiltin _ _ _ optid ef al tyargs vargs tr m2 vres
          (eval_exprlist_export hge hal) (external_call_export hge hx)
    | .exec_Sseq_1 _ _ _ a b t1 le1 m1 t2 le2 m2 out h1 h2 =>
        intro c hc
        match hc with
        | .seq ha hb =>
            obtain ⟨c1, hw1, hc1⟩ := ha.core
            obtain ⟨c2, hw2, hc2⟩ := hb.core
            exact .exec_Sseq_1 _ _ _ _ _ _ le1 m1 _ le2 m2 out
              (hw1.exec (exec_export_core hge h1 hc1)) (hw2.exec (exec_export_core hge h2 hc2))
        | .atom _ hs => cases hs
    | .exec_Sseq_2 _ _ _ a b t1 le1 m1 out h1 hne =>
        intro c hc
        match hc with
        | .seq ha _ =>
            obtain ⟨c1, hw1, hc1⟩ := ha.core
            exact .exec_Sseq_2 _ _ _ _ _ _ le1 m1 out (hw1.exec (exec_export_core hge h1 hc1)) hne
        | .atom _ hs => cases hs
    | .exec_Sifthenelse _ _ _ a s1 s2 v1 b tr le2 m2 out ha hb hs =>
        intro c hc
        match hc with
        | .ite (s1 := t1) (s2 := t2) _ h1 h2 =>
            have hr : ExportRel (if b then s1 else s2) (if b then t1 else t2) := by
              cases b
              · exact h2
              · exact h1
            obtain ⟨c1, hw1, hc1⟩ := hr.core
            exact .exec_Sifthenelse _ _ _ a _ _ v1 b tr le2 m2 out (eval_expr_export hge ha) hb
              (hw1.exec (exec_export_core hge hs hc1))
        | .atom _ hs => cases hs
    | .exec_Sreturn_none .. => intro c hc; cases hc; exact .exec_Sreturn_none _ _ _
    | .exec_Sreturn_some _ _ _ a v hv =>
        intro c hc
        cases hc
        exact .exec_Sreturn_some _ _ _ a v (eval_expr_export hge hv)
    | .exec_Sbreak .. => intro c hc; cases hc; exact .exec_Sbreak _ _ _
    | .exec_Scontinue .. => intro c hc; cases hc; exact .exec_Scontinue _ _ _
    | .exec_Sloop_stop1 _ _ _ a b tr le2 m2 out' out h1 hbr =>
        intro c hc
        match hc with
        | .loop ha _ =>
            obtain ⟨c1, hw1, hc1⟩ := ha.core
            exact .exec_Sloop_stop1 _ _ _ _ _ _ le2 m2 out' out
              (hw1.exec (exec_export_core hge h1 hc1)) hbr
        | .atom _ hs => cases hs
    | .exec_Sloop_stop2 _ _ _ a b t1 le1 m1 out1 t2 le2 m2 out2 out h1 hnc h2 hbr =>
        intro c hc
        match hc with
        | .loop ha hb =>
            obtain ⟨c1, hw1, hc1⟩ := ha.core
            obtain ⟨c2, hw2, hc2⟩ := hb.core
            exact .exec_Sloop_stop2 _ _ _ _ _ _ le1 m1 out1 _ le2 m2 out2 out
              (hw1.exec (exec_export_core hge h1 hc1)) hnc
              (hw2.exec (exec_export_core hge h2 hc2)) hbr
        | .atom _ hs => cases hs
    | .exec_Sloop_loop _ _ _ a b t1 le1 m1 out1 t2 le2 m2 t3 le3 m3 out h1 hnc h2 h3 =>
        intro c hc
        match hc with
        | .loop ha hb =>
            obtain ⟨c1, hw1, hc1⟩ := ha.core
            obtain ⟨c2, hw2, hc2⟩ := hb.core
            exact .exec_Sloop_loop _ _ _ _ _ _ le1 m1 out1 _ le2 m2 _ le3 m3 out
              (hw1.exec (exec_export_core hge h1 hc1)) hnc
              (hw2.exec (exec_export_core hge h2 hc2)) (exec_export_core hge h3 (.loop ha hb))
        | .atom _ hs => cases hs

  theorem funcall_export (hge : GenvExport ge' ge) {m : mem} {fd' : fundef function}
      {vargs : List val} {t : trace} {m' : mem} {vres : val}
      (h : eval_funcall A X ge' m fd' vargs t m' vres) :
      ∀ {fd : fundef function}, fd' = exportFundef fd → eval_funcall A X ge m fd vargs t m' vres := by
    match h with
    | .eval_funcall_internal _ f' _ tr e le1 le2 m1 m2 out _ m3 hentry hbody hres hfree =>
        intro fd hfd
        match fd, hfd with
        | .Internal f, hfd =>
            have hf : f' = exportFunction f := by injection hfd
            have hr : ExportRel f'.fn_body f.fn_body := by rw [hf]; exact exportStmt_rel _
            obtain ⟨c, hw, hc⟩ := hr.core
            have he : function_entry2 f vargs m e le1 m1 := by
              rw [hf] at hentry
              cases hentry with
              | intro _ hv hn hd hb => exact .intro _ hv hn hd hb
            have hres' : outcome_result_value out f.fn_return vres m2 := by
              rw [hf] at hres; exact hres
            exact .eval_funcall_internal _ f _ tr e le1 le2 m1 m2 out _ m3 he
              (hw.exec (exec_export_core hge hbody hc)) hres' hfree
        | .External .., hfd => cases hfd
    | .eval_funcall_external _ ef targs tres cconv _ tr _ _ hx =>
        intro fd hfd
        match fd, hfd with
        | .External .., hfd =>
            cases hfd
            exact .eval_funcall_external _ ef targs tres cconv _ tr _ _ (external_call_export hge hx)
        | .Internal _, hfd => cases hfd
end

/-- A run of the file's statement is a run of every statement related to it. -/
theorem exec_export (hge : GenvExport ge' ge) {e : env} {le : temp_env} {m : mem}
    {s' : statement} {t : trace} {le' : temp_env} {m' : mem} {out : outcome}
    (h : exec_stmt A X ge' e le m s' t le' m' out) {s : statement} (hr : ExportRel s' s) :
    exec_stmt A X ge e le m s t le' m' out := by
  obtain ⟨c, hw, hc⟩ := hr.core
  exact hw.exec (exec_export_core hge h hc)

end

/-! ## Whole programs -/

theorem GenvExport.find_funct_ptr {ge' ge : genv} (h : GenvExport ge' ge) {b : block}
    {fd' : fundef function} (hf : Genv.find_funct_ptr ge' b = some fd') :
    ∃ fd, Genv.find_funct_ptr ge b = some fd ∧ fd' = exportFundef fd := by
  have := h.find_funct (v := .Vptr b Ptrofs.zero) (by simpa [Genv.find_funct] using hf)
  simpa [Genv.find_funct] using this

theorem add_globals_export :
    ∀ (gl : List (ident × globdef (fundef function) type)) (ge ge' : genv),
      ge'.genv_next = ge.genv_next → GenvExport ge' ge →
      (Genv.add_globals ge' (gl.map fun d => (d.1, exportGlobdef d.2))).genv_next =
          (Genv.add_globals ge gl).genv_next ∧
        GenvExport (Genv.add_globals ge' (gl.map fun d => (d.1, exportGlobdef d.2)))
          (Genv.add_globals ge gl)
  | [], _, _, hn, h => ⟨hn, h⟩
  | x :: gl, ge, ge', hn, h => by
      refine add_globals_export gl (Genv.add_global ge x)
        (Genv.add_global ge' (x.1, exportGlobdef x.2)) (by simp [Genv.add_global, hn])
        ⟨by simp [Genv.add_global, h.symb, hn], fun b => ?_⟩
      simp only [Genv.find_def, Genv.add_global, hn]
      by_cases hb : ge.genv_next = b
      · subst hb
        rw [Std.TreeMap.getElem?_insert_self, Std.TreeMap.getElem?_insert_self]
        rfl
      · rw [Genv.defs_insert_ne _ hb, Genv.defs_insert_ne _ hb]
        exact h.defs b

theorem globalenv_export (p : program function) :
    GenvExport (globalenv (exportProgram p)) (globalenv p) :=
  (add_globals_export p.prog_defs (Genv.empty_genv p.prog_public)
    (Genv.empty_genv p.prog_public) rfl ⟨rfl, fun b => by simp [Genv.find_def, Genv.empty_genv]⟩).2

theorem store_init_data_list_export {ge' ge : genv} (h : GenvExport ge' ge) (b : block) :
    ∀ (l : List init_data) (m : mem) (p : _root_.Int),
      Genv.store_init_data_list ge' m b p l = Genv.store_init_data_list ge m b p l
  | [], _, _ => rfl
  | d :: l, m, p => by
      have hstore : Genv.store_init_data ge' m b p d = Genv.store_init_data ge m b p d := by
        cases d with
        | Init_addrof id ofs => simp [Genv.store_init_data, h.find_symbol]
        | _ => rfl
      simp only [Genv.store_init_data_list, hstore]
      cases Genv.store_init_data ge m b p d with
      | none => rfl
      | some m' => exact store_init_data_list_export h b l m' _

theorem alloc_globals_export {ge' ge : genv} (h : GenvExport ge' ge) :
    ∀ (gl : List (ident × globdef (fundef function) type)) (m : mem),
      Genv.alloc_globals ge' m (gl.map fun d => (d.1, exportGlobdef d.2)) =
        Genv.alloc_globals ge m gl
  | [], _ => rfl
  | x :: gl, m => by
      have hx : Genv.alloc_global ge' m (x.1, exportGlobdef x.2) = Genv.alloc_global ge m x := by
        obtain ⟨id, d⟩ := x
        cases d with
        | Gfun f => rfl
        | Gvar v => simp only [Genv.alloc_global, exportGlobdef, store_init_data_list_export h]
      simp only [List.map_cons, Genv.alloc_globals] at hx ⊢
      rw [hx]
      cases Genv.alloc_global ge m x with
      | none => rfl
      | some m' => exact alloc_globals_export h gl m'

theorem init_mem_export (p : program function) : init_mem (exportProgram p) = init_mem p :=
  alloc_globals_export (globalenv_export p) p.prog_defs Mem.empty

/-- A run of the program of `clightgen`'s Coq file is a run of the program inside `clightgen`
with the same trace and result. -/
theorem bigstep_program_terminates_export {A : Archi} {X : ExtSem} {p : program function}
    {t : trace} {r : int} (h : bigstep_program_terminates A X (exportProgram p) t r) :
    bigstep_program_terminates A X p t r := by
  obtain ⟨b, fd', m0, m1, t, r, hinit, hs, hf, hty, hcall⟩ := h
  have hge := globalenv_export p
  obtain ⟨fd, hfd, hfe⟩ := hge.find_funct_ptr hf
  exact .bigstep_program_terminates_intro b fd m0 m1 t r (by rw [← init_mem_export]; exact hinit)
    (by rw [← hge.find_symbol]; exact hs) hfd (by rw [← type_of_exportFundef, ← hfe]; exact hty)
    (funcall_export hge hcall hfe)

end LClight
