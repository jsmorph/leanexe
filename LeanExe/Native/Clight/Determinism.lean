import LeanExe.Native.Clight.Bigstep

/-!
The big-step semantics of `Bigstep.lean` is deterministic relative to the trace.  Expression
evaluation is a function of the global environment, the local and temporary environments, and
the memory (`eval_expr_determ`, `eval_lvalue_determ`, and `eval_exprlist_determ`).  Two
executions of a statement or a call from one state with one trace end in the same state with the
same outcome or result (`exec_stmt_determ` and `eval_funcall_determ`), and a program terminates
with at most one result for a trace (`bigstep_program_terminates_determ`).

External functions and volatile loads take values from outside the program, and the trace
records them, so the theorems compare executions with equal traces.  The semantics `X` of
external functions is a parameter, and the theorems assume `X.Determ`: two calls of an external
function on the same symbols, arguments, and memory, whose traces agree up to the length of the
shorter, have the same trace, result, and memory.  CompCert's `ec_determ` (`Events.v`, lines 701
to 704) implies it, since `match_traces` relates only traces of equal length.  A hypothesis about
equal traces alone would not suffice.  If an external function may return 0 with the trace `[e]`
or 1 with the trace `[e, e']`, a call to it followed by a statement that emits `e'` when the
result is 0 has two executions with the trace `[e, e']` and different results.

The proofs go by induction on the first execution.  The two executions of `s₁; s₂` may divide
their trace differently between `s₁` and `s₂`, so the induction compares traces that agree up to
the length of the shorter, as `X.Determ` does.  `exec_stmt_determ_prefix`,
`eval_funcall_determ_prefix`, and `bigstep_program_terminates_determ_prefix` state this form:
such executions have the same trace and end in the same state.  A termination of a program with
the empty trace is therefore its only termination (`bigstep_program_terminates_E0`).

CompCert 3.18 proves no determinism theorem for Clight in either of its semantics.  For the
small-step semantics, `Clight.v` proves receptiveness (`semantics_receptive`, line 738).
CompCert's determinacy theorems are `semantics_determinate` of Cminor (`backend/Cminor.v`, line
635) and of each target's Asm, whose field `sd_determ` states that two steps from one state have
traces that `match_traces` relates and, with equal traces, reach one state.
-/

namespace LClight

/-- The external functions of `X` are deterministic relative to the trace: two calls of one
function on the same symbols, arguments, and memory, whose traces agree up to the length of the
shorter, have the same trace, result, and memory. -/
def ExtSem.Determ (X : ExtSem) : Prop :=
  ∀ (name : String) (sg : signature) (symb : Std.TreeMap ident block) (vargs : List val)
    (m : mem) (t₁ : trace) (vres₁ : val) (m₁ : mem) (t₂ : trace) (vres₂ : val) (m₂ : mem)
    (u₁ u₂ : trace),
    X.external_functions_sem name sg symb vargs m t₁ vres₁ m₁ →
    X.external_functions_sem name sg symb vargs m t₂ vres₂ m₂ →
    t₁ ++ u₁ = t₂ ++ u₂ → t₁ = t₂ ∧ vres₁ = vres₂ ∧ m₁ = m₂

private theorem singleton_append_eq {α : Type} {a b : α} {u₁ u₂ : List α}
    (h : [a] ++ u₁ = [b] ++ u₂) : a = b :=
  (List.cons.inj h).1

/-! ## External calls -/

theorem eventval_match_determ {ev : eventval} {ty : typ} {v₁ v₂ : val}
    (h₁ : eventval_match ev ty v₁) (h₂ : eventval_match ev ty v₂) : v₁ = v₂ := by
  cases h₁ <;> cases h₂ <;> rfl

theorem volatile_load_determ {F V : Type} {ge : Genv.t F V} {chunk : memory_chunk} {m : mem}
    {b : block} {ofs : ptrofs} {t₁ t₂ u₁ u₂ : trace} {v₁ v₂ : val}
    (h₁ : volatile_load ge chunk m b ofs t₁ v₁) (h₂ : volatile_load ge chunk m b ofs t₂ v₂)
    (hu : t₁ ++ u₁ = t₂ ++ u₂) : t₁ = t₂ ∧ v₁ = v₂ := by
  cases h₁ with
  | volatile_load_vol _ _ _ hvol _ hm =>
      cases h₂ with
      | volatile_load_vol _ _ _ _ _ hm' =>
          cases singleton_append_eq hu
          exact ⟨rfl, by rw [eventval_match_determ hm hm']⟩
      | volatile_load_nonvol _ hvol' _ =>
          rw [hvol] at hvol'
          cases hvol'
  | volatile_load_nonvol _ hvol hl =>
      cases h₂ with
      | volatile_load_vol _ _ _ hvol' _ _ =>
          rw [hvol] at hvol'
          cases hvol'
      | volatile_load_nonvol _ _ hl' =>
          exact ⟨rfl, Option.some.inj (hl.symm.trans hl')⟩

theorem volatile_store_determ {F V : Type} {ge : Genv.t F V} {chunk : memory_chunk} {m : mem}
    {b : block} {ofs : ptrofs} {v : val} {t₁ t₂ u₁ u₂ : trace} {m₁ m₂ : mem}
    (h₁ : volatile_store ge chunk m b ofs v t₁ m₁) (h₂ : volatile_store ge chunk m b ofs v t₂ m₂)
    (hu : t₁ ++ u₁ = t₂ ++ u₂) : t₁ = t₂ ∧ m₁ = m₂ := by
  cases h₁ with
  | volatile_store_vol _ _ _ hvol _ _ =>
      cases h₂ with
      | volatile_store_vol _ _ _ _ _ _ =>
          cases singleton_append_eq hu
          exact ⟨rfl, rfl⟩
      | volatile_store_nonvol _ _ hvol' _ =>
          rw [hvol] at hvol'
          cases hvol'
  | volatile_store_nonvol _ _ hvol hs =>
      cases h₂ with
      | volatile_store_vol _ _ _ hvol' _ _ =>
          rw [hvol] at hvol'
          cases hvol'
      | volatile_store_nonvol _ _ _ hs' =>
          exact ⟨rfl, Option.some.inj (hs.symm.trans hs')⟩

theorem external_call_determ {A : Archi} {X : ExtSem} (hX : X.Determ) {F V : Type}
    {ef : external_function} {ge : Genv.t F V} {vargs : List val} {m : mem}
    {t₁ t₂ u₁ u₂ : trace} {vres₁ vres₂ : val} {m₁ m₂ : mem}
    (h₁ : external_call A X ef ge vargs m t₁ vres₁ m₁)
    (h₂ : external_call A X ef ge vargs m t₂ vres₂ m₂) (hu : t₁ ++ u₁ = t₂ ++ u₂) :
    t₁ = t₂ ∧ vres₁ = vres₂ ∧ m₁ = m₂ := by
  cases ef with
  | EF_external name sg => exact hX name sg _ vargs m t₁ vres₁ m₁ t₂ vres₂ m₂ u₁ u₂ h₁ h₂ hu
  | EF_builtin name sg =>
      cases hb : lookup_builtin_function name sg with
      | none => simp [external_call, hb] at h₁
      | some bf =>
          simp only [external_call, hb, known_builtin_sem] at h₁ h₂
          obtain ⟨hv₁, rfl, rfl⟩ := h₁
          obtain ⟨hv₂, rfl, rfl⟩ := h₂
          exact ⟨rfl, Option.some.inj (hv₁.symm.trans hv₂), rfl⟩
  | EF_vload chunk =>
      simp only [external_call] at h₁ h₂
      cases h₁ with
      | volatile_load_sem_intro _ _ _ _ _ hl =>
          cases h₂ with
          | volatile_load_sem_intro _ _ _ _ _ hl' =>
              obtain ⟨rfl, rfl⟩ := volatile_load_determ hl hl' hu
              exact ⟨rfl, rfl, rfl⟩
  | EF_vstore chunk =>
      simp only [external_call] at h₁ h₂
      cases h₁ with
      | volatile_store_sem_intro _ _ _ _ _ _ hs =>
          cases h₂ with
          | volatile_store_sem_intro _ _ _ _ _ _ hs' =>
              obtain ⟨rfl, rfl⟩ := volatile_store_determ hs hs' hu
              exact ⟨rfl, rfl, rfl⟩
  | _ => simp [external_call] at h₁

/-! ## Expressions -/

section Eval

variable {A : Archi} {ge : genv} {e : env} {le : temp_env} {m : mem}

theorem deref_loc_determ {ty : type} {m : mem} {b : block} {ofs : ptrofs} {bf : bitfield}
    {v₁ v₂ : val} (h₁ : deref_loc ty m b ofs bf v₁) (h₂ : deref_loc ty m b ofs bf v₂) :
    v₁ = v₂ := by
  cases h₁ with
  | deref_loc_value _ _ ha hl =>
      cases h₂ with
      | deref_loc_value _ _ ha' hl' =>
          rw [ha] at ha'
          cases ha'
          exact Option.some.inj (hl.symm.trans hl')
      | deref_loc_reference ha' =>
          rw [ha] at ha'
          cases ha'
  | deref_loc_reference ha =>
      cases h₂ with
      | deref_loc_value _ _ ha' _ =>
          rw [ha] at ha'
          cases ha'
      | deref_loc_reference _ => rfl

theorem assign_loc_determ {ty : type} {m : mem} {b : block} {ofs : ptrofs} {bf : bitfield}
    {v : val} {m₁ m₂ : mem} (h₁ : assign_loc ty m b ofs bf v m₁)
    (h₂ : assign_loc ty m b ofs bf v m₂) : m₁ = m₂ := by
  cases h₁ with
  | assign_loc_value _ _ _ ha hs =>
      cases h₂ with
      | assign_loc_value _ _ _ ha' hs' =>
          rw [ha] at ha'
          cases ha'
          exact Option.some.inj (hs.symm.trans hs')

/-- `eval_expr` and `eval_lvalue` are functions together: the value of `Eaddrof a` is the
location of `a`, and the location of `Ederef a` is the value of `a`. -/
theorem eval_determ (a : expr) :
    (∀ {v₁ v₂ : val}, eval_expr A ge e le m a v₁ → eval_expr A ge e le m a v₂ → v₁ = v₂) ∧
    (∀ {l₁ l₂ : block} {o₁ o₂ : ptrofs} {bf₁ bf₂ : bitfield},
      eval_lvalue A ge e le m a l₁ o₁ bf₁ → eval_lvalue A ge e le m a l₂ o₂ bf₂ →
      l₁ = l₂ ∧ o₁ = o₂ ∧ bf₁ = bf₂) := by
  induction a with
  | Econst_int i ty =>
      refine ⟨fun h₁ h₂ => ?_, fun h₁ _ => nomatch h₁⟩
      cases h₁ with
      | eval_Econst_int =>
          cases h₂ with
          | eval_Econst_int => rfl
          | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
      | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
  | Econst_float f ty =>
      refine ⟨fun h₁ h₂ => ?_, fun h₁ _ => nomatch h₁⟩
      cases h₁ with
      | eval_Econst_float =>
          cases h₂ with
          | eval_Econst_float => rfl
          | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
      | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
  | Econst_single f ty =>
      refine ⟨fun h₁ h₂ => ?_, fun h₁ _ => nomatch h₁⟩
      cases h₁ with
      | eval_Econst_single =>
          cases h₂ with
          | eval_Econst_single => rfl
          | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
      | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
  | Econst_long i ty =>
      refine ⟨fun h₁ h₂ => ?_, fun h₁ _ => nomatch h₁⟩
      cases h₁ with
      | eval_Econst_long =>
          cases h₂ with
          | eval_Econst_long => rfl
          | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
      | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
  | Evar id ty =>
      have hlv : ∀ {l₁ l₂ : block} {o₁ o₂ : ptrofs} {bf₁ bf₂ : bitfield},
          eval_lvalue A ge e le m (.Evar id ty) l₁ o₁ bf₁ →
          eval_lvalue A ge e le m (.Evar id ty) l₂ o₂ bf₂ → l₁ = l₂ ∧ o₁ = o₂ ∧ bf₁ = bf₂ := by
        intro l₁ l₂ o₁ o₂ bf₁ bf₂ h₁ h₂
        cases h₁ with
        | eval_Evar_local _ _ _ he =>
            cases h₂ with
            | eval_Evar_local _ _ _ he' =>
                rw [he] at he'
                cases he'
                exact ⟨rfl, rfl, rfl⟩
            | eval_Evar_global _ _ _ he' _ =>
                rw [he] at he'
                cases he'
        | eval_Evar_global _ _ _ he hs =>
            cases h₂ with
            | eval_Evar_local _ _ _ he' =>
                rw [he] at he'
                cases he'
            | eval_Evar_global _ _ _ _ hs' =>
                rw [hs] at hs'
                cases hs'
                exact ⟨rfl, rfl, rfl⟩
      refine ⟨fun h₁ h₂ => ?_, hlv⟩
      cases h₁ with
      | eval_Elvalue _ _ _ _ _ hl hd =>
          cases h₂ with
          | eval_Elvalue _ _ _ _ _ hl' hd' =>
              obtain ⟨rfl, rfl, rfl⟩ := hlv hl hl'
              exact deref_loc_determ hd hd'
  | Etempvar id ty =>
      refine ⟨fun h₁ h₂ => ?_, fun h₁ _ => nomatch h₁⟩
      cases h₁ with
      | eval_Etempvar _ _ _ hv =>
          cases h₂ with
          | eval_Etempvar _ _ _ hv' => exact Option.some.inj (hv.symm.trans hv')
          | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
      | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
  | Ederef a ty ih =>
      have hlv : ∀ {l₁ l₂ : block} {o₁ o₂ : ptrofs} {bf₁ bf₂ : bitfield},
          eval_lvalue A ge e le m (.Ederef a ty) l₁ o₁ bf₁ →
          eval_lvalue A ge e le m (.Ederef a ty) l₂ o₂ bf₂ → l₁ = l₂ ∧ o₁ = o₂ ∧ bf₁ = bf₂ := by
        intro l₁ l₂ o₁ o₂ bf₁ bf₂ h₁ h₂
        cases h₁ with
        | eval_Ederef _ _ _ _ hv =>
            cases h₂ with
            | eval_Ederef _ _ _ _ hv' =>
                cases ih.1 hv hv'
                exact ⟨rfl, rfl, rfl⟩
      refine ⟨fun h₁ h₂ => ?_, hlv⟩
      cases h₁ with
      | eval_Elvalue _ _ _ _ _ hl hd =>
          cases h₂ with
          | eval_Elvalue _ _ _ _ _ hl' hd' =>
              obtain ⟨rfl, rfl, rfl⟩ := hlv hl hl'
              exact deref_loc_determ hd hd'
  | Eaddrof a ty ih =>
      refine ⟨fun h₁ h₂ => ?_, fun h₁ _ => nomatch h₁⟩
      cases h₁ with
      | eval_Eaddrof _ _ _ _ hl =>
          cases h₂ with
          | eval_Eaddrof _ _ _ _ hl' =>
              obtain ⟨rfl, rfl, -⟩ := ih.2 hl hl'
              rfl
          | eval_Elvalue _ _ _ _ _ hl' _ => nomatch hl'
      | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
  | Eunop op a ty ih =>
      refine ⟨fun h₁ h₂ => ?_, fun h₁ _ => nomatch h₁⟩
      cases h₁ with
      | eval_Eunop _ _ _ _ _ he hs =>
          cases h₂ with
          | eval_Eunop _ _ _ _ _ he' hs' =>
              rw [ih.1 he he'] at hs
              exact Option.some.inj (hs.symm.trans hs')
          | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
      | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
  | Ebinop op a₁ a₂ ty ih₁ ih₂ =>
      refine ⟨fun h₁ h₂ => ?_, fun h₁ _ => nomatch h₁⟩
      cases h₁ with
      | eval_Ebinop _ _ _ _ _ _ _ he₁ he₂ hs =>
          cases h₂ with
          | eval_Ebinop _ _ _ _ _ _ _ he₁' he₂' hs' =>
              rw [ih₁.1 he₁ he₁', ih₂.1 he₂ he₂'] at hs
              exact Option.some.inj (hs.symm.trans hs')
          | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
      | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
  | Ecast a ty ih =>
      refine ⟨fun h₁ h₂ => ?_, fun h₁ _ => nomatch h₁⟩
      cases h₁ with
      | eval_Ecast _ _ _ _ he hs =>
          cases h₂ with
          | eval_Ecast _ _ _ _ he' hs' =>
              rw [ih.1 he he'] at hs
              exact Option.some.inj (hs.symm.trans hs')
          | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
      | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
  | Efield a f ty _ =>
      refine ⟨fun h₁ _ => ?_, fun h₁ _ => nomatch h₁⟩
      cases h₁ with
      | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
  | Esizeof ty₁ ty =>
      refine ⟨fun h₁ _ => ?_, fun h₁ _ => nomatch h₁⟩
      cases h₁ with
      | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl
  | Ealignof ty₁ ty =>
      refine ⟨fun h₁ _ => ?_, fun h₁ _ => nomatch h₁⟩
      cases h₁ with
      | eval_Elvalue _ _ _ _ _ hl _ => nomatch hl

/-- `eval_expr` is a function of the environments, the memory, and the expression. -/
theorem eval_expr_determ {a : expr} {v₁ v₂ : val} (h₁ : eval_expr A ge e le m a v₁)
    (h₂ : eval_expr A ge e le m a v₂) : v₁ = v₂ :=
  (eval_determ a).1 h₁ h₂

/-- `eval_lvalue` is a function of the environments, the memory, and the expression. -/
theorem eval_lvalue_determ {a : expr} {l₁ l₂ : block} {o₁ o₂ : ptrofs} {bf₁ bf₂ : bitfield}
    (h₁ : eval_lvalue A ge e le m a l₁ o₁ bf₁) (h₂ : eval_lvalue A ge e le m a l₂ o₂ bf₂) :
    l₁ = l₂ ∧ o₁ = o₂ ∧ bf₁ = bf₂ :=
  (eval_determ a).2 h₁ h₂

/-- `eval_exprlist` is a function of the environments, the memory, the expressions, and the
types to which it casts their values. -/
theorem eval_exprlist_determ {al : List expr} {tyl : List type} {vl₁ vl₂ : List val}
    (h₁ : eval_exprlist A ge e le m al tyl vl₁) (h₂ : eval_exprlist A ge e le m al tyl vl₂) :
    vl₁ = vl₂ := by
  induction h₁ generalizing vl₂ with
  | eval_Enil =>
      cases h₂
      rfl
  | eval_Econs _ _ _ _ _ _ _ he hc _ ih =>
      cases h₂ with
      | eval_Econs _ _ _ _ _ _ _ he' hc' hl' =>
          rw [eval_expr_determ he he'] at hc
          rw [Option.some.inj (hc.symm.trans hc'), ih hl']

end Eval

/-! ## Statements and calls -/

theorem function_entry2_determ {f : function} {vargs : List val} {m : mem} {e₁ e₂ : env}
    {le₁ le₂ : temp_env} {m₁ m₂ : mem} (h₁ : function_entry2 f vargs m e₁ le₁ m₁)
    (h₂ : function_entry2 f vargs m e₂ le₂ m₂) : e₁ = e₂ ∧ le₁ = le₂ ∧ m₁ = m₂ := by
  cases h₁ with
  | intro _ _ _ _ hb =>
      cases h₂ with
      | intro _ _ _ _ hb' => exact ⟨rfl, Option.some.inj (hb.symm.trans hb'), rfl⟩

theorem outcome_result_value_determ {out : outcome} {ty : type} {v₁ v₂ : val} {m : mem}
    (h₁ : outcome_result_value out ty v₁ m) (h₂ : outcome_result_value out ty v₂ m) :
    v₁ = v₂ := by
  unfold outcome_result_value at h₁ h₂
  split at h₁ <;> simp_all

theorem out_break_or_return_determ {o o₁ o₂ : outcome} (h₁ : out_break_or_return o o₁)
    (h₂ : out_break_or_return o o₂) : o₁ = o₂ := by
  cases h₁ <;> cases h₂ <;> rfl

theorem out_break_or_return_normal_or_continue {o o' : outcome}
    (h₁ : out_break_or_return o o') (h₂ : out_normal_or_continue o) : False := by
  cases h₁ <;> cases h₂

section Exec

variable {A : Archi} {X : ExtSem} {ge : genv}

mutual

/-- Two executions of a statement from one state, whose traces agree up to the length of the
shorter, have the same trace and end in the same state with the same outcome. -/
theorem exec_stmt_determ_prefix (hX : X.Determ) {e : env} {le : temp_env} {m : mem}
    {s : statement} {t₁ : trace} {le₁ : temp_env} {m₁ : mem} {out₁ : outcome}
    (h₁ : exec_stmt A X ge e le m s t₁ le₁ m₁ out₁) :
    ∀ {t₂ : trace} {le₂ : temp_env} {m₂ : mem} {out₂ : outcome} {u₁ u₂ : trace},
      exec_stmt A X ge e le m s t₂ le₂ m₂ out₂ → t₁ ++ u₁ = t₂ ++ u₂ →
      t₁ = t₂ ∧ le₁ = le₂ ∧ m₁ = m₂ ∧ out₁ = out₂ := by
  match h₁ with
  | .exec_Sskip _ _ _ =>
      intro t₂ le₂ m₂ out₂ u₁ u₂ h₂ hu
      cases h₂
      exact ⟨rfl, rfl, rfl, rfl⟩
  | .exec_Sassign _ _ _ _ _ _ _ _ _ _ _ hl he hc ha =>
      intro t₂ le₂ m₂ out₂ u₁ u₂ h₂ hu
      cases h₂ with
      | exec_Sassign _ _ _ _ _ _ _ _ _ _ _ hl' he' hc' ha' =>
          obtain ⟨rfl, rfl, rfl⟩ := eval_lvalue_determ hl hl'
          cases eval_expr_determ he he'
          cases Option.some.inj (hc.symm.trans hc')
          exact ⟨rfl, rfl, assign_loc_determ ha ha', rfl⟩
  | .exec_Sset _ _ _ _ _ _ he =>
      intro t₂ le₂ m₂ out₂ u₁ u₂ h₂ hu
      cases h₂ with
      | exec_Sset _ _ _ _ _ _ he' =>
          cases eval_expr_determ he he'
          exact ⟨rfl, rfl, rfl, rfl⟩
  | .exec_Scall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcl he hal hf _ hcall =>
      intro t₂ le₂ m₂ out₂ u₁ u₂ h₂ hu
      cases h₂ with
      | exec_Scall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcl' he' hal' hf' _ hcall' =>
          rw [hcl] at hcl'
          cases hcl'
          cases eval_expr_determ he he'
          cases eval_exprlist_determ hal hal'
          rw [hf] at hf'
          cases hf'
          obtain ⟨rfl, rfl, rfl⟩ := eval_funcall_determ_prefix hX hcall hcall' hu
          exact ⟨rfl, rfl, rfl, rfl⟩
  | .exec_Sbuiltin _ _ _ _ _ _ _ _ _ _ _ hal hext =>
      intro t₂ le₂ m₂ out₂ u₁ u₂ h₂ hu
      cases h₂ with
      | exec_Sbuiltin _ _ _ _ _ _ _ _ _ _ _ hal' hext' =>
          cases eval_exprlist_determ hal hal'
          obtain ⟨rfl, rfl, rfl⟩ := external_call_determ hX hext hext' hu
          exact ⟨rfl, rfl, rfl, rfl⟩
  | .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hs₁ hs₂ =>
      intro t₂ le₂ m₂ out₂ u₁ u₂ h₂ hu
      cases h₂ with
      | exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hs₁' hs₂' =>
          simp only [List.append_assoc] at hu
          obtain ⟨rfl, rfl, rfl, -⟩ := exec_stmt_determ_prefix hX hs₁ hs₁' hu
          obtain ⟨rfl, rfl, rfl, rfl⟩ :=
            exec_stmt_determ_prefix hX hs₂ hs₂' (List.append_cancel_left hu)
          exact ⟨rfl, rfl, rfl, rfl⟩
      | exec_Sseq_2 _ _ _ _ _ _ _ _ _ hs₁' hne =>
          simp only [List.append_assoc] at hu
          obtain ⟨-, -, -, h⟩ := exec_stmt_determ_prefix hX hs₁ hs₁' hu
          exact absurd h.symm hne
  | .exec_Sseq_2 _ _ _ _ _ _ _ _ _ hs₁ hne =>
      intro t₂ le₂ m₂ out₂ u₁ u₂ h₂ hu
      cases h₂ with
      | exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hs₁' _ =>
          simp only [List.append_assoc] at hu
          obtain ⟨-, -, -, h⟩ := exec_stmt_determ_prefix hX hs₁ hs₁' hu
          exact absurd h hne
      | exec_Sseq_2 _ _ _ _ _ _ _ _ _ hs₁' _ =>
          exact exec_stmt_determ_prefix hX hs₁ hs₁' hu
  | .exec_Sifthenelse _ _ _ _ _ _ _ _ _ _ _ _ he hb hs =>
      intro t₂ le₂ m₂ out₂ u₁ u₂ h₂ hu
      cases h₂ with
      | exec_Sifthenelse _ _ _ _ _ _ _ _ _ _ _ _ he' hb' hs' =>
          cases eval_expr_determ he he'
          rw [hb] at hb'
          cases hb'
          exact exec_stmt_determ_prefix hX hs hs' hu
  | .exec_Sreturn_none _ _ _ =>
      intro t₂ le₂ m₂ out₂ u₁ u₂ h₂ hu
      cases h₂
      exact ⟨rfl, rfl, rfl, rfl⟩
  | .exec_Sreturn_some _ _ _ _ _ he =>
      intro t₂ le₂ m₂ out₂ u₁ u₂ h₂ hu
      cases h₂ with
      | exec_Sreturn_some _ _ _ _ _ he' =>
          cases eval_expr_determ he he'
          exact ⟨rfl, rfl, rfl, rfl⟩
  | .exec_Sbreak _ _ _ =>
      intro t₂ le₂ m₂ out₂ u₁ u₂ h₂ hu
      cases h₂
      exact ⟨rfl, rfl, rfl, rfl⟩
  | .exec_Scontinue _ _ _ =>
      intro t₂ le₂ m₂ out₂ u₁ u₂ h₂ hu
      cases h₂
      exact ⟨rfl, rfl, rfl, rfl⟩
  | .exec_Sloop_stop1 _ _ _ _ _ _ _ _ _ _ hs hbr =>
      intro t₂ le₂ m₂ out₂ u₁ u₂ h₂ hu
      cases h₂ with
      | exec_Sloop_stop1 _ _ _ _ _ _ _ _ _ _ hs' hbr' =>
          obtain ⟨rfl, rfl, rfl, rfl⟩ := exec_stmt_determ_prefix hX hs hs' hu
          exact ⟨rfl, rfl, rfl, out_break_or_return_determ hbr hbr'⟩
      | exec_Sloop_stop2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁' hnc' _ _ =>
          simp only [List.append_assoc] at hu
          obtain ⟨-, -, -, rfl⟩ := exec_stmt_determ_prefix hX hs hs₁' hu
          exact (out_break_or_return_normal_or_continue hbr hnc').elim
      | exec_Sloop_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁' hnc' _ _ =>
          simp only [List.append_assoc] at hu
          obtain ⟨-, -, -, rfl⟩ := exec_stmt_determ_prefix hX hs hs₁' hu
          exact (out_break_or_return_normal_or_continue hbr hnc').elim
  | .exec_Sloop_stop2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁ hnc hs₂ hbr =>
      intro t₂ le₂ m₂ out₂ u₁ u₂ h₂ hu
      cases h₂ with
      | exec_Sloop_stop1 _ _ _ _ _ _ _ _ _ _ hs' hbr' =>
          simp only [List.append_assoc] at hu
          obtain ⟨-, -, -, rfl⟩ := exec_stmt_determ_prefix hX hs₁ hs' hu
          exact (out_break_or_return_normal_or_continue hbr' hnc).elim
      | exec_Sloop_stop2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁' _ hs₂' hbr' =>
          simp only [List.append_assoc] at hu
          obtain ⟨rfl, rfl, rfl, rfl⟩ := exec_stmt_determ_prefix hX hs₁ hs₁' hu
          obtain ⟨rfl, rfl, rfl, rfl⟩ :=
            exec_stmt_determ_prefix hX hs₂ hs₂' (List.append_cancel_left hu)
          exact ⟨rfl, rfl, rfl, out_break_or_return_determ hbr hbr'⟩
      | exec_Sloop_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁' _ hs₂' _ =>
          simp only [List.append_assoc] at hu
          obtain ⟨rfl, rfl, rfl, rfl⟩ := exec_stmt_determ_prefix hX hs₁ hs₁' hu
          obtain ⟨-, -, -, rfl⟩ :=
            exec_stmt_determ_prefix hX hs₂ hs₂' (List.append_cancel_left hu)
          cases hbr
  | .exec_Sloop_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁ hnc hs₂ hl =>
      intro t₂ le₂ m₂ out₂ u₁ u₂ h₂ hu
      cases h₂ with
      | exec_Sloop_stop1 _ _ _ _ _ _ _ _ _ _ hs' hbr' =>
          simp only [List.append_assoc] at hu
          obtain ⟨-, -, -, rfl⟩ := exec_stmt_determ_prefix hX hs₁ hs' hu
          exact (out_break_or_return_normal_or_continue hbr' hnc).elim
      | exec_Sloop_stop2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁' _ hs₂' hbr' =>
          simp only [List.append_assoc] at hu
          obtain ⟨rfl, rfl, rfl, rfl⟩ := exec_stmt_determ_prefix hX hs₁ hs₁' hu
          obtain ⟨-, -, -, rfl⟩ :=
            exec_stmt_determ_prefix hX hs₂ hs₂' (List.append_cancel_left hu)
          cases hbr'
      | exec_Sloop_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁' _ hs₂' hl' =>
          simp only [List.append_assoc] at hu
          obtain ⟨rfl, rfl, rfl, rfl⟩ := exec_stmt_determ_prefix hX hs₁ hs₁' hu
          have hu' := List.append_cancel_left hu
          obtain ⟨rfl, rfl, rfl, -⟩ := exec_stmt_determ_prefix hX hs₂ hs₂' hu'
          obtain ⟨rfl, rfl, rfl, rfl⟩ :=
            exec_stmt_determ_prefix hX hl hl' (List.append_cancel_left hu')
          exact ⟨rfl, rfl, rfl, rfl⟩
termination_by structural h₁

/-- Two executions of a call from one memory, whose traces agree up to the length of the
shorter, have the same trace, final memory, and result. -/
theorem eval_funcall_determ_prefix (hX : X.Determ) {m : mem} {f : fundef function}
    {vargs : List val} {t₁ : trace} {m₁ : mem} {v₁ : val}
    (h₁ : eval_funcall A X ge m f vargs t₁ m₁ v₁) :
    ∀ {t₂ : trace} {m₂ : mem} {v₂ : val} {u₁ u₂ : trace},
      eval_funcall A X ge m f vargs t₂ m₂ v₂ → t₁ ++ u₁ = t₂ ++ u₂ →
      t₁ = t₂ ∧ m₁ = m₂ ∧ v₁ = v₂ := by
  match h₁ with
  | .eval_funcall_internal _ _ _ _ _ _ _ _ _ _ _ _ hent hbody hres hfree =>
      intro t₂ m₂ v₂ u₁ u₂ h₂ hu
      cases h₂ with
      | eval_funcall_internal _ _ _ _ _ _ _ _ _ _ _ _ hent' hbody' hres' hfree' =>
          obtain ⟨rfl, rfl, rfl⟩ := function_entry2_determ hent hent'
          obtain ⟨rfl, rfl, rfl, rfl⟩ := exec_stmt_determ_prefix hX hbody hbody' hu
          cases outcome_result_value_determ hres hres'
          rw [hfree] at hfree'
          cases hfree'
          exact ⟨rfl, rfl, rfl⟩
  | .eval_funcall_external _ _ _ _ _ _ _ _ _ hext =>
      intro t₂ m₂ v₂ u₁ u₂ h₂ hu
      cases h₂ with
      | eval_funcall_external _ _ _ _ _ _ _ _ _ hext' =>
          obtain ⟨rfl, rfl, rfl⟩ := external_call_determ hX hext hext' hu
          exact ⟨rfl, rfl, rfl⟩
termination_by structural h₁

end

/-- Two executions of a statement from one state with one trace end in the same state with the
same outcome. -/
theorem exec_stmt_determ (hX : X.Determ) {e : env} {le : temp_env} {m : mem} {s : statement}
    {t : trace} {le₁ le₂ : temp_env} {m₁ m₂ : mem} {out₁ out₂ : outcome}
    (h₁ : exec_stmt A X ge e le m s t le₁ m₁ out₁) (h₂ : exec_stmt A X ge e le m s t le₂ m₂ out₂) :
    le₁ = le₂ ∧ m₁ = m₂ ∧ out₁ = out₂ :=
  (exec_stmt_determ_prefix hX h₁ h₂ (u₁ := []) (u₂ := []) rfl).2

/-- Two executions of a call from one memory with one trace end with the same memory and
result. -/
theorem eval_funcall_determ (hX : X.Determ) {m : mem} {f : fundef function} {vargs : List val}
    {t : trace} {m₁ m₂ : mem} {v₁ v₂ : val} (h₁ : eval_funcall A X ge m f vargs t m₁ v₁)
    (h₂ : eval_funcall A X ge m f vargs t m₂ v₂) : m₁ = m₂ ∧ v₁ = v₂ :=
  (eval_funcall_determ_prefix hX h₁ h₂ (u₁ := []) (u₂ := []) rfl).2

end Exec

/-! ## Programs -/

section Program

variable {A : Archi} {X : ExtSem}

/-- Two terminations of a program whose traces agree up to the length of the shorter have the
same trace and result. -/
theorem bigstep_program_terminates_determ_prefix (hX : X.Determ) {p : program function}
    {t₁ t₂ u₁ u₂ : trace} {r₁ r₂ : int} (h₁ : bigstep_program_terminates A X p t₁ r₁)
    (h₂ : bigstep_program_terminates A X p t₂ r₂) (hu : t₁ ++ u₁ = t₂ ++ u₂) :
    t₁ = t₂ ∧ r₁ = r₂ := by
  cases h₁ with
  | bigstep_program_terminates_intro _ _ _ _ _ _ hi hs hf _ hc =>
      cases h₂ with
      | bigstep_program_terminates_intro _ _ _ _ _ _ hi' hs' hf' _ hc' =>
          rw [hi] at hi'
          cases hi'
          rw [hs] at hs'
          cases hs'
          rw [hf] at hf'
          cases hf'
          obtain ⟨rfl, -, hr⟩ := eval_funcall_determ_prefix hX hc hc' hu
          cases hr
          exact ⟨rfl, rfl⟩

/-- A program terminates with at most one result for a trace. -/
theorem bigstep_program_terminates_determ (hX : X.Determ) {p : program function} {t : trace}
    {r₁ r₂ : int} (h₁ : bigstep_program_terminates A X p t r₁)
    (h₂ : bigstep_program_terminates A X p t r₂) : r₁ = r₂ :=
  (bigstep_program_terminates_determ_prefix hX h₁ h₂ (u₁ := []) (u₂ := []) rfl).2

/-- A program that terminates with the empty trace has no other termination. -/
theorem bigstep_program_terminates_E0 (hX : X.Determ) {p : program function} {t : trace}
    {r₁ r₂ : int} (h₁ : bigstep_program_terminates A X p E0 r₁)
    (h₂ : bigstep_program_terminates A X p t r₂) : t = E0 ∧ r₁ = r₂ := by
  obtain ⟨ht, hr⟩ := bigstep_program_terminates_determ_prefix hX h₁ h₂ (u₁ := t) (u₂ := [])
    (by simp [E0])
  exact ⟨ht.symm, hr⟩

end Program

end LClight
