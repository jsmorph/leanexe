import LeanExe.Native.Clight.Bigstep

/-!
`run`, an evaluator for the big-step semantics of `Bigstep.lean`.  Expressions evaluate by
structural recursion.  Statements and calls take fuel, which each statement and each call
consumes, so a result `.ok` means a derivation of at most that height exists.  `RunSound.lean`
proves that every `.ok` result is an execution of `exec_stmt` or `eval_funcall`.  A result
`.error .stuck` means that no rule applies at the point the evaluator reached; the evaluator
gives `EF_external` calls no result, since their semantics is a parameter.
-/

namespace LClight

inductive Failure where
  | stuck
  | outOfFuel
  deriving Repr, DecidableEq

section Eval

variable (A : Archi) (ge : genv)

/-- The block and offset of the variable `id` at type `ty`, as `eval_Evar_local` and
`eval_Evar_global` give them. -/
def lvar (e : env) (id : ident) (ty : type) : Option (block × ptrofs) :=
  match e[id]? with
  | some (l, ty') => if ty' = ty then some (l, Ptrofs.zero) else none
  | none =>
      match Genv.find_symbol ge id with
      | some l => some (l, Ptrofs.zero)
      | none => none

/-- `deref_loc` at a full access. -/
def deref_loc_fn (ty : type) (m : mem) (b : block) (ofs : ptrofs) : Option val :=
  match access_mode ty with
  | .By_value chunk => Mem.loadv chunk m (.Vptr b ofs)
  | .By_reference => some (.Vptr b ofs)
  | _ => none

def assign_loc_fn (ty : type) (m : mem) (b : block) (ofs : ptrofs) (bf : bitfield) (v : val) :
    Option mem :=
  match bf with
  | .Full =>
      match access_mode ty with
      | .By_value chunk => Mem.storev chunk m (.Vptr b ofs) v
      | _ => none
  | .Bits _ _ _ _ => none

def eval_expr_fn (e : env) (le : temp_env) (m : mem) : expr → Option val
  | .Econst_int i _ => some (.Vint i)
  | .Econst_float f _ => some (.Vfloat f)
  | .Econst_single f _ => some (.Vsingle f)
  | .Econst_long i _ => some (.Vlong i)
  | .Etempvar id _ => le[id]?
  | .Eaddrof a _ =>
      match a with
      | .Evar id ty =>
          match lvar ge e id ty with
          | some (l, ofs) => some (.Vptr l ofs)
          | none => none
      | .Ederef b _ =>
          match eval_expr_fn e le m b with
          | some (.Vptr l ofs) => some (.Vptr l ofs)
          | _ => none
      | _ => none
  | .Eunop op a _ =>
      match eval_expr_fn e le m a with
      | some v1 => sem_unary_operation op v1 (typeof a) m
      | none => none
  | .Ebinop op a1 a2 _ =>
      match eval_expr_fn e le m a1 with
      | some v1 =>
          match eval_expr_fn e le m a2 with
          | some v2 => sem_binary_operation A op v1 (typeof a1) v2 (typeof a2) m
          | none => none
      | none => none
  | .Ecast a ty =>
      match eval_expr_fn e le m a with
      | some v1 => sem_cast v1 (typeof a) ty m
      | none => none
  | .Evar id ty =>
      match lvar ge e id ty with
      | some (l, ofs) => deref_loc_fn ty m l ofs
      | none => none
  | .Ederef a ty =>
      match eval_expr_fn e le m a with
      | some (.Vptr l ofs) => deref_loc_fn ty m l ofs
      | _ => none
  | .Efield _ _ _ => none
  | .Esizeof _ _ => none
  | .Ealignof _ _ => none

def eval_lvalue_fn (e : env) (le : temp_env) (m : mem) : expr → Option (block × ptrofs × bitfield)
  | .Evar id ty =>
      match lvar ge e id ty with
      | some (l, ofs) => some (l, ofs, .Full)
      | none => none
  | .Ederef a _ =>
      match eval_expr_fn A ge e le m a with
      | some (.Vptr l ofs) => some (l, ofs, .Full)
      | _ => none
  | _ => none

def eval_exprlist_fn (e : env) (le : temp_env) (m : mem) :
    List expr → List type → Option (List val)
  | [], [] => some []
  | a :: bl, ty :: tyl =>
      match eval_expr_fn A ge e le m a with
      | some v1 =>
          match sem_cast v1 (typeof a) ty m with
          | some v2 =>
              match eval_exprlist_fn e le m bl tyl with
              | some vl => some (v2 :: vl)
              | none => none
          | none => none
      | none => none
  | _, _ => none

/-- `external_call` for the known built-in functions; other external functions are stuck. -/
def external_call_fn (ef : external_function) (vargs : List val) (m : mem) :
    Option (trace × val × mem) :=
  match ef with
  | .EF_builtin name sg =>
      match lookup_builtin_function name sg with
      | some bf =>
          match builtin_function_sem A bf vargs with
          | some vres => some (E0, vres, m)
          | none => none
      | none => none
  | _ => none

def function_entry2_fn (f : function) (vargs : List val) : Option temp_env :=
  if f.fn_vars = [] ∧ (var_names f.fn_params).Nodup ∧
      (∀ x ∈ var_names f.fn_params, ∀ y ∈ var_names f.fn_temps, x ≠ y) then
    bind_parameter_temps f.fn_params vargs (create_undef_temps f.fn_temps)
  else none

def outcome_result_value_fn (out : outcome) (t : type) (m : mem) : Option val :=
  match out, t with
  | .Out_normal, .Tvoid => some .Vundef
  | .Out_return none, .Tvoid => some .Vundef
  | .Out_return (some (v', t')), ty => if ty = .Tvoid then none else sem_cast v' t' ty m
  | _, _ => none

mutual
  def exec_fn : Nat → env → temp_env → mem → statement →
      Except Failure (trace × temp_env × mem × outcome)
    | 0, _, _, _, _ => .error .outOfFuel
    | fuel + 1, e, le, m, s =>
      match s with
      | .Sskip => .ok (E0, le, m, .Out_normal)
      | .Sassign a1 a2 =>
          match eval_lvalue_fn A ge e le m a1 with
          | some (loc, ofs, bf) =>
              match eval_expr_fn A ge e le m a2 with
              | some v2 =>
                  match sem_cast v2 (typeof a2) (typeof a1) m with
                  | some v =>
                      match assign_loc_fn (typeof a1) m loc ofs bf v with
                      | some m' => .ok (E0, le, m', .Out_normal)
                      | none => .error .stuck
                  | none => .error .stuck
              | none => .error .stuck
          | none => .error .stuck
      | .Sset id a =>
          match eval_expr_fn A ge e le m a with
          | some v => .ok (E0, le.insert id v, m, .Out_normal)
          | none => .error .stuck
      | .Scall optid a al =>
          match classify_fun (typeof a) with
          | .fun_case_f tyargs tyres cconv =>
              match eval_expr_fn A ge e le m a with
              | some vf =>
                  match eval_exprlist_fn A ge e le m al tyargs with
                  | some vargs =>
                      match Genv.find_funct ge vf with
                      | some f =>
                          if type_of_fundef f = .Tfunction tyargs tyres cconv then
                            match eval_funcall_fn fuel m f vargs with
                            | .ok (t, m', vres) =>
                                .ok (t, set_opttemp optid vres le, m', .Out_normal)
                            | .error err => .error err
                          else .error .stuck
                      | none => .error .stuck
                  | none => .error .stuck
              | none => .error .stuck
          | .fun_default => .error .stuck
      | .Sbuiltin optid ef tyargs al =>
          match eval_exprlist_fn A ge e le m al tyargs with
          | some vargs =>
              match external_call_fn A ef vargs m with
              | some (t, vres, m') => .ok (t, set_opttemp optid vres le, m', .Out_normal)
              | none => .error .stuck
          | none => .error .stuck
      | .Ssequence s1 s2 =>
          match exec_fn fuel e le m s1 with
          | .ok (t1, le1, m1, .Out_normal) =>
              match exec_fn fuel e le1 m1 s2 with
              | .ok (t2, le2, m2, out) => .ok (t1 ++ t2, le2, m2, out)
              | .error err => .error err
          | .ok r => .ok r
          | .error err => .error err
      | .Sifthenelse a s1 s2 =>
          match eval_expr_fn A ge e le m a with
          | some v1 =>
              match bool_val v1 (typeof a) m with
              | some b => exec_fn fuel e le m (if b then s1 else s2)
              | none => .error .stuck
          | none => .error .stuck
      | .Sloop s1 s2 =>
          match exec_fn fuel e le m s1 with
          | .ok (t1, le1, m1, .Out_break) => .ok (t1, le1, m1, .Out_normal)
          | .ok (t1, le1, m1, .Out_return ov) => .ok (t1, le1, m1, .Out_return ov)
          | .ok (t1, le1, m1, _) =>
              match exec_fn fuel e le1 m1 s2 with
              | .ok (t2, le2, m2, .Out_normal) =>
                  match exec_fn fuel e le2 m2 (.Sloop s1 s2) with
                  | .ok (t3, le3, m3, out) => .ok (t1 ++ t2 ++ t3, le3, m3, out)
                  | .error err => .error err
              | .ok (t2, le2, m2, .Out_break) => .ok (t1 ++ t2, le2, m2, .Out_normal)
              | .ok (t2, le2, m2, .Out_return ov) => .ok (t1 ++ t2, le2, m2, .Out_return ov)
              | .ok (_, _, _, .Out_continue) => .error .stuck
              | .error err => .error err
          | .error err => .error err
      | .Sreturn none => .ok (E0, le, m, .Out_return none)
      | .Sreturn (some a) =>
          match eval_expr_fn A ge e le m a with
          | some v => .ok (E0, le, m, .Out_return (some (v, typeof a)))
          | none => .error .stuck
      | .Sbreak => .ok (E0, le, m, .Out_break)
      | .Scontinue => .ok (E0, le, m, .Out_continue)
      | .Sswitch _ _ => .error .stuck
      | .Slabel _ _ => .error .stuck
      | .Sgoto _ => .error .stuck

  def eval_funcall_fn : Nat → mem → fundef function → List val →
      Except Failure (trace × mem × val)
    | 0, _, _, _ => .error .outOfFuel
    | fuel + 1, m, fd, vargs =>
      match fd with
      | .Internal f =>
          match function_entry2_fn f vargs with
          | some le1 =>
              match exec_fn fuel empty_env le1 m f.fn_body with
              | .ok (t, _, m2, out) =>
                  match outcome_result_value_fn out f.fn_return m2 with
                  | some vres =>
                      match Mem.free_list m2 (blocks_of_env empty_env) with
                      | some m3 => .ok (t, m3, vres)
                      | none => .error .stuck
                  | none => .error .stuck
              | .error err => .error err
          | none => .error .stuck
      | .External ef _ _ _ =>
          match external_call_fn A ef vargs m with
          | some (t, vres, m') => .ok (t, m', vres)
          | none => .error .stuck
end

end Eval

/-- Calls the function at symbol `name` of `p` with `args` from the initial memory of `p`, with
`fuel` for the statements and calls it runs.  The result is the trace, the final memory, and the
returned value. -/
def run (A : Archi) (p : program function) (name : ident) (args : List val) (fuel : Nat) :
    Except Failure (trace × mem × val) :=
  let ge := globalenv p
  match init_mem p with
  | none => .error .stuck
  | some m0 =>
      match Genv.find_symbol ge name with
      | none => .error .stuck
      | some b =>
          match Genv.find_funct_ptr ge b with
          | none => .error .stuck
          | some fd => eval_funcall_fn A ge fuel m0 fd args

end LClight
