/-
Derived from CompCert 3.18, the file `cfrontend/ClightBigstep.v`.  CompCert is Copyright Institut
National de Recherche en Informatique et en Automatique (INRIA) and AbsInt Angewandte Informatik
GmbH, and its source files carry INRIA's copyright.

This file is distributed under the GNU Lesser General Public License, version 2.1 or (at your
option) any later version, one of the two licenses CompCert offers for its source files.  The
text of version 2.1 is in `LICENSE-LGPL-2.1` in this directory.

Changed from CompCert on 2026-10-26: transcribed from Coq into Lean, with the changes that
`LeanExe/Native/NOTICE` and the documentation comment below describe.
-/
import LeanExe.Native.Clight.Clight

/-!
The big-step semantics of terminating Clight statements and calls, from CompCert 3.18's
`cfrontend/ClightBigstep.v`, with `function_entry2`.  CompCert's `bigstep_semantics_sound`
relates it to the small-step semantics `semantics2`, which its compiler theorem is about.  The
copy has no rule for `Sswitch`, whose rule `exec_Sswitch` it omits; `ClightBigstep.v` itself has
none for `Slabel` and `Sgoto`.  `A` gives the NaN results of floating-point operations and `X`
the semantics of external functions.
-/

namespace LClight

inductive outcome where
  | Out_break
  | Out_continue
  | Out_normal
  | Out_return (r : Option (val × type))
  deriving Repr, DecidableEq

inductive out_normal_or_continue : outcome → Prop
  | Out_normal_or_continue_N : out_normal_or_continue .Out_normal
  | Out_normal_or_continue_C : out_normal_or_continue .Out_continue

inductive out_break_or_return : outcome → outcome → Prop
  | Out_break_or_return_B : out_break_or_return .Out_break .Out_normal
  | Out_break_or_return_R (ov : Option (val × type)) :
      out_break_or_return (.Out_return ov) (.Out_return ov)

def outcome_result_value (out : outcome) (t : type) (v : val) (m : mem) : Prop :=
  match out, t with
  | .Out_normal, .Tvoid => v = .Vundef
  | .Out_return none, .Tvoid => v = .Vundef
  | .Out_return (some (v', t')), ty => ty ≠ .Tvoid ∧ sem_cast v' t' ty m = some v
  | _, _ => False

mutual
  inductive exec_stmt (A : Archi) (X : ExtSem) (ge : genv) :
      env → temp_env → mem → statement → trace → temp_env → mem → outcome → Prop
    | exec_Sskip (e : env) (le : temp_env) (m : mem) :
        exec_stmt A X ge e le m .Sskip E0 le m .Out_normal
    | exec_Sassign (e : env) (le : temp_env) (m : mem) (a1 a2 : expr) (loc : block)
        (ofs : ptrofs) (bf : bitfield) (v2 v : val) (m' : mem) :
        eval_lvalue A ge e le m a1 loc ofs bf →
        eval_expr A ge e le m a2 v2 →
        sem_cast v2 (typeof a2) (typeof a1) m = some v →
        assign_loc (typeof a1) m loc ofs bf v m' →
        exec_stmt A X ge e le m (.Sassign a1 a2) E0 le m' .Out_normal
    | exec_Sset (e : env) (le : temp_env) (m : mem) (id : ident) (a : expr) (v : val) :
        eval_expr A ge e le m a v →
        exec_stmt A X ge e le m (.Sset id a) E0 (le.insert id v) m .Out_normal
    | exec_Scall (e : env) (le : temp_env) (m : mem) (optid : Option ident) (a : expr)
        (al : List expr) (tyargs : List type) (tyres : type) (cconv : calling_convention)
        (vf : val) (vargs : List val) (f : fundef function) (t : trace) (m' : mem) (vres : val) :
        classify_fun (typeof a) = .fun_case_f tyargs tyres cconv →
        eval_expr A ge e le m a vf →
        eval_exprlist A ge e le m al tyargs vargs →
        Genv.find_funct ge vf = some f →
        type_of_fundef f = .Tfunction tyargs tyres cconv →
        eval_funcall A X ge m f vargs t m' vres →
        exec_stmt A X ge e le m (.Scall optid a al) t (set_opttemp optid vres le) m' .Out_normal
    | exec_Sbuiltin (e : env) (le : temp_env) (m : mem) (optid : Option ident)
        (ef : external_function) (al : List expr) (tyargs : List type) (vargs : List val)
        (t : trace) (m' : mem) (vres : val) :
        eval_exprlist A ge e le m al tyargs vargs →
        external_call A X ef ge.genv_symb vargs m t vres m' →
        exec_stmt A X ge e le m (.Sbuiltin optid ef tyargs al) t (set_opttemp optid vres le) m'
          .Out_normal
    | exec_Sseq_1 (e : env) (le : temp_env) (m : mem) (s1 s2 : statement) (t1 : trace)
        (le1 : temp_env) (m1 : mem) (t2 : trace) (le2 : temp_env) (m2 : mem) (out : outcome) :
        exec_stmt A X ge e le m s1 t1 le1 m1 .Out_normal →
        exec_stmt A X ge e le1 m1 s2 t2 le2 m2 out →
        exec_stmt A X ge e le m (.Ssequence s1 s2) (t1 ++ t2) le2 m2 out
    | exec_Sseq_2 (e : env) (le : temp_env) (m : mem) (s1 s2 : statement) (t1 : trace)
        (le1 : temp_env) (m1 : mem) (out : outcome) :
        exec_stmt A X ge e le m s1 t1 le1 m1 out →
        out ≠ .Out_normal →
        exec_stmt A X ge e le m (.Ssequence s1 s2) t1 le1 m1 out
    | exec_Sifthenelse (e : env) (le : temp_env) (m : mem) (a : expr) (s1 s2 : statement)
        (v1 : val) (b : Bool) (t : trace) (le' : temp_env) (m' : mem) (out : outcome) :
        eval_expr A ge e le m a v1 →
        bool_val v1 (typeof a) m = some b →
        exec_stmt A X ge e le m (if b then s1 else s2) t le' m' out →
        exec_stmt A X ge e le m (.Sifthenelse a s1 s2) t le' m' out
    | exec_Sreturn_none (e : env) (le : temp_env) (m : mem) :
        exec_stmt A X ge e le m (.Sreturn none) E0 le m (.Out_return none)
    | exec_Sreturn_some (e : env) (le : temp_env) (m : mem) (a : expr) (v : val) :
        eval_expr A ge e le m a v →
        exec_stmt A X ge e le m (.Sreturn (some a)) E0 le m (.Out_return (some (v, typeof a)))
    | exec_Sbreak (e : env) (le : temp_env) (m : mem) :
        exec_stmt A X ge e le m .Sbreak E0 le m .Out_break
    | exec_Scontinue (e : env) (le : temp_env) (m : mem) :
        exec_stmt A X ge e le m .Scontinue E0 le m .Out_continue
    | exec_Sloop_stop1 (e : env) (le : temp_env) (m : mem) (s1 s2 : statement) (t : trace)
        (le' : temp_env) (m' : mem) (out' out : outcome) :
        exec_stmt A X ge e le m s1 t le' m' out' →
        out_break_or_return out' out →
        exec_stmt A X ge e le m (.Sloop s1 s2) t le' m' out
    | exec_Sloop_stop2 (e : env) (le : temp_env) (m : mem) (s1 s2 : statement) (t1 : trace)
        (le1 : temp_env) (m1 : mem) (out1 : outcome) (t2 : trace) (le2 : temp_env) (m2 : mem)
        (out2 out : outcome) :
        exec_stmt A X ge e le m s1 t1 le1 m1 out1 →
        out_normal_or_continue out1 →
        exec_stmt A X ge e le1 m1 s2 t2 le2 m2 out2 →
        out_break_or_return out2 out →
        exec_stmt A X ge e le m (.Sloop s1 s2) (t1 ++ t2) le2 m2 out
    | exec_Sloop_loop (e : env) (le : temp_env) (m : mem) (s1 s2 : statement) (t1 : trace)
        (le1 : temp_env) (m1 : mem) (out1 : outcome) (t2 : trace) (le2 : temp_env) (m2 : mem)
        (t3 : trace) (le3 : temp_env) (m3 : mem) (out : outcome) :
        exec_stmt A X ge e le m s1 t1 le1 m1 out1 →
        out_normal_or_continue out1 →
        exec_stmt A X ge e le1 m1 s2 t2 le2 m2 .Out_normal →
        exec_stmt A X ge e le2 m2 (.Sloop s1 s2) t3 le3 m3 out →
        exec_stmt A X ge e le m (.Sloop s1 s2) (t1 ++ t2 ++ t3) le3 m3 out

  inductive eval_funcall (A : Archi) (X : ExtSem) (ge : genv) :
      mem → fundef function → List val → trace → mem → val → Prop
    | eval_funcall_internal (m : mem) (f : function) (vargs : List val) (t : trace) (e : env)
        (le1 le2 : temp_env) (m1 m2 : mem) (out : outcome) (vres : val) (m3 : mem) :
        function_entry2 f vargs m e le1 m1 →
        exec_stmt A X ge e le1 m1 f.fn_body t le2 m2 out →
        outcome_result_value out f.fn_return vres m2 →
        Mem.free_list m2 (blocks_of_env e) = some m3 →
        eval_funcall A X ge m (.Internal f) vargs t m3 vres
    | eval_funcall_external (m : mem) (ef : external_function) (targs : List type)
        (tres : type) (cconv : calling_convention) (vargs : List val) (t : trace) (vres : val)
        (m' : mem) :
        external_call A X ef ge.genv_symb vargs m t vres m' →
        eval_funcall A X ge m (.External ef targs tres cconv) vargs t m' vres
end

end LClight
