import LeanExe.Native.Proof.Export
import LeanExe.Native.Proof.Rename

/-!
The judgment of a `main` that runs forever: `LoopReacts A X p t0 W` states that `main` runs
statements `init` with the trace `t0` and then enters a loop whose iteration `n` runs with the
trace `W n`, each nonempty.  An invariant indexed by the iteration carries the state from one
iteration to the next, so the judgment uses only the terminating judgments of the copy, and the
pair of the invariant at 0 and its preservation is the witness of an infinite execution.  The
Rocq definition `loop_reacts` of `rocq/` states the same over CompCert's Clight, and Rocq carries
it to a reactive behavior of the compiled program with the trace `t0` followed by every `W n`.

`LoopEntry s init body post` locates the loop `Sloop body post` in the body `s` of `main`: `s` is
the loop, a sequence whose first part contains it, or a sequence whose second part contains it,
in which case the first part runs before the loop and joins `init`.  The judgment allows every
sequence with `Sskip` that `clightgen`'s export drops, so it transfers from the program of
`clightgen`'s Coq file to the program inside `clightgen`, `loopReacts_export`, and across
renamings of identifiers, `loopReacts_rename` and `loopReacts_rename_on`.
-/

namespace LClight

/-- `s` runs `init` and then the loop `Sloop body post`. -/
inductive LoopEntry : statement → statement → statement → statement → Prop
  | loop (body post : statement) : LoopEntry (.Sloop body post) .Sskip body post
  | seq_after {s init body post : statement} (rest : statement) :
      LoopEntry s init body post → LoopEntry (.Ssequence s rest) init body post
  | seq_before {s init body post : statement} (pre : statement) :
      LoopEntry s init body post → LoopEntry (.Ssequence pre s) (.Ssequence pre init) body post

/-- `main` of the type `int(void)`, called with no arguments from the memory of `init_mem`, runs
`init` with the trace `t0` into a state of `Inv 0`, and from every state of `Inv n` one iteration
of its loop runs with the trace `W n` into a state of `Inv (n + 1)`. -/
def LoopReacts (A : Archi) (X : ExtSem) (p : program function) (t0 : trace)
    (W : Nat → trace) : Prop :=
  (∀ n, W n ≠ []) ∧
  ∃ (b : block) (f : function) (m0 m1 : mem) (e : env) (le0 : temp_env)
    (init body post : statement) (Inv : Nat → temp_env → mem → Prop),
    init_mem A p = some m0 ∧
    Genv.find_symbol (globalenv p) p.prog_main = some b ∧
    Genv.find_funct_ptr (globalenv p) b = some (.Internal f) ∧
    type_of_function f = .Tfunction [] type_int32s cc_default ∧
    LoopEntry f.fn_body init body post ∧
    function_entry2 f [] m0 e le0 m1 ∧
    (∃ le m, exec_stmt A X (globalenv p) e le0 m1 init t0 le m .Out_normal ∧ Inv 0 le m) ∧
    ∀ n le m, Inv n le m → ∃ le' m',
      exec_stmt A X (globalenv p) e le m (.Ssequence body post) (W n) le' m' .Out_normal ∧
        Inv (n + 1) le' m'

/-! ## The export of `clightgen` -/

theorem LoopEntry.export {s' s : statement} (h : ExportRel s' s) :
    ∀ {init' body' post' : statement}, LoopEntry s' init' body' post' →
      ∃ init body post, LoopEntry s init body post ∧ ExportRel init' init ∧
        ExportRel body' body ∧ ExportRel post' post := by
  induction h with
  | skip_left _ ih =>
      intro init' body' post' hl
      obtain ⟨init, body, post, hl', hi, hb, hp⟩ := ih hl
      exact ⟨_, body, post, .seq_before .Sskip hl', .skip_left hi, hb, hp⟩
  | skip_right _ ih =>
      intro init' body' post' hl
      obtain ⟨init, body, post, hl', hi, hb, hp⟩ := ih hl
      exact ⟨init, body, post, .seq_after .Sskip hl', hi, hb, hp⟩
  | atom s hs =>
      intro init' body' post' hl
      cases hl <;> simp [isAtom] at hs
  | seq ha _ iha ihb =>
      intro init' body' post' hl
      cases hl with
      | seq_after rest hl =>
          obtain ⟨init, body, post, hl', hi, hb, hp⟩ := iha hl
          exact ⟨init, body, post, .seq_after _ hl', hi, hb, hp⟩
      | seq_before pre hl =>
          obtain ⟨init, body, post, hl', hi, hb, hp⟩ := ihb hl
          exact ⟨_, body, post, .seq_before _ hl', .seq ha hi, hb, hp⟩
  | ite e _ _ _ _ => intro _ _ _ hl; cases hl
  | loop ha hb _ _ =>
      intro init' body' post' hl
      cases hl
      exact ⟨.Sskip, _, _, .loop _ _, .skip, ha, hb⟩
  | switch e ls ls' => intro _ _ _ hl; cases hl
  | label l s s' => intro _ _ _ hl; cases hl

/-- A loop of the program of `clightgen`'s Coq file is a loop of the program inside `clightgen`
with the same traces. -/
theorem loopReacts_export {A : Archi} {X : ExtSem} {p : program function} {t0 : trace}
    {W : Nat → trace} (h : LoopReacts A X (exportProgram p) t0 W) : LoopReacts A X p t0 W := by
  obtain ⟨hne, b, f', m0, m1, e, le0, init', body', post', Inv, hinit, hs, hf, hty, hl, hentry,
    ⟨le, m, hx0, hi0⟩, hstep⟩ := h
  have hge := globalenv_export p
  obtain ⟨fd, hfd, hfe⟩ := hge.find_funct_ptr hf
  cases fd with
  | External ef targs tres cc => cases hfe
  | Internal f =>
      simp only [exportFundef, fundef.Internal.injEq] at hfe
      subst hfe
      obtain ⟨init, body, post, hl', hri, hrb, hrp⟩ :=
        LoopEntry.export (exportStmt_rel f.fn_body) hl
      refine ⟨hne, b, f, m0, m1, e, le0, init, body, post, Inv, init_mem_export A p ▸ hinit,
        hge.find_symbol _ ▸ hs, hfd, hty, hl', ?_, ⟨le, m, exec_export hge hx0 hri, hi0⟩, ?_⟩
      · cases hentry with
        | intro _ hv hn hd hb => exact .intro _ hv hn hd hb
      · intro n le m hinv
        obtain ⟨le', m', hx, hi⟩ := hstep n le m hinv
        exact ⟨le', m', exec_export hge hx (.seq hrb hrp), hi⟩

/-! ## Renamings -/

theorem LoopEntry.ren (g t : ident → ident) {s init body post : statement}
    (h : LoopEntry s init body post) :
    LoopEntry (renStmt g t s) (renStmt g t init) (renStmt g t body) (renStmt g t post) := by
  induction h with
  | loop body post => exact .loop _ _
  | seq_after rest _ ih => exact .seq_after _ ih
  | seq_before pre _ ih => exact .seq_before _ ih

/-- The loop judgment is preserved by an injective renaming `g` of globals and injective
renamings `τ` of the temporaries of each function, with the identifiers of the traces renamed by
`g`, as `bigstep_program_terminates_rename` states for a termination. -/
theorem loopReacts_rename {A : Archi} {X X' : ExtSem} {g : ident → ident}
    {τ : ident → ident → ident} (hg : Function.Injective g) (hτ : ∀ id, Function.Injective (τ id))
    (hX : ExtRen g X X') {p p' : program function}
    (hdefs : p'.prog_defs = renDefs g τ p.prog_defs) (hmain : p'.prog_main = g p.prog_main)
    {t0 : trace} {W : Nat → trace} (h : LoopReacts A X p t0 W) :
    LoopReacts A X' p' (renTrace g t0) (fun n => renTrace g (W n)) := by
  obtain ⟨hne, b, f, m0, m1, e, le0, init, body, post, Inv, hinit, hs, hf, hty, hl, hentry,
    ⟨le, m, hx0, hi0⟩, hstep⟩ := h
  have hge := globalenv_ren (τ := τ) hg hdefs
  obtain ⟨id, hd⟩ := hge.defs b
  have hf' : Genv.find_funct_ptr (globalenv p') b = some (.Internal (renFunction g (τ id) f)) := by
    simp only [Genv.find_funct_ptr, hd] at hf ⊢
    cases hdef : Genv.find_def (globalenv p) b with
    | none => simp [hdef] at hf
    | some d =>
        cases d with
        | Gfun fd =>
            simp only [hdef, Option.some.injEq] at hf
            subst hf
            simp [renGlobdef, renFundef]
        | Gvar v => simp [hdef] at hf
  obtain ⟨le0', hentry', hr0, he⟩ := function_entry2_ren g (hτ id) hentry
  obtain ⟨lea, hx0', hra⟩ := exec_stmt_ren hX hge hτ (hτ id) he hx0 hr0
  refine ⟨fun n hn => hne n (List.map_eq_nil_iff.mp hn), b, renFunction g (τ id) f, m0, m1, e,
    le0', renStmt g (τ id) init, renStmt g (τ id) body, renStmt g (τ id) post,
    fun n le' m => ∃ le, Inv n le m ∧ TempRen (τ id) le le',
    by rw [init_mem_ren hg hdefs]; exact hinit, by rw [hmain, hge.symb]; exact hs, hf', ?_,
    hl.ren g (τ id), hentry', ⟨lea, m, hx0', le, hi0, hra⟩, ?_⟩
  · have hty' := type_of_fundef_ren g (τ id) (.Internal f)
    simp only [renFundef, type_of_fundef] at hty'
    rw [hty']
    exact hty
  rintro n le' m ⟨le, hinv, hr⟩
  obtain ⟨le2, m2, hx, hi⟩ := hstep n le m hinv
  obtain ⟨le2', hx', hr2⟩ := exec_stmt_ren hX hge hτ (hτ id) he hx hr
  exact ⟨le2', m2, hx', le2, hi, hr2⟩

/-- The loop judgment is preserved by every renaming that is injective on the identifiers of
globals in the program and, for each identifier `id`, on the temporaries of the definitions under
`id`, as `bigstep_program_terminates_rename_on` states for a termination.  The traces are renamed
by an injective map that agrees with `g` on `progG p`. -/
theorem loopReacts_rename_on {A : Archi} {g : ident → ident} {τ : ident → ident → ident}
    {p p' : program function}
    (hg : ∀ x ∈ progG p, ∀ y ∈ progG p, g x = g y → x = y)
    (hτ : ∀ id, ∀ x ∈ tempsOf p.prog_defs id, ∀ y ∈ tempsOf p.prog_defs id,
      τ id x = τ id y → x = y)
    (hdefs : p'.prog_defs = renDefs g τ p.prog_defs) (hmain : p'.prog_main = g p.prog_main)
    {t0 : trace} {W : Nat → trace} (h : LoopReacts A ExtSem.none p t0 W) (X' : ExtSem) :
    ∃ g' : ident → ident, (∀ x ∈ progG p, g' x = g x) ∧
      LoopReacts A X' p' (renTrace g' t0) (fun n => renTrace g' (W n)) := by
  obtain ⟨g', τ', hinj, hτ', heq, hsame⟩ := exists_injective_renaming hg hτ
  exact ⟨g', heq, loopReacts_rename hinj hτ' (ExtRen.none g' X') (by rw [hdefs, hsame])
    (by rw [hmain, heq _ (List.mem_cons_self ..)]) h⟩

end LClight
