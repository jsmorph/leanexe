import LeanExe.Native.Proof.Run
import LeanExe.Native.Proof.Genv

/-!
`translate_correct`: every function of a translated program simulates its Talos function.  For
any global environment that holds the program's globals and functions, a run of function `k`
by Talos's `run` that returns or traps is matched by a call of the C function in CompCert's
big-step semantics, with the result, the globals, and `lx_status` related as `RunOutcome`
states.
-/

namespace LeanExe.Native

open Wasm LClight

theorem mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ a ∈ l, ∃ b ∈ l', f a = some b
  | [], _, _, a, ha => by simp at ha
  | x :: l, l', h, a, ha => by
      simp [Option.bind_eq_some_iff] at h
      obtain ⟨b, hb, l'', hl, rfl⟩ := h
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨b, by simp, hb⟩
      · obtain ⟨b', hb', hfb⟩ := mapM_mem hl a ha
        exact ⟨b', by simp [hb'], hfb⟩

theorem mapM_mem' {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ b ∈ l', ∃ a ∈ l, f a = some b
  | [], l', h, b, hb => by simp at h; subst h; simp at hb
  | x :: l, l', h, b, hb => by
      simp [Option.bind_eq_some_iff] at h
      obtain ⟨b0, hb0, l'', hl, rfl⟩ := h
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨x, by simp, hb0⟩
      · obtain ⟨a, ha, hfa⟩ := mapM_mem' hl b hb
        exact ⟨a, by simp [ha], hfa⟩

theorem violation_imports {m : Module} (h : violation m = none) : m.imports = [] := by
  unfold violation shapeViolation at h
  cases hi : m.imports with
  | nil => rfl
  | cons _ _ => simp [hi] at h

theorem funId_inj {k k' : Nat} (h : funId k = funId k') : k = k' := by
  have e : (4 * k + 3 : Nat) = 4 * k' + 3 := h
  omega

theorem funId_div (k : Nat) : funId k / 4 = k := by
  show (4 * k + 3 : Nat) / 4 = k
  omega

theorem guard_some {p : Prop} [Decidable p] {x : Unit} (h : (guard p : Option Unit) = some x) :
    p := by
  by_cases hp : p
  · exact hp
  · simp [guard, hp] at h

/-- What the proof uses of a translation. -/
theorem translate_spec {m : Module} {T : Translation} (h : translate m = some T) :
    m.imports = [] ∧
    ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ f, m.funcs[k]? = some f ∧
        trFunction (m.funcs.map signatureOf) m.globals.length f = some fd ∧
        ∀ k', funId k' ∈ callees fd.fn_body →
          ∃ fd', (funId k', globdef.Gfun (fundef.Internal fd')) ∈ T.cprogram.prog_defs := by
  simp [translate, Option.bind_eq_some_iff] at h
  obtain ⟨⟨_, hv⟩, gdefs, -, ⟨_, hclosed⟩, funs, hfuns, rfl⟩ := h
  replace hv := guard_some hv
  replace hclosed := guard_some hclosed
  refine ⟨violation_imports hv, ?_⟩
  intro k fd hk
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hk
  rcases hk with hk | ⟨⟨g, i⟩, -, hk⟩ | hk
  · simp at hk
  · simp at hk
  · obtain ⟨k0, hk0, hdef⟩ := mapM_mem' hfuns _ hk
    cases hfd0 : (fdefsOf m)[k0]?.join with
    | none => simp [funDef, hfd0] at hdef
    | some fd0 =>
    simp [funDef, hfd0] at hdef
    obtain ⟨hid, rfl⟩ := hdef
    have : k0 = k := funId_inj hid
    subst this
    cases hf : m.funcs[k0]? with
    | none => simp [fdefsOf, hf] at hfd0
    | some f =>
    have htr : trFunction (m.funcs.map signatureOf) m.globals.length f = some fd0 := by
      simpa [fdefsOf, hf] using hfd0
    refine ⟨f, rfl, htr, fun k' hk' => ?_⟩
    have hcall : k' ∈ callsOf m k0 := by
      unfold callsOf
      rw [hfd0]
      exact List.mem_map.mpr ⟨funId k', hk', funId_div k'⟩
    have hin := hclosed k0 hk0 k' hcall
    obtain ⟨d, hd, hfd⟩ := mapM_mem hfuns k' hin
    cases hfd' : (fdefsOf m)[k']?.join with
    | none => simp [funDef, hfd'] at hfd
    | some fd' =>
    simp [funDef, hfd'] at hfd
    subst hfd
    exact ⟨fd', List.mem_cons_of_mem _ (List.mem_append_right _ hd)⟩

/-- Each function index of a translation has its definition in the program. -/
theorem translate_funcs {m : Module} {T : Translation} (h : translate m = some T) {k : Nat}
    (hk : k ∈ T.funcs) :
    ∃ fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs := by
  simp [translate, Option.bind_eq_some_iff] at h
  obtain ⟨-, gdefs, -, -, funs, hfuns, rfl⟩ := h
  obtain ⟨d, hd, hfd⟩ := mapM_mem hfuns k hk
  cases hfd' : (fdefsOf m)[k]?.join with
  | none => simp [funDef, hfd'] at hfd
  | some fd =>
  simp [funDef, hfd'] at hfd
  subst hfd
  exact ⟨fd, List.mem_cons_of_mem _ (List.mem_append_right _ hd)⟩

theorem type_of_params_zipIdx (ps : List VT) (start : Nat) :
    type_of_params ((ps.zipIdx start).map fun x => (localId x.2, x.1.ty)) = ps.map VT.ty := by
  induction ps generalizing start with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.zipIdx_cons, List.map_cons, type_of_params] at ih ⊢
      rw [ih]

theorem trFunction_sig {sigs : List (Option (List VT × Option VT))} {G : Nat} {f : Function}
    {fd : function} (h : trFunction sigs G f = some fd) :
    ∃ ps r, signatureOf f = some (ps, r) ∧ type_of_function fd = funType ps r := by
  obtain ⟨ps, ls, r, body, nc, hps, -, hrs, -, rfl⟩ := trFunction_spec h
  refine ⟨ps, r, ?_, ?_⟩
  · unfold signatureOf
    rw [hps, hrs]
    cases r <;> rfl
  · simp only [type_of_function, funType]
    rw [type_of_params_zipIdx]

section

variable {A : Archi} {X : ExtSem} {E : Env}

/-- Every function of a translated program simulates its Talos function at every fuel. -/
theorem translate_correct {m : Module} {T : Translation} (h : translate m = some T)
    (hE : EnvOk E) (hG : E.globals.length = m.globals.length)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd)) :
    ∀ F k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ f ps r, m.funcs[k]? = some f ∧ signatureOf f = some (ps, r) ∧
        RunSimFun A X E m F k ps r fd := by
  obtain ⟨himp, hfuns⟩ := translate_spec h
  intro F
  induction F using Nat.strongRecOn with
  | _ F ih =>
      intro k fd hk
      obtain ⟨f, hf, htr, hclosed⟩ := hfuns k fd hk
      obtain ⟨ps, r, hsig, -⟩ := trFunction_sig htr
      refine ⟨f, ps, r, hf, hsig, ?_⟩
      refine run_sim_fun (CallOk := fun k' => ∃ fd',
          (funId k', globdef.Gfun (fundef.Internal fd')) ∈ T.cprogram.prog_defs)
        hE himp hf hG.symm htr hsig ?_ hclosed
      intro k' ⟨fd', hk'⟩ g hg c hc
      obtain ⟨f', ps', r', hf', hsig', hrun⟩ := ih g hg k' fd' hk'
      obtain ⟨f'', hf'', htr', -⟩ := hfuns k' fd' hk'
      rw [hf'] at hf''
      cases hf''
      obtain ⟨ps'', r'', hsig'', hty⟩ := trFunction_sig htr'
      rw [hsig'] at hsig''
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsig'')
      obtain ⟨b, hsym, hptr⟩ := hF k' fd' hk'
      refine ⟨ps', r', b, fd', ?_, hsym, hptr, hty, hrun⟩
      rw [hc]
      simp [List.getElem?_map, hf', hsig']

end

end LeanExe.Native
