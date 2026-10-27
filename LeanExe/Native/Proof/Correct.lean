import LeanExe.Native.Proof.Run
import LeanExe.Native.Proof.Genv

/-!
`translate_correct`: every function of a translated program simulates its Talos function.  For
any global environment that holds the program's globals, `lx_pages`, `lx_mem`, and functions,
with `lx_mem` of the `cap` pages of the translation, a run of function `k` by Talos's `run` that
returns or traps is matched by a call of the C function in CompCert's big-step semantics, with
the result, the globals, the memory, and `lx_status` related as `RunOutcome` states.
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

theorem violation_memIs64 {m : Module} (h : violation m = none) : m.memIs64 = false := by
  unfold violation at h
  cases hs : shapeViolation m with
  | some r => simp [hs] at h
  | none =>
      cases hm : memoryViolation m.memory with
      | some r => simp [hs, hm] at h
      | none =>
          unfold Module.memIs64
          cases hd : m.memory with
          | none => rfl
          | some d =>
              rw [hd] at hm
              by_cases h64 : d.is64
              · simp [memoryViolation, h64] at hm
              · simpa using h64

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
theorem translate_spec {m : Module} {cap : Nat} {T : Translation} (h : translate cap m = some T) :
    m.imports = [] ∧ m.memIs64 = false ∧
    ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ f, m.funcs[k]? = some f ∧ k ∈ T.funcs ∧
        trFunction cap (m.funcs.map signatureOf) m.globals.length f = some fd ∧
        ∀ k', funId k' ∈ callees fd.fn_body →
          ∃ fd', (funId k', globdef.Gfun (fundef.Internal fd')) ∈ T.cprogram.prog_defs := by
  simp [translate, Option.bind_eq_some_iff] at h
  obtain ⟨hv, decl, -, -, gdefs, -, hclosed, funs, hfuns, rfl⟩ := h
  refine ⟨violation_imports hv, violation_memIs64 hv, ?_⟩
  intro k fd hk
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hk
  rcases hk with hk | ⟨⟨g, i⟩, -, hk⟩ | hk | hk | hk | hk | hk | hk | hk | hk
  · simp at hk
  · simp at hk
  · simp at hk
  · simp at hk
  · simp at hk
  · simp [sqrtDef, sqrtFun] at hk
  · simp [resDefs] at hk
  · obtain ⟨k0, hk0, hdef⟩ := mapM_mem' hfuns _ hk
    cases hfd0 : (fdefsOf cap m)[k0]?.join with
    | none => simp [funDef, hfd0] at hdef
    | some fd0 =>
    simp [funDef, hfd0] at hdef
    obtain ⟨hid, rfl⟩ := hdef
    have : k0 = k := funId_inj hid
    subst this
    cases hf : m.funcs[k0]? with
    | none => simp [fdefsOf, hf] at hfd0
    | some f =>
    have htr : trFunction cap (m.funcs.map signatureOf) m.globals.length f = some fd0 := by
      simpa [fdefsOf, hf] using hfd0
    refine ⟨f, rfl, hk0, htr, fun k' hk' => ?_⟩
    have hcall : k' ∈ callsOf cap m k0 := by
      unfold callsOf
      rw [hfd0]
      have hm : funId k' % 4 = 3 := by show (4 * k' + 3 : Nat) % 4 = 3; omega
      exact List.mem_filterMap.mpr ⟨funId k', hk', by rw [ite_eq_left hm, funId_div]⟩
    have hin := hclosed k0 hk0 k' hcall
    obtain ⟨d, hd, hfd⟩ := mapM_mem hfuns k' hin
    cases hfd' : (fdefsOf cap m)[k']?.join with
    | none => simp [funDef, hfd'] at hfd
    | some fd' =>
    simp [funDef, hfd'] at hfd
    subst hfd
    exact ⟨fd', by simp [hd]⟩
  · simp only [Prod.mk.injEq] at hk
    have e : (4 * k + 3 : Nat) = 16 := hk.1
    omega
  · simp at hk

theorem translate_nres {m : Module} {cap : Nat} {T : Translation} (h : translate cap m = some T) :
    T.nres = maxResults m T.funcs := by
  simp [translate, Option.bind_eq_some_iff] at h
  obtain ⟨-, decl, -, -, gdefs, -, -, funs, -, rfl⟩ := h
  rfl

/-- Each function index of a translation has its definition in the program. -/
theorem translate_funcs {m : Module} {cap : Nat} {T : Translation} (h : translate cap m = some T)
    {k : Nat} (hk : k ∈ T.funcs) :
    ∃ fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs := by
  simp [translate, Option.bind_eq_some_iff] at h
  obtain ⟨-, decl, -, -, gdefs, -, -, funs, hfuns, rfl⟩ := h
  obtain ⟨d, hd, hfd⟩ := mapM_mem hfuns k hk
  cases hfd' : (fdefsOf cap m)[k]?.join with
  | none => simp [funDef, hfd'] at hfd
  | some fd =>
  simp [funDef, hfd'] at hfd
  subst hfd
  exact ⟨fd, by simp [hd]⟩

theorem type_of_params_zipIdx (ps : List VT) (start : Nat) :
    type_of_params ((ps.zipIdx start).map fun x => (localId x.2, x.1.ty)) = ps.map VT.ty := by
  induction ps generalizing start with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.zipIdx_cons, List.map_cons, type_of_params] at ih ⊢
      rw [ih]

theorem trFunction_sig {cap : Nat} {sigs : List (Option (List VT × List VT))} {G : Nat}
    {f : Function} {fd : function} (h : trFunction cap sigs G f = some fd) :
    ∃ ps rs, signatureOf f = some (ps, rs) ∧ type_of_function fd = funType ps rs ∧
      resultsOk rs = true ∧ f.results.length = rs.length := by
  obtain ⟨ps, ls, rs, body, nc, hps, -, hrs, hok, -, rfl⟩ := trFunction_spec h
  refine ⟨ps, rs, ?_, ?_, hok, (mapM_length hrs).symm⟩
  · unfold signatureOf
    rw [hps, hrs]
    simp [hok]
  · simp only [type_of_function, funType]
    rw [type_of_params_zipIdx]

theorem maxStep_le (m : Module) (acc k : Nat) : acc ≤ maxStep m acc k := by
  unfold maxStep
  split
  · split
    · exact Nat.le_max_left _ _
    · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem foldl_maxStep_le (m : Module) : ∀ (ks : List Nat) (acc : Nat),
    acc ≤ ks.foldl (maxStep m) acc
  | [], _ => Nat.le_refl _
  | k :: ks, acc => Nat.le_trans (maxStep_le m acc k) (foldl_maxStep_le m ks _)

theorem le_maxResults (m : Module) {k : Nat} {f : Function} (hf : m.funcs[k]? = some f)
    (h2 : 2 ≤ f.results.length) :
    ∀ (ks : List Nat) (acc : Nat), k ∈ ks → f.results.length ≤ ks.foldl (maxStep m) acc
  | [], _, h => by simp at h
  | k' :: ks, acc, h => by
      rcases List.mem_cons.mp h with rfl | h
      · refine Nat.le_trans ?_ (foldl_maxStep_le m ks _)
        simp only [maxStep, hf, ite_eq_left h2]
        exact Nat.le_max_right _ _
      · exact le_maxResults m hf h2 ks _ h

/-- Several results of a function of a translation fit in `nres` result globals that the
translation's `maxResults` bounds. -/
theorem resOk_of {E : Env} {m : Module} {k : Nat} {f : Function} {ks : List Nat} {rs : List VT}
    (hf : m.funcs[k]? = some f) (hk : k ∈ ks) (hnres : maxResults m ks ≤ E.nres)
    (hok : resultsOk rs = true) (hlen : f.results.length = rs.length) : ResOk E rs := by
  intro h2
  refine ⟨?_, ?_⟩
  · have := le_maxResults m hf (by omega) ks 0 hk
    unfold maxResults at hnres
    omega
  · unfold resultsOk at hok
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hok
    rcases hok with h | h
    · omega
    · exact h

section

variable {A : Archi} {X : ExtSem} {E : Env}

/-- Every function of a translated program simulates its Talos function at every fuel. -/
theorem translate_correct {m : Module} {cap : Nat} {T : Translation} (h : translate cap m = some T)
    (hE : EnvOk E) (hG : E.globals.length = m.globals.length) (hcap : E.cap = cap)
    (hnres : T.nres ≤ E.nres)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd)) :
    ∀ F k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ f ps rs, m.funcs[k]? = some f ∧ signatureOf f = some (ps, rs) ∧
        RunSimFun A X E m F k ps rs fd := by
  obtain ⟨himp, h64, hfuns⟩ := translate_spec h
  rw [translate_nres h] at hnres
  intro F
  induction F using Nat.strongRecOn with
  | _ F ih =>
      intro k fd hk
      obtain ⟨f, hf, hkf, htr, hclosed⟩ := hfuns k fd hk
      obtain ⟨ps, rs, hsig, -, hok, hlen⟩ := trFunction_sig htr
      refine ⟨f, ps, rs, hf, hsig, ?_⟩
      refine run_sim_fun (CallOk := fun k' => ∃ fd',
          (funId k', globdef.Gfun (fundef.Internal fd')) ∈ T.cprogram.prog_defs)
        hE himp hf hG.symm hcap.symm h64 htr hsig (resOk_of hf hkf hnres hok hlen) ?_ hclosed
      intro k' ⟨fd', hk'⟩ g hg c hc
      obtain ⟨f', ps', rs', hf', hsig', hrun⟩ := ih g hg k' fd' hk'
      obtain ⟨f'', hf'', hkf', htr', -⟩ := hfuns k' fd' hk'
      rw [hf'] at hf''
      cases hf''
      obtain ⟨ps'', rs'', hsig'', hty, hok', hlen'⟩ := trFunction_sig htr'
      rw [hsig'] at hsig''
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsig'')
      obtain ⟨b, hsym, hptr⟩ := hF k' fd' hk'
      refine ⟨ps', rs', b, fd', ?_, hsym, hptr, hty, resOk_of hf' hkf' hnres hok' hlen', hrun⟩
      rw [hc]
      simp [List.getElem?_map, hf', hsig']

end

end LeanExe.Native
