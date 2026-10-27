import TestSupport.Native.Gcd
import LeanExe.Native.Proof.Correct

/-!
The theorems of the translated GCD functions, from the verified compiler's theorems and
`translate_correct`.  `loop_native`: for every global environment that holds the C globals and
functions of the translation, and every C memory whose globals hold a Talos store's globals and
whose `lx_status` is 0, the call of `lxf_gcd` on `a` and `b` terminates, returns `gcd a b`, and
leaves the globals and `lx_status` as they were.  `rec_native` states the same of the recursion
that takes the call depth, except that the call may instead end with `lx_status` set to the code
of `unreachable`, for a Talos store that meets the premises of the verified compiler's theorem.
-/

namespace TestSupport.Native.Gcd

open Wasm LClight LeanExe.Native LeanExe.Pipeline

/-- The translations exist and contain the expected functions. -/
theorem loop_translates : ∃ T, translate loopCompiled.module = some T ∧ T.funcs = [2] :=
  ⟨_, rfl, rfl⟩

theorem rec_translates : ∃ T, translate recCompiled.module = some T ∧ T.funcs = [2, 3] :=
  ⟨_, rfl, rfl⟩

section

variable {A : Archi} {X : ExtSem} {E : Env}

theorem loop_native {T : Translation} (hT : translate loopCompiled.module = some T)
    {fd : function} (hfd : (funId 2, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs)
    (hE : EnvOk E) (hG : E.globals.length = loopCompiled.module.globals.length)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd))
    (st : Store Unit) (m : mem) (a b : UInt64)
    (hg : GlobalsRel E st.globals.globals m) (hs : StatusRel E m 0) :
    ∃ t m', eval_funcall A X E.ge m (.Internal fd) [.Vlong a, .Vlong b] t m'
        (.Vlong (gcd a b)) ∧
      GlobalsRel E st.globals.globals m' ∧ StatusRel E m' 0 := by
  obtain ⟨N, hN⟩ := loopCompiled.gcd.pure {} st (a, b)
  rcases hN N (Nat.le_refl _) with ⟨vs, st', hrun, hst, hvals⟩ | hfalse
  · obtain ⟨f, ps, r, hf, hsig, hsim⟩ := translate_correct (A := A) (X := X) hT hE hG hF N 2 fd hfd
    have hsig' : signatureOf f = some ([.i64, .i64], some .i64) := by
      have : loopCompiled.module.funcs[2]? = some f := hf
      rw [show loopCompiled.module.funcs[2]? = some (loopCompiled.module.funcs[2]'(by decide))
        from rfl] at this
      cases this
      rfl
    rw [hsig'] at hsig
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsig)
    have hargs : ArgsTyped [.i64, .i64] [.i64 b, .i64 a] := ⟨by simp, by simp [AllHas, VT.has]⟩
    have ho := hsim st [.i64 b, .i64 a] m {} hargs hg hs
    have hrun' : run N loopCompiled.module 2 st [.i64 b, .i64 a] {} = .Success vs st' := hrun
    rw [hrun'] at ho
    obtain ⟨t, m', vres, hcall, hg', hs', hres⟩ := ho
    obtain ⟨v, hv, -, rfl⟩ := hres
    subst hv
    simp [Scalar.values] at hvals
    subst hvals
    rw [hst] at hg'
    exact ⟨t, m', hcall, hg', hs'⟩
  · exact hfalse.elim

theorem rec_native {T : Translation} (hT : translate recCompiled.module = some T)
    {fd : function} (hfd : (funId 3, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs)
    (hE : EnvOk E) (hG : E.globals.length = recCompiled.module.globals.length)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd))
    (st : Store Unit) (heap : Heap) (hheap : heap.At st)
    (hcap : st.memoryCap recCompiled.module 0 ≤ 65535) (m : mem) (a b : UInt64)
    (hg : GlobalsRel E st.globals.globals m) (hs : StatusRel E m 0) :
    ∃ t m' vres, eval_funcall A X E.ge m (.Internal fd) [.Vlong a, .Vlong b] t m' vres ∧
      ((vres = .Vlong (gcd a b) ∧ StatusRel E m' 0) ∨ StatusRel E m' trapUnreachable) := by
  obtain ⟨N, hN⟩ := recCompiled.gcd.implements {} st heap [.i64 a, .i64 b] (a, b) hheap trivial
    (by first | rfl | exact ⟨[.i64 a], [.i64 b], rfl, rfl, rfl⟩)
    (by first | exact Separate.nil | exact ⟨.nil, fun _ h => by simp at h⟩) hcap
  obtain ⟨f, ps, r, hf, hsig, hsim⟩ := translate_correct (A := A) (X := X) hT hE hG hF N 3 fd hfd
  have hsig' : signatureOf f = some ([.i64, .i64], some .i64) := by
    have : recCompiled.module.funcs[3]? = some f := hf
    rw [show recCompiled.module.funcs[3]? = some (recCompiled.module.funcs[3]'(by decide))
      from rfl] at this
    cases this
    rfl
  rw [hsig'] at hsig
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsig)
  have hargs : ArgsTyped [.i64, .i64] [.i64 b, .i64 a] := ⟨by simp, by simp [AllHas, VT.has]⟩
  have ho := hsim st [.i64 b, .i64 a] m {} hargs hg hs
  rcases hN N (Nat.le_refl _) with ⟨vs, st', hrun, heap', -, hown, -⟩ | ⟨st', hrun⟩
  · have hrun' : run N recCompiled.module 3 st [.i64 b, .i64 a] {} = .Success vs st' := hrun
    rw [hrun'] at ho
    obtain ⟨t, m', vres, hcall, -, hs', hres⟩ := ho
    obtain ⟨v, hv, -, rfl⟩ := hres
    subst hv
    have hv' : [v].reverse = [Value.i64 (gcd a b)] := hown
    simp at hv'
    subst hv'
    exact ⟨t, m', _, hcall, .inl ⟨rfl, hs'⟩⟩
  · have hrun' : run N recCompiled.module 3 st [.i64 b, .i64 a] {} = .Trap st' "unreachable" :=
      hrun
    rw [hrun'] at ho
    obtain ⟨t, m', vres, hcall, -, hs', -⟩ := ho
    exact ⟨t, m', vres, hcall, .inr (by rw [trapCode_unreachable] at hs'; exact hs')⟩

end

/-! ## From the program's initial memory -/

/-- The translation of the loop GCD. -/
def loopT : Translation := (translate loopCompiled.module).get (by decide)

theorem loopT_eq : translate loopCompiled.module = some loopT := (Option.some_get _).symm

/-- The global environment of the translated program: `lx_status` is block 1, the Wasm globals
are blocks 2 to 5, and `lxf_gcd` is block 6. -/
def loopE : Env := { ge := globalenv loopT.cprogram, status := 1, globals := [2, 3, 4, 5] }

theorem loopE_ok : EnvOk loopE where
  status := by decide
  globals := by decide
  nodup := by decide
  status_not := by decide

theorem loop_funs : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ loopT.cprogram.prog_defs →
    ∃ b, Genv.find_symbol loopE.ge (funId k) = some b ∧
      Genv.find_funct_ptr loopE.ge b = some (.Internal fd) := by
  intro k fd h
  obtain ⟨b, hs, hd⟩ := Genv.find_add_globals _ _ (by decide) h
  exact ⟨b, hs, Genv.find_funct_ptr_of_def hd⟩

/-- The initial memory of the translated program. -/
def loopM0 : mem := (init_mem loopT.cprogram).get (by decide)

/-- The Talos store in which the module starts. -/
def loopStore : Store Unit := loopCompiled.module.initialStore

/-- A decidable form of `GlobalsRel` for one global. -/
def globalCheck (E : Env) (gs : List Value) (m : mem) (i : Nat) : Bool :=
  match gs[i]?, E.globals[i]? with
  | some (.i64 n), some b =>
      decide (Mem.load .Mint64 m b 0 = some (.Vlong n)) && decide (Mem.valid_access m .Mint64 b 0 .Writable)
  | _, _ => false

theorem GlobalsRel.of_check {E : Env} {gs : List Value} {m : mem}
    (hlen : gs.length = E.globals.length)
    (h : ∀ i, i < E.globals.length → globalCheck E gs m i = true) : GlobalsRel E gs m := by
  refine ⟨hlen, fun i hi => ?_⟩
  have := h i hi
  unfold globalCheck at this
  rw [List.getElem?_eq_getElem hi] at this
  split at this
  · rename_i n b hg hb
    simp at hb
    subst hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨n, hg, this.1, this.2⟩
  · simp at this

theorem loop_globals : GlobalsRel loopE loopStore.globals.globals loopM0 :=
  GlobalsRel.of_check (by decide) (by decide)

theorem loop_status : StatusRel loopE loopM0 0 := ⟨by decide, by decide⟩

/-- From the translated program's initial memory, `lxf_gcd` on `a` and `b` returns `gcd a b`
and leaves `lx_status` at 0. -/
theorem loop_native_init (A : Archi) (X : ExtSem) (a b : UInt64) :
    ∃ fd t m', (funId 2, globdef.Gfun (fundef.Internal fd)) ∈ loopT.cprogram.prog_defs ∧
      eval_funcall A X (globalenv loopT.cprogram) loopM0 (.Internal fd) [.Vlong a, .Vlong b] t m'
        (.Vlong (gcd a b)) ∧ StatusRel loopE m' 0 := by
  obtain ⟨fd, hfd⟩ := translate_funcs loopT_eq (k := 2) (by decide)
  obtain ⟨t, m', hcall, -, hs⟩ := loop_native (A := A) (X := X) loopT_eq hfd loopE_ok (by decide)
    loop_funs loopStore loopM0 a b loop_globals loop_status
  exact ⟨fd, t, m', hfd, hcall, hs⟩

/-- The translation of the recursive GCD. -/
def recT : Translation := (translate recCompiled.module).get (by decide)

theorem recT_eq : translate recCompiled.module = some recT := (Option.some_get _).symm

/-- `lx_status` is block 1, the Wasm globals are blocks 2 to 5, and `lxf_2` and `lxf_gcd` are
blocks 6 and 7. -/
def recE : Env := { ge := globalenv recT.cprogram, status := 1, globals := [2, 3, 4, 5] }

theorem recE_ok : EnvOk recE where
  status := by decide
  globals := by decide
  nodup := by decide
  status_not := by decide

theorem rec_funs : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ recT.cprogram.prog_defs →
    ∃ b, Genv.find_symbol recE.ge (funId k) = some b ∧
      Genv.find_funct_ptr recE.ge b = some (.Internal fd) := by
  intro k fd h
  obtain ⟨b, hs, hd⟩ := Genv.find_add_globals _ _ (by decide) h
  exact ⟨b, hs, Genv.find_funct_ptr_of_def hd⟩

def recM0 : mem := (init_mem recT.cprogram).get (by decide)

def recStore : Store Unit := recCompiled.module.initialStore

theorem rec_globals : GlobalsRel recE recStore.globals.globals recM0 :=
  GlobalsRel.of_check (by decide) (by decide)

theorem rec_status : StatusRel recE recM0 0 := ⟨by decide, by decide⟩

/-- From the translated program's initial memory, `lxf_gcd` on `a` and `b` returns `gcd a b`
with `lx_status` 0, or ends with `lx_status` set to the code of `unreachable`. -/
theorem rec_native_init (A : Archi) (X : ExtSem) (a b : UInt64) :
    ∃ fd t m' vres, (funId 3, globdef.Gfun (fundef.Internal fd)) ∈ recT.cprogram.prog_defs ∧
      eval_funcall A X (globalenv recT.cprogram) recM0 (.Internal fd) [.Vlong a, .Vlong b] t m'
        vres ∧
      ((vres = .Vlong (gcd a b) ∧ StatusRel recE m' 0) ∨ StatusRel recE m' trapUnreachable) := by
  obtain ⟨fd, hfd⟩ := translate_funcs recT_eq (k := 3) (by decide)
  obtain ⟨hheap, hcap, -⟩ := recCompiled.initial
  obtain ⟨t, m', vres, hcall, hres⟩ := rec_native (A := A) (X := X) recT_eq hfd recE_ok
    (by decide) rec_funs recStore _ hheap hcap recM0 a b rec_globals rec_status
  exact ⟨fd, t, m', vres, hfd, hcall, hres⟩

end TestSupport.Native.Gcd
