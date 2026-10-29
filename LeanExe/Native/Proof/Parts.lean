import LeanExe.Native.Proof.Init

/-!
The theorems `p.inSubset` and `p.translation_funcs` of `verified_compile` from one part per
function.  `verified_compile` defines a module as `compileWith` of a program, so the kernel
compiles the module when it reduces a statement about it, and a statement about the whole
module holds the whole module in one check.  `inSubset_of_parts` derives `InSubset m` from the
module's shape, its memory, and each function's `functionViolation`.
`translate_funcs_of_parts` derives the list of functions of `translate cap m` from the guards of
`translate` on the memory and the globals and from each function's `callInfo`: the functions
that its C function calls, or `none` when it has no C function.  `verified_compile` states the
part of each function in its own theorem, as the encoding's theorems `func_ok_k` do.
-/

namespace LeanExe.Native

open Wasm LClight

/-- The functions that the C function of `k` calls, or `none` when `k` has no C function. -/
def callInfo (cap : Nat) (m : Module) (k : Nat) (alignedAccess : Bool := false) :
    Option (List Nat) :=
  ((fdefsOf cap m alignedAccess)[k]?.join).map fun f =>
    (callees f.fn_body).filterMap fun id => if id % 4 = 3 then some (id / 4) else none

/-- `includedOf` from the `callInfo` of each function. -/
def includedFrom (infos : List (Option (List Nat))) : List Nat :=
  closeUnderCalls (fun k => (infos[k]?.join).getD []) (infos.length + 1)
    ((List.range infos.length).filter fun k => (infos[k]?.join).isSome)

/-- The guard of `translate` that the functions of `L` call only functions of `L`, from the
`callInfo` of each function. -/
def closedFrom (infos : List (Option (List Nat))) (L : List Nat) : Bool :=
  L.all fun k => ((infos[k]?.join).getD []).all (L.contains ·)

/-- The guard of `translate` on the memory. -/
def memoryOk (cap : Nat) (m : Module) : Bool :=
  match m.memory with
  | some decl => decide (decl.pagesMin.toNat ≤ cap ∧ cap ≤ 65535)
  | none => false

theorem inSubset_of_parts {m : Module} {n : Nat} (hs : shapeViolation m = none)
    (hm : memoryViolation m.memory = none) (hn : m.funcs.length = n)
    (hf : ∀ k < n, functionViolation k m.funcs[k]! = none) : InSubset m := by
  simp only [InSubset, violation, hs, hm, List.findSome?_eq_none_iff]
  rintro ⟨f, k⟩ hmem
  have hk : m.funcs[k]? = some f := List.mem_zipIdx_iff_getElem?.mp hmem
  have hlt : k < m.funcs.length := (List.getElem?_eq_some_iff.mp hk).1
  have hf' : m.funcs[k]! = f := by rw [List.getElem!_eq_getElem?_getD, hk]; rfl
  rw [← hf']
  exact hf k (hn ▸ hlt)

theorem callsOf_eq_callInfo (cap : Nat) (m : Module) (k : Nat) :
    callsOf cap m k = (callInfo cap m k).getD [] := by
  unfold callsOf callInfo
  cases (fdefsOf cap m)[k]?.join <;> rfl

theorem callInfo_isSome (cap : Nat) (m : Module) (k : Nat) :
    (callInfo cap m k).isSome = ((fdefsOf cap m)[k]?.join).isSome := by
  unfold callInfo
  cases (fdefsOf cap m)[k]?.join <;> rfl

theorem callInfo_of_parts {cap : Nat} {m : Module} {infos : List (Option (List Nat))}
    (hlen : m.funcs.length = infos.length)
    (h : ∀ k < infos.length, callInfo cap m k = infos[k]?.join) (k : Nat) :
    callInfo cap m k = infos[k]?.join := by
  by_cases hk : k < infos.length
  · exact h k hk
  · have h1 : (fdefsOf cap m)[k]? = none :=
      List.getElem?_eq_none (by simp only [fdefsOf, List.length_map]; omega)
    have h2 : infos[k]? = none := List.getElem?_eq_none (by omega)
    simp [callInfo, h1, h2]

theorem callsOf_of_parts {cap : Nat} {m : Module} {infos : List (Option (List Nat))}
    (hlen : m.funcs.length = infos.length)
    (h : ∀ k < infos.length, callInfo cap m k = infos[k]?.join) :
    callsOf cap m = fun k => (infos[k]?.join).getD [] := by
  funext k
  rw [callsOf_eq_callInfo, callInfo_of_parts hlen h]

theorem includedOf_of_parts {cap : Nat} {m : Module} {infos : List (Option (List Nat))}
    (hlen : m.funcs.length = infos.length)
    (h : ∀ k < infos.length, callInfo cap m k = infos[k]?.join) :
    includedOf cap m = includedFrom infos := by
  have hs : (fun k : Nat => ((fdefsOf cap m)[k]?.join).isSome) =
      fun k : Nat => (infos[k]?.join).isSome := by
    funext k
    rw [← callInfo_isSome, callInfo_of_parts hlen h]
  unfold includedOf includedFrom
  rw [callsOf_of_parts hlen h, hs, hlen]

theorem mapM_isSome {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, (f a).isSome = true) → (l.mapM f).isSome = true
  | [], _ => rfl
  | a :: l, h => by
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (by simp))
      obtain ⟨l', hl⟩ := Option.isSome_iff_exists.mp
        (mapM_isSome (l := l) fun x hx => h x (by simp [hx]))
      simp [hb, hl]

theorem translate_funcs_of_parts {cap : Nat} {m : Module} {infos : List (Option (List Nat))}
    {L : List Nat} {n : Nat} (hv : InSubset m) (hmem : memoryOk cap m = true)
    (hg : (m.globals.mapM globalDef).isSome = true) (hn : m.funcs.length = n)
    (hi : infos.length = n) (hparts : ∀ k < n, callInfo cap m k = infos[k]?.join)
    (hL : includedFrom infos = L) (hc : closedFrom infos L = true) :
    (translate cap m).map Translation.funcs = some L := by
  have hlen : m.funcs.length = infos.length := hn.trans hi.symm
  have h : ∀ k < infos.length, callInfo cap m k = infos[k]?.join :=
    fun k hk => hparts k (hi ▸ hk)
  have hinc : includedOf cap m = L := (includedOf_of_parts hlen h).trans hL
  obtain ⟨decl, hdecl, hcap⟩ :
      ∃ decl, m.memory = some decl ∧ decl.pagesMin.toNat ≤ cap ∧ cap ≤ 65535 := by
    unfold memoryOk at hmem
    cases hd : m.memory with
    | none => rw [hd] at hmem; cases hmem
    | some decl => rw [hd] at hmem; exact ⟨decl, rfl, of_decide_eq_true hmem⟩
  obtain ⟨gdefs, hgdefs⟩ := Option.isSome_iff_exists.mp hg
  have hclosed : ∀ k ∈ L, ∀ j ∈ callsOf cap m k, j ∈ L := by
    have hc' : (L.all fun k => (callsOf cap m k).all (L.contains ·)) = true := by
      simp only [callsOf_eq_callInfo, callInfo_of_parts hlen h]
      exact hc
    simpa using hc'
  have hfuns : (L.mapM (funDef cap m)).isSome = true := by
    apply mapM_isSome
    intro k hk
    have hk' : k ∈ (List.range m.funcs.length).filter
        fun k => ((fdefsOf cap m)[k]?.join).isSome := by
      rw [← hinc] at hk
      exact (closeUnderCalls_sublist _ _ _).subset hk
    have hsome := (List.mem_filter.mp hk').2
    unfold funDef
    cases hj : (fdefsOf cap m)[k]?.join with
    | none => rw [hj] at hsome; cases hsome
    | some f => rfl
  obtain ⟨funs, hfuns'⟩ := Option.isSome_iff_exists.mp hfuns
  have hv' : violation m = none := hv
  simp [translate, hv', hdecl, hcap, hgdefs, hinc, hfuns']
  rw [guard, ite_eq_left hclosed]
  rfl

end LeanExe.Native
