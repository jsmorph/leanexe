import Verified.AlignedEntries
import Verified.AlignedCopy

/-!
The alignment theorems of a compiled program without byte literals, which `verified_compile`
instantiates for each function.  `Prog.callsAlignedWith` is `Prog.correctWith` under the flag at
`strict = true`: it discharges the premises of `Prog.callsX` for the module that `compileWith`
builds, by `Runtime.releaseAligned`, `Runtime.allocAligned`, and `copyCodeX`.
`Prog.implementsAlignedWith` gives `ImplementsAligned` of a function whose code takes no call
depth, at its call index, `Prog.entry_alignedWith` gives it at the exported entry of a function
whose code takes the call depth, and `Prog.wrapper_alignedWith` gives `ImplementsTablesAligned` at
a wrapper's entry.  `ImplementsAligned.transferAgree` and `ImplementsTablesAligned.transferAgree`
carry them to a type whose representation agrees with the function's, as
`ImplementsA.transferAgree` does.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- `Prog.correctWith` under the flag: every function of the module meets `FunSpecX true`. -/
theorem Prog.callsAlignedWith {S : List Sig} (prog : Prog S) (funs : Funs S)
    (h : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) (hNoLiterals : prog.literals = []) :
    CallsX true (compileWith prog tables wrappers) funs prog.flags (prog.boundsAt funs)
      (prog.fitsAt funs) ⟨tablesEnd tables, []⟩ := by
  have hm := compileWith_runtime prog tables wrappers
  apply prog.callsX funs h _ hm (fun _ => Runtime.releaseAligned hm)
    (fun _ => Runtime.allocAligned hm) (fun _ => copyCodeX hm)
  · intro k hk
    rw [compileWith_funcs prog tables wrappers hk]
    simp only [Prog.literalPool, hNoLiterals, List.eraseDups_nil]
  · simp [Prog.Covered, hNoLiterals]

/-- `ImplementsAligned` of a function whose code takes no call depth, at its call index. -/
theorem Prog.implementsAlignedWith {S : List Sig} (prog : Prog S) (funs : Funs S)
    (h : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) (hNoLiterals : prog.literals = [])
    {g : Sig} (f : FVar S g) (hd : g.depth = false)
    {Pre : Env g.params → Heap → Store Unit → Prop} :
    @ImplementsAligned _ (Env.represent g.params g.modes) (compileWith prog tables wrappers)
      f.callIndex Pre :=
  FunSpecX.implementsAligned (prog.callsAlignedWith funs h tables wrappers hNoLiterals f 0) hd

/-- `ImplementsAligned` at the exported entry of the `j`-th function whose code takes the call
depth. -/
theorem Prog.entry_alignedWith {S : List Sig} (prog : Prog S) (funs : Funs S)
    (h : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) {g : Sig} (f : FVar S g) (hd : g.depth = true)
    {j : Nat} (hj : prog.depthFuns[j]? = some (f.callIndex, g.params, g.result))
    (hNoLiterals : prog.literals = []) {Pre : Env g.params → Heap → Store Unit → Prop} :
    @ImplementsAligned _ (Env.represent g.params g.modes) (compileWith prog tables wrappers)
      (2 + S.length + j) Pre :=
  entry_aligned (compileWith_runtime prog tables wrappers)
    ((prog.callsAlignedWith funs h tables wrappers hNoLiterals f 0).2 rfl) hd rfl
    (compileWith_entries prog tables wrappers hj)

/-- `ImplementsTablesAligned` of the `j`-th wrapper, at its entry. -/
theorem Prog.wrapper_alignedWith {S : List Sig} (prog : Prog S) (funs : Funs S)
    (h : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) {j : Nat} {w : Wrapper S tables.length}
    (hj : wrappers[j]? = some w) (hNoLiterals : prog.literals = [])
    {Pre : Env w.params → Heap → Store Unit → Prop} :
    @ImplementsTablesAligned _ (Env.represent w.params (w.modes.drop w.tables.length))
      (compileWith prog tables wrappers) (2 + S.length + prog.depthFuns.length + j)
      (w.tables.map fun k => (tableAddr tables k.val, tables[k])) Pre :=
  wrapper_aligned (compileWith_runtime prog tables wrappers) w
    (prog.callsAlignedWith funs h tables wrappers hNoLiterals)
    (compileWith_wrappers prog tables wrappers hj)

/-- `ImplementsAligned` for a type whose representation agrees with the theorem's along `g`. -/
theorem ImplementsAligned.transferAgree {α β : Type} {ia : Represent α} {ib : Represent β}
    {m : Module} {entry : Nat} {Pre : α → Heap → Store Unit → Prop}
    (h : @ImplementsAligned α ia m entry Pre) (g : β → α) (hArgs : Agree ib ia g) :
    @ImplementsAligned β ib m entry (fun y => Pre (g y)) := by
  intro env store heap vs y hAt hPre hY hSep hCap hIn
  refine h env store heap vs (g y) hAt hPre ((hArgs.borrowed _ _ _ _).mp hY) ?_ hCap ?_
  · rw [← hArgs.moves, ← hArgs.reads]
    exact hSep
  · obtain ⟨h1, h2, h3⟩ := hIn
    refine ⟨h1, fun p hp => h2 p ?_, fun r hr => h3 r ?_⟩
    · rw [hArgs.moves]
      exact hp
    · rw [hArgs.reads]
      exact hr

/-- `ImplementsTablesAligned` for a type whose representation agrees with the theorem's along
`g`. -/
theorem ImplementsTablesAligned.transferAgree {α β : Type} {ia : Represent α} {ib : Represent β}
    {m : Module} {entry : Nat} {tables : List (UInt64 × Array UInt64)}
    {Pre : α → Heap → Store Unit → Prop}
    (h : @ImplementsTablesAligned α ia m entry tables Pre) (g : β → α) (hArgs : Agree ib ia g) :
    @ImplementsTablesAligned β ib m entry tables (fun y => Pre (g y)) := by
  intro env store heap vs y hAt hPre hTables hY hSep hCap hIn
  refine h env store heap vs (g y) hAt hPre (fun t ht => ?_) ((hArgs.borrowed _ _ _ _).mp hY) ?_
    hCap ?_
  · rw [← hArgs.moves]
    exact hTables t ht
  · rw [← hArgs.moves, ← hArgs.reads]
    exact hSep
  · obtain ⟨h1, h2, h3⟩ := hIn
    refine ⟨h1, fun p hp => h2 p ?_, fun r hr => h3 r ?_⟩
    · rw [hArgs.moves]
      exact hp
    · rw [hArgs.reads]
      exact hr

end Verified
