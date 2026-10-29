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
a wrapper's entry, each with the trap flag, function, and conditions of the `ImplementsA` or
`ImplementsTables` theorem at the same index.  `ImplementsAligned.transferAgree` and
`ImplementsTablesAligned.transferAgree` carry them to types whose representations agree with the
function's arguments and result, as `ImplementsA.transferAgree` and
`ImplementsTables.transferAgree` do.
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

/-- `Prog.correctWith`'s counterpart for `ImplementsAligned`: a function whose code takes no call
depth, at its call index, with the trap flag, function, and conditions of `p.f.implements`. -/
theorem Prog.implementsAlignedWith {S : List Sig} (prog : Prog S) (funs : Funs S)
    (h : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) (hNoLiterals : prog.literals = [])
    {g : Sig} (f : FVar S g) (hd : g.depth = false) :
    @ImplementsAligned _ _ (Env.represent g.params g.modes) (Ty.represent g.result) g.aborts
      (compileWith prog tables wrappers) f.callIndex (funs.get f) (fun _ _ _ => True)
      (fun _ _ _ _ _ => True) :=
  FunSpecX.implementsAligned (prog.callsAlignedWith funs h tables wrappers hNoLiterals f 0) hd

/-- `Prog.correct_entryWith`'s counterpart for `ImplementsAligned`: the exported entry of the
`j`-th function whose code takes the call depth. -/
theorem Prog.entry_alignedWith {S : List Sig} (prog : Prog S) (funs : Funs S)
    (h : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) {g : Sig} (f : FVar S g) (hd : g.depth = true)
    {j : Nat} (hj : prog.depthFuns[j]? = some (f.callIndex, g.params, g.result))
    (hNoLiterals : prog.literals = []) :
    @ImplementsAligned _ _ (Env.represent g.params g.modes) (Ty.represent g.result) true
      (compileWith prog tables wrappers) (2 + S.length + j) (funs.get f) (fun _ _ _ => True)
      (fun _ _ _ _ _ => True) :=
  entry_aligned (compileWith_runtime prog tables wrappers)
    ((prog.callsAlignedWith funs h tables wrappers hNoLiterals f 0).2 rfl) hd rfl
    (compileWith_entries prog tables wrappers hj)

/-- `Prog.correct_wrapper`'s counterpart for `ImplementsTablesAligned`: the entry of the `j`-th
wrapper. -/
theorem Prog.wrapper_alignedWith {S : List Sig} (prog : Prog S) (funs : Funs S)
    (h : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) {j : Nat} {w : Wrapper S tables.length}
    (hj : wrappers[j]? = some w) (hNoLiterals : prog.literals = []) :
    @ImplementsTablesAligned _ _ (Env.represent w.params (w.modes.drop w.tables.length))
      (Ty.represent w.result) (w.aborts || w.depth) (compileWith prog tables wrappers)
      (2 + S.length + prog.depthFuns.length + j)
      (fun env => funs.get w.callee (Env.withTables tables w.tables env))
      (w.tables.map fun k => (tableAddr tables k.val, tables[k])) (fun _ _ _ => True)
      (fun _ _ _ _ _ => True) :=
  wrapper_aligned (compileWith_runtime prog tables wrappers) w
    (prog.callsAlignedWith funs h tables wrappers hNoLiterals)
    (compileWith_wrappers prog tables wrappers hj)

/-- `ImplementsA.transferAgree` for `ImplementsAligned`: the theorem for types whose
representations agree with the theorem's along `g` and `r`. -/
theorem ImplementsAligned.transferAgree {α β γ δ : Type} {ia : Represent α} {ib : Represent β}
    {ic : Represent γ} {id : Represent δ} {aborts : Bool} {m : Module} {entry : Nat}
    {f : α → γ} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsAligned aborts m entry f Pre Post)
    (g : β → α) (r : δ → γ) (F : β → δ) (hF : ∀ y, f (g y) = r (F y)) (hArgs : Agree ib ia g)
    (hResult : Agree id ic r) :
    ImplementsAligned aborts m entry F (fun y => Pre (g y)) (fun y => Post (g y)) := by
  intro env store heap vs y hAt hPre hY hSep hCap hIn
  have hBlocks : ∀ store vs, @Represent.blocks _ id store vs (F y) =
      @Represent.blocks _ ic store vs (f (g y)) := fun _ _ => by
    rw [hF]
    exact hResult.blocks _ _ _
  have hSep' : Separate store (@Represent.moves _ ia store vs (g y))
      (@Represent.reads _ ia store vs (g y)) := by
    rw [← hArgs.moves, ← hArgs.reads]
    exact hSep
  have hIn' : @AlignedInput _ ia heap store vs (g y) := by
    obtain ⟨h1, h2, h3⟩ := hIn
    refine ⟨h1, fun p hp => h2 p ?_, fun r hr => h3 r ?_⟩
    · rw [hArgs.moves]
      exact hp
    · rw [hArgs.reads]
      exact hr
  obtain ⟨hA, hRun⟩ := h env store heap vs (g y) hAt hPre ((hArgs.borrowed _ _ _ _).mp hY) hSep'
    hCap hIn'
  refine ⟨hA, hRun.mono fun final values ⟨heap', hAt', hOwned, hCaps, hRegions, hPost, hHeapAl,
    hOut⟩ => ⟨heap', hAt', (hResult.owned _ _ _ _).mpr (hF y ▸ hOwned), hCaps,
    fun rg hr hpos hAp => ?_, hPost, hHeapAl, fun b hb => hOut b (by rw [← hBlocks]; exact hb)⟩⟩
  obtain ⟨hb, hreg, hout⟩ := hRegions rg hr hpos (by rw [← hArgs.moves]; exact hAp)
  refine ⟨hb, hreg, ?_⟩
  simp only [Represent.outside, hBlocks]
  exact hout

/-- `ImplementsTables.transferAgree` for `ImplementsTablesAligned`. -/
theorem ImplementsTablesAligned.transferAgree {α β γ δ : Type} {ia : Represent α}
    {ib : Represent β} {ic : Represent γ} {id : Represent δ} {aborts : Bool} {m : Module}
    {entry : Nat} {f : α → γ} {tables : List (UInt64 × Array UInt64)}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsTablesAligned aborts m entry f tables Pre Post)
    (g : β → α) (r : δ → γ) (F : β → δ) (hF : ∀ y, f (g y) = r (F y)) (hArgs : Agree ib ia g)
    (hResult : Agree id ic r) :
    ImplementsTablesAligned aborts m entry F tables (fun y => Pre (g y)) (fun y => Post (g y)) := by
  intro env store heap vs y hAt hPre hT hY hSep hCap hIn
  have hBlocks : ∀ store vs, @Represent.blocks _ id store vs (F y) =
      @Represent.blocks _ ic store vs (f (g y)) := fun _ _ => by
    rw [hF]
    exact hResult.blocks _ _ _
  have hSep' : Separate store (@Represent.moves _ ia store vs (g y))
      (@Represent.reads _ ia store vs (g y)) := by
    rw [← hArgs.moves, ← hArgs.reads]
    exact hSep
  have hIn' : @AlignedInput _ ia heap store vs (g y) := by
    obtain ⟨h1, h2, h3⟩ := hIn
    refine ⟨h1, fun p hp => h2 p ?_, fun r hr => h3 r ?_⟩
    · rw [hArgs.moves]
      exact hp
    · rw [hArgs.reads]
      exact hr
  obtain ⟨hA, hRun⟩ := h env store heap vs (g y) hAt hPre (fun t ht => by
      rw [← hArgs.moves]
      exact hT t ht) ((hArgs.borrowed _ _ _ _).mp hY) hSep' hCap hIn'
  refine ⟨hA, hRun.mono fun final values ⟨heap', hAt', hOwned, hCaps, hRegions, hPost, hHeapAl,
    hOut⟩ => ⟨heap', hAt', (hResult.owned _ _ _ _).mpr (hF y ▸ hOwned), hCaps,
    fun rg hr hpos hAp => ?_, hPost, hHeapAl, fun b hb => hOut b (by rw [← hBlocks]; exact hb)⟩⟩
  obtain ⟨hb, hreg, hout⟩ := hRegions rg hr hpos (by rw [← hArgs.moves]; exact hAp)
  refine ⟨hb, hreg, ?_⟩
  simp only [Represent.outside, hBlocks]
  exact hout

end Verified
