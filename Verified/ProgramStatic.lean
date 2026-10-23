import Verified.Correct

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem ImplementsStatic.mono {α β : Type} {_ : Represent α} {_ : Represent β}
    {pool : Bytes.LiteralPool} {aborts : Bool} {m : Module} {entry : Nat} {f : α → β}
    {tables : List (UInt64 × Array UInt64)}
    {Pre Pre' : α → Heap → Store Unit → Prop}
    {Post Post' : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsStatic pool aborts m entry f tables Pre Post)
    (hPre : ∀ x heap store, Pre' x heap store → Pre x heap store)
    (hPost : ∀ x heap store heap' store', Pre' x heap store →
      Post x heap store heap' store' → Post' x heap store heap' store') :
    ImplementsStatic pool aborts m entry f tables Pre' Post' :=
  fun host store heap words value hAt hPre' hInput hTables hRep hSep hCap =>
    (h host store heap words value hAt (hPre value heap store hPre')
      hInput hTables hRep hSep hCap).mono
      fun final _ ⟨heap', at_, owned, caps, regions, post⟩ =>
        ⟨heap', at_, owned, caps, regions, hPost value heap store heap' final hPre' post⟩

theorem ImplementsStatic.implementsTables {α β : Type} {_ : Represent α} {_ : Represent β}
    {base : Nat} {aborts : Bool} {m : Module} {entry : Nat} {f : α → β}
    {tables : List (UInt64 × Array UInt64)}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsStatic ⟨base, []⟩ aborts m entry f tables Pre Post) :
    ImplementsTables aborts m entry f tables Pre Post :=
  fun host store heap words value at_ pre tableRep rep sep cap =>
    h host store heap words value at_ pre (Bytes.LiteralPool.Input.empty _ _ _ _ _)
      tableRep rep sep cap

theorem FunSpec.implementsStatic {m : Module} {g : Sig} {idx : Nat}
    {F : Env g.params → g.result.denote} {pf : List Bool} {rf : Bool}
    {A : Env g.params → Nat} {Fi : Env g.params → Bool} {D : UInt64 → Prop}
    {pool : Bytes.LiteralPool} (hF : FunSpec m g idx F pf rf A Fi D pool)
    (hd : g.depth = false) :
    @ImplementsStatic _ _ (Env.represent g.params g.modes) (Ty.represent g.result)
      pool g.aborts m idx F [] (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  intro host store heap words value at_ _ input _ rep sep cap
  exact ((hF.1 hd host store heap words value trivial at_ input rep sep cap).of_imp
    (fun h => by simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h; exact h.1)).mono
    fun _ _ ⟨heap', at_', owned, caps, regions, _⟩ =>
      ⟨heap', at_', owned, caps, regions, trivial⟩

theorem FunSpec.trapFreeStatic {m : Module} {g : Sig} {idx : Nat}
    {F : Env g.params → g.result.denote} {pf : List Bool} {rf : Bool}
    {A : Env g.params → Nat} {Fi : Env g.params → Bool} {D : UInt64 → Prop}
    {pool : Bytes.LiteralPool} (hF : FunSpec m g idx F pf rf A Fi D pool)
    (hd : g.depth = false) :
    @ImplementsStatic _ _ (Env.represent g.params g.modes) (Ty.represent g.result)
      pool false m idx F []
      (fun value heap store => heap.Within store m (Env.credit (g.paidSel pf) value + A value))
      (fun value heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + Env.credit (g.paidSel pf) value + A value) := by
  intro host store heap words value at_ within input _ rep sep cap
  have hle := Env.argPot_le_paidCredit (pf := pf) rep
  have hWithin : heap.Within store m
      (Env.argPot store (g.paidSel pf) words value + A value) := within.mono (by omega)
  have run := hF.1 hd host store heap words value trivial at_ input rep sep cap
  simp only [Bool.not_true, Bool.false_or, hWithin, decide_true, Bool.not_true,
    Bool.and_false] at run
  exact run.mono fun _ _ ⟨heap', at_', owned, caps, regions, top⟩ =>
    ⟨heap', at_', owned, caps, regions, by
      have bound := top trivial
      simp only at bound ⊢
      omega⟩

theorem FunSpec.implementsStaticBounded {m : Module} {g : Sig} {idx : Nat}
    {F : Env g.params → g.result.denote} {pf : List Bool} {rf : Bool}
    {A : Env g.params → Nat} {Fi : Env g.params → Bool} {D : UInt64 → Prop}
    {pool : Bytes.LiteralPool} (hF : FunSpec m g idx F pf rf A Fi D pool)
    (hd : g.depth = false) :
    @ImplementsStatic _ _ (Env.represent g.params g.modes) (Ty.represent g.result)
      pool g.aborts m idx F [] (fun _ _ _ => True)
      (fun value heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + Env.credit (g.paidSel pf) value + A value) := by
  intro host store heap words value at_ _ input _ rep sep cap
  have hle := Env.argPot_le_paidCredit (pf := pf) rep
  exact ((hF.1 hd host store heap words value trivial at_ input rep sep cap).of_imp
    (fun h => by simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h; exact h.1)).mono
    fun _ _ ⟨heap', at_', owned, caps, regions, top⟩ =>
      ⟨heap', at_', owned, caps, regions, by
        have bound := top rfl
        simp only at bound ⊢
        omega⟩

theorem FunSpec.implementsStaticBounded_unpaid {m : Module} {g : Sig} {idx : Nat}
    {F : Env g.params → g.result.denote} {pf : List Bool} {rf : Bool}
    {A : Env g.params → Nat} {Fi : Env g.params → Bool} {D : UInt64 → Prop}
    {pool : Bytes.LiteralPool} (hF : FunSpec m g idx F pf rf A Fi D pool)
    (hd : g.depth = false) (hpf : (pf.all fun paid => !paid) = true) :
    @ImplementsStatic _ _ (Env.represent g.params g.modes) (Ty.represent g.result)
      pool g.aborts m idx F [] (fun _ _ _ => True)
      (fun value heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + A value) := by
  have result := hF.implementsStaticBounded hd
  simpa only [Env.credit_eq_zero (Sig.paidSel_none hpf), Nat.add_zero] using result

theorem FunSpec.trapFreeStatic_unpaid {m : Module} {g : Sig} {idx : Nat}
    {F : Env g.params → g.result.denote} {pf : List Bool} {rf : Bool}
    {A : Env g.params → Nat} {Fi : Env g.params → Bool} {D : UInt64 → Prop}
    {pool : Bytes.LiteralPool} (hF : FunSpec m g idx F pf rf A Fi D pool)
    (hd : g.depth = false) (hpf : (pf.all fun paid => !paid) = true) :
    @ImplementsStatic _ _ (Env.represent g.params g.modes) (Ty.represent g.result)
      pool false m idx F [] (fun value heap store => heap.Within store m (A value))
      (fun value heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + A value) := by
  have result := hF.trapFreeStatic hd
  simpa only [Env.credit_eq_zero (Sig.paidSel_none hpf), Nat.add_zero, Nat.zero_add] using result

theorem wrapper_correctStatic {m : Module} (hm : Runtime m) {S : List Sig}
    {tables : List (Array UInt64)} (w : Wrapper S tables.length) {funs : Funs S}
    {flags : Flags S} {bounds : Nat → Bounds S} {fits : Nat → Fits S}
    {pool : Bytes.LiteralPool} (hCalls : Calls m funs flags bounds fits pool) {entry : Nat}
    (hEntry : m.funcs[entry]? = some (wrapperFunction
      (w.tables.map fun k => tableAddr tables k.val) w.params w.result w.depth
      w.callee.callIndex entry)) :
    @ImplementsStatic _ _ (Env.represent w.params (w.modes.drop w.tables.length))
      (Ty.represent w.result) pool (w.aborts || w.depth) m entry
      (fun env => funs.get w.callee (Env.withTables tables w.tables env))
      (w.tables.map fun k => (tableAddr tables k.val, tables[k]))
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  intro host store heap words value at_ _ input tableRep rep sep cap
  exact ((wrapper_runs hm w hCalls hEntry host at_ input tableRep rep sep cap).of_imp
    (fun h => by
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
      rcases h with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inr h
      · simpa only [Bool.or_eq_true] using h)).mono
    fun _ _ ⟨heap', at_', owned, caps, regions, _⟩ =>
      ⟨heap', at_', owned, caps, regions, trivial⟩

theorem wrapper_trapFreeStatic {m : Module} (hm : Runtime m) {S : List Sig}
    {tables : List (Array UInt64)} (w : Wrapper S tables.length) {funs : Funs S}
    {flags : Flags S} {bounds : Nat → Bounds S} {fits : Nat → Fits S}
    {pool : Bytes.LiteralPool} (hCalls : Calls m funs flags bounds fits pool) {entry : Nat}
    (hEntry : m.funcs[entry]? = some (wrapperFunction
      (w.tables.map fun k => tableAddr tables k.val) w.params w.result w.depth
      w.callee.callIndex entry)) :
    @ImplementsStatic _ _ (Env.represent w.params (w.modes.drop w.tables.length))
      (Ty.represent w.result) pool false m entry
      (fun env => funs.get w.callee (Env.withTables tables w.tables env))
      (w.tables.map fun k => (tableAddr tables k.val, tables[k]))
      (fun value heap store =>
        (w.depth && !(fits (framesAt 0)).get w.callee (Env.withTables tables w.tables value)) =
          false ∧ heap.Within store m (Wrapper.bound tables w flags (bounds (framesAt 0)) value))
      (fun value heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + Wrapper.bound tables w flags (bounds (framesAt 0)) value) := by
  intro host store heap words value at_ pre input tableRep rep sep cap
  have run := wrapper_runs hm w hCalls hEntry host at_ input tableRep rep sep cap
  simp only [pre.1, pre.2, decide_true, Bool.not_true, Bool.and_false, Bool.or_self] at run
  exact run.mono fun _ _ ⟨heap', at_', owned, caps, regions, top⟩ =>
    ⟨heap', at_', owned, caps, regions, top trivial⟩

theorem ImplementsStatic.transfer {α β γ δ : Type} {_ : Represent α} [Represent β]
    {_ : Represent γ} [Represent δ] {pool : Bytes.LiteralPool} {aborts : Bool} {m : Module}
    {entry : Nat} {f : α → γ} {tables : List (UInt64 × Array UInt64)}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsStatic pool aborts m entry f tables Pre Post) (g : β → α) (F : β → δ)
    (hArgs : ∀ heap store words value, Represent.borrowed heap store words value →
      Represent.borrowed heap store words (g value))
    (hSep : ∀ heap store words value, Represent.borrowed heap store words value →
      Separate store (Represent.moves store words value) (Represent.reads store words value) →
      Separate store (Represent.moves store words (g value)) (Represent.reads store words (g value)))
    (hMoves : ∀ heap store words value, Represent.borrowed heap store words value →
      Represent.moves store words (g value) = Represent.moves store words value)
    (hResult : ∀ heap store words value, Represent.owned heap store words (f (g value)) →
      Represent.owned heap store words (F value))
    (hBlocks : ∀ store words value,
      Represent.blocks store words (F value) = Represent.blocks store words (f (g value))) :
    ImplementsStatic pool aborts m entry F tables (fun value => Pre (g value))
      (fun value => Post (g value)) := by
  intro host store heap words value at_ pre input tableRep rep sep cap
  have moves := hMoves heap store words value rep
  have input' : pool.Input heap store words (g value) :=
    ⟨input.1, fun region hr => by rw [moves]; exact input.2 region hr⟩
  have tables' : ∀ table ∈ tables, heap.Borrowed store table.1 table.2 ∧
      Apart store (Represent.moves store words (g value))
        (table.1.toNat, 8 * (table.2.size + 1)) := by
    simpa only [moves] using tableRep
  exact (h host store heap words (g value) at_ pre input' tables'
      (hArgs _ _ _ _ rep) (hSep _ _ _ _ rep sep) cap).mono
    fun final values ⟨heap', at_', owned, caps, regions, post⟩ =>
      ⟨heap', at_', hResult _ _ _ _ owned, caps, fun region hr positive apart => by
        obtain ⟨bytes, valid, outside⟩ := regions region hr positive (by rw [moves]; exact apart)
        exact ⟨bytes, valid, by simpa only [Represent.outside, hBlocks] using outside⟩, post⟩

theorem ImplementsStatic.transferAgree {α β γ δ : Type} {ia : Represent α} {ib : Represent β}
    {ic : Represent γ} {id : Represent δ} {pool : Bytes.LiteralPool} {aborts : Bool}
    {m : Module} {entry : Nat} {f : α → γ} {tables : List (UInt64 × Array UInt64)}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsStatic pool aborts m entry f tables Pre Post)
    (g : β → α) (r : δ → γ) (F : β → δ) (hF : ∀ value, f (g value) = r (F value))
    (hArgs : Agree ib ia g) (hResult : Agree id ic r) :
    ImplementsStatic pool aborts m entry F tables (fun value => Pre (g value))
      (fun value => Post (g value)) :=
  ImplementsStatic.transfer h g F
    (fun _ _ _ _ rep => (hArgs.borrowed _ _ _ _).mp rep)
    (fun _ _ _ _ _ sep => by rw [← hArgs.moves, ← hArgs.reads]; exact sep)
    (fun _ _ _ _ _ => (hArgs.moves _ _ _).symm)
    (fun _ _ _ value owned => (hResult.owned _ _ _ _).mpr (hF value ▸ owned))
    (fun _ _ value => by rw [hF]; exact hResult.blocks _ _ _)

theorem ImplementsStatic.lean {ps : List Ty} {ms : List Mode} {r : Ty}
    {pool : Bytes.LiteralPool} {aborts : Bool} {m : Module} {entry : Nat}
    {f : Env ps → r.denote} {tables : List (UInt64 × Array UInt64)}
    {Pre : Env ps → Heap → Store Unit → Prop}
    {Post : Env ps → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : @ImplementsStatic _ _ (Env.represent ps ms) (Ty.represent r)
      pool aborts m entry f tables Pre Post) :
    @ImplementsStatic _ _ (argsInst ps ms) r.leanInst pool aborts m entry
      (fun value => f (Env.ofArgs ps ms value)) tables
      (fun value => Pre (Env.ofArgs ps ms value))
      (fun value => Post (Env.ofArgs ps ms value)) :=
  @ImplementsStatic.transfer _ _ _ _ (Env.represent ps ms) (argsInst ps ms)
    (Ty.represent r) r.leanInst pool aborts m entry f tables Pre Post h
    (Env.ofArgs ps ms) (fun value => f (Env.ofArgs ps ms value))
    (fun _ _ _ _ rep => (argsInst_borrowed ps ms).mp rep)
    (fun _ _ _ _ rep sep => by
      have length := ((argsInst_borrowed ps ms).mp rep).length
      rw [argsInst_moves ps ms length, argsInst_reads ps ms length] at sep
      exact sep)
    (fun _ _ _ _ rep =>
      (argsInst_moves ps ms ((argsInst_borrowed ps ms).mp rep).length).symm)
    (fun _ _ _ _ owned => r.leanInst_owned.mpr owned)
    (fun _ _ _ => r.leanInst_blocks)

theorem Prog.correct_entryStaticWith {S : List Sig} (prog : Prog S) (funs : Funs S)
    (meaning : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) {g : Sig} (f : FVar S g)
    (depth : g.depth = true) {j : Nat}
    (entry : prog.depthFuns[j]? = some (f.callIndex, g.params, g.result))
    (pool : Bytes.LiteralPool := prog.literalPool (tablesEnd tables))
    (covered : prog.Covered pool) :
    @ImplementsStatic _ _ (Env.represent g.params g.modes) (Ty.represent g.result)
      pool true (compileWith prog tables wrappers pool) (2 + S.length + j) (funs.get f) []
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  entry_correctStatic (compileWith_runtime prog tables wrappers pool)
    (prog.correctStaticWith funs meaning tables wrappers pool covered f 0) depth rfl
    (compileWith_entries prog tables wrappers entry pool)

theorem Prog.entry_trapFreeStaticWith {S : List Sig} (prog : Prog S) (funs : Funs S)
    (meaning : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) {g : Sig} (f : FVar S g)
    (depth : g.depth = true) {j : Nat}
    (entry : prog.depthFuns[j]? = some (f.callIndex, g.params, g.result))
    (pool : Bytes.LiteralPool := prog.literalPool (tablesEnd tables))
    (covered : prog.Covered pool) :
    @ImplementsStatic _ _ (Env.represent g.params g.modes) (Ty.represent g.result)
      pool false (compileWith prog tables wrappers pool) (2 + S.length + j) (funs.get f) []
      (fun value heap store => (prog.fitsAt funs (framesAt 0)).get f value = true ∧
        heap.Within store (compileWith prog tables wrappers pool)
          (Env.credit (g.paidSel (prog.flags.params f)) value +
            (prog.boundsAt funs (framesAt 0)).get f value))
      (fun value heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat +
        (Env.credit (g.paidSel (prog.flags.params f)) value +
          (prog.boundsAt funs (framesAt 0)).get f value)) :=
  entry_trapFreeStatic (compileWith_runtime prog tables wrappers pool)
    (prog.correctStaticWith funs meaning tables wrappers pool covered f 0) depth rfl
    (compileWith_entries prog tables wrappers entry pool)

theorem Prog.entry_trapFreeStaticWith_unpaid {S : List Sig} (prog : Prog S) (funs : Funs S)
    (meaning : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) {g : Sig} (f : FVar S g)
    (depth : g.depth = true) {j : Nat}
    (entry : prog.depthFuns[j]? = some (f.callIndex, g.params, g.result))
    (unpaid : ((prog.flags.params f).all fun paid => !paid) = true)
    (pool : Bytes.LiteralPool := prog.literalPool (tablesEnd tables))
    (covered : prog.Covered pool) :
    @ImplementsStatic _ _ (Env.represent g.params g.modes) (Ty.represent g.result)
      pool false (compileWith prog tables wrappers pool) (2 + S.length + j) (funs.get f) []
      (fun value heap store => (prog.fitsAt funs (framesAt 0)).get f value = true ∧
        heap.Within store (compileWith prog tables wrappers pool)
          ((prog.boundsAt funs (framesAt 0)).get f value))
      (fun value heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat +
        (prog.boundsAt funs (framesAt 0)).get f value) := by
  have result := prog.entry_trapFreeStaticWith funs meaning tables wrappers f depth entry pool covered
  simpa only [Env.credit_eq_zero (Sig.paidSel_none unpaid), Nat.zero_add] using result

theorem Prog.correct_wrapperStatic {S : List Sig} (prog : Prog S) (funs : Funs S)
    (meaning : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) {j : Nat} {w : Wrapper S tables.length}
    (entry : wrappers[j]? = some w)
    (pool : Bytes.LiteralPool := prog.literalPool (tablesEnd tables))
    (covered : prog.Covered pool) :
    @ImplementsStatic _ _ (Env.represent w.params (w.modes.drop w.tables.length))
      (Ty.represent w.result) pool (w.aborts || w.depth) (compileWith prog tables wrappers pool)
      (2 + S.length + prog.depthFuns.length + j)
      (fun env => funs.get w.callee (Env.withTables tables w.tables env))
      (w.tables.map fun k => (tableAddr tables k.val, tables[k]))
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  wrapper_correctStatic (compileWith_runtime prog tables wrappers pool) w
    (prog.correctStaticWith funs meaning tables wrappers pool covered)
    (compileWith_wrappers prog tables wrappers entry pool)

theorem Prog.wrapper_trapFreeStatic {S : List Sig} (prog : Prog S) (funs : Funs S)
    (meaning : prog.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper S tables.length)) {j : Nat} {w : Wrapper S tables.length}
    (entry : wrappers[j]? = some w)
    (pool : Bytes.LiteralPool := prog.literalPool (tablesEnd tables))
    (covered : prog.Covered pool) :
    @ImplementsStatic _ _ (Env.represent w.params (w.modes.drop w.tables.length))
      (Ty.represent w.result) pool false (compileWith prog tables wrappers pool)
      (2 + S.length + prog.depthFuns.length + j)
      (fun env => funs.get w.callee (Env.withTables tables w.tables env))
      (w.tables.map fun k => (tableAddr tables k.val, tables[k]))
      (fun value heap store =>
        (w.depth && !(prog.fitsAt funs (framesAt 0)).get w.callee
          (Env.withTables tables w.tables value)) = false ∧
        heap.Within store (compileWith prog tables wrappers pool)
          (Wrapper.bound tables w prog.flags (prog.boundsAt funs (framesAt 0)) value))
      (fun value heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat +
        Wrapper.bound tables w prog.flags (prog.boundsAt funs (framesAt 0)) value) :=
  Verified.wrapper_trapFreeStatic (compileWith_runtime prog tables wrappers pool) w
    (prog.correctStaticWith funs meaning tables wrappers pool covered)
    (compileWith_wrappers prog tables wrappers entry pool)

end Verified
