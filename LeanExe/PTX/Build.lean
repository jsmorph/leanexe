import LeanExe.PTX.Translate
import LeanExe.PTX.Launch
import LeanExe.Source.Build
import LeanExe.Dialect.Build

/-!
The PTX kernel of a build: thread `g` with `g` below the count stores the element of index `g` to
output word `1 + g`.  Each parameter has its own buffer, numbered by its parameter index: a word
parameter's holds the word, and an array parameter's holds its length followed by its elements.
The output buffer comes after them, and its word 0 holds the count, which the host writes.

The `.b64` registers follow the source locals.  Register `j` holds word local `j`, the index
local, or a variable of the statements.  Array parameter `a` has its length in register `a` and a
pointer to its buffer in register `W + a`, where `W` is the source width, and the size local of a
count `.size l src` reads register `src`.  The output pointer is in register `W + p` for `p`
parameters, and fresh registers start at `W + p + 3`.  The prologue reads `%ctaid.x`, `%ntid.x`,
and `%tid.x` into `.b32` registers 0 to 2 and computes the index, then converts each parameter
address and loads each word parameter and array length.  Predicate 0 holds the test of the index
against the count.

`Spec.ptx_thread` states each thread's run with the input oracle, `Spec.ptx_launch` the launch's
sequential output and race freedom, and `Spec.ptx_executions` the launch under the memory model of
`MemoryModel.lean`.
-/

namespace LeanExe.PTX

/-- The buffer of an argument: a word, or an array's length followed by its elements.  A float
parameter, which `Spec.ptx` rejects, gives its bits. -/
def _root_.LeanExe.Source.Arg.ptxBuffer : Source.Arg → Array UInt64
  | .word v => #[v]
  | .float bits => #[bits.toUInt64]
  | .array xs => #[UInt64.ofNat xs.size] ++ xs

/-- The register that holds the count: a word parameter's register, or an array's length
register. -/
def _root_.LeanExe.Source.Count.ptxReg : Source.Count → Nat
  | .size _ src => src
  | .param j => j

/-- The registers of the source locals and arrays. -/
def _root_.LeanExe.Source.Spec.ptxLayout (K : Source.Spec) : Layout where
  scalar j :=
    if j < K.kinds.length then (if K.kinds[j]? = some .word then some j else none)
    else if j = K.index then some j
    else if K.count.sizeLocal? = some j then some K.count.ptxReg
    else if (K.vars.lookup j).isSome then some j
    else none
  array a := if K.kinds[a]? = some .array then some (K.width + a, a) else none
  assigned j := K.vars.lookup j

/-- `ld.param` and `cvta.to.global.u64` of parameters `0` to `k - 1` into registers from `W`. -/
def paramCode (W k : Nat) : List Stmt :=
  (List.range k).flatMap fun j =>
    [inst (.ldParam (W + j) j), inst (.cvtaGlobal (W + j) (W + j))]

/-- Loads of word 0 of buffers `0` to `k - 1` into registers `0` to `k - 1`. -/
def loadCode (W k : Nat) : List Stmt :=
  (List.range k).map fun j => inst (.ld j (W + j) 0)

/-- The prologue: the index, the parameters' pointers, and the first word of each parameter. -/
def _root_.LeanExe.Source.Spec.ptxPrologue (K : Source.Spec) : List Stmt :=
  [inst (.special 0 .ctaidX), inst (.special 1 .ntidX), inst (.special 2 .tidX),
    inst (.widen K.index 2), inst (.madWide K.index 0 1 K.index)] ++
  paramCode K.width (K.kinds.length + 1) ++ loadCode K.width K.kinds.length

/-- The store of register `res` to output word `1 + index`, with register `d` for the address. -/
def storeCode (index out d res : Nat) : List Stmt :=
  [inst (.shift .shl d index (.imm 3)), inst (.bin64 .add d out (.reg d)), inst (.st d 8 res)]

/-- The kernel, or `none` when a parameter is a float or the statements or the element are outside
the translated subset. -/
def _root_.LeanExe.Source.Spec.ptx (K : Source.Spec) : Option Module :=
  if K.kinds.contains .float then none else do
    let p := K.kinds.length
    let (sb, n1) ← trStmt K.ptxLayout K.body (K.width + p + 3)
    let (se, res, n2) ← trExpr K.ptxLayout K.element n1
    pure { inputs := p, regs32 := n2 + 1, regs64 := n2 + 1, regsF := n2 + 1,
           preds := n2 + 1
           body := K.ptxPrologue ++ [inst (.setp .lt 0 K.index (.reg K.count.ptxReg)),
             .ite 0 (sb ++ se ++ storeCode K.index (K.width + p) n2 res) []] }

/-! ### The layout -/

theorem _root_.LeanExe.Source.Spec.ptxLayout_below (K : Source.Spec) (hK : K.WF) :
    K.ptxLayout.Below (K.width + K.kinds.length + 3) := by
  have hc := hK.count
  refine ⟨fun j r hr => ?_, fun a base len ha => ?_⟩
  · simp only [Source.Spec.ptxLayout] at hr
    split at hr
    · split at hr
      · cases hr; have := hK.kindsW; omega
      · cases hr
    · split at hr
      · cases hr; have := hK.indexW; omega
      · split at hr
        · rename_i hs
          cases hr
          cases hcount : K.count with
          | param j' => rw [hcount] at hs; simp [Source.Count.sizeLocal?] at hs
          | size l src =>
              rw [hcount] at hc
              have := (List.getElem?_eq_some_iff.mp hc.2.2.2).1
              have := hK.kindsW
              simp [Source.Count.ptxReg]
              omega
        · split at hr
          · rename_i hl
            cases hr
            obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hl
            have := (hK.vars _ t (Source.lookup_mem ht)).2.1
            omega
          · cases hr
  · simp only [Source.Spec.ptxLayout] at ha
    split at ha
    · rename_i hk
      cases ha
      have := (List.getElem?_eq_some_iff.mp hk).1
      omega
    · cases ha

theorem _root_.LeanExe.Source.Spec.ptxLayout_scalar {K : Source.Spec} {j r : Nat}
    (h : K.ptxLayout.scalar j = some r) :
    (r = j ∧ (j < K.kinds.length → K.kinds[j]? = some .word)) ∨
      (K.count.sizeLocal? = some j ∧ r = K.count.ptxReg) := by
  simp only [Source.Spec.ptxLayout] at h
  split at h
  · split at h
    · cases h; exact .inl ⟨rfl, fun _ => by assumption⟩
    · cases h
  · rename_i hj
    split at h
    · cases h; exact .inl ⟨rfl, fun h' => absurd h' hj⟩
    · split at h
      · cases h; exact .inr ⟨by assumption, rfl⟩
      · split at h
        · cases h; exact .inl ⟨rfl, fun h' => absurd h' hj⟩
        · cases h

theorem _root_.LeanExe.Source.Spec.ptxLayout_assigned {K : Source.Spec} (hK : K.WF) {j : Nat}
    {t : Source.ScalarType} (ht : K.ptxLayout.assigned j = some t) :
    K.ptxLayout.scalar j = some j ∧ K.kinds.length ≤ j ∧ j < K.width ∧ j ≠ K.index := by
  have hmem := Source.lookup_mem ht
  obtain ⟨h1, h2, h3, h4⟩ := hK.vars j t hmem
  refine ⟨?_, h1, h2, h3⟩
  simp only [Source.Spec.ptxLayout, show ¬j < K.kinds.length by omega, h3, ↓reduceIte]
  split
  · rename_i hs; exact absurd hs h4
  · simp only [Source.Spec.ptxLayout] at ht
    simp [ht]

theorem _root_.LeanExe.Source.Spec.ptxLayout_distinct (K : Source.Spec) (hK : K.WF) :
    K.ptxLayout.Distinct := by
  have hc := hK.count
  have hsrc : ∀ j, K.count.sizeLocal? = some j → K.kinds[K.count.ptxReg]? = some .array := by
    intro j hj
    cases hcount : K.count with
    | param _ => rw [hcount] at hj; simp [Source.Count.sizeLocal?] at hj
    | size l src => rw [hcount] at hc; simpa [Source.Count.ptxReg] using hc.2.2.2
  have hsize : ∀ j, K.count.sizeLocal? = some j → K.kinds.length ≤ j ∧ j ≠ K.index := by
    intro j hj
    cases hcount : K.count with
    | param _ => rw [hcount] at hj; simp [Source.Count.sizeLocal?] at hj
    | size l src =>
        rw [hcount] at hc hj
        simp only [Source.Count.sizeLocal?, Option.some.injEq] at hj
        subst hj
        exact ⟨hc.1, hc.2.2.1⟩
  refine ⟨fun j j' r h1 h2 => ?_, fun j t r a base len ht hr ha => ?_⟩
  · rcases K.ptxLayout_scalar h1 with ⟨rfl, hw⟩ | ⟨hs, rfl⟩ <;>
      rcases K.ptxLayout_scalar h2 with ⟨hj', hw'⟩ | ⟨hs', hr'⟩
    · exact hj'
    · have ha := hsrc j' hs'
      rw [← hr'] at ha
      have hlt := (List.getElem?_eq_some_iff.mp ha).1
      rw [hw hlt] at ha
      cases ha
    · have ha := hsrc j hs
      rw [hj'] at ha
      have hlt := (List.getElem?_eq_some_iff.mp ha).1
      rw [hw' hlt] at ha
      cases ha
    · rw [hs] at hs'
      exact Option.some.inj hs'
  · obtain ⟨hrj', h1, h2, -⟩ := K.ptxLayout_assigned hK ht
    rw [hrj'] at hr
    cases hr
    simp only [Source.Spec.ptxLayout] at ha
    split at ha
    · rename_i hk
      cases ha
      have := (List.getElem?_eq_some_iff.mp hk).1
      omega
    · cases ha

/-! ### The prologue -/

theorem paramCode_succ (W k : Nat) : paramCode W (k + 1) =
    paramCode W k ++ [inst (.ldParam (W + k) k), inst (.cvtaGlobal (W + k) (W + k))] := by
  simp [paramCode, List.range_succ]

theorem loadCode_succ (W k : Nat) : loadCode W (k + 1) = loadCode W k ++ [inst (.ld k (W + k) 0)] :=
  by simp [loadCode, List.range_succ]

theorem params_runs {s : Shape} {o : Oracle} (W : Nat) :
    ∀ k (l : Local), l.returned = false → k ≤ s.sizes.length + 1 →
      Runs s o l (paramCode W k) fun l' =>
        (∀ j, j < k → l'.r64 (W + j) = some (.ptr j 0)) ∧ Same W l l' := by
  intro k
  induction k with
  | zero => intro l hr _; exact Runs.nil hr ⟨fun j hj => absurd hj (by omega), Same.refl _ _⟩
  | succ k ih =>
      intro l hr hk
      rw [paramCode_succ]
      refine Runs.append (ih l hr (by omega)) fun l1 ⟨h1, hs1⟩ hr1 => ?_
      refine Runs.cons (P := (· = l1.set64 (W + k) (.ptr k 0)))
        (Runs.step hr1 (fun evs => by simp [Instr.exec, show k ≤ s.sizes.length by omega])
          (by simpa using hr1) rfl) ?_
      rintro l2 rfl hr2
      refine Runs.step hr2 (l' := (l1.set64 (W + k) (.ptr k 0)).set64 (W + k) (.ptr k 0))
        (fun evs => by simp [Instr.exec]) (by simpa using hr2) ⟨fun j hj => ?_, ?_⟩
      · by_cases hjk : j = k
        · subst hjk
          simp
        · rw [Local.set64_r64_ne _ _ (by omega), Local.set64_r64_ne _ _ (by omega)]
          exact h1 j (by omega)
      · exact hs1.trans ((Same.set64 (by omega) _ _).trans (Same.set64 (by omega) _ _))

theorem loads_runs {s : Shape} {o : Oracle} (W : Nat) (vals : Nat → UInt64) :
    ∀ k (l : Local), l.returned = false →
      (∀ j, j < k → l.r64 (W + j) = some (.ptr j 0) ∧
        ∃ size, s.sizes[j]? = some size ∧ 0 < size ∧ ∀ c, o c j 0 = vals j) →
      Runs s o l (loadCode W k) fun l' =>
        (∀ j, j < k → l'.r64 j = some (.word (vals j))) ∧
          ∀ r, k ≤ r → l'.r64 r = l.r64 r := by
  intro k
  induction k with
  | zero => intro l hr _; exact Runs.nil hr ⟨fun j hj => absurd hj (by omega), fun _ _ => rfl⟩
  | succ k ih =>
      intro l hr hl
      rw [loadCode_succ]
      refine Runs.append (ih l hr fun j hj => hl j (by omega)) fun l1 ⟨h1, hf1⟩ hr1 => ?_
      obtain ⟨hp, size, hsize, hpos, ho⟩ := hl k (by omega)
      refine Runs.load hr1 ((hf1 (W + k) (by omega)).trans hp) hsize
        (by simp [wordAt]; omega) ho ⟨fun j hj => ?_, fun r hr' => ?_⟩
      · by_cases hjk : j = k
        · subst hjk
          simp
        · rw [Local.set64_r64_ne _ _ hjk]
          exact h1 j (by omega)
      · rw [Local.set64_r64_ne _ _ (by omega)]
        exact hf1 r (by omega)

theorem _root_.LeanExe.Source.Spec.ptxPrologue_runs (K : Source.Spec) (hK : K.WF) (s : Shape)
    (o : Oracle) (vals : Nat → UInt64) (hsizes : s.sizes.length = K.kinds.length)
    (hbuf : ∀ j, j < K.kinds.length →
      ∃ size, s.sizes[j]? = some size ∧ 0 < size ∧ ∀ c, o c j 0 = vals j) :
    Runs s o Local.initial K.ptxPrologue fun l =>
      l.r64 K.index = some (.word (s.ctaid.toUInt64 * s.ntid.toUInt64 + s.tid.toUInt64)) ∧
      (∀ j, j ≤ K.kinds.length → l.r64 (K.width + j) = some (.ptr j 0)) ∧
      (∀ j, j < K.kinds.length → l.r64 j = some (.word (vals j))) := by
  have hp := hK.index
  have hiW := hK.indexW
  have hpW := hK.kindsW
  unfold Source.Spec.ptxPrologue
  rw [List.append_assoc]
  let l3 := ((Local.initial.set32 0 s.ctaid).set32 1 s.ntid).set32 2 s.tid
  let l4 := l3.set64 K.index (.word s.tid.toUInt64)
  let l5 := l4.set64 K.index (.word (s.ctaid.toUInt64 * s.ntid.toUInt64 + s.tid.toUInt64))
  have h5 : Runs s o Local.initial [inst (.special 0 .ctaidX), inst (.special 1 .ntidX),
      inst (.special 2 .tidX), inst (.widen K.index 2), inst (.madWide K.index 0 1 K.index)]
      (· = l5) := by
    refine Runs.cons (Runs.step rfl (fun evs => rfl) rfl rfl) fun l' h hr => ?_
    subst h
    refine Runs.cons (Runs.step hr (fun evs => rfl) rfl rfl) fun l' h hr => ?_
    subst h
    refine Runs.cons (Runs.step hr (fun evs => rfl) rfl rfl) fun l' h hr => ?_
    subst h
    refine Runs.cons (Runs.step (l' := l4) hr (fun evs => by
      simp [Instr.exec, l4, l3, Local.set32]) rfl rfl) fun l' h hr => ?_
    subst h
    exact Runs.step (l' := l5) hr (fun evs => by
      simp [Instr.exec, l5, l4, l3, Local.set32, Local.word]) rfl rfl
  refine Runs.append h5 fun l h hr => ?_
  subst h
  refine Runs.append (params_runs K.width (K.kinds.length + 1) l5 hr (by omega))
    fun l6 ⟨h6, hs6⟩ hr6 => ?_
  refine (loads_runs K.width vals K.kinds.length l6 hr6 fun j hj =>
    ⟨h6 j (by omega), hbuf j hj⟩).mono fun l7 ⟨h7, hf7⟩ => ⟨?_, fun j hj => ?_, h7⟩
  · rw [hf7 K.index hp, hs6 K.index hiW]
    simp [l5]
  · rw [hf7 (K.width + j) (by omega)]
    exact h6 j (by omega)

/-! ### Threads -/

theorem _root_.LeanExe.Source.Spec.ptx_agrees (K : Source.Spec) (hK : K.WF)
    (args : List Source.Arg) (n : Nat) (h : K.Fits args n) (k : Nat) (s : Shape)
    (hs : s.sizes = (args.map Source.Arg.ptxBuffer).map (·.size)) (l : Local)
    (hidx : l.r64 K.index = some (.word (UInt64.ofNat k)))
    (hptr : ∀ j, j ≤ K.kinds.length → l.r64 (K.width + j) = some (.ptr j 0))
    (hval : ∀ j, j < K.kinds.length →
      l.r64 j = some (.word (inputOracle (args.map Source.Arg.ptxBuffer) 0 j 0))) :
    K.ptxLayout.Agrees (K.locals args k n) (Source.Spec.arrays args) s
      (inputOracle (args.map Source.Arg.ptxBuffer)) l := by
  have hlen : args.length = K.kinds.length := by rw [← h.kinds]; simp
  have hkind : ∀ (j : Nat) (a : Source.Arg), args[j]? = some a → K.kinds[j]? = some a.kind := by
    intro j a ha
    rw [← h.kinds, List.getElem?_map, ha]
    rfl
  have hfirst : ∀ (j : Nat) (a : Source.Arg), args[j]? = some a →
      inputOracle (args.map Source.Arg.ptxBuffer) 0 j 0 =
        match a with
        | .word v => v
        | .float bits => bits.toUInt64
        | .array xs => UInt64.ofNat xs.size := by
    intro j a ha
    cases a <;> simp [inputOracle, List.getElem?_map, ha, Source.Arg.ptxBuffer]
  refine ⟨fun j v hj => ?_, fun a xs ha => ?_⟩
  · simp only [Source.Spec.locals] at hj
    by_cases hji : j = K.index
    · subst hji
      simp only [↓reduceIte, Option.some.injEq, Wasm.Value.i64.injEq] at hj
      subst hj
      refine ⟨K.index, ?_, hidx⟩
      simp [Source.Spec.ptxLayout, show ¬K.index < K.kinds.length by have := hK.index; omega]
    · simp only [hji, ↓reduceIte] at hj
      by_cases hjs : K.count.sizeLocal? = some j
      · simp only [hjs, ↓reduceIte, Option.some.injEq, Wasm.Value.i64.injEq] at hj
        subst hj
        have hc := hK.count
        have hfc := h.count
        cases hcount : K.count with
        | param _ => rw [hcount] at hjs; simp [Source.Count.sizeLocal?] at hjs
        | size l src =>
            rw [hcount] at hc hfc hjs
            simp only [Source.Count.sizeLocal?, Option.some.injEq] at hjs
            subst hjs
            obtain ⟨xs, hxs, hn⟩ := hfc
            refine ⟨src, ?_, ?_⟩
            · simp [Source.Spec.ptxLayout, show ¬l < K.kinds.length by omega, hc.2.2.1, hcount,
                Source.Count.sizeLocal?, Source.Count.ptxReg]
            · have hsrc : src < K.kinds.length := (List.getElem?_eq_some_iff.mp hc.2.2.2).1
              rw [hval src hsrc, hfirst src _ hxs]
              simp [hn]
      · simp only [hjs, ↓reduceIte] at hj
        cases harg : args[j]? with
        | none => simp [harg] at hj
        | some a =>
            cases a with
            | word w =>
                simp only [harg, Option.some.injEq, Wasm.Value.i64.injEq] at hj
                subst hj
                have hjl : j < K.kinds.length := by
                  rw [← hlen]; exact (List.getElem?_eq_some_iff.mp harg).1
                refine ⟨j, ?_, ?_⟩
                · have hw : K.kinds[j]? = some .word := hkind j _ harg
                  simp only [Source.Spec.ptxLayout, hjl, hw, ↓reduceIte]
                · rw [hval j hjl, hfirst j _ harg]
            | float _ => simp [harg] at hj
            | array _ => simp [harg] at hj
  · simp only [Source.Spec.arrays] at ha
    cases harg : args[a]? with
    | none => simp [harg] at ha
    | some arg =>
        cases arg with
        | array ys =>
            simp only [harg, Option.some.injEq] at ha
            subst ha
            have hal : a < K.kinds.length := by
              rw [← hlen]; exact (List.getElem?_eq_some_iff.mp harg).1
            refine ⟨h.sizes ys (List.mem_of_getElem? harg), K.width + a, a, a, ?_,
              hptr a (by omega),
              ?_, ?_, fun c i hi => ?_⟩
            · simp [Source.Spec.ptxLayout, hkind a _ harg, Source.Arg.kind]
            · rw [hval a hal, hfirst a _ harg]
            · simp [hs, List.getElem?_map, harg, Source.Arg.ptxBuffer]
              omega
            · simp [inputOracle, List.getElem?_map, harg, Source.Arg.ptxBuffer, get_tail, hi]
        | word _ => simp [harg] at ha
        | float _ => simp [harg] at ha

theorem Res.andThen_some (r : Res Local) : r.andThen (fun evs l => (evs, some l)) = r := by
  rcases r with ⟨evs, _ | l⟩ <;> rfl

/-- The test of register `a` against register `c` into predicate `p`, and the conditional on it. -/
theorem test_exec (s : Shape) (o : Oracle) {l : Local} (evs : List Event) {p a c : Nat}
    (body : List Stmt) {x y : UInt64} (hr : l.returned = false)
    (hx : l.r64 a = some (.word x)) (hy : l.r64 c = some (.word y)) :
    Stmt.execList s o l evs [inst (.setp .lt p a (.reg c)), .ite p body []] =
      if x < y then Stmt.execList s o (l.setp p true) evs body
      else (evs, some (l.setp p false)) := by
  by_cases hxy : x < y
  · simp [Stmt.execList, Stmt.exec, Instr.exec, hr, Local.word, hx, hy, Src64.word, Src64.get,
      Cmp.apply, hxy, Res.andThen]
    rcases Stmt.execList s o (l.setp p true) evs body with ⟨_, _ | _⟩ <;> rfl
  · simp [Stmt.execList, Stmt.exec, Instr.exec, hr, Local.word, hx, hy, Src64.word, Src64.get,
      Cmp.apply, hxy, Res.andThen]

/-- The store of the element in register `res` to output word `g + 1`. -/
theorem store_exec (s : Shape) (o : Oracle) {l : Local} (evs : List Event) {index out d res : Nat}
    {g : Nat} {v : UInt64} (hr : l.returned = false)
    (hidx : l.r64 index = some (.word (UInt64.ofNat g)))
    (hout : l.r64 out = some (.ptr s.sizes.length 0)) (hres : l.r64 res = some (.word v))
    (hd : res ≠ d) (hod : out ≠ d) (hg : g < 2 ^ 60) (hk : g + 1 < s.outputSize) :
    Stmt.execList s o l evs (storeCode index out d res) =
      (evs ++ [.write (g + 1) v],
        some ((l.set64 d (.word (Shift.apply .shl (UInt64.ofNat g) 3))).set64 d
          (.ptr s.sizes.length (0 + Shift.apply .shl (UInt64.ofNat g) 3)))) := by
  have h3 : (3 : UInt32).toNat < 64 := by decide
  have hw : (Shift.apply .shl (UInt64.ofNat g) 3).toNat = 8 * g := by
    simp only [Shift.apply, h3, ↓reduceIte, UInt64.toNat_shiftLeft]
    simp [Nat.shiftLeft_eq]
    omega
  have hword : wordAt s.outputSize (Shift.apply .shl (UInt64.ofNat g) 3) 8 = some (g + 1) := by
    have h8 : (8 : UInt64).toNat = 8 := rfl
    simp only [wordAt, hw, h8]
    have : (8 * g + 8) / 8 = g + 1 := by omega
    simp [this]
    omega
  simp [storeCode, Stmt.execList, Stmt.exec, Instr.exec, Res.andThen, hr, Local.word, hidx,
    Src32.get, Src64.get, Local.set64_r64_ne _ _ hod, Local.set64_r64_ne _ _ hd, hout, hres,
    Bin64.apply, hword]

theorem ofNat_lt_ofNat {g n : Nat} (hg : g < 2 ^ 60) (hn : n < 2 ^ 60) :
    UInt64.ofNat g < UInt64.ofNat n ↔ g < n := by
  simp [UInt64.lt_iff_toNat_lt]
  omega

/-- With the input oracle, every thread of a build kernel ends.  Thread `g` with `g < n` stores
the element of index `g` to output word `g + 1`, and the other threads store nothing. -/
theorem _root_.LeanExe.Source.Spec.ptx_thread (K : Source.Spec) (hK : K.WF) {m : Module}
    (hm : K.ptx = some m) (args : List Source.Arg) (n : Nat) (h : K.Fits args n)
    (f : UInt64 → UInt64)
    (hElem : ∀ k, k < n → ∃ L', K.body.denote (Source.Spec.arrays args) (K.locals args k n) =
      some L' ∧ K.element.denote L' (Source.Spec.arrays args) = some (f (UInt64.ofNat k)))
    (block g : Nat) (hb : 0 < block) (hb32 : block < 2 ^ 32) (hq : g / block < 2 ^ 32)
    (hg : g < 2 ^ 60) :
    ∃ evs, m.invoke ((args.map Source.Arg.ptxBuffer).map (·.size)) (n + 1) block
        (inputOracle (args.map Source.Arg.ptxBuffer)) g = (evs, true) ∧
      writesOf evs = if g < n then [(g + 1, f (UInt64.ofNat g))] else [] := by
  have hlen : args.length = K.kinds.length := by rw [← h.kinds]; simp
  have hW := hK.kindsW
  have hp := hK.index
  have hiW := hK.indexW
  have hnb := h.bound
  simp only [Source.Spec.ptx] at hm
  split at hm
  · cases hm
  simp only [Option.bind_eq_bind] at hm
  cases hb' : trStmt K.ptxLayout K.body (K.width + K.kinds.length + 3) with
  | none => simp [hb'] at hm
  | some rb =>
  obtain ⟨sb, n1⟩ := rb
  cases he : trExpr K.ptxLayout K.element n1 with
  | none => simp [hb', he] at hm
  | some re =>
  obtain ⟨se, res, n2⟩ := re
  simp only [hb', he, Option.bind_some, Option.pure_def, Option.some.injEq] at hm
  subst hm
  have hn1 := trStmt_mono _ _ _ _ _ hb'
  have hB := K.ptxLayout_below hK
  have hmono := trExpr_mono _ _ _ _ _ _ he
  have hres : res < n2 := hmono.2 (hB.mono (by omega))
  set inputs := args.map Source.Arg.ptxBuffer with hinputs
  set s := threadShape (inputs.map (·.size)) (n + 1) block g with hs
  set o := inputOracle inputs with ho
  have hsizes : s.sizes.length = K.kinds.length := by simp [hs, threadShape, hinputs, hlen]
  have hbuf : ∀ j, j < K.kinds.length →
      ∃ size, s.sizes[j]? = some size ∧ 0 < size ∧ ∀ c, o c j 0 = o 0 j 0 := by
    intro j hj
    obtain ⟨a, ha⟩ : ∃ a, args[j]? = some a :=
      Option.isSome_iff_exists.mp (by simp [List.getElem?_eq_getElem (hlen ▸ hj)])
    refine ⟨a.ptxBuffer.size, by simp [hs, threadShape, hinputs, ha], ?_, fun _ => rfl⟩
    cases a <;> simp [Source.Arg.ptxBuffer]
  obtain ⟨a1, l1, he1, hw1, hr1, hidx, hptr, hval⟩ :=
    K.ptxPrologue_runs hK s o (fun j => o 0 j 0) hsizes hbuf []
  have hidx' : l1.r64 K.index = some (.word (UInt64.ofNat g)) := by
    rw [hidx]
    simp [hs, threadShape, index_eq hb hb32 hq hg]
  have hA := K.ptx_agrees hK args n h g s (by simp [hs, threadShape, hinputs]) l1 hidx' hptr hval
  have hcount : l1.r64 K.count.ptxReg = some (.word (UInt64.ofNat n)) := by
    have hc := hK.count
    have hfc := h.count
    cases hcount : K.count with
    | param j =>
        rw [hcount] at hc hfc
        have hj : j < K.kinds.length := (List.getElem?_eq_some_iff.mp hc).1
        rw [Source.Count.ptxReg, hval j hj]
        simp [ho, inputOracle, hinputs, List.getElem?_map, hfc, Source.Arg.ptxBuffer]
    | size l src =>
        rw [hcount] at hc hfc
        obtain ⟨xs, hxs, hn⟩ := hfc
        have hj : src < K.kinds.length := (List.getElem?_eq_some_iff.mp hc.2.2.2).1
        rw [Source.Count.ptxReg, hval src hj]
        simp [ho, inputOracle, hinputs, List.getElem?_map, hxs, Source.Arg.ptxBuffer, hn]
  have hcase : ∃ evs' l', Stmt.execList s o l1 a1
      [inst (.setp .lt 0 K.index (.reg K.count.ptxReg)),
        .ite 0 (sb ++ se ++ storeCode K.index (K.width + K.kinds.length) n2 res) []] =
        (a1 ++ evs', some l') ∧
      writesOf evs' = if g < n then [(g + 1, f (UInt64.ofNat g))] else [] := by
    rw [test_exec s o a1 _ hr1 hidx' hcount]
    by_cases hgn : g < n
    · have hlt : UInt64.ofNat g < UInt64.ofNat n := (ofNat_lt_ofNat hg (by omega)).mpr hgn
      simp only [hlt, ↓reduceIte, hgn]
      obtain ⟨L', hbody, helem⟩ := hElem g hgn
      have hA2 : K.ptxLayout.Agrees (K.locals args g n) (Source.Spec.arrays args) s o
          (l1.setp 0 true) := hA.same hB fun _ _ => rfl
      have hr2 : (l1.setp 0 true).returned = false := by simpa using hr1
      have hnot : ∀ r, (K.width + K.kinds.length ≤ r ∨ r = K.index) →
          ∀ j t, K.ptxLayout.assigned j = some t → K.ptxLayout.scalar j ≠ some r := by
        intro r hr j t ht hsj
        obtain ⟨hj, -, hjW, hne⟩ := K.ptxLayout_assigned hK ht
        rw [hj] at hsj
        have := Option.some.inj hsj
        omega
      have hrun : Runs s o (l1.setp 0 true) (sb ++ se) fun l4 =>
          l4.r64 res = some (.word (f (UInt64.ofNat g))) ∧
          l4.r64 K.index = some (.word (UInt64.ofNat g)) ∧
          l4.r64 (K.width + K.kinds.length) = some (.ptr K.kinds.length 0) := by
        refine Runs.append (trStmt_sim K.ptxLayout (K.ptxLayout_distinct hK)
          (Source.Spec.arrays args) s o K.body _ sb n1 hb' hB _ L' hbody _ hA2 hr2)
          fun l3 ⟨hA3, hk3⟩ hr3 => ?_
        refine (trExpr_sim K.ptxLayout L' (Source.Spec.arrays args) s o K.element n1 se res n2 he
          _ helem l3 hA3 (hB.mono (by omega)) hr3).mono fun l4 ⟨h4, hv4⟩ => ⟨hv4, ?_, ?_⟩
        · rw [h4 K.index (by omega), hk3 K.index (by omega) (hnot K.index (.inr rfl))]
          exact hidx'
        · rw [h4 _ (by omega), hk3 _ (by omega) (hnot _ (.inl (le_refl _)))]
          exact hptr _ (le_refl _)
      obtain ⟨a2, l4, he2, hw2, hr4, hv4, hi4, ho4⟩ := hrun a1
      rw [Stmt.execList_append, he2]
      simp only [Res.andThen]
      rw [store_exec s o (a1 ++ a2) hr4 hi4 (by rw [hsizes]; exact ho4) hv4 (by omega)
        (by omega) hg (by simp [hs, threadShape]; omega)]
      exact ⟨a2 ++ [.write (g + 1) (f (UInt64.ofNat g))], _, by rw [List.append_assoc],
        by rw [writesOf_append, hw2]; rfl⟩
    · have hlt : ¬UInt64.ofNat g < UInt64.ofNat n := fun h' =>
        hgn ((ofNat_lt_ofNat hg (by omega)).mp h')
      simp only [hlt, ↓reduceIte, hgn]
      exact ⟨[], l1.setp 0 false, by simp, rfl⟩
  obtain ⟨evs', l', hrun, hwr⟩ := hcase
  have hall : Stmt.execList s o Local.initial [] (K.ptxPrologue ++
      [inst (.setp .lt 0 K.index (.reg K.count.ptxReg)),
        .ite 0 (sb ++ se ++ storeCode K.index (K.width + K.kinds.length) n2 res) []]) =
      (a1 ++ evs', some l') := by
    rw [Stmt.execList_append, he1]
    simpa [Res.andThen] using hrun
  refine ⟨a1 ++ evs', ?_, by simp [hw1, hwr]⟩
  have hinv : (inputs.map (·.size)).length = K.kinds.length := by simp [hinputs, hlen]
  simp only [Module.invoke, hinv, ↓reduceIte]
  rw [← hs, hall]
  rfl

/-! ### Launches -/

/-- A launch of a build kernel on the arguments' buffers, with an output whose word 0 is the count
`n` and whose other words are `ys`. -/
def buildLaunch (m : Module) (args : List Source.Arg) (n : Nat) (ys : Array UInt64)
    (blocks block : Nat) : Launch :=
  ⟨m, args.map Source.Arg.ptxBuffer, #[UInt64.ofNat n] ++ ys, blocks, block⟩

/-- The sequential run of a build kernel leaves the count followed by the build's elements, and
distinct threads store to distinct words. -/
theorem _root_.LeanExe.Source.Spec.ptx_launch (K : Source.Spec) (hK : K.WF) {m : Module}
    (hm : K.ptx = some m) (args : List Source.Arg) (n : Nat) (h : K.Fits args n)
    (f : UInt64 → UInt64)
    (hElem : ∀ k, k < n → ∃ L', K.body.denote (Source.Spec.arrays args) (K.locals args k n) =
      some L' ∧ K.element.denote L' (Source.Spec.arrays args) = some (f (UInt64.ofNat k)))
    (ys : Array UInt64) (hys : ys.size = n) (blocks block : Nat) (hb : 0 < block)
    (hb32 : block < 2 ^ 32) (hbl : blocks < 2 ^ 32) (hcover : n ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    (buildLaunch m args n ys blocks block).seq =
        some (#[UInt64.ofNat n] ++ LeanExe.build (UInt64.ofNat n) f) ∧
      (buildLaunch m args n ys blocks block).RaceFree := by
  set L := buildLaunch m args n ys blocks block with hL
  have hnb := h.bound
  have hsz : (#[UInt64.ofNat n] ++ ys).size = n + 1 := by simp [hys]; omega
  have hn64 : (UInt64.ofNat n).toNat = n := by simp; omega
  have hthreadsL : L.threads = blocks * block := rfl
  have hthread : ∀ g, g < L.threads →
      L.events (inputOracle L.inputs) g = ((L.events (inputOracle L.inputs) g).1, true) ∧
      writesOf (L.events (inputOracle L.inputs) g).1 =
        if g < n then [(g + 1, f (UInt64.ofNat g))] else [] := by
    intro g hg
    rw [hthreadsL] at hg
    obtain ⟨evs, he, hw⟩ := K.ptx_thread hK hm args n h f hElem block g hb hb32
      (by have := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at hg; exact hg); omega) (by omega)
    have he' : L.events (inputOracle L.inputs) g = (evs, true) := by
      simpa [hL, buildLaunch, Launch.events, hsz] using he
    rw [he']
    exact ⟨rfl, hw⟩
  have hwrite : ∀ g, g < L.threads → ∀ w ∈ writesOf (L.events (inputOracle L.inputs) g).1,
      w.1 = g + 1 := by
    intro g hg w hw
    rw [(hthread g hg).2] at hw
    split at hw <;> simp_all
  refine ⟨?_, ?_⟩
  · rw [Launch.seq_some L (fun g => (L.events (inputOracle L.inputs) g).1)
      fun g hg => (hthread g hg).1]
    congr 1
    apply Array.ext_getElem?
    intro i
    by_cases hi : i < n + 1
    · rw [setAll_get (by simpa [hL, buildLaunch, hsz] using hi)]
      cases i with
      | zero =>
          rw [lastVal_flatMap _ 0 L.threads L.threads (fun g hg _ w hw => by
            rw [hwrite g hg w hw]; omega) _ _ (Nat.le_refl _)]
          simp [hL, buildLaunch]
      | succ j =>
          have hj : j < n := by omega
          have hjt : j < L.threads := by omega
          rw [lastVal_flatMap _ (j + 1) j L.threads (fun g hg hne w hw => by
            rw [hwrite g hg w hw]; omega) _ _ (Nat.le_refl _)]
          simp [(hthread j hjt).2, hj, hjt, lastVal, get_tail, LeanExe.build, hn64]
    · rw [Array.getElem?_eq_none (by simpa [hL, buildLaunch, hsz] using hi),
        Array.getElem?_eq_none (by simp [LeanExe.build, hn64]; omega)]
  · intro g k hg hk hgk i v w hv hw
    obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hv
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hw
    have h1 := hwrite g hg _ (mem_writesOf hp)
    have h2 := hwrite k hk _ (mem_writesOf hq)
    simp only at h1 h2
    omega

/-- In every consistent execution of a launch of a build kernel with at least `n` threads, no
access of a thread is in a data race, every thread ends, and the copy back reads the count
followed by the build's elements.  A consistent execution exists. -/
theorem _root_.LeanExe.Source.Spec.ptx_executions (K : Source.Spec) (hK : K.WF) {m : Module}
    (hm : K.ptx = some m) (args : List Source.Arg) (n : Nat) (h : K.Fits args n)
    (f : UInt64 → UInt64)
    (hElem : ∀ k, k < n → ∃ L', K.body.denote (Source.Spec.arrays args) (K.locals args k n) =
      some L' ∧ K.element.denote L' (Source.Spec.arrays args) = some (f (UInt64.ofNat k)))
    (ys : Array UInt64) (hys : ys.size = n) (blocks block : Nat) (hb : 0 < block)
    (hb32 : block < 2 ^ 32) (hbl : blocks < 2 ^ 32) (hcover : n ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    (∃ E, (buildLaunch m args n ys blocks block).Consistent E) ∧
      ∀ E, (buildLaunch m args n ys blocks block).Consistent E →
        (buildLaunch m args n ys blocks block).NoDataRace E ∧
        (∀ g, g < blocks * block →
          ((buildLaunch m args n ys blocks block).events (E.oracle g) g).2 = true) ∧
        ∀ i, i < n + 1 →
          (#[UInt64.ofNat n] ++ LeanExe.build (UInt64.ofNat n) f)[i]? = some (E.observed i) := by
  obtain ⟨hs, hr⟩ := K.ptx_launch hK hm args n h f hElem ys hys blocks block hb hb32 hbl hcover
    hthreads
  refine ⟨Launch.execution_exists _ hs hr, fun E hE => ?_⟩
  obtain ⟨hg, hrace, hout⟩ := Launch.executions _ hs hr E hE
  exact ⟨hrace, fun g hg' => (hg g hg').2,
    fun i hi => hout i (by simp [buildLaunch, hys]; omega)⟩

end LeanExe.PTX

#print axioms LeanExe.Source.Spec.ptx_executions
