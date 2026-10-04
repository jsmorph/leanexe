import Project.WGSL.Translate

import LeanExe.Build

/-!
The kernel of a build whose count is an array's length: the IR `seq (arraySize s src) (build dst
limit index (get s) element)` with an empty per-element body.  Each IR parameter has its own
buffer, numbered by its parameter index: an array parameter's holds its Wasm array, and a scalar
parameter's holds its two words, a `u64`'s halves or a binary32 value's bits and 0.  The output
buffer comes after them.  Invocation `g` binds the index pair `vec2(gid.x, 0)` to variable 0 and
parameter `j`'s value, or an array parameter's length pair, to variable `1 + j`, returns when the
index is not below the count, runs the element's translation, and stores the element's halves.
-/

namespace Project.WGSL

inductive Kind where
  | word
  | float
  | array
  deriving DecidableEq, Repr

/-- An argument of a kernel. -/
inductive Arg where
  | word (value : UInt64)
  | float (bits : UInt32)
  | array (xs : Array UInt64)

def Arg.kind : Arg → Kind
  | .word _ => .word
  | .float _ => .float
  | .array _ => .array

/-- The buffer that holds an argument. -/
def Arg.buffer : Arg → Array UInt32
  | .word v => #[v.toUInt32, (v >>> 32).toUInt32]
  | .float bits => #[bits, 0]
  | .array xs => arrayWords xs

/-- The WGSL value of an argument's variable: a word's pair, a binary32 value, or an array's
length pair. -/
def Arg.value : Arg → Value
  | .word v => pairOf v
  | .float bits => .f32 bits
  | .array xs => .vec2 (UInt32.ofNat xs.size) 0

structure Spec where
  kinds : List Kind
  index : Nat
  sizeLocal : Nat
  sizeSource : Nat
  element : Project.IR.Expr .u64

/-- The statement that binds parameter `j`'s variable from its buffer. -/
def paramStmt (j : Nat) : Kind → Stmt
  | .float => .let_ (1 + j) .f32 (.toF32 (.index j (.lit 0)))
  | _ => .let_ (1 + j) .vec2u (.vec2 (.index j (.lit 0)) (.index j (.lit 1)))

def Spec.layout (K : Spec) : Layout where
  scalar j :=
    if h : j < K.kinds.length then (if K.kinds[j] = .array then none else some (1 + j))
    else if j = K.index then some 0
    else if j = K.sizeLocal then some (1 + K.sizeSource)
    else none
  array a := if h : a < K.kinds.length then (if K.kinds[a] = .array then some (a, 1 + a) else none)
    else none

/-- The prologue: the index pair, then each parameter's variable. -/
def Spec.prologue (K : Spec) : List Stmt :=
  .let_ 0 .vec2u (.vec2 .gidX (.lit 0)) :: (K.kinds.zipIdx.map fun (k, j) => paramStmt j k)

/-- The kernel, or `none` when the element is outside the translated subset. -/
def Spec.module (K : Spec) : Option Module := do
  let p := K.kinds.length
  let (stmts, res, _) ← trExpr K.layout K.element (1 + p)
  pure { inputs := p, workgroupSize := 64
         body := K.prologue ++ [.ite (.not (lt64 0 (1 + K.sizeSource))) [.ret] []] ++ stmts ++
           [.store p (.bin .add (.lit 2) (.bin .mul (.lit 2) (.fst 0))) (.fst res),
            .store p (.bin .add (.lit 3) (.bin .mul (.lit 2) (.fst 0))) (.snd res)] }

/-- The IR locals and arrays that the element's denotation reads at index `k` with count `n`. -/
def Spec.locals (K : Spec) (args : List Arg) (k n : Nat) (j : Nat) : Option Wasm.Value :=
  if j = K.index then some (.i64 (UInt64.ofNat k))
  else if j = K.sizeLocal then some (.i64 (UInt64.ofNat n))
  else match args[j]? with
    | some (.word v) => some (.i64 v)
    | some (.float bits) => some (.f32 bits)
    | _ => none

def Spec.arrays (args : List Arg) (a : Nat) : Option (Array UInt64) :=
  match args[a]? with
  | some (.array xs) => some xs
  | _ => none

theorem pairOf_ofNat (k : Nat) (hk : k < 2 ^ 32) : pairOf (UInt64.ofNat k) = .vec2 (UInt32.ofNat k) 0 := by
  simp only [pairOf, Value.vec2.injEq]
  constructor
  · apply UInt32.toNat_inj.mp
    simp only [UInt64.toNat_toUInt32, UInt32.toNat_ofNat', UInt64.toNat_ofNat']
    omega
  · apply UInt32.toNat_inj.mp
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    omega

theorem Env.find_cons_ne (env : Env) (x m : Nat) (v : Value) (mu : Bool) (h : x ≠ m) :
    Env.find ((x, v, mu) :: env) m = Env.find env m := by
  simp [Env.find, List.find?_cons, h]

/-- The value a parameter's statement binds. -/
theorem paramStmt_eval (ctx : Context) (env : Env) (j : Nat) (a : Arg)
    (hbuf : ctx.inputs[j]? = some a.buffer) (hsize : ∀ xs, a = .array xs → xs.size < 2 ^ 29) :
    ∃ e ty, paramStmt j a.kind = .let_ (1 + j) ty e ∧ e.eval ctx env = some a.value ∧
      ty.holds a.value = true := by
  cases a with
  | word v =>
      refine ⟨_, _, rfl, ?_, by simp [Arg.value, pairOf, Ty.holds]⟩
      simp [Expr.eval, hbuf, Arg.buffer, Arg.value, pairOf]
  | float bits =>
      refine ⟨_, _, rfl, ?_, by simp [Arg.value, Ty.holds]⟩
      simp [Expr.eval, hbuf, Arg.buffer, Arg.value]
  | array xs =>
      have hs := hsize xs rfl
      obtain ⟨h0, h1, -, -⟩ : (arrayWords xs)[0]? = some (UInt32.ofNat xs.size) ∧
          (arrayWords xs)[1]? = some 0 ∧ True ∧ True := by
        refine ⟨?_, ?_, trivial, trivial⟩
        · rw [arrayWords_get _ 0 (by omega)]; simp [wordHalf]
        · rw [arrayWords_get _ 1 (by omega)]
          simp only [wordHalf]
          simp
          apply UInt32.toNat_inj.mp
          simp [UInt64.toNat_shiftRight]
          omega
      refine ⟨_, _, rfl, ?_, by simp [Arg.value, Ty.holds]⟩
      simp [Expr.eval, hbuf, Arg.buffer, Arg.value, h0, h1]

/-- The parameters' statements bind each parameter's variable. -/
theorem params_run (ctx : Context) (writes : List (Nat × UInt32)) :
    ∀ (rest : List Arg) (n : Nat) (env : Env),
    (∀ i a, rest[i]? = some a → ctx.inputs[n + i]? = some a.buffer) →
    (∀ xs, Arg.array xs ∈ rest → xs.size < 2 ^ 29) →
    (∀ m, n + 1 ≤ m → Env.find env m = none) →
    Stmt.execList ctx ⟨env, writes, false⟩ ((rest.zipIdx n).map fun (a, j) => paramStmt j a.kind) =
      some ⟨((rest.zipIdx n).map fun (a, j) => (1 + j, a.value, false)).reverse ++ env, writes, false⟩ := by
  intro rest
  induction rest with
  | nil => intro n env _ _ _; simp [Stmt.execList]
  | cons a rest ih =>
      intro n env hbuf hsize hfresh
      obtain ⟨e, ty, hstmt, hev, hty⟩ := paramStmt_eval ctx env n a (by simpa using hbuf 0 a rfl)
        (fun xs h => hsize xs (by simp [h]))
      simp only [List.zipIdx_cons, List.map_cons, Stmt.execList, Bool.false_eq_true, ite_false]
      rw [hstmt]
      have hfree : Env.find env (1 + n) = none := hfresh (1 + n) (by omega)
      simp only [Stmt.exec, hev, Option.bind_eq_bind, Option.bind_some, hty, hfree, Option.isNone_none,
        Bool.and_self, ite_true]
      rw [ih (n + 1) ((1 + n, a.value, false) :: env)
        (fun i b hb => by have := hbuf (i + 1) b (by simpa using hb); rwa [show n + (i + 1) = n + 1 + i by omega] at this)
        (fun xs h => hsize xs (by simp [h]))
        (fun m hm => by
          rw [Env.find_cons_ne env (1 + n) m a.value false (by omega)]
          exact hfresh m (by omega))]
      simp [List.reverse_cons]

/-- The bindings the parameters' statements add. -/
def paramBindings (args : List Arg) (n : Nat) : Env :=
  ((args.zipIdx n).map fun (a, j) => (1 + j, a.value, false)).reverse

theorem paramBindings_names (args : List Arg) (n : Nat) :
    ∀ b ∈ paramBindings args n, n + 1 ≤ b.1 ∧ b.1 < n + 1 + args.length := by
  intro b hb
  simp only [paramBindings, List.mem_reverse, List.mem_map] at hb
  obtain ⟨⟨a, j⟩, hj, rfl⟩ := hb
  have := List.mem_zipIdx hj
  simp only at this ⊢
  omega

theorem find_paramBindings (args : List Arg) :
    ∀ (env : Env) (n j : Nat) (a : Arg), args[j]? = some a →
      Env.find (paramBindings args n ++ env) (1 + (n + j)) = some (a.value, false) := by
  induction args with
  | nil => intro env n j a h; simp at h
  | cons x rest ih =>
      intro env n j a h
      simp only [paramBindings, List.zipIdx_cons, List.map_cons, List.reverse_cons,
        List.append_assoc, List.cons_append, List.nil_append]
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          rw [Env.find_append_fresh _ _ _ (fun b hb => by
            have := paramBindings_names rest (n + 1) b hb; omega)]
          simp [Env.find]
      | succ j =>
          simp only [List.getElem?_cons_succ] at h
          have := ih ((1 + n, x.value, false) :: env) (n + 1) j a h
          rw [show 1 + (n + (j + 1)) = 1 + (n + 1 + j) by omega]
          simpa [paramBindings, List.append_assoc] using this

theorem zipIdx_map_kind (args : List Arg) (n : Nat) :
    ((args.map Arg.kind).zipIdx n).map (fun (k, j) => paramStmt j k) =
      (args.zipIdx n).map fun (a, j) => paramStmt j a.kind := by
  induction args generalizing n with
  | nil => rfl
  | cons a rest ih => simp [List.zipIdx_cons, ih]

/-- The conditions a kernel's arguments meet. -/
structure Spec.Fits (K : Spec) (args : List Arg) (xs : Array UInt64) : Prop where
  kinds : args.map Arg.kind = K.kinds
  sizes : ∀ ys, Arg.array ys ∈ args → ys.size < 2 ^ 29
  source : args[K.sizeSource]? = some (.array xs)
  index : K.kinds.length ≤ K.index
  sizeLocal : K.kinds.length ≤ K.sizeLocal
  distinct : K.index ≠ K.sizeLocal

theorem Spec.agrees (K : Spec) (args : List Arg) (xs : Array UInt64) (h : K.Fits args xs)
    (ctx : Context) (hin : ctx.inputs = args.map Arg.buffer) (g : Nat) (hg : g < 2 ^ 32)
    (hgid : ctx.gid = UInt32.ofNat g) :
    K.layout.Agrees (K.locals args g xs.size) (Spec.arrays args) ctx
      (paramBindings args 0 ++ [(0, .vec2 (UInt32.ofNat g) 0, false)]) := by
  have hlen : args.length = K.kinds.length := by rw [← h.kinds, List.length_map]
  have hsrcLt : K.sizeSource < args.length := by
    have := h.source; rw [List.getElem?_eq_some_iff] at this; exact this.1
  have hxs := h.sizes xs (List.mem_of_getElem? h.source)
  have hfind0 : Env.find (paramBindings args 0 ++ [(0, .vec2 (UInt32.ofNat g) 0, false)]) 0 =
      some (.vec2 (UInt32.ofNat g) 0, false) := by
    rw [Env.find_append_fresh _ _ 0 (fun b hb => by have := paramBindings_names args 0 b hb; omega)]
    simp [Env.find]
  have hfindj : ∀ j a, args[j]? = some a →
      Env.find (paramBindings args 0 ++ [(0, .vec2 (UInt32.ofNat g) 0, false)]) (1 + j) =
        some (a.value, false) := fun j a hj => by
    simpa using find_paramBindings args _ 0 j a hj
  have hkind : ∀ j (hj : j < K.kinds.length), K.kinds[j] = (args[j]'(by omega)).kind := by
    intro j hj
    have := congrArg (fun l => l[j]?) h.kinds
    simp only [List.getElem?_map] at this
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hj] at this
    simpa using this.symm
  refine ⟨fun j v hj => ?_, fun j b hj => ?_, fun a ys ha => ?_⟩
  · simp only [Spec.locals] at hj
    by_cases hji : j = K.index
    · subst hji
      simp only [ite_true, Option.some.injEq, Wasm.Value.i64.injEq] at hj
      subst hj
      refine ⟨0, by simp [Spec.layout, show ¬ K.index < K.kinds.length by have := h.index; omega],
        by rw [hfind0, pairOf_ofNat g hg]⟩
    · by_cases hjs : j = K.sizeLocal
      · subst hjs
        simp only [hji, ite_false, ite_true, Option.some.injEq, Wasm.Value.i64.injEq] at hj
        subst hj
        refine ⟨1 + K.sizeSource, by
          simp [Spec.layout, show ¬ K.sizeLocal < K.kinds.length by have := h.sizeLocal; omega,
            Ne.symm h.distinct], ?_⟩
        rw [hfindj _ _ h.source, pairOf_ofNat xs.size (by omega)]
        rfl
      · simp only [hji, hjs, ite_false] at hj
        split at hj
        · rename_i v' hv
          simp only [Option.some.injEq, Wasm.Value.i64.injEq] at hj
          subst hj
          have hjl : j < K.kinds.length := by
            obtain ⟨hj', _⟩ := List.getElem?_eq_some_iff.mp hv; omega
          refine ⟨1 + j, ?_, by rw [hfindj _ _ hv]; rfl⟩
          have : K.kinds[j] = .word := by
            rw [hkind j hjl]; rw [List.getElem?_eq_some_iff] at hv; obtain ⟨_, hv⟩ := hv; simp [hv, Arg.kind]
          simp [Spec.layout, hjl, this]
        · simp at hj
        · simp at hj
  · simp only [Spec.locals] at hj
    by_cases hji : j = K.index
    · rw [if_pos hji] at hj; cases hj
    · by_cases hjs : j = K.sizeLocal
      · rw [if_neg hji, if_pos hjs] at hj; cases hj
      · simp only [hji, hjs, ite_false] at hj
        split at hj
        · simp at hj
        · rename_i bits hv
          simp only [Option.some.injEq, Wasm.Value.f32.injEq] at hj
          subst hj
          have hjl : j < K.kinds.length := by
            obtain ⟨hj', _⟩ := List.getElem?_eq_some_iff.mp hv; omega
          refine ⟨1 + j, ?_, by rw [hfindj _ _ hv]; rfl⟩
          have : K.kinds[j] = .float := by
            rw [hkind j hjl]; rw [List.getElem?_eq_some_iff] at hv; obtain ⟨_, hv⟩ := hv; simp [hv, Arg.kind]
          simp [Spec.layout, hjl, this]
        · simp at hj
  · simp only [Spec.arrays] at ha
    split at ha
    · rename_i ys' hv
      simp only [Option.some.injEq] at ha
      subst ha
      have hal : a < K.kinds.length := by
        obtain ⟨ha', _⟩ := List.getElem?_eq_some_iff.mp hv; omega
      refine ⟨h.sizes _ (List.mem_of_getElem? hv), a, 1 + a, ?_, ?_, by rw [hfindj _ _ hv]; rfl⟩
      · have : K.kinds[a] = .array := by
          rw [hkind a hal]; rw [List.getElem?_eq_some_iff] at hv; obtain ⟨_, hv⟩ := hv; simp [hv, Arg.kind]
        simp [Spec.layout, hal, this]
      · rw [hin, List.getElem?_map, hv]; rfl
    · simp at ha

theorem execList_returned (ctx : Context) (run : Run) (h : run.returned = true) (l : List Stmt) :
    Stmt.execList ctx run l = some run := by
  cases l <;> simp [Stmt.execList, h]

/-- What invocation `g` of a build kernel stores: element `g`'s halves when `g` is below the
count, and nothing otherwise. -/
theorem Spec.invoke_eq (K : Spec) (m : Module) (hm : K.module = some m) (args : List Arg)
    (xs : Array UInt64) (h : K.Fits args xs) (f : UInt64 → UInt64)
    (hElem : ∀ k, k < xs.size → K.element.denote (K.locals args k xs.size) (Spec.arrays args) =
      some (f (UInt64.ofNat k)))
    (outputSize : Nat) (hOut : outputSize = 2 + 2 * xs.size) (g : Nat) (hg : g < 2 ^ 32) :
    m.invoke (args.map Arg.buffer) outputSize (UInt32.ofNat g) =
      some (if g < xs.size then [(2 + 2 * g, (f (UInt64.ofNat g)).toUInt32),
        (3 + 2 * g, (f (UInt64.ofNat g) >>> 32).toUInt32)] else []) := by
  simp only [Spec.module, Option.bind_eq_bind] at hm
  cases htr : trExpr K.layout K.element (1 + K.kinds.length) with
  | none => simp [htr] at hm
  | some r =>
    obtain ⟨stmts, res, next'⟩ := r
    simp only [htr, Option.bind_some, Option.pure_def, Option.some.injEq] at hm
    subst hm
    have hlen : args.length = K.kinds.length := by rw [← h.kinds, List.length_map]
    have hxs := h.sizes xs (List.mem_of_getElem? h.source)
    unfold Module.invoke
    rw [if_pos (by simp [hlen])]
    set ctx : Context := { gid := UInt32.ofNat g, inputs := args.map Arg.buffer, outputSize }
      with hctx
    set envP := paramBindings args 0 ++ [(0, .vec2 (UInt32.ofNat g) 0, false)] with henvP
    have hpro : Stmt.execList ctx ⟨[], [], false⟩ K.prologue = some ⟨envP, [], false⟩ := by
      simp only [Spec.prologue, Stmt.execList, Bool.false_eq_true, ite_false, Stmt.exec,
        Expr.eval, Option.bind_eq_bind, Option.bind_some, Ty.holds, Env.find, List.find?_nil,
        Option.map_none, Option.isNone_none, Bool.and_self, ite_true]
      rw [← h.kinds, zipIdx_map_kind args 0]
      rw [params_run ctx [] args 0 _
        (fun i a ha => by simp [ctx, List.getElem?_map, ha])
        h.sizes
        (fun m hm => by
          simp only [Env.find, List.find?_cons, List.find?_nil]
          have : ¬ (0 = m) := by omega
          simp [this])]
      rfl
    have hfind0 : Env.find envP 0 = some (pairOf (UInt64.ofNat g), false) := by
      rw [henvP, Env.find_append_fresh _ _ 0 (fun b hb => by
        have := paramBindings_names args 0 b hb; omega), pairOf_ofNat g hg]
      simp [Env.find]
    have hfindSrc : Env.find envP (1 + K.sizeSource) =
        some (pairOf (UInt64.ofNat xs.size), false) := by
      rw [pairOf_ofNat xs.size (by omega)]
      simpa [Arg.value] using find_paramBindings args _ 0 K.sizeSource _ h.source
    have hguard := lt64_word ctx envP 0 (1 + K.sizeSource) _ _ hfind0 hfindSrc
    have hcmp : decide (UInt64.ofNat g < UInt64.ofNat xs.size) = decide (g < xs.size) := by
      simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [List.append_assoc, execList_append, hpro, Option.bind_some]
    by_cases hgn : g < xs.size
    · -- The guard passes; the element runs; the two stores follow.
      have hite : Stmt.execList ctx ⟨envP, [], false⟩
          [.ite (.not (lt64 0 (1 + K.sizeSource))) [.ret] []] = some ⟨envP, [], false⟩ := by
        simp [Stmt.execList, Stmt.exec, Expr.eval, hguard, hcmp, hgn]
      rw [hite, Option.bind_some]
      have hAgree := K.agrees args xs h ctx rfl g hg rfl
      have hfresh : ∀ n, 1 + K.kinds.length ≤ n → Env.find envP n = none := fun n hn => by
        rw [henvP, Env.find_append_fresh _ _ n (fun b hb => by
          have := paramBindings_names args 0 b hb; rw [← hlen] at hn; omega)]
        simp only [Env.find, List.find?_cons, List.find?_nil]
        have : ¬ (0 = n) := by omega
        simp [this]
      obtain ⟨added, hrun, hb, hle, hlt, hres⟩ := trExpr_sim K.layout (K.locals args g xs.size)
        (Spec.arrays args) ctx [] K.element (1 + K.kinds.length) stmts res next' htr
        (f (UInt64.ofNat g)) (hElem g hgn) envP hAgree hfresh
      rw [hrun, Option.bind_some]
      have h0' : Env.find (added ++ envP) 0 = some (pairOf (UInt64.ofNat g), false) := by
        rw [Env.find_append_fresh _ _ 0 (fun b hb' => by have := hb b hb'; omega)]
        exact hfind0
      have hG : (UInt64.ofNat g).toUInt32 = UInt32.ofNat g := by
        apply UInt32.toNat_inj.mp; simp only [UInt64.toNat_toUInt32, UInt32.toNat_ofNat',
          UInt64.toNat_ofNat']; omega
      have hpos2 : (2 + 2 * UInt32.ofNat g).toNat = 2 + 2 * g := by
        rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat']
        simp only [UInt32.reduceToNat]; omega
      have hpos3 : (3 + 2 * UInt32.ofNat g).toNat = 3 + 2 * g := by
        rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat']
        simp only [UInt32.reduceToNat]; omega
      simp only [wgslValue] at hres
      simp only [pairOf] at h0' hres
      rw [hG] at h0'
      simp [Stmt.execList, Stmt.exec, Expr.eval, h0', hres, BinOp.apply, ctx, hlen, hpos2,
        hpos3, hOut, hgn]
      omega
    · have hite : Stmt.execList ctx ⟨envP, [], false⟩
          [.ite (.not (lt64 0 (1 + K.sizeSource))) [.ret] []] = some ⟨envP, [], true⟩ := by
        simp [Stmt.execList, Stmt.exec, Expr.eval, hguard, hcmp, hgn]
      rw [hite, Option.bind_some, execList_returned _ _ rfl, Option.bind_some,
        execList_returned _ _ rfl]
      simp [hgn]

/-- The stores of invocation `g` of a build kernel with count `n` and element words `word`. -/
def buildWrites (n : Nat) (word : Nat → UInt64) (g : Nat) : List (Nat × UInt32) :=
  if g < n then [(2 + 2 * g, (word g).toUInt32), (3 + 2 * g, (word g >>> 32).toUInt32)] else []

/-- Word `i` of the output after the invocations below `k`. -/
def buildWord (n : Nat) (word : Nat → UInt64) (output : Array UInt32) (k i : Nat) : Option UInt32 :=
  if 2 ≤ i ∧ (i - 2) / 2 < k ∧ (i - 2) / 2 < n then
    some (if i % 2 = 0 then (word ((i - 2) / 2)).toUInt32 else (word ((i - 2) / 2) >>> 32).toUInt32)
  else output[i]?

theorem build_fold (n : Nat) (word : Nat → UInt64) (output : Array UInt32)
    (hOut : output.size = 2 + 2 * n) :
    ∀ k, ∀ i, ((List.range k).foldl (fun out g => applyWrites out (buildWrites n word g))
      output)[i]? = buildWord n word output k i ∧
      ((List.range k).foldl (fun out g => applyWrites out (buildWrites n word g)) output).size =
        output.size := by
  intro k
  induction k with
  | zero => intro i; simp [buildWord]
  | succ k ih =>
      intro i
      rw [List.range_succ, List.foldl_append]
      have hsize := (ih 0).2
      have hi := (ih i).1
      simp only [List.foldl_cons, List.foldl_nil]
      generalize (List.range k).foldl _ output = out at hi hsize
      by_cases hk : k < n
      · simp only [buildWrites, hk, ite_true, applyWrites, List.foldl_cons, List.foldl_nil]
        refine ⟨?_, by simp [hsize]⟩
        rw [Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds, Array.size_setIfInBounds,
          hsize, hi]
        unfold buildWord
        by_cases h3 : 3 + 2 * k = i
        · subst h3
          have hd : (3 + 2 * k - 2) / 2 = k := by omega
          rw [if_pos rfl, if_pos (by omega),
            if_pos (show 2 ≤ 3 + 2 * k ∧ (3 + 2 * k - 2) / 2 < k + 1 ∧ (3 + 2 * k - 2) / 2 < n by
              omega), hd, if_neg (by omega)]
        · rw [if_neg h3]
          by_cases h2 : 2 + 2 * k = i
          · subst h2
            have hd : (2 + 2 * k - 2) / 2 = k := by omega
            rw [if_pos rfl, if_pos (by omega),
              if_pos (show 2 ≤ 2 + 2 * k ∧ (2 + 2 * k - 2) / 2 < k + 1 ∧ (2 + 2 * k - 2) / 2 < n by
                omega), hd, if_pos (by omega)]
          · rw [if_neg h2]
            by_cases hc : 2 ≤ i ∧ (i - 2) / 2 < k ∧ (i - 2) / 2 < n
            · rw [if_pos hc, if_pos (show 2 ≤ i ∧ (i - 2) / 2 < k + 1 ∧ (i - 2) / 2 < n by omega)]
            · rw [if_neg hc, if_neg (show ¬(2 ≤ i ∧ (i - 2) / 2 < k + 1 ∧ (i - 2) / 2 < n) by omega)]
      · simp only [buildWrites, hk, ite_false, applyWrites, List.foldl_nil]
        refine ⟨?_, hsize⟩
        rw [hi]
        unfold buildWord
        by_cases hc : 2 ≤ i ∧ (i - 2) / 2 < k ∧ (i - 2) / 2 < n
        · rw [if_pos hc, if_pos (show 2 ≤ i ∧ (i - 2) / 2 < k + 1 ∧ (i - 2) / 2 < n by omega)]
        · rw [if_neg hc, if_neg (show ¬(2 ≤ i ∧ (i - 2) / 2 < k + 1 ∧ (i - 2) / 2 < n) by omega)]

/-- A build kernel computes its build: with the arguments' buffers, an output of the result's size
whose length word the host has written, and at least the count of invocations, the dispatch leaves
the output holding `LeanExe.build n f` as a Wasm array, and distinct invocations store to distinct
words. -/
theorem Spec.dispatch_eq (K : Spec) (m : Module) (hm : K.module = some m) (args : List Arg)
    (xs : Array UInt64) (h : K.Fits args xs) (f : UInt64 → UInt64)
    (hElem : ∀ k, k < xs.size → K.element.denote (K.locals args k xs.size) (Spec.arrays args) =
      some (f (UInt64.ofNat k)))
    (output : Array UInt32) (hOut : output.size = 2 + 2 * xs.size)
    (hL0 : output[0]? = some (UInt32.ofNat xs.size)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : xs.size ≤ count) (h32 : count ≤ 2 ^ 32) :
    m.dispatch (args.map Arg.buffer) output count =
        some (arrayWords (LeanExe.build (UInt64.ofNat xs.size) f)) ∧
      m.RaceFree (args.map Arg.buffer) output.size count := by
  have hxs := h.sizes xs (List.mem_of_getElem? h.source)
  have hinv := fun g (hg : g < 2 ^ 32) =>
    K.invoke_eq m hm args xs h f hElem output.size hOut g hg
  have hn64 : (UInt64.ofNat xs.size).toNat = xs.size := by simp; omega
  have hbuild : ∀ k, k < xs.size → (LeanExe.build (UInt64.ofNat xs.size) f)[k]! = f (UInt64.ofNat k) := by
    intro k hk
    rw [getElem!_pos _ k (by simp [LeanExe.build, hn64]; omega)]
    simp [LeanExe.build]
  have hbsize : (LeanExe.build (UInt64.ofNat xs.size) f).size = xs.size := by
    simp [LeanExe.build, hn64]
  refine ⟨?_, ?_⟩
  · unfold Module.dispatch
    rw [foldlM_some _ (fun out g => applyWrites out (buildWrites xs.size (fun g => f (UInt64.ofNat g)) g))
      (List.range count) (fun b g hg => by
        rw [hinv g (by simp at hg; omega)]; rfl)]
    congr 1
    apply Array.ext_getElem?
    intro i
    rw [(build_fold xs.size _ output hOut count i).1]
    unfold buildWord
    by_cases hi : i < 2 + 2 * xs.size
    · rw [arrayWords_get _ _ (by rw [hbsize]; omega)]
      by_cases hi2 : i < 2
      · rw [if_neg (by omega), if_pos hi2]
        simp only [hbsize, wordHalf]
        interval_cases i
        · simp [hL0]
        · simp only [hL1, if_pos (show (1 : Nat) = 1 from rfl)]
          congr 1
          apply UInt32.toNat_inj.mp
          simp [UInt64.toNat_shiftRight]
          omega
      · rw [if_pos (show 2 ≤ i ∧ (i - 2) / 2 < count ∧ (i - 2) / 2 < xs.size by omega),
          if_neg hi2, hbuild _ (by omega)]
        by_cases hev : i % 2 = 0
        · simp [hev, wordHalf]
        · have : i % 2 = 1 := by omega
          simp [hev, this, wordHalf]
    · rw [if_neg (show ¬(2 ≤ i ∧ (i - 2) / 2 < count ∧ (i - 2) / 2 < xs.size) by omega),
        Array.getElem?_eq_none (by omega),
        Array.getElem?_eq_none (by simp [arrayWords_size, hbsize]; omega)]
  · intro g k hg hk hgk wg wk hwg hwk
    rw [hinv g (by omega)] at hwg
    rw [hinv k (by omega)] at hwk
    cases hwg
    cases hwk
    intro p hp q hq
    split at hp <;> split at hq <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
    · rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp <;> omega
    all_goals exact hp.elim <|> exact hq.elim

end Project.WGSL
