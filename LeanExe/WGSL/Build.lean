import LeanExe.WGSL.TranslateStmt

import LeanExe.Dialect.Build

/-!
The kernel of a build: the IR `buildWith dst limit index (get c) body element`, whose count local
`c` is a `u64` parameter or the local of an `arraySize` statement before the build.  Each IR
parameter has its own buffer, numbered by its parameter index: an array parameter's holds its
Wasm array, and a scalar parameter's holds its two words, a `u64`'s halves or a binary32 value's
bits and 0.  The output buffer comes after them.  Invocation `g` binds the index pair
`vec2(gid.x, 0)` to variable 0, parameter `j`'s value or an array parameter's length pair to
variable `1 + j`, and declares a `var` `1 + j` for each local `j` that the body assigns.  It
returns when the index is not below the count, runs the translations of the body and the
element, and stores the element's halves.
-/

namespace LeanExe.WGSL

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

/-- Where a build kernel's count comes from: the length of array parameter `src`, which an
`arraySize` statement puts in local `sizeLocal` before the build, or `u64` parameter `j`. -/
inductive Count where
  | size (sizeLocal src : Nat)
  | param (j : Nat)

/-- The variable that holds the count's pair. -/
def Count.var : Count → Nat
  | .size _ src => 1 + src
  | .param j => 1 + j

def Count.sizeLocal? : Count → Option Nat
  | .size l _ => some l
  | .param _ => none

/-- A build kernel: the parameters' kinds, the build's index local, the count, the locals that
the per-element statements assign with their types, a bound on the IR locals, the per-element
statements, and the element. -/
structure Spec where
  kinds : List Kind
  index : Nat
  count : Count
  vars : List (Nat × LeanExe.IR.ScalarType)
  width : Nat
  body : LeanExe.IR.Stmt
  element : LeanExe.IR.Expr .u64

/-- The statement that binds parameter `j`'s variable from its buffer. -/
def paramStmt (j : Nat) : Kind → Stmt
  | .float => .let_ (1 + j) .f32 (.toF32 (.index j (.lit 0)))
  | _ => .let_ (1 + j) .vec2u (.vec2 (.index j (.lit 0)) (.index j (.lit 1)))

/-- Variable 0 holds the index; variable `1 + j` holds parameter `j`, an array's length, or an
assigned local `j`; the size local reads its array's length variable. -/
def Spec.layout (K : Spec) : Layout where
  scalar j :=
    if h : j < K.kinds.length then (if K.kinds[j] = .array then none else some (1 + j))
    else if j = K.index then some 0
    else if K.count.sizeLocal? = some j then some K.count.var
    else if (K.vars.lookup j).isSome then some (1 + j)
    else none
  array a := if h : a < K.kinds.length then (if K.kinds[a] = .array then some (a, 1 + a) else none)
    else none
  assigned j := K.vars.lookup j

/-- The prologue: the index pair, then each parameter's variable. -/
def Spec.prologue (K : Spec) : List Stmt :=
  .let_ 0 .vec2u (.vec2 .gidX (.lit 0)) :: (K.kinds.zipIdx.map fun (k, j) => paramStmt j k)

/-- The zero of an IR scalar type, as a WGSL expression and value. -/
def zeroExpr : LeanExe.IR.ScalarType → Expr
  | .f32 => .toF32 (.lit 0)
  | .bool => .bool false
  | _ => .vec2 (.lit 0) (.lit 0)

def zeroValue : LeanExe.IR.ScalarType → Value
  | .f32 => .f32 0
  | .bool => .bool false
  | _ => .vec2 0 0

/-- The declarations of the assigned locals' variables. -/
def Spec.decls (K : Spec) : List Stmt :=
  K.vars.map fun (j, type) => .var (1 + j) (wgslTy type) (zeroExpr type)

/-- The kernel, or `none` when the statements or the element are outside the translated subset. -/
def Spec.module (K : Spec) : Option Module := do
  let p := K.kinds.length
  let (sb, n1) ← trStmt K.layout K.body (1 + K.width)
  let (stmts, res, _) ← trExpr K.layout K.element n1
  pure { inputs := p, workgroupSize := 64
         body := K.prologue ++ K.decls ++ [.ite (.not (lt64 0 K.count.var)) [.ret] []] ++ sb ++
           stmts ++
           [.store p (.bin .add (.lit 2) (.bin .mul (.lit 2) (.fst 0))) (.fst res),
            .store p (.bin .add (.lit 3) (.bin .mul (.lit 2) (.fst 0))) (.snd res)] }

/-- The IR locals that the statements' denotation reads at index `k` with count `n`. -/
def Spec.locals (K : Spec) (args : List Arg) (k n : Nat) (j : Nat) : Option Wasm.Value :=
  if j = K.index then some (.i64 (UInt64.ofNat k))
  else if K.count.sizeLocal? = some j then some (.i64 (UInt64.ofNat n))
  else match args[j]? with
    | some (.word v) => some (.i64 v)
    | some (.float bits) => some (.f32 bits)
    | _ => none

def Spec.arrays (args : List Arg) (a : Nat) : Option (Array UInt64) :=
  match args[a]? with
  | some (.array xs) => some xs
  | _ => none

/-- The conditions on a kernel's own indices, checked by evaluation. -/
def Spec.wfb (K : Spec) : Bool :=
  decide (K.kinds.length ≤ K.index) && decide (K.index < K.width) &&
  decide (K.kinds.length ≤ K.width) &&
  (match K.count with
    | .size l src => decide (K.kinds.length ≤ l) && decide (l < K.width) && decide (l ≠ K.index) &&
        decide (K.kinds[src]? = some .array)
    | .param j => decide (K.kinds[j]? = some .word)) &&
  decide (K.vars.map (·.1)).Nodup &&
  K.vars.all fun (j, _) => decide (K.kinds.length ≤ j) && decide (j < K.width) &&
    decide (j ≠ K.index) && decide (K.count.sizeLocal? ≠ some j)

theorem pairOf_ofNat (k : Nat) (hk : k < 2 ^ 32) : pairOf (UInt64.ofNat k) = .vec2 (UInt32.ofNat k) 0 := by
  simp only [pairOf, Value.vec2.injEq]
  constructor
  · apply UInt32.toNat_inj.mp
    simp only [UInt64.toNat_toUInt32, UInt32.toNat_ofNat', UInt64.toNat_ofNat']
    omega
  · apply UInt32.toNat_inj.mp
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    omega

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

/-- The conditions a kernel's arguments meet, with count `n`. -/
structure Spec.Fits (K : Spec) (args : List Arg) (n : Nat) : Prop where
  kinds : args.map Arg.kind = K.kinds
  sizes : ∀ ys, Arg.array ys ∈ args → ys.size < 2 ^ 29
  count : match K.count with
    | .size _ src => ∃ xs, args[src]? = some (.array xs) ∧ xs.size = n
    | .param j => args[j]? = some (.word (UInt64.ofNat n))
  bound : n < 2 ^ 29

/-- The facts that `Spec.wfb` checks. -/
structure Spec.WF (K : Spec) : Prop where
  index : K.kinds.length ≤ K.index
  indexW : K.index < K.width
  kindsW : K.kinds.length ≤ K.width
  count : match K.count with
    | .size l src => K.kinds.length ≤ l ∧ l < K.width ∧ l ≠ K.index ∧ K.kinds[src]? = some .array
    | .param j => K.kinds[j]? = some .word
  nodup : (K.vars.map (·.1)).Nodup
  vars : ∀ j type, (j, type) ∈ K.vars → K.kinds.length ≤ j ∧ j < K.width ∧ j ≠ K.index ∧
    K.count.sizeLocal? ≠ some j

theorem Spec.wf_of_wfb (K : Spec) (h : K.wfb = true) : K.WF := by
  simp only [Spec.wfb, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, ?_, h5, fun j type hj => ?_⟩
  · cases hc : K.count <;> simp_all
  · have h' := h6 (j, type) hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    exact ⟨h'.1.1.1, h'.1.1.2, h'.1.2, h'.2⟩

theorem lookup_mem {vars : List (Nat × LeanExe.IR.ScalarType)} {j : Nat}
    {type : LeanExe.IR.ScalarType} (h : vars.lookup j = some type) : (j, type) ∈ vars := by
  induction vars with
  | nil => simp at h
  | cons x vars ih =>
      obtain ⟨a, t⟩ := x
      by_cases ha : j = a
      · subst ha
        simp only [List.lookup_cons, BEq.rfl, Option.some.injEq] at h
        subst h
        simp
      · simp only [List.lookup_cons, show (j == a) = false by simpa using ha] at h
        exact List.mem_cons_of_mem _ (ih h)

theorem lookup_of_mem {vars : List (Nat × LeanExe.IR.ScalarType)} (hnd : (vars.map (·.1)).Nodup)
    {j : Nat} {type : LeanExe.IR.ScalarType} (h : (j, type) ∈ vars) : vars.lookup j = some type := by
  induction vars with
  | nil => cases h
  | cons x vars ih =>
      obtain ⟨a, t⟩ := x
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      rcases List.mem_cons.mp h with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp
      · have hne : j ≠ a := fun hj => hnd.1 ⟨(j, type), h, by simp [hj]⟩
        simp only [List.lookup_cons, show (j == a) = false by simpa using hne]
        exact ih hnd.2 h

theorem Spec.layout_var (K : Spec) (hK : K.WF) {j : Nat} {type : LeanExe.IR.ScalarType}
    (h : (j, type) ∈ K.vars) : K.layout.scalar j = some (1 + j) := by
  obtain ⟨h1, h2, h3, h4⟩ := hK.vars j type h
  have hl : (K.vars.lookup j).isSome := by simp [lookup_of_mem hK.nodup h]
  simp only [Spec.layout, show ¬ j < K.kinds.length by omega, dite_false, h3, ↓reduceIte, hl]
  split
  · rename_i hc; exact absurd hc h4
  · rfl

theorem Spec.layout_below (K : Spec) (hK : K.WF) : K.layout.Below (1 + K.width) := by
  have hc := hK.count
  refine ⟨fun j w hw => ?_, fun a b len hF => ?_⟩
  · simp only [Spec.layout] at hw
    split at hw
    · split at hw
      · cases hw
      · cases hw; have := hK.kindsW; omega
    · split at hw
      · cases hw; omega
      · split at hw
        · cases hw
          revert hc
          cases K.count with
          | size l src =>
              intro hc
              have := (List.getElem?_eq_some_iff.mp hc.2.2.2).1
              have := hK.kindsW
              simp [Count.var]; omega
          | param j' =>
              intro hc
              have := (List.getElem?_eq_some_iff.mp hc).1
              have := hK.kindsW
              simp [Count.var]; omega
        · split at hw
          · cases hw
            rename_i hl
            obtain ⟨type, ht⟩ := Option.isSome_iff_exists.mp hl
            have := (hK.vars j type (lookup_mem ht)).2.1
            omega
          · cases hw
  · simp only [Spec.layout] at hF
    split at hF
    · split at hF
      · cases hF; have := hK.kindsW; omega
      · cases hF
    · cases hF

theorem Spec.layout_distinct (K : Spec) (hK : K.WF) : K.layout.Distinct := by
  have hc := hK.count
  refine ⟨fun j j' type w hj hw hw' => ?_, fun j type w a b len hj hw hF => ?_⟩
  · have hmem := lookup_mem (show K.vars.lookup j = some type from hj)
    rw [K.layout_var hK hmem] at hw
    obtain rfl := (Option.some.inj hw).symm
    obtain ⟨hp, hwid, hi, hs⟩ := hK.vars j type hmem
    simp only [Spec.layout] at hw'
    split at hw'
    · split at hw'
      · cases hw'
      · rename_i hj' _
        have := Option.some.inj hw'
        omega
    · split at hw'
      · have := Option.some.inj hw'
        omega
      · split at hw'
        · have hcv := Option.some.inj hw'
          revert hc hcv
          cases K.count with
          | size l src =>
              intro hc hcv
              have := (List.getElem?_eq_some_iff.mp hc.2.2.2).1
              simp only [Count.var] at hcv
              omega
          | param j'' =>
              intro hc hcv
              have := (List.getElem?_eq_some_iff.mp hc).1
              simp only [Count.var] at hcv
              omega
        · split at hw'
          · have := Option.some.inj hw'
            omega
          · cases hw'
  · have hmem := lookup_mem (show K.vars.lookup j = some type from hj)
    rw [K.layout_var hK hmem] at hw
    obtain rfl := (Option.some.inj hw).symm
    obtain ⟨hp, -, -, -⟩ := hK.vars j type hmem
    simp only [Spec.layout] at hF
    split at hF
    · split at hF
      · rename_i ha _
        have := congrArg Prod.snd (Option.some.inj hF)
        simp only at this
        omega
      · cases hF
    · cases hF

theorem Spec.agrees (K : Spec) (hK : K.WF) (args : List Arg) (n : Nat) (h : K.Fits args n)
    (ctx : Context) (hin : ctx.inputs = args.map Arg.buffer) (g : Nat) (hg : g < 2 ^ 32) :
    K.layout.Agrees (K.locals args g n) (Spec.arrays args) ctx
      (paramBindings args 0 ++ [(0, .vec2 (UInt32.ofNat g) 0, false)]) := by
  have hlen : args.length = K.kinds.length := by rw [← h.kinds, List.length_map]
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
  have hidx := hK.index
  refine ⟨fun j v hj => ?_, fun j b hj => ?_, fun a ys ha => ?_⟩
  · simp only [Spec.locals] at hj
    by_cases hji : j = K.index
    · subst hji
      simp only [ite_true, Option.some.injEq, Wasm.Value.i64.injEq] at hj
      subst hj
      refine ⟨0, false, by simp [Spec.layout, show ¬ K.index < K.kinds.length by omega],
        by rw [hfind0, pairOf_ofNat g hg]⟩
    · by_cases hjs : K.count.sizeLocal? = some j
      · simp only [hji, ite_false, hjs, ite_true, Option.some.injEq, Wasm.Value.i64.injEq] at hj
        subst hj
        have hc := hK.count
        have hf := h.count
        cases hcount : K.count with
        | param j' => rw [hcount] at hjs; simp [Count.sizeLocal?] at hjs
        | size l src =>
            rw [hcount] at hc hf hjs
            simp only [Count.sizeLocal?, Option.some.injEq] at hjs
            subst hjs
            simp only at hc hf
            obtain ⟨xs, hxs, hn⟩ := hf
            refine ⟨1 + src, false, ?_, ?_⟩
            · simp [Spec.layout, show ¬ l < K.kinds.length by omega, hc.2.2.1, hcount,
                Count.sizeLocal?, Count.var]
            · rw [hfindj _ _ hxs, pairOf_ofNat n (by have := h.bound; omega), ← hn]
              rfl
      · simp only [hji, hjs, ite_false] at hj
        split at hj
        · rename_i v' hv
          simp only [Option.some.injEq, Wasm.Value.i64.injEq] at hj
          subst hj
          have hjl : j < K.kinds.length := by
            obtain ⟨hj', _⟩ := List.getElem?_eq_some_iff.mp hv; omega
          refine ⟨1 + j, false, ?_, by rw [hfindj _ _ hv]; rfl⟩
          have : K.kinds[j] = .word := by
            rw [hkind j hjl]; rw [List.getElem?_eq_some_iff] at hv; obtain ⟨_, hv⟩ := hv; simp [hv, Arg.kind]
          simp [Spec.layout, hjl, this]
        · simp at hj
        · simp at hj
  · simp only [Spec.locals] at hj
    by_cases hji : j = K.index
    · simp only [hji, ite_true] at hj; cases hj
    · by_cases hjs : K.count.sizeLocal? = some j
      · simp only [hji, hjs, ite_false, ite_true] at hj; cases hj
      · simp only [hji, hjs, ite_false] at hj
        split at hj
        · simp at hj
        · rename_i bits hv
          simp only [Option.some.injEq, Wasm.Value.f32.injEq] at hj
          subst hj
          have hjl : j < K.kinds.length := by
            obtain ⟨hj', _⟩ := List.getElem?_eq_some_iff.mp hv; omega
          refine ⟨1 + j, false, ?_, by rw [hfindj _ _ hv]; rfl⟩
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

theorem Env.find_append_left {a b : Env} {w : Nat} {x : Value × Bool} (h : a.find w = some x) :
    (a ++ b).find w = some x := by
  simp only [Env.find, List.find?_append, Option.map_eq_some_iff] at h ⊢
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨y, by simp [hy], rfl⟩

/-- The bindings of the assigned locals' declarations. -/
def declBindings (vars : List (Nat × LeanExe.IR.ScalarType)) : Env :=
  (vars.map fun (j, type) => (1 + j, zeroValue type, true)).reverse

theorem zero_holds (type : LeanExe.IR.ScalarType) : (wgslTy type).holds (zeroValue type) = true := by
  cases type <;> rfl

theorem decls_run (ctx : Context) (writes : List (Nat × UInt32)) :
    ∀ (vars : List (Nat × LeanExe.IR.ScalarType)) (env : Env), (vars.map (·.1)).Nodup →
      (∀ x ∈ vars, Env.find env (1 + x.1) = none) →
      Stmt.execList ctx ⟨env, writes, false⟩
          (vars.map fun (j, type) => .var (1 + j) (wgslTy type) (zeroExpr type)) =
        some ⟨declBindings vars ++ env, writes, false⟩ := by
  intro vars
  induction vars with
  | nil => intro env _ _; simp [Stmt.execList, declBindings]
  | cons x vars ih =>
      intro env hnd hfree
      obtain ⟨j, type⟩ := x
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      have hz : (zeroExpr type).eval ctx env = some (zeroValue type) := by
        cases type <;> rfl
      simp only [List.map_cons, Stmt.execList, Bool.false_eq_true, ↓reduceIte, Stmt.exec, hz,
        Option.bind_eq_bind, Option.bind_some, zero_holds, hfree (j, type) (by simp),
        Option.isNone_none, Bool.and_self]
      rw [ih ((1 + j, zeroValue type, true) :: env) hnd.2 (fun y hy => by
        have hne : 1 + j ≠ 1 + y.1 := fun h => hnd.1 ⟨y, hy, by omega⟩
        rw [Env.find_cons_ne _ _ _ _ _ hne]
        exact hfree y (by simp [hy]))]
      simp [declBindings]

theorem declBindings_nodup (vars : List (Nat × LeanExe.IR.ScalarType))
    (h : (vars.map (·.1)).Nodup) : ((declBindings vars).map (·.1)).Nodup := by
  have : (declBindings vars).map (·.1) = ((vars.map (·.1)).map (1 + ·)).reverse := by
    simp [declBindings, List.map_reverse, List.map_map, Function.comp_def]
  rw [this, List.nodup_reverse]
  exact List.Nodup.map (fun a b (hab : 1 + a = 1 + b) => by omega) h

theorem declBindings_names (vars : List (Nat × LeanExe.IR.ScalarType)) :
    ∀ b ∈ declBindings vars, ∃ x ∈ vars, b = (1 + x.1, zeroValue x.2, true) := by
  intro b hb
  simp only [declBindings, List.mem_reverse, List.mem_map] at hb
  obtain ⟨⟨j, t⟩, hj, rfl⟩ := hb
  exact ⟨(j, t), hj, rfl⟩

/-- What invocation `g` of a build kernel stores: element `g`'s halves when `g` is below the
count, and nothing otherwise. -/
theorem Spec.invoke_eq (K : Spec) (hK : K.WF) (m : Module) (hm : K.module = some m)
    (args : List Arg) (n : Nat) (h : K.Fits args n) (f : UInt64 → UInt64)
    (hElem : ∀ k, k < n → ∃ L', K.body.denote (Spec.arrays args) (K.locals args k n) = some L' ∧
      K.element.denote L' (Spec.arrays args) = some (f (UInt64.ofNat k)))
    (outputSize : Nat) (hOut : outputSize = 2 + 2 * n) (g : Nat) (hg : g < 2 ^ 32) :
    m.invoke (args.map Arg.buffer) outputSize (UInt32.ofNat g) =
      some (if g < n then [(2 + 2 * g, (f (UInt64.ofNat g)).toUInt32),
        (3 + 2 * g, (f (UInt64.ofNat g) >>> 32).toUInt32)] else []) := by
  simp only [Spec.module, Option.bind_eq_bind] at hm
  cases hsb : trStmt K.layout K.body (1 + K.width) with
  | none => simp [hsb] at hm
  | some rb =>
  obtain ⟨sb, n1⟩ := rb
  cases htr : trExpr K.layout K.element n1 with
  | none => simp [hsb, htr] at hm
  | some r =>
    obtain ⟨stmts, res, next'⟩ := r
    simp only [hsb, htr, Option.bind_some, Option.pure_def, Option.some.injEq] at hm
    subst hm
    have hlen : args.length = K.kinds.length := by rw [← h.kinds, List.length_map]
    have hn := h.bound
    have hidx := hK.index
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
    have hPnames : ∀ b ∈ envP, b.1 < 1 + K.kinds.length := by
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · have := paramBindings_names args 0 b hb; omega
      · simp at hb; subst hb; simp
    have hVnames : ∀ x ∈ K.vars, K.kinds.length ≤ x.1 ∧ x.1 < K.width := fun x hx => by
      have := hK.vars x.1 x.2 hx; exact ⟨this.1, this.2.1⟩
    set envD := declBindings K.vars ++ envP with henvD
    have hdecl : Stmt.execList ctx ⟨envP, [], false⟩ K.decls = some ⟨envD, [], false⟩ :=
      decls_run ctx [] K.vars envP hK.nodup fun x hx =>
        find_none_of_names hPnames (1 + x.1) (by have := hVnames x hx; omega)
    have hDnames : ∀ b ∈ envD, b.1 < 1 + K.width := by
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · obtain ⟨x, hx, rfl⟩ := declBindings_names K.vars b hb
        have := hVnames x hx; simp; omega
      · have := hPnames b hb; have := hK.kindsW; omega
    have hdeclFresh : ∀ b ∈ declBindings K.vars, Env.find envP b.1 = none := fun b hb => by
      obtain ⟨x, hx, rfl⟩ := declBindings_names K.vars b hb
      exact find_none_of_names hPnames _ (by have := hVnames x hx; simp; omega)
    have hfind0 : Env.find envD 0 = some (pairOf (UInt64.ofNat g), false) := by
      rw [henvD, Env.find_append_fresh _ _ 0 (fun b hb => by
        obtain ⟨x, hx, rfl⟩ := declBindings_names K.vars b hb; simp)]
      rw [henvP, Env.find_append_fresh _ _ 0 (fun b hb => by
        have := paramBindings_names args 0 b hb; omega), pairOf_ofNat g hg]
      simp [Env.find]
    have hfindC : Env.find envD K.count.var = some (pairOf (UInt64.ofNat n), false) := by
      have hc := hK.count
      have hf := h.count
      have hCvar : K.count.var < 1 + K.kinds.length := by
        revert hc
        cases K.count with
        | size l src =>
            intro hc; have := (List.getElem?_eq_some_iff.mp hc.2.2.2).1; simp [Count.var]; omega
        | param j => intro hc; have := (List.getElem?_eq_some_iff.mp hc).1; simp [Count.var]; omega
      rw [henvD, Env.find_append_fresh _ _ _ (fun b hb => by
        obtain ⟨x, hx, rfl⟩ := declBindings_names K.vars b hb
        have := hVnames x hx; simp; omega)]
      revert hf hCvar
      cases K.count with
      | size l src =>
          intro hf _
          obtain ⟨xs, hxs, hxn⟩ := hf
          rw [pairOf_ofNat n (by omega), ← hxn]
          simpa [Arg.value, Count.var] using find_paramBindings args _ 0 src _ hxs
      | param j =>
          intro hf _
          simpa [Arg.value, Count.var] using find_paramBindings args _ 0 j _ hf
    have hguard := lt64_word ctx envD 0 K.count.var _ _ hfind0 hfindC
    have hcmp : decide (UInt64.ofNat g < UInt64.ofNat n) = decide (g < n) := by
      simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [List.append_assoc, execList_append, hpro, Option.bind_some, hdecl]
    by_cases hgn : g < n
    · -- The guard passes; the statements and the element run; the two stores follow.
      have hite : Stmt.execList ctx ⟨envD, [], false⟩
          [.ite (.not (lt64 0 K.count.var)) [.ret] []] = some ⟨envD, [], false⟩ := by
        simp [Stmt.execList, Stmt.exec, Expr.eval, hguard, hcmp, hgn]
      rw [hite, Option.bind_some]
      obtain ⟨L', hden, hel⟩ := hElem g hgn
      have hB := K.layout_below hK
      have hD := K.layout_distinct hK
      have hAgreeD : K.layout.Agrees (K.locals args g n) (Spec.arrays args) ctx envD :=
        (K.agrees hK args n h ctx rfl g hg).extend _ hdeclFresh
      have hW : K.layout.Writable envD := by
        intro j type hj
        have hmem := lookup_mem (show K.vars.lookup j = some type from hj)
        refine ⟨1 + j, zeroValue type, K.layout_var hK hmem, ?_, zero_holds type⟩
        rw [henvD]
        refine Env.find_append_left (Env.find_of_mem (declBindings_nodup K.vars hK.nodup) ?_)
        simp only [declBindings, List.mem_reverse, List.mem_map]
        exact ⟨(j, type), hmem, rfl⟩
      have hFreshD : ∀ k, 1 + K.width ≤ k → Env.find envD k = none := find_none_of_names hDnames
      obtain ⟨added1, E1, hrun1, hS1, hb1, hA1, hW1⟩ := trStmt_sim K.layout hD (Spec.arrays args)
        ctx [] K.body (1 + K.width) sb n1 hsb hB (K.locals args g n) L' hden envD hAgreeD hW hFreshD
      rw [hrun1, Option.bind_some]
      have hle1 := trStmt_mono K.layout K.body _ _ _ hsb
      have hE1 : ∀ x ∈ E1, x.1 < 1 + K.width := fun x hx => by
        obtain ⟨y, hy, hxy⟩ := hS1.names x hx
        have := hDnames y hy
        omega
      have hA1' := hA1.extend added1 (fun x hx => find_none_of_names hE1 x.1 (hb1 x hx).1)
      have hFresh1 : ∀ k, n1 ≤ k → Env.find (added1 ++ E1) k = none :=
        find_none_of_names fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact (hb1 x hx).2
          · have := hE1 x hx; omega
      obtain ⟨added2, hrun2, hb2, hle2, hlt2, mres, hres⟩ := trExpr_sim K.layout L'
        (Spec.arrays args) ctx [] K.element n1 stmts res next' htr _ hel (added1 ++ E1) hA1'
        hFresh1
      rw [hrun2, Option.bind_some]
      have hidxW : K.index ∉ K.body.writes := fun hw => by
        have := trStmt_writes K.layout K.body _ _ _ hsb K.index hw
        obtain ⟨type, ht⟩ := Option.isSome_iff_exists.mp this
        exact (hK.vars K.index type (lookup_mem ht)).2.2.1 rfl
      have hL'idx : L' K.index = some (.i64 (UInt64.ofNat g)) := by
        rw [LeanExe.IR.Stmt.denote_frame _ K.body _ L' hden K.index hidxW]
        simp [Spec.locals]
      obtain ⟨w0, m0, hw0, hf0⟩ := hA1.word K.index _ hL'idx
      have hw00 : w0 = 0 := by
        simp only [Spec.layout, show ¬ K.index < K.kinds.length by omega, dite_false, ↓reduceIte,
          Option.some.injEq] at hw0
        exact hw0.symm
      subst hw00
      have h0' : Env.find (added2 ++ (added1 ++ E1)) 0 = some (pairOf (UInt64.ofNat g), m0) := by
        rw [Env.find_append_fresh _ _ 0 (fun b hb' => by have := hb2 b hb'; omega),
          Env.find_append_fresh _ _ 0 (fun b hb' => by have := hb1 b hb'; omega)]
        exact hf0
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
    · have hite : Stmt.execList ctx ⟨envD, [], false⟩
          [.ite (.not (lt64 0 K.count.var)) [.ret] []] = some ⟨envD, [], true⟩ := by
        simp [Stmt.execList, Stmt.exec, Expr.eval, hguard, hcmp, hgn]
      rw [hite, Option.bind_some, execList_returned _ _ rfl, Option.bind_some,
        execList_returned _ _ rfl, Option.bind_some, execList_returned _ _ rfl]
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
theorem Spec.dispatch_eq (K : Spec) (hK : K.WF) (m : Module) (hm : K.module = some m)
    (args : List Arg) (n : Nat) (h : K.Fits args n) (f : UInt64 → UInt64)
    (hElem : ∀ k, k < n → ∃ L', K.body.denote (Spec.arrays args) (K.locals args k n) = some L' ∧
      K.element.denote L' (Spec.arrays args) = some (f (UInt64.ofNat k)))
    (output : Array UInt32) (hOut : output.size = 2 + 2 * n)
    (hL0 : output[0]? = some (UInt32.ofNat n)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : n ≤ count) (h32 : count ≤ 2 ^ 32) :
    m.dispatch (args.map Arg.buffer) output count =
        some (arrayWords (LeanExe.build (UInt64.ofNat n) f)) ∧
      m.RaceFree (args.map Arg.buffer) output.size count := by
  have hxs := h.bound
  have hinv := fun g (hg : g < 2 ^ 32) =>
    K.invoke_eq hK m hm args n h f hElem output.size hOut g hg
  have hn64 : (UInt64.ofNat n).toNat = n := by simp; omega
  have hbuild : ∀ k, k < n → (LeanExe.build (UInt64.ofNat n) f)[k]! = f (UInt64.ofNat k) := by
    intro k hk
    rw [getElem!_pos _ k (by simp [LeanExe.build, hn64]; omega)]
    simp [LeanExe.build]
  have hbsize : (LeanExe.build (UInt64.ofNat n) f).size = n := by
    simp [LeanExe.build, hn64]
  refine ⟨?_, ?_⟩
  · unfold Module.dispatch
    rw [foldlM_some _ (fun out g => applyWrites out (buildWrites n (fun g => f (UInt64.ofNat g)) g))
      (List.range count) (fun b g hg => by
        rw [hinv g (by simp at hg; omega)]; rfl)]
    congr 1
    apply Array.ext_getElem?
    intro i
    rw [(build_fold n _ output hOut count i).1]
    unfold buildWord
    by_cases hi : i < 2 + 2 * n
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
      · rw [if_pos (show 2 ≤ i ∧ (i - 2) / 2 < count ∧ (i - 2) / 2 < n by omega),
          if_neg hi2, hbuild _ (by omega)]
        by_cases hev : i % 2 = 0
        · simp [hev, wordHalf]
        · have : i % 2 = 1 := by omega
          simp [hev, this, wordHalf]
    · rw [if_neg (show ¬(2 ≤ i ∧ (i - 2) / 2 < count ∧ (i - 2) / 2 < n) by omega),
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

end LeanExe.WGSL
