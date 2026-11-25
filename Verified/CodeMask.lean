module

public import Verified.Compile

public section

/-!
`Expr.codeMask`, `TailBody.codeWithMask`, `loopCodeMask`, and `ListFold.loopCodeMask` take the
variables live after an expression as a bitmask, and the kernel evaluates them in every byte
theorem, while the proofs unfold `Expr.code` and its helpers, which take those variables as a
function.  Each `_eq` theorem of this module states a mask form equal to its original under
`Nat.testBit` of the mask, and `releaseMask_eq` states `releaseMask` equal to `releaseWhere` on
the bits of its mask.  The `testBit` equations state the bits of each mask operation as a
function, so that `simp` rewrites a set of live variables built from masks into the function that
the original builds.
-/

namespace Verified

open Wasm

theorem testBit_or_eq (a b : Nat) : Nat.testBit (a ||| b) = fun i => a.testBit i || b.testBit i :=
  funext fun _ => Nat.testBit_or ..

theorem testBit_shiftRight_eq (a k : Nat) : Nat.testBit (a >>> k) = fun i => a.testBit (i + k) :=
  funext fun i => by rw [Nat.testBit_shiftRight, Nat.add_comm]

theorem testBit_shiftLeft_eq (a k : Nat) : Nat.testBit (a <<< k) = shift k a.testBit := by
  funext i
  rw [Nat.testBit_shiftLeft, shift]
  by_cases below : i < k
  · simp [below, Nat.not_le.mpr below]
  · simp [below, Nat.le_of_not_lt below]

theorem testBit_one_eq : Nat.testBit 1 = fun i => i == 0 := by
  funext i
  simpa using testBit_one_shiftLeft 0 i

theorem testBit_zero_eq : Nat.testBit 0 = fun _ => false :=
  funext Nat.zero_testBit

/-- The bits of `1 <<< k` with the test that most selectors write.  `testBit_shiftLeft_eq` also
matches `1 <<< k` and gives a shifted test, so a proof rewrites with this equation in one `simp`
call and with `testBit_shiftLeft_eq` in a later one. -/
theorem testBit_one_shiftLeft_eq (k : Nat) : Nat.testBit (1 <<< k) = fun i => i == k :=
  funext (testBit_one_shiftLeft k)

/-- The bits of `1 <<< k` with the test of the selectors of `treeCase`. -/
theorem testBit_one_shiftLeft_decide_eq (k : Nat) :
    Nat.testBit (1 <<< k) = fun i => decide (i = k) := by
  funext i
  rw [testBit_one_shiftLeft]
  by_cases h : i = k <;> simp [h]

theorem testBit_two_pow_sub_one_eq (k : Nat) :
    Nat.testBit (2 ^ k - 1) = fun i => decide (i < k) :=
  funext (Nat.testBit_two_pow_sub_one k)

theorem testBit_maskDiff_eq (a b : Nat) :
    Nat.testBit (maskDiff a b) = fun i => a.testBit i && !b.testBit i := by
  funext i
  simp only [maskDiff, Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem testBit_maskIf_eq (b : Bool) (m : Nat) :
    Nat.testBit (maskIf b m) = fun i => b && m.testBit i := by
  funext i
  cases b <;> simp [maskIf]

theorem testBit_argsMask_eq {n : Nat} (b : (i : Fin n) → Nat) :
    Nat.testBit (argsMask b) = fun i => argsAny fun j => (b j).testBit i :=
  funext (argsMask_testBit b)

theorem testBit_optionVarMask_eq (value : Option (Var Γ t)) :
    Nat.testBit (optionVarMask value) = optionVarUses value :=
  funext (optionVarMask_testBit value)

theorem testBit_dite_eq (c : Prop) [Decidable c] (f : c → Nat) :
    Nat.testBit (if hc : c then f hc else 0) =
      fun i => if hc : c then (f hc).testBit i else false := by
  funext i
  by_cases hc : c <;> simp [hc]

theorem releaseVar_cons_succ (t : Ty) (Γ : List Ty) (slots : List Slot) (i : Nat) :
    releaseVar (t :: Γ) slots (i + 1) = releaseVar Γ slots.tail i := by
  cases slots <;> simp [releaseVar]

theorem releaseWhere_nil (slots : List Slot) (sel : Nat → Bool) :
    releaseWhere [] slots sel = [] := by
  simp [releaseWhere]

theorem releaseWhere_false (Γ : List Ty) (slots : List Slot) :
    releaseWhere Γ slots (fun _ => false) = [] := by
  simp [releaseWhere]

/-- `releaseWhere` releases the first variable, when `sel` selects it, and then those of the rest
of the context, whose indices are one less. -/
theorem releaseWhere_cons (t : Ty) (Γ : List Ty) (slots : List Slot) (sel : Nat → Bool) :
    releaseWhere (t :: Γ) slots sel =
      (if sel 0 then releaseVar (t :: Γ) slots 0 else []) ++
        releaseWhere Γ slots.tail (fun i => sel (i + 1)) := by
  have hTail : (((List.range Γ.length).map Nat.succ).filter sel).flatMap
      (releaseVar (t :: Γ) slots) =
      ((List.range Γ.length).filter fun i => sel (i + 1)).flatMap (releaseVar Γ slots.tail) := by
    rw [List.filter_map, List.flatMap_map]
    congr 1
    funext i
    exact releaseVar_cons_succ t Γ slots i
  unfold releaseWhere
  rw [List.length_cons, List.range_succ_eq_map, List.filter_cons]
  cases h : sel 0 <;> simp only [Bool.false_eq_true, ↓reduceIte, List.flatMap_cons, hTail,
    List.nil_append]

theorem releaseMask_eq : (Γ : List Ty) → (slots : List Slot) → (mask : Nat) →
    releaseMask Γ slots mask = releaseWhere Γ slots mask.testBit
  | [], slots, mask => by simp [releaseMask, releaseWhere_nil]
  | t :: Γ, slots, mask => by
    rw [releaseWhere_cons, releaseMask]
    by_cases h : mask = 0
    · subst h
      simp [Nat.zero_testBit, releaseWhere_false]
    · simp only [h, ↓reduceIte]
      rw [releaseMask_eq Γ slots.tail (mask >>> 1), testBit_shiftRight_eq]

theorem loopCodeMask_eq (h : Nat) (slots : List Slot) (base live : Nat)
    {Γ : List Ty} {t : Ty} (init : Expr S Γ t) (cond : Expr S (t :: Γ) .bool)
    (body : Expr S (t :: .word :: Γ) t)
    (countM initM condM bodyM : List Slot → Nat → Nat → Program)
    (countC initC condC bodyC : List Slot → Nat → (Nat → Bool) → Program)
    (hCount : ∀ slots base live, countM slots base live = countC slots base live.testBit)
    (hInit : ∀ slots base live, initM slots base live = initC slots base live.testBit)
    (hCond : ∀ slots base live, condM slots base live = condC slots base live.testBit)
    (hBody : ∀ slots base live, bodyM slots base live = bodyC slots base live.testBit) :
    loopCodeMask h slots base live init cond body countM initM condM bodyM =
      loopCode h slots base live.testBit init cond body countC initC condC bodyC := by
  simp only [loopCodeMask, loopCode, hCount, hInit, hCond, hBody, releaseMask_eq,
    testBit_or_eq, testBit_shiftRight_eq, testBit_shiftLeft_eq, testBit_one_eq,
    testBit_maskDiff_eq, Expr.usesFast]

theorem TailBody.codeWithMask_eq
    (exprCodeM : {Γ : List Ty} → {t : Ty} → Expr S Γ t → List Slot → Nat → Nat → Program)
    (exprCode : {Γ : List Ty} → {t : Ty} → Expr S Γ t → List Slot → Nat → (Nat → Bool) →
      Program)
    (hE : ∀ {Γ : List Ty} {t : Ty} (e : Expr S Γ t) slots base live,
      exprCodeM e slots base live = exprCode e slots base live.testBit)
    (targetModes : List Mode) (h p0 resultBase : Nat) (body : TailBody S params result Γ) :
    ∀ slots base exitLabel nextLabel,
      body.codeWithMask exprCodeM targetModes h p0 resultBase slots base exitLabel nextLabel =
        body.codeWith exprCode targetModes h p0 resultBase slots base exitLabel nextLabel := by
  induction body with
  | ret value =>
    intro slots base exitLabel nextLabel
    simp only [TailBody.codeWithMask, TailBody.codeWith, hE, testBit_zero_eq]
  | next args =>
    intro slots base exitLabel nextLabel
    simp only [TailBody.codeWithMask, TailBody.codeWith, hE, releaseMask_eq, testBit_maskDiff_eq,
      testBit_argsMask_eq, testBit_maskIf_eq, Expr.usesFast]
  | ite cond yes no yesIh noIh =>
    intro slots base exitLabel nextLabel
    simp only [TailBody.codeWithMask, TailBody.codeWith, hE, yesIh, noIh, releaseMask_eq,
      testBit_maskDiff_eq, testBit_or_eq, TailBody.usesFast]
  | letE value body bodyIh | letPair value body bodyIh =>
    intro slots base exitLabel nextLabel
    simp only [TailBody.codeWithMask, TailBody.codeWith, hE, bodyIh, testBit_shiftRight_eq,
      TailBody.usesFast]
  | treeCase x empty nodes emptyIh nodesIh =>
    intro slots base exitLabel nextLabel
    simp only [TailBody.codeWithMask, TailBody.codeWith, emptyIh, nodesIh, releaseMask_eq,
      testBit_maskDiff_eq, testBit_or_eq, testBit_argsMask_eq, testBit_shiftRight_eq,
      testBit_one_shiftLeft_decide_eq, testBit_two_pow_sub_one_eq, testBit_dite_eq,
      TailBody.usesFast]

theorem ListFold.leafCodeMask_eq {S : List Sig} (h : Nat)
    (bodyM : List Slot → Nat → Nat → Program) (bodyC : List Slot → Nat → (Nat → Bool) → Program)
    (hB : ∀ slots base live, bodyM slots base live = bodyC slots base live.testBit)
    {Γ : List Ty} {t : Ty} (value : Expr S Γ t) (slots : List Slot) (base live : Nat) :
    ListFold.leafCodeMask h bodyM value slots base live =
      ListFold.leafCode h bodyC value slots base live.testBit := by
  cases value <;> simp only [ListFold.leafCodeMask, ListFold.leafCode, hB]

theorem ListFold.loopCodeMask_eq {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (ListFold.context e captures) (.elem e)) (h stateBase : Nat)
    (bodyM : List Slot → Nat → Nat → Program) (bodyC : List Slot → Nat → (Nat → Bool) → Program)
    (hB : ∀ slots base live, bodyM slots base live = bodyC slots base live.testBit) :
    ListFold.loopCodeMask body h stateBase bodyM = ListFold.loopCode body h stateBase bodyC := by
  simp only [ListFold.loopCodeMask, ListFold.loopCode,
    TailBody.codeWithMask_eq _ _ (ListFold.leafCodeMask_eq h bodyM bodyC hB)]

/-- The code that the kernel evaluates is the code that the proofs unfold.  A case that builds a
set from `1 <<< k` rewrites with `testBit_one_shiftLeft_eq` before `testBit_shiftLeft_eq`. -/
theorem Expr.codeMask_eq (h : Nat) (pool : Bytes.LiteralPool) {Γ : List Ty} {t : Ty}
    (e : Expr S Γ t) : ∀ (slots : List Slot) (base live : Nat),
      e.codeMask h slots base live pool = e.code (pool := pool) h slots base live.testBit := by
  induction e with
  | word | bytesEmpty | bytesLiteral | bytesSize | treeNil | bool | float32 | float | var
  | size | leSize | proj => intro _ _ _; rfl
  | loop count init cond body countIh initIh condIh bodyIh =>
    intro slots base live
    simp only [Expr.codeMask, Expr.code]
    exact loopCodeMask_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ countIh initIh condIh bodyIh
  | fold x init body initIh bodyIh =>
    intro slots base live
    simp only [Expr.codeMask, Expr.code]
    refine loopCodeMask_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ _ => rfl) initIh
      (fun _ _ _ => rfl) fun slots base live => ?_
    simp only [bodyIh, testBit_or_eq, testBit_shiftRight_eq, testBit_shiftLeft_eq,
      Expr.usesFast]
  | listFold args body argsIh bodyIh =>
    intro slots base live
    simp only [Expr.codeMask, Expr.code, argsIh, releaseMask_eq, testBit_maskDiff_eq,
      testBit_or_eq, testBit_argsMask_eq, Expr.usesFast,
      ListFold.loopCodeMask_eq body h base
        (fun slots base live => body.codeMask h slots base live pool)
        (fun slots base live => body.code (pool := pool) h slots base live) bodyIh]
  | treeCase x empty nodes emptyIh nodesIh =>
    intro slots base live
    simp only [Expr.codeMask, Expr.code, emptyIh, nodesIh, releaseMask_eq, testBit_maskDiff_eq,
      testBit_or_eq, testBit_argsMask_eq, testBit_shiftRight_eq, testBit_one_shiftLeft_decide_eq,
      testBit_two_pow_sub_one_eq, testBit_dite_eq, Expr.usesFast]
    simp only [testBit_shiftLeft_eq]
  | treeNode r reuse words arrays buffers children wordsIh arraysIh buffersIh childrenIh =>
    intro slots base live
    cases reuse <;>
      simp only [Expr.codeMask, Expr.code, wordsIh, arraysIh, buffersIh, childrenIh,
        testBit_maskIf_eq, testBit_or_eq, testBit_argsMask_eq, testBit_optionVarMask_eq,
        Expr.usesFast]
  | get x i iIh =>
    intro slots base live
    simp only [Expr.codeMask, Expr.code, getCode, iIh, testBit_or_eq, testBit_one_shiftLeft_eq]
  | _ =>
    intro slots base live
    simp_all only [Expr.codeMask, Expr.code, releaseMask_eq, testBit_maskDiff_eq,
      testBit_maskIf_eq, testBit_or_eq, testBit_argsMask_eq, testBit_shiftRight_eq,
      testBit_one_shiftLeft_eq, Expr.usesFast] <;>
    simp only [testBit_shiftLeft_eq, testBit_or_eq, testBit_shiftRight_eq]

theorem TailBody.codeMask_eq (targetModes : List Mode) (h p0 resultBase : Nat)
    {Γ : List Ty} (body : TailBody S params result Γ) (slots : List Slot)
    (base exitLabel nextLabel : Nat) (pool : Bytes.LiteralPool) :
    body.codeMask targetModes h p0 resultBase slots base exitLabel nextLabel pool =
      body.code targetModes h p0 resultBase slots base exitLabel nextLabel pool :=
  TailBody.codeWithMask_eq _ _ (fun e slots base live => Expr.codeMask_eq h pool e slots base live)
    targetModes h p0 resultBase body slots base exitLabel nextLabel

end Verified
