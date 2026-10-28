import Verified.TreeNodeCode
import Verified.TreeNodeBound
import Verified.TreeFinish

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem spec_treeNode {S : List Sig} {Γ : List Ty} {shape : TreeShape}
    {r : Fin shape.records} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (reuse : Option (Var Γ (.treeHeader shape r)))
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes)
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (wordSpec : ∀ i env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (words i) env slots paid live)
    (arraySpec : ∀ i env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (arrays i) env slots paid live)
    (bufferSpec : ∀ i env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (buffers i) env slots paid live)
    (childSpec : ∀ i env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (children i) env slots paid live) :
    ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv
        (Expr.treeNode r reuse words arrays buffers children) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hSafe hCap hBase hRoom hPlace
    rest Q hTrap hNext
  let e := Expr.treeNode r reuse words arrays buffers children
  let ps : List Ty := tysOfFn (shape.words r) (shape.wordTy r) ++
    (List.replicate (shape.children r) (.tree shape) ++
      (tysOfFn (shape.arrays r) (shape.arrayTy r) ++
        (List.replicate (shape.buffers r) .bytes ++ [])))
  let args := treeArgs words children arrays buffers
  let kept := fun k => live k || optionVarUses reuse k
  let L := fieldLive args.get kept
  let cost := argsSum (fieldCost funs flags bounds (slots.map Slot.mode) paid L args.get env)
  have hLen : ps.length =
      shape.words r + shape.children r + shape.arrays r + shape.buffers r := by
    simp [ps, tysOfFn_length, Nat.add_assoc]
  have hIn : L 0 = fun i => live i || e.uses i :=
    treeNode_entryLive reuse words arrays buffers children live
  have hEnd : L ps.length = kept := funext (fieldLive_end args.get kept)
  have hVars0 : Holds env slots (L 0) base heap store s := by rw [hIn]; exact hVars
  have hKept : ∀ i, kept i = true → L 0 i = true := by
    intro i hi
    simp only [L, fieldLive_zero, hi, Bool.true_or]
  have hLive : ∀ i, live i = true → kept i = true := by
    intro i hi
    simp only [kept, hi, Bool.true_or]
  have hSplit := dyingPot_split (store := store) (s := s) (env := env) (slots := slots)
    (paid := paid) (L 0) kept live hKept hLive
  have hCost : cost + treeParentCost shape r reuse slots live =
      e.allocs funs flags bounds (slots.map Slot.mode) paid live env :=
    treeNode_fieldCost reuse words arrays buffers children funs flags bounds slots paid live env
  have hWidthSum : (ps.map Ty.width).sum =
      shape.words r + shape.children r + shape.arrays r + 2 * shape.buffers r :=
    treeArgs_widths shape r
  have hArgsSpec : ∀ i live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (args.get i) env slots paid live :=
    treeArgs_forall (fun {t} _ (value : Expr S Γ t) => ∀ live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv value env slots paid live) words
      children arrays buffers
      (fun i => wordSpec i env slots paid) (fun i => childSpec i env slots paid)
      (fun i => arraySpec i env slots paid) (fun i => bufferSpec i env slots paid)
  simp only [Expr.placeArgs, Bool.and_eq_true, Bool.not_eq_true'] at hPlace
  have hArgsPlace : ∀ i, (args.get i).placeArgs = true :=
    treeArgs_forall (fun {t} _ (value : Expr S Γ t) => value.placeArgs = true) words children
      arrays buffers
      (fun i => by simpa using argsAny_eq_false hPlace.1.1.1 i)
      (fun i => by simpa using argsAny_eq_false hPlace.1.1.2 i)
      (fun i => by simpa using argsAny_eq_false hPlace.1.2 i)
      (fun i => by simpa using argsAny_eq_false hPlace.2 i)
  have hArgsD : ∀ i, (!(args.get i).fits funs fits env) = true →
      (!(e.fits funs fits env)) = true := by
    apply treeArgs_forall (fun {t} _ (value : Expr S Γ t) =>
      (!(value.fits funs fits env)) = true → (!(e.fits funs fits env)) = true) words children
      arrays buffers
    · intro i hi
      have hf : (words i).fits funs fits env = false := by simpa using hi
      simp only [e, Expr.fits, argsAll_false (fun j => (words j).fits funs fits env) i hf,
        Bool.false_and, Bool.and_false, Bool.not_false]
    · intro i hi
      have hf : (children i).fits funs fits env = false := by simpa using hi
      simp only [e, Expr.fits, argsAll_false (fun j => (children j).fits funs fits env) i hf,
        Bool.false_and, Bool.and_false, Bool.not_false]
    · intro i hi
      have hf : (arrays i).fits funs fits env = false := by simpa using hi
      simp only [e, Expr.fits, argsAll_false (fun j => (arrays j).fits funs fits env) i hf,
        Bool.false_and, Bool.and_false, Bool.not_false]
    · intro i hi
      have hf : (buffers i).fits funs fits env = false := by simpa using hi
      simp only [e, Expr.fits, argsAll_false (fun j => (buffers j).fits funs fits env) i hf,
        Bool.and_false, Bool.not_false]
  have hWidths : ∀ i,
      base + shape.bindWidth r + max (args.get i).width (copyWidth (ps.get i)) ≤ h := by
    simp only [Expr.width] at hRoom
    let W := argsMax fun j => (words j).width
    let C := argsMax fun j => max (children j).width (copyWidth (.tree shape))
    let A := argsMax fun j => max (arrays j).width (copyWidth (shape.arrayTy r j))
    let B := argsMax fun j => max (buffers j).width (copyWidth .bytes)
    have hW := Nat.le_max_left W (max C (max A B))
    have hCAB := Nat.le_max_right W (max C (max A B))
    have hC := Nat.le_max_left C (max A B)
    have hAB := Nat.le_max_right C (max A B)
    have hA := Nat.le_max_left A B
    apply treeArgs_forall (fun {t} _ (value : Expr S Γ t) =>
      base + shape.bindWidth r + max value.width (copyWidth t) ≤ h) words children arrays buffers
    · intro i
      have hi := le_argsMax (fun j => (words j).width) i
      have hCopy : copyWidth (shape.wordTy r i) = 0 := by
        simp only [copyWidth, TreeShape.wordTy, Ty.scalar, ↓reduceIte]
      rw [hCopy, Nat.max_zero]
      omega
    · intro i
      have hi := le_argsMax (fun j => max (children j).width (copyWidth (.tree shape))) i
      omega
    · intro i
      have hi := le_argsMax (fun j => max (arrays j).width (copyWidth (shape.arrayTy r j))) i
      omega
    · intro i
      have hi := le_argsMax (fun j => max (buffers j).width (copyWidth .bytes)) i
      have hB := Nat.le_max_right A B
      omega
  have hParentRoom : base < h := by
    have hb : 1 ≤ shape.bindWidth r := by
      simp only [TreeShape.bindWidth, TreeShape.bindCount]
      omega
    simp only [Expr.width] at hRoom
    omega
  have hValues : (Env.ofFn fun i => (args.get i).denote funs env) =
      shape.fieldEnv r (fun i => (words i).denote funs env) (fun i => (arrays i).denote funs env)
        (fun i => (buffers i).denote funs env) (fun i => (children i).denote funs env) :=
    (Args.denote_eq_ofFn funs env args).symm.trans
      (treeArgs_denote funs env words children arrays buffers)
  have hBudget : TrapOK (!(e.fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid (L 0) live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env))) Q := by
    simpa only [trapFlag, Expr.aborts, Bool.true_or, Bool.true_and, hIn] using hTrap
  rw [treeNode_code_eq]
  simp only [List.append_assoc]
  have hRun := fieldsMixed_spec hm ps args.get L
    (fieldLive_step args.get kept) (fun i => hArgsSpec i (L (i.val + 1))) hArgsPlace hArgsD
    (fieldBase := base + 1) (scratch := base + shape.bindWidth r) (by omega)
    (by rw [hWidthSum]; simp only [TreeShape.bindWidth, TreeShape.bindCount]; omega) hWidths
    heap store s hh hpv hBase hVars0 hAt (by rw [hIn]; exact hSafe) hCap
    (treeParentCode shape r reuse slots base live ++ (shape.tagStoreCode r base ++
      (treeStoreFields h base (shape.wordTypes r) (base + 1) (base + 1 + shape.words r)
        shape.fieldStart (shape.fields r) ++
        (treeStoreHeaps base (shape.kinds r) (base + 1 + shape.words r + shape.children r)
          (base + 1 + shape.words r + shape.children r + shape.arrays r)
          (shape.fieldStart + (shape.fields r).length) ++
          (sealRecordCode (shape.width r) base (shape.mask r) ++ (.localGet base :: rest)))))) Q
    (hBudget.allocPart id (fun _ hw => hw.mono (by rw [hEnd, hSplit, ← hCost]; omega)))
    (fun heap1 store1 s1 ws aFields hFrameFields holdFields hNormalFields hTopFields => by
      rw [hEnd] at aFields hTopFields
      rw [hValues] at aFields
      rw [treeArgs_types] at holdFields
      let sField : Locals := { s1 with values := s.values }
      have a := aFields.reframe (Frame.ofValues (values := s.values))
      refine wp_treeParent reuse hm a.holds a.step.at_ (by rw [a.step.cap m]; exact hCap)
        (by rw [a.frame.params]; exact hBase) (by rw [a.frame.positions, hh]; exact hParentRoom)
        (hBudget.allocPart (d' := false) nofun (fun hd hw => hw.shift
          (by simpa only [Nat.add_assoc] using hTopFields hd)
          (by rw [hSplit, ← hCost]; omega) (a.step.cap m)))
        fun heap2 store2 s2 p hRootStep hRootFrame hRootHolds hRaw hCount hPtr hStack hOther hApart
          hTopRoot => ?_
      have holdFields2 : LocalsHold s2 (base + 1) (shape.fieldTypes r) ws := by
        intro k hk
        have hold := holdFields k hk
        rw [hRootFrame.positions, hOther _ (by
          cases (shape.fieldTypes r).getD k .i64 <;> simp only [slotIndex] <;> omega)]
        exact hold
      have hFinish := wp_finishTree (m := m) (host := host) (Q := Q) (rest := rest)
        hVars0 a hRootStep hRootFrame hRootHolds hKept hLive hRaw hCount hPtr
        hStack (hRootFrame.positions.trans (a.frame.positions.trans hh)) hNormalFields holdFields2
        hApart
        (fun store3 hAfter => by
          refine hNext heap2 store3 s2 [.i64 p]
            (by
              have hNorm := normalFamily_eq (α := fun i => Array (shape.arrayElem r i).denote)
                (fun i => (arrays i).denote funs env)
              simpa only [hIn, e, Expr.mode, Expr.denote, normalFamily_eq, hNorm] using hAfter)
            fun hf => ?_
          have hd : (!(e.fits funs fits env)) = false := by simpa only [Bool.not_eq_false'] using hf
          have hTop1 := hTopFields hd
          change heap2.top.toNat ≤ heap.top.toNat +
            dyingPot store s env slots paid (fun i => live i || e.uses i) live +
              e.allocs funs flags bounds (slots.map Slot.mode) paid live env
          rw [← hIn, hSplit, ← hCost]
          omega)
      simpa only [List.append_assoc] using hFinish)
  simpa only [ps, args, L, kept, List.append_assoc, List.cons_append, List.nil_append] using hRun

end Verified
