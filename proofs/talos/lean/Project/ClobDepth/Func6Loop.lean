import Project.ClobDepth.Func6Fold

/-!
# Fold loop invariant for function 6

The loop invariant carries the consumed order prefix, the exact allocator
globals through the fold recursions, the owned result array, the preserved
orders representation, and the byte frame below the initial heap top.  The
frame predicate states only the locals the loop reads: the side parameter,
the orders base, the owner and root pair, the cursor, and the limit.
-/

namespace Project.ClobDepth.Func6Loop

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation
  Project.ClobDepth.Func6Fold

set_option maxRecDepth 1048576

structure LoopLocalsAt (s : Locals) (os : List OrderL)
    (side orders ownerv root : UInt64) (k count : Nat) : Prop where
  params : s.params.length = 3
  locals : s.locals.length = 43
  values : s.values = []
  side : s.params[2]? = some (.i64 side)
  orders : s.locals[18]? = some (.i64 orders)
  owner : s.locals[1]? = some (.i64 ownerv)
  root : s.locals[2]? = some (.i64 root)
  cursor : s.locals[20]? = some (.i64 (UInt64.ofNat k))
  limit : s.locals[22]? = some (.i64 (UInt64.ofNat count))

structure FoldState (st0 : Store Unit) (os : List OrderL)
    (side orders : UInt64) (g0n : Nat) (g2 : UInt64)
    (st : Store Unit) (k : Nat) : Prop where
  pages : st.mem.pages = st0.mem.pages
  global0 : st.globals.globals[0]? =
    some (.i64 (UInt64.ofNat (foldTop os side g0n k)))
  global1 : st.globals.globals[1]? = some (.i64 0)
  global2 : st.globals.globals[2]? =
    some (.i64 (g2 + 2 + UInt64.ofNat (matchCount os side k)))
  resultOwned : OwnedLevelArrayAt st
    (UInt64.ofNat (foldRoot os side g0n k))
    (UInt64.ofNat (foldCap os side k)) (foldLevels os side k)
  ordersRep : OrdersAt st orders os
  bytesBefore : ∀ a : Nat, a < g0n → st.mem.bytes a = st0.mem.bytes a

def FoldInvariant (st0 : Store Unit) (base : Locals) (os : List OrderL)
    (side orders : UInt64) (g0n : Nat) (g2 : UInt64) (count : Nat) :
    AssertionF Unit :=
  fun st s =>
    ∃ k, k ≤ count ∧
      s.params = base.params ∧
      LoopLocalsAt s os side orders
        (UInt64.ofNat (foldOwner os side g0n k))
        (UInt64.ofNat (foldRoot os side g0n k)) k count ∧
      FoldState st0 os side orders g0n g2 st k

def foldMeasure (count : Nat) (_ : Store Unit) (s : Locals) : Nat :=
  match s.locals[20]? with
  | some (Value.i64 k) => count - k.toNat
  | _ => 0

def initialStore (st : Store Unit) (g0 g2 : UInt64) : Store Unit :=
  Func6Alloc.allocStore (Func6Alloc.allocStore st g0 g2) (g0 + 56) (g2 + 1)

set_option Elab.async false in
theorem foldState_initial
    (st : Store Unit) (os : List OrderL)
    (side orders ordersCapacity g0 g2 : UInt64)
    (hFit32 : g0.toNat + 112 < 4294967296)
    (hFit : g0.toNat + 112 ≤ st.mem.pages * 65536)
    (hOrders : OrdersAt st orders os)
    (hOrders32 :
      orders.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hOrders48 : 48 ≤ orders.toNat)
    (hOrdersCap :
      fixedArrayBytes os.length 5 ≤ ordersCapacity.toNat)
    (hOrdersBelow : orders.toNat + ordersCapacity.toNat ≤ g0.toNat)
    (hGlobal0 : st.globals.globals[0]? = some (.i64 g0))
    (hGlobal1 : st.globals.globals[1]? = some (.i64 0))
    (hGlobal2 : st.globals.globals[2]? = some (.i64 g2)) :
    FoldState st os side orders g0.toNat g2 (initialStore st g0 g2) 0 := by
  have h56 : (g0 + 56).toNat = g0.toNat + 56 := by
    rw [UInt64.toNat_add]
    have h : (56 : UInt64).toNat = 56 := rfl
    rw [h]
    exact Nat.mod_eq_of_lt (by have := UInt64.toNat_lt_size g0; omega)
  have hInner32 : (g0 + 56).toNat + 56 < 4294967296 := by
    rw [h56]
    omega
  have hInnerPages :
      (Func6Alloc.allocStore st g0 g2).mem.pages = st.mem.pages :=
    Func6Alloc.allocStore_pages st g0 g2
  have hInnerFit : (g0 + 56).toNat + 56 ≤
      (Func6Alloc.allocStore st g0 g2).mem.pages * 65536 := by
    rw [hInnerPages, h56]
    omega
  have hBytes : ∀ a : Nat, a < g0.toNat →
      (initialStore st g0 g2).mem.bytes a = st.mem.bytes a := by
    intro a ha
    unfold initialStore
    rw [Func6Alloc.allocStore_bytes_before _ _ _ a hInner32
      (by rw [h56]; omega)]
    exact Func6Alloc.allocStore_bytes_before st g0 g2 a (by omega) ha
  have hPages : (initialStore st g0 g2).mem.pages = st.mem.pages := by
    unfold initialStore
    rw [Func6Alloc.allocStore_pages, hInnerPages]
  refine {
    pages := hPages
    global0 := ?_
    global1 := ?_
    global2 := ?_
    resultOwned := ?_
    ordersRep := ?_
    bytesBefore := hBytes }
  · have hInner := Func6Alloc.allocStore_global0 st g0 g2 _ hGlobal0
    have hOuter := Func6Alloc.allocStore_global0
      (Func6Alloc.allocStore st g0 g2) (g0 + 56) (g2 + 1) _ hInner
    rw [show foldTop os side g0.toNat 0 = g0.toNat + 112 from rfl]
    have hValue : g0 + 56 + 56 = UInt64.ofNat (g0.toNat + 112) := by
      apply UInt64.toNat.inj
      rw [UInt64.toNat_add, h56,
        show (56 : UInt64).toNat = 56 from rfl,
        toNat_ofNat_lt (by rw [size_eq]; omega),
        Nat.mod_eq_of_lt (by have := UInt64.toNat_lt_size g0; omega)]
    rw [← hValue]
    exact hOuter
  · have hInner := Func6Alloc.allocStore_global1 st g0 g2 0 hGlobal1
    exact Func6Alloc.allocStore_global1
      (Func6Alloc.allocStore st g0 g2) (g0 + 56) (g2 + 1) 0 hInner
  · have hInner := Func6Alloc.allocStore_global2 st g0 g2 _ hGlobal2
    have hOuter := Func6Alloc.allocStore_global2
      (Func6Alloc.allocStore st g0 g2) (g0 + 56) (g2 + 1) _ hInner
    rw [show matchCount os side 0 = 0 from rfl]
    have hValue : g2 + 1 + 1 = g2 + 2 + UInt64.ofNat 0 := by
      rw [UInt64.add_assoc]
      rw [show (1 : UInt64) + 1 = 2 by decide,
        show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero]
    rw [← hValue]
    exact hOuter
  · have hEmpty := Func6Alloc.allocStore_empty_levels
      (Func6Alloc.allocStore st g0 g2) (g0 + 56) (g2 + 1)
      hInner32 hInnerFit
    rw [show foldLevels os side 0 = [] from rfl]
    have hRoot : UInt64.ofNat (foldRoot os side g0.toNat 0) =
        g0 + 56 + 48 := by
      rw [show foldRoot os side g0.toNat 0 = g0.toNat + 104 from rfl]
      apply UInt64.toNat.inj
      rw [toNat_ofNat_lt (by rw [size_eq]; omega), UInt64.toNat_add, h56,
        show (48 : UInt64).toNat = 48 from rfl,
        Nat.mod_eq_of_lt (by have := UInt64.toNat_lt_size g0; omega)]
    have hCap : UInt64.ofNat (foldCap os side 0) = 8 := by
      rw [show foldCap os side 0 = 8 from rfl]
      rfl
    rw [hRoot, hCap]
    exact hEmpty
  · apply OrdersAt.frame_region hOrders32 hOrders48 hOrdersCap hPages
      ?_ hOrders
    intro a _ ha
    exact hBytes a (by omega)

set_option Elab.async false in
theorem FoldState.step_match
    {st0 st st1 : Store Unit} {os : List OrderL}
    {side orders : UInt64} {g0n : Nat} {g2 : UInt64} {k count : Nat}
    (hState : FoldState st0 os side orders g0n g2 st k)
    (hk : k < count) (hkos : k < os.length) (hcount : count ≤ os.length)
    (hCount32 : count < 4294967296)
    (hSide : os[k]!.oside = side)
    (hBudget32 : g0n + 112 + count * stepBytes count < 4294967296)
    (hOrders32 :
      orders.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hOrders48 : 48 ≤ orders.toNat)
    (hOrdersCap : ∃ ordersCapacity : Nat,
      fixedArrayBytes os.length 5 ≤ ordersCapacity ∧
      orders.toNat + ordersCapacity ≤ g0n)
    (hUpdate : Func3.UpdateResult st st1
      (UInt64.ofNat (foldTop os side g0n k))
      (g2 + 2 + UInt64.ofNat (matchCount os side k))
      (UInt64.ofNat (foldRoot os side g0n k))
      (UInt64.ofNat (foldCap os side k))
      os[k]!.oprice os[k]!.oqty (foldLevels os side k)) :
    FoldState st0 os side orders g0n g2 st1 (k + 1) := by
  have hTopLe := foldTop_le os side g0n count k (by omega) hcount
  have hTopLe1 := foldTop_le os side g0n count (k + 1) (by omega) hcount
  have hStepLe : k * stepBytes count ≤ count * stepBytes count :=
    Nat.mul_le_mul_right _ (by omega)
  have hStepLe1 : (k + 1) * stepBytes count ≤ count * stepBytes count :=
    Nat.mul_le_mul_right _ (by omega)
  have hTop32 : foldTop os side g0n k < 4294967296 := by omega
  have hTop32' : foldTop os side g0n (k + 1) < 4294967296 := by omega
  have hTopGe := foldTop_ge os side g0n k
  have hTopNat : (UInt64.ofNat (foldTop os side g0n k)).toNat =
      foldTop os side g0n k :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have hLevels1 : foldLevels os side (k + 1) =
      addLevelL (foldLevels os side k) os[k]!.oprice os[k]!.oqty := by
    rw [foldLevels_succ os side k hkos, if_pos hSide]
  have hTopSucc : foldTop os side g0n (k + 1) =
      foldTop os side g0n k + 48 +
        fixedArrayBytes (foldLevels os side (k + 1)).length 2 := by
    simp only [foldTop]
    rw [if_pos hSide]
  have hBytesLt :
      fixedArrayBytes (foldLevels os side (k + 1)).length 2 <
        4294967296 := by
    omega
  have hRootSucc : foldRoot os side g0n (k + 1) =
      foldTop os side g0n k + 48 := by
    simp only [foldRoot]
    rw [if_pos hSide]
  have hCapSucc : foldCap os side (k + 1) =
      fixedArrayBytes (foldLevels os side (k + 1)).length 2 := by
    simp only [foldCap]
    rw [if_pos hSide]
  have hBytesU : Func3.capacity (foldLevels os side k)
      os[k]!.oprice os[k]!.oqty =
      UInt64.ofNat
        (fixedArrayBytes (foldLevels os side (k + 1)).length 2) := by
    unfold Func3.capacity
    rw [← hLevels1]
    have hLenLt : (foldLevels os side (k + 1)).length < 4294967296 := by
      have h := hBytesLt
      unfold fixedArrayBytes at h
      omega
    apply UInt64.toNat.inj
    rw [fixedArrayBytesU_toNat _ 2 (by rw [size_eq]; omega) (by decide)
        (by rw [size_eq]; omega),
      toNat_ofNat_lt (by rw [size_eq]; omega)]
  have hTarget : Func3.target (UInt64.ofNat (foldTop os side g0n k)) =
      UInt64.ofNat (foldRoot os side g0n (k + 1)) := by
    unfold Func3.target
    rw [hRootSucc]
    apply UInt64.toNat.inj
    rw [UInt64.toNat_add, hTopNat,
      show (48 : UInt64).toNat = 48 from rfl,
      toNat_ofNat_lt (by rw [size_eq]; omega)]
    omega
  have hTopValue : UInt64.ofNat (foldTop os side g0n k) + 48 +
      Func3.capacity (foldLevels os side k) os[k]!.oprice os[k]!.oqty =
      UInt64.ofNat (foldTop os side g0n (k + 1)) := by
    rw [hBytesU]
    apply UInt64.toNat.inj
    rw [UInt64.toNat_add, UInt64.toNat_add, hTopNat,
      show (48 : UInt64).toNat = 48 from rfl,
      toNat_ofNat_lt (by rw [size_eq]; omega),
      toNat_ofNat_lt (by rw [size_eq]; omega), hTopSucc]
    omega
  have hOfNat : UInt64.ofNat (matchCount os side k + 1) =
      UInt64.ofNat (matchCount os side k) + 1 := by
    have hM := matchCount_le os side k
    apply UInt64.toNat.inj
    rw [toNat_ofNat_lt (by rw [size_eq]; omega),
      toNat_add_one (by
        rw [toNat_ofNat_lt (by rw [size_eq]; omega), size_eq]
        omega),
      toNat_ofNat_lt (by rw [size_eq]; omega)]
  have hCounter : g2 + 2 + UInt64.ofNat (matchCount os side k) + 1 =
      g2 + 2 + UInt64.ofNat (matchCount os side (k + 1)) := by
    rw [matchCount_succ os side k hkos, if_pos hSide, hOfNat,
      UInt64.add_assoc]
  have hLen0 : 0 < st.globals.globals.length := by
    have := (List.getElem?_eq_some_iff.mp hState.global0).1
    omega
  have hLen2 : 2 < st.globals.globals.length := by
    have := (List.getElem?_eq_some_iff.mp hState.global2).1
    omega
  refine {
    pages := hUpdate.pages.trans hState.pages
    global0 := ?_
    global1 := ?_
    global2 := ?_
    resultOwned := ?_
    ordersRep := ?_
    bytesBefore := ?_ }
  · rw [hUpdate.globals, ← hTopValue]
    simp [hLen0]
  · rw [hUpdate.globals]
    simpa [List.getElem?_set] using hState.global1
  · rw [hUpdate.globals, ← hCounter]
    simp [List.length_set, hLen2]
  · have hOwned := hUpdate.resultOwned
    rw [hTarget, hBytesU, ← hLevels1, ← hCapSucc] at hOwned
    exact hOwned
  · obtain ⟨ordersCapacity, hCap, hBelow⟩ := hOrdersCap
    have hCapU : (UInt64.ofNat ordersCapacity).toNat = ordersCapacity :=
      toNat_ofNat_lt (by rw [size_eq]; omega)
    apply OrdersAt.frame_region hOrders32 hOrders48
      (capacity := UInt64.ofNat ordersCapacity)
      (by rw [hCapU]; exact hCap) hUpdate.pages ?_ hState.ordersRep
    intro a _ ha
    apply hUpdate.bytesBefore
    rw [hTopNat]
    rw [hCapU] at ha
    omega
  · intro a ha
    rw [hUpdate.bytesBefore a (by rw [hTopNat]; omega)]
    exact hState.bytesBefore a ha

theorem FoldState.step_skip
    {st0 st : Store Unit} {os : List OrderL}
    {side orders : UInt64} {g0n : Nat} {g2 : UInt64} {k : Nat}
    (hState : FoldState st0 os side orders g0n g2 st k)
    (hkos : k < os.length)
    (hSide : ¬os[k]!.oside = side) :
    FoldState st0 os side orders g0n g2 st (k + 1) := by
  have hLevels : foldLevels os side (k + 1) = foldLevels os side k := by
    rw [foldLevels_succ os side k hkos, if_neg hSide]
  have hTop : foldTop os side g0n (k + 1) = foldTop os side g0n k := by
    simp only [foldTop]
    rw [if_neg hSide]
  have hRoot : foldRoot os side g0n (k + 1) = foldRoot os side g0n k := by
    simp only [foldRoot]
    rw [if_neg hSide]
  have hCap : foldCap os side (k + 1) = foldCap os side k := by
    simp only [foldCap]
    rw [if_neg hSide]
  have hMatch : matchCount os side (k + 1) = matchCount os side k := by
    rw [matchCount_succ os side k hkos, if_neg hSide]
    omega
  refine {
    pages := hState.pages
    global0 := by rw [hTop]; exact hState.global0
    global1 := hState.global1
    global2 := by rw [hMatch]; exact hState.global2
    resultOwned := by
      rw [hLevels, hRoot, hCap]
      exact hState.resultOwned
    ordersRep := hState.ordersRep
    bytesBefore := hState.bytesBefore }

end Project.ClobDepth.Func6Loop
