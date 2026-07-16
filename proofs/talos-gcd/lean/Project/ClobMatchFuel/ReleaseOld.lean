import Project.ClobMatchFuel.ReleaseFrame
import Interpreter.Wasm.Wp.Call

/-!
# Consumed-array release block

The common matching branch conditionally releases its prior book and trade
roots after producing replacements.  The first theorem isolates the generated
alias guards and two calls from the fixed-array memory semantics.
-/

namespace Project.ClobMatchFuel.ReleaseOld

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame
  Project.ClobMatchFuel.ReleaseFrame

def releaseOldValuesProg : Wasm.Program :=
  [
  .localGet 19,
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 1 [
    .localGet 19,
    .localGet 44,
    .eqI64,
    .eqz
  ] [
    .const 0
  ],
  .iff 0 1 [
    .localGet 19,
    .localGet 46,
    .eqI64,
    .eqz
  ] [
    .const 0
  ],
  .iff 0 0 [
    .localGet 19,
    .call 18
  ] [],
  .localGet 20,
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 1 [
    .localGet 20,
    .localGet 19,
    .eqI64,
    .eqz
  ] [
    .const 0
  ],
  .iff 0 1 [
    .localGet 20,
    .localGet 44,
    .eqI64,
    .eqz
  ] [
    .const 0
  ],
  .iff 0 1 [
    .localGet 20,
    .localGet 46,
    .eqI64,
    .eqz
  ] [
    .const 0
  ],
  .iff 0 0 [
    .localGet 20,
    .call 18
  ] []
  ]

set_option Elab.async false in
theorem releaseOldValuesProg_calls
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (oldBook oldTrades newBook newTrades : UInt64)
    (bookPost : Store Unit → Prop)
    (tradePost : Store Unit → Store Unit → Prop)
    (hOldBookLocal : base.get 19 = some (.i64 oldBook))
    (hOldTradesLocal : base.get 20 = some (.i64 oldTrades))
    (hNewBookLocal : base.get 44 = some (.i64 newBook))
    (hNewTradesLocal : base.get 46 = some (.i64 newTrades))
    (hValues : base.values = [])
    (hOldBookNonzero : oldBook ≠ 0)
    (hOldBookNewBook : oldBook ≠ newBook)
    (hOldBookNewTrades : oldBook ≠ newTrades)
    (hOldTradesNonzero : oldTrades ≠ 0)
    (hOldTradesOldBook : oldTrades ≠ oldBook)
    (hOldTradesNewBook : oldTrades ≠ newBook)
    (hOldTradesNewTrades : oldTrades ≠ newTrades)
    (hReleaseBook :
      TerminatesWith (m := «module») (id := 18) (initial := st) (env := env)
        [.i64 oldBook] (fun st1 vs => vs = [] ∧ bookPost st1))
    (hReleaseTrades : ∀ st1, bookPost st1 →
      TerminatesWith (m := «module») (id := 18) (initial := st1) (env := env)
        [.i64 oldTrades] (fun st2 vs => vs = [] ∧ tradePost st1 st2))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 st2, bookPost st1 → tradePost st1 st2 →
      wp «module» rest Q st2 base env) :
    wp «module» (releaseOldValuesProg ++ rest) Q st base env := by
  rcases base with ⟨params, locals, values⟩
  dsimp only at hValues
  subst values
  simp only [releaseOldValuesProg, List.cons_append, List.nil_append]
  simp_all only [wp_simp, Locals.get]
  refine wp_iff_cons
    (s := { params, locals, values := [.i32 1] })
    (c := 1) (vs := []) rfl ?_
  rw [if_pos (by decide)]
  simp_all only [wp_simp, Locals.get]
  try simp
  refine wp_iff_cons
    (s := { params, locals, values := [.i32 1] })
    (c := 1) (vs := []) rfl ?_
  rw [if_pos (by decide)]
  simp_all only [wp_simp, Locals.get]
  try simp
  refine wp_iff_cons
    (s := { params, locals, values := [.i32 1] })
    (c := 1) (vs := []) rfl ?_
  rw [if_pos (by decide)]
  simp_all only [wp_simp, Locals.get]
  try simp
  refine wp_call_tw hReleaseBook ?_
  rintro st1 vs ⟨rfl, hBookPost⟩
  simp_all only [wp_simp]
  refine wp_iff_cons
    (s := { params, locals, values := [.i32 1] })
    (c := 1) (vs := []) rfl ?_
  rw [if_pos (by decide)]
  simp_all only [wp_simp, Locals.get]
  try simp
  refine wp_iff_cons
    (s := { params, locals, values := [.i32 1] })
    (c := 1) (vs := []) rfl ?_
  rw [if_pos (by decide)]
  simp_all only [wp_simp, Locals.get]
  try simp
  refine wp_iff_cons
    (s := { params, locals, values := [.i32 1] })
    (c := 1) (vs := []) rfl ?_
  rw [if_pos (by decide)]
  simp_all only [wp_simp, Locals.get]
  try simp
  refine wp_iff_cons
    (s := { params, locals, values := [.i32 1] })
    (c := 1) (vs := []) rfl ?_
  rw [if_pos (by decide)]
  simp_all only [wp_simp, Locals.get]
  try simp
  refine wp_call_tw (hReleaseTrades st1 hBookPost) ?_
  rintro st2 vs ⟨rfl, hTradePost⟩
  wp_run
  try simp
  exact hDone st1 st2 hBookPost hTradePost

set_option Elab.async false in
theorem releaseOwnedArraysProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (oldBook oldBookCapacity oldTrades oldTradesCapacity : UInt64)
    (newBook newBookCapacity newTrades newTradesCapacity : UInt64)
    (g4 g5 : UInt64)
    (oldOrders newOrders : List OrderL)
    (oldTradeValues newTradeValues : List TradeL)
    (nodes : List FreeNode)
    (hOldBookLocal : base.get 19 = some (.i64 oldBook))
    (hOldTradesLocal : base.get 20 = some (.i64 oldTrades))
    (hNewBookLocal : base.get 44 = some (.i64 newBook))
    (hNewTradesLocal : base.get 46 = some (.i64 newTrades))
    (hValues : base.values = [])
    (hOldBook48 : 48 ≤ oldBook.toNat)
    (hOldBook32 :
      oldBook.toNat + oldBookCapacity.toNat < 4294967296)
    (hOldBookFit :
      oldBook.toNat + oldBookCapacity.toNat ≤ st.mem.pages * 65536)
    (hOldBookCapacity :
      fixedArrayBytes oldOrders.length 5 ≤ oldBookCapacity.toNat)
    (hOldTrades48 : 48 ≤ oldTrades.toNat)
    (hOldTrades32 :
      oldTrades.toNat + oldTradesCapacity.toNat < 4294967296)
    (hOldTradesFit :
      oldTrades.toNat + oldTradesCapacity.toNat ≤ st.mem.pages * 65536)
    (hOldTradesCapacity :
      fixedArrayBytes oldTradeValues.length 4 ≤ oldTradesCapacity.toNat)
    (hNewBook48 : 48 ≤ newBook.toNat)
    (hNewBook32 : newBook.toNat + newBookCapacity.toNat < 4294967296)
    (hNewBookCapacity :
      fixedArrayBytes newOrders.length 5 ≤ newBookCapacity.toNat)
    (hNewTrades48 : 48 ≤ newTrades.toNat)
    (hNewTrades32 :
      newTrades.toNat + newTradesCapacity.toNat < 4294967296)
    (hNewTradesCapacity :
      fixedArrayBytes newTradeValues.length 4 ≤ newTradesCapacity.toNat)
    (hOldBookOwned :
      OwnedOrderArrayAt st oldBook oldBookCapacity oldOrders)
    (hOldTradesOwned :
      OwnedTradeArrayAt st oldTrades oldTradesCapacity oldTradeValues)
    (hNewBookOwned :
      OwnedOrderArrayAt st newBook newBookCapacity newOrders)
    (hNewTradesOwned :
      OwnedTradeArrayAt st newTrades newTradesCapacity newTradeValues)
    (hOldBookOldTrades :
      regionsDisjoint (fixedArrayRegion oldBook oldBookCapacity)
        (fixedArrayRegion oldTrades oldTradesCapacity))
    (hOldBookNewBook :
      regionsDisjoint (fixedArrayRegion oldBook oldBookCapacity)
        (fixedArrayRegion newBook newBookCapacity))
    (hOldBookNewTrades :
      regionsDisjoint (fixedArrayRegion oldBook oldBookCapacity)
        (fixedArrayRegion newTrades newTradesCapacity))
    (hOldTradesNewBook :
      regionsDisjoint (fixedArrayRegion oldTrades oldTradesCapacity)
        (fixedArrayRegion newBook newBookCapacity))
    (hOldTradesNewTrades :
      regionsDisjoint (fixedArrayRegion oldTrades oldTradesCapacity)
        (fixedArrayRegion newTrades newTradesCapacity))
    (hOldBookNodes : ∀ node ∈ nodes,
      regionsDisjoint (fixedArrayRegion oldBook oldBookCapacity) node.region)
    (hOldTradesNodes : ∀ node ∈ nodes,
      regionsDisjoint (fixedArrayRegion oldTrades oldTradesCapacity)
        node.region)
    (hList : FreeListAt st.mem nodes)
    (hg1 : st.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hg4 : st.globals.globals[4]? = some (.i64 g4))
    (hg5 : st.globals.globals[5]? = some (.i64 g5))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 st2,
      st1.mem = fixedArrayReleaseMem st oldBook (freeHead nodes) →
      st1.globals.globals = fixedArrayReleaseGlobals st oldBook g4 g5 →
      st2.mem = fixedArrayReleaseMem st1 oldTrades oldBook →
      st2.globals.globals =
        fixedArrayReleaseGlobals st1 oldTrades (g4 + 1) (g5 + 1) →
      OwnedOrderArrayAt st2 newBook newBookCapacity newOrders →
      OwnedTradeArrayAt st2 newTrades newTradesCapacity newTradeValues →
      FreeListAt st2.mem
        (releasedNode oldTrades oldTradesCapacity ::
          releasedNode oldBook oldBookCapacity :: nodes) →
      wp «module» rest Q st2 base env) :
    wp «module» (releaseOldValuesProg ++ rest) Q st base env := by
  have hOldBookContent32 :
      oldBook.toNat + fixedArrayBytes oldOrders.length 5 < 4294967296 := by
    omega
  have hOldTradesContent32 :
      oldTrades.toNat + fixedArrayBytes oldTradeValues.length 4 <
        4294967296 := by
    omega
  have hNewBookContent32 :
      newBook.toNat + fixedArrayBytes newOrders.length 5 < 4294967296 := by
    omega
  have hNewTradesContent32 :
      newTrades.toNat + fixedArrayBytes newTradeValues.length 4 <
        4294967296 := by
    omega
  have hOldBookLength32 : oldOrders.length < 4294967296 := by
    unfold fixedArrayBytes at hOldBookContent32
    omega
  have hOldTradesLength32 : oldTradeValues.length < 4294967296 := by
    unfold fixedArrayBytes at hOldTradesContent32
    omega
  have hGlobalsLength : 5 < st.globals.globals.length :=
    (List.getElem?_eq_some_iff.mp hg5).1
  apply releaseOldValuesProg_calls env st base oldBook oldTrades newBook
    newTrades
    (fun st1 =>
      st1.mem = fixedArrayReleaseMem st oldBook (freeHead nodes) ∧
      st1.globals.globals = fixedArrayReleaseGlobals st oldBook g4 g5)
    (fun st1 st2 =>
      st2.mem = fixedArrayReleaseMem st1 oldTrades oldBook ∧
      st2.globals.globals =
        fixedArrayReleaseGlobals st1 oldTrades (g4 + 1) (g5 + 1))
    hOldBookLocal hOldTradesLocal hNewBookLocal hNewTradesLocal hValues
  · intro hzero
    subst oldBook
    simp at hOldBook48
  · exact fixedArrayRoots_ne_of_regionsDisjoint hOldBookNewBook
  · exact fixedArrayRoots_ne_of_regionsDisjoint hOldBookNewTrades
  · intro hzero
    subst oldTrades
    simp at hOldTrades48
  · exact (fixedArrayRoots_ne_of_regionsDisjoint hOldBookOldTrades).symm
  · exact fixedArrayRoots_ne_of_regionsDisjoint hOldTradesNewBook
  · exact fixedArrayRoots_ne_of_regionsDisjoint hOldTradesNewTrades
  · apply func18_frees_fixed_array_zero_mask env st oldBook oldBookCapacity
      (freeHead nodes) g4 g5 oldOrders.length 5 hOldBookLength32 (by decide)
      hOldBook48 (by omega)
    · have hFit := hOldBookOwned.2.1.2
      rw [Nat.mod_eq_of_lt (by omega)] at hFit
      exact hFit
    · simpa using hOldBookOwned.1
    · simpa only [toUInt32_eq_ofNat] using hOldBookOwned.2.1.1
    · exact hg1
    · exact hg4
    · exact hg5
  · intro st1 hBookPost
    rcases hBookPost with ⟨hMem1, hGlobals1⟩
    have hOldTradesOwned1 :
        OwnedTradeArrayAt st1 oldTrades oldTradesCapacity oldTradeValues :=
      ReleaseFrame.OwnedTradeArrayAt.frame_release hOldBook48 hOldBook32
        hOldTrades48 hOldTradesContent32 hOldTradesCapacity
        hOldBookOldTrades hMem1 hOldTradesOwned
    have hg1First : st1.globals.globals[1]? = some (.i64 oldBook) := by
      rw [hGlobals1]
      simp [fixedArrayReleaseGlobals,
        (by omega : 1 < st.globals.globals.length)]
    have hg4First : st1.globals.globals[4]? = some (.i64 (g4 + 1)) := by
      rw [hGlobals1]
      simp [fixedArrayReleaseGlobals,
        (by omega : 4 < st.globals.globals.length)]
    have hg5First : st1.globals.globals[5]? = some (.i64 (g5 + 1)) := by
      rw [hGlobals1]
      simp [fixedArrayReleaseGlobals, hGlobalsLength]
    apply func18_frees_fixed_array_zero_mask env st1 oldTrades
      oldTradesCapacity oldBook (g4 + 1) (g5 + 1)
      oldTradeValues.length 4 hOldTradesLength32 (by decide) hOldTrades48
      (by omega)
    · have hFit := hOldTradesOwned1.2.1.2
      rw [Nat.mod_eq_of_lt (by omega)] at hFit
      exact hFit
    · simpa using hOldTradesOwned1.1
    · simpa only [toUInt32_eq_ofNat] using hOldTradesOwned1.2.1.1
    · exact hg1First
    · exact hg4First
    · exact hg5First
  · intro st1 st2 hBookPost hTradePost
    rcases hBookPost with ⟨hMem1, hGlobals1⟩
    rcases hTradePost with ⟨hMem2, hGlobals2⟩
    have hOldTradesOwned1 :
        OwnedTradeArrayAt st1 oldTrades oldTradesCapacity oldTradeValues :=
      ReleaseFrame.OwnedTradeArrayAt.frame_release hOldBook48 hOldBook32
        hOldTrades48 hOldTradesContent32 hOldTradesCapacity
        hOldBookOldTrades hMem1 hOldTradesOwned
    have hNewBookOwned1 :
        OwnedOrderArrayAt st1 newBook newBookCapacity newOrders :=
      ReleaseFrame.OwnedOrderArrayAt.frame_release hOldBook48 hOldBook32
        hNewBook48 hNewBookContent32 hNewBookCapacity hOldBookNewBook hMem1
        hNewBookOwned
    have hNewTradesOwned1 :
        OwnedTradeArrayAt st1 newTrades newTradesCapacity newTradeValues :=
      ReleaseFrame.OwnedTradeArrayAt.frame_release hOldBook48 hOldBook32
        hNewTrades48 hNewTradesContent32 hNewTradesCapacity
        hOldBookNewTrades hMem1 hNewTradesOwned
    have hNewBookOwned2 :
        OwnedOrderArrayAt st2 newBook newBookCapacity newOrders :=
      ReleaseFrame.OwnedOrderArrayAt.frame_release hOldTrades48 hOldTrades32
        hNewBook48 hNewBookContent32 hNewBookCapacity hOldTradesNewBook hMem2
        hNewBookOwned1
    have hNewTradesOwned2 :
        OwnedTradeArrayAt st2 newTrades newTradesCapacity newTradeValues :=
      ReleaseFrame.OwnedTradeArrayAt.frame_release hOldTrades48 hOldTrades32
        hNewTrades48 hNewTradesContent32 hNewTradesCapacity
        hOldTradesNewTrades hMem2 hNewTradesOwned1
    have hList1Mem := freeListAt_fixedArrayReleaseMem st oldBook
      oldBookCapacity nodes hOldBook48 hOldBook32 hOldBookFit
      hOldBookOwned.1.2.2.1 hOldBookNodes hList
    have hList1 : FreeListAt st1.mem
        (releasedNode oldBook oldBookCapacity :: nodes) := by
      rw [hMem1]
      exact hList1Mem
    have hOldTradesFit1 :
        oldTrades.toNat + oldTradesCapacity.toNat ≤
          st1.mem.pages * 65536 := by
      rw [hMem1]
      exact hOldTradesFit
    have hOldTradesNodes1 : ∀ node ∈
        releasedNode oldBook oldBookCapacity :: nodes,
        regionsDisjoint (fixedArrayRegion oldTrades oldTradesCapacity)
          node.region := by
      intro node hmem
      rcases List.mem_cons.mp hmem with rfl | htail
      · simpa [releasedNode, fixedArrayRegion, FreeNode.region] using
          regionsDisjoint_symm hOldBookOldTrades
      · exact hOldTradesNodes node htail
    have hList2Mem := freeListAt_fixedArrayReleaseMem st1 oldTrades
      oldTradesCapacity (releasedNode oldBook oldBookCapacity :: nodes)
      hOldTrades48 hOldTrades32 hOldTradesFit1
      hOldTradesOwned1.1.2.2.1 hOldTradesNodes1 hList1
    have hList2 : FreeListAt st2.mem
        (releasedNode oldTrades oldTradesCapacity ::
          releasedNode oldBook oldBookCapacity :: nodes) := by
      rw [hMem2]
      exact hList2Mem
    exact hDone st1 st2 hMem1 hGlobals1 hMem2 hGlobals2 hNewBookOwned2
      hNewTradesOwned2 hList2

end Project.ClobMatchFuel.ReleaseOld
