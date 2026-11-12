import Verified.Wasi.ReadAllLoop
import Verified.Wasi.ReadAllCost
import Verified.Wasi.ReadAllocation

/-! The code of `readAll` from the limit on the stack to the errno, root, and length on the stack:
the test of the limit, the allocation of the buffer, and the read loop.  The code changes the
locals from `base` to `base + 5` and no others. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- The locals after the iff that holds the overflow branch and the loop: the three words of the
result follow on the stack. -/
theorem wp_readAll_return {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {s : Locals}
    {base : Nat} {errno root length : UInt64} {rest : Program} {Q : Assertion α}
    (hErrno : s.get (base + 1) = some (.i64 errno)) (hRoot : s.get (base + 2) = some (.i64 root))
    (hLength : s.get (base + 3) = some (.i64 length))
    (h : wp m rest Q st { s with values := .i64 length :: .i64 root :: .i64 errno :: s.values }
      env) :
    wp m (.localGet (base + 1) :: .localGet (base + 2) :: .localGet (base + 3) :: rest) Q st s
      env := by
  simpa only [wp_localGet_cons, Locals.get_values, hErrno, hRoot, hLength] using h

theorem wp_get_add {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {s : Locals}
    {a : Nat} {x y : UInt64} {rest : Program} {Q : Assertion α}
    (hA : s.get a = some (.i64 x))
    (h : wp m rest Q st { s with values := .i64 (x + y) :: s.values } env) :
    wp m (.localGet a :: .constI64 y :: .addI64 :: rest) Q st s env := by
  simpa only [wp_localGet_cons, hA, wp_constI64_cons, wp_addI64_cons] using h

theorem wp_readAll_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {limit : UInt64} {s : Locals}
    {base : Nat} {values : List Value} {rest : Program} {Q : Assertion (Observed World)}
    {aborts : Bool}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hRoom : limit.toNat < 4294963200 → aborts = false →
      heap.Room (PureTransport.erase initial) source (allocSize (limit + 4096)))
    (hResource : aborts = true → ∀ final : Store (Observed World),
      final.host = initial.host → Q (.Trap final "unreachable"))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (finalLocals : Locals)
      (root length : UInt64) (result : LeanExe.Wasi.ReadResult) (trace : List Event),
      Exec (observedHost host) (readAll limit) initial.host trace (.returned result) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap' (PureTransport.erase final) root length result.bytes →
      heap'.top.toNat ≤ heap.top.toNat + readAllCost limit →
      Frame base s finalLocals →
      wp target rest Q final
        { finalLocals with values := .i64 length :: .i64 root :: .i64 result.errno :: values } env)
    (hTrap : ∀ (heap' : Heap) (final : Store (Observed World)) (root : UInt64)
      (message : String) (trace : List Event),
      Exec (observedHost host) (readAll limit) initial.host trace (.trapped message) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      heap'.top.toNat ≤ heap.top.toNat + readAllCost limit → Q (.Trap final message)) :
    wp target (readAllCodeWith calls base ++ rest) Q initial { s with values := .i64 limit :: values }
      env := by
  let s0 : Locals := { s with values := values }
  have hLow0 : s0.params.length ≤ base := hLow
  have hHigh0 : base + 6 ≤ s0.positions := hHigh
  have outside0 : ReadAllOutside base s0 s0 := ReadAllOutside.refl base s0
  have bound := fun i (hi : base ≤ i) (hi' : i < base + 6) =>
    outside0.bounds hLow0 hHigh0 hi hi'
  simp only [readAllCodeWith, List.cons_append]
  refine wp_localSet_local (s := s) (vs := values) (bound base le_rfl (by omega)).1
    (bound base le_rfl (by omega)).2 ?_
  let s1 := setLocal s0 base (.i64 limit)
  have outside1 : ReadAllOutside base s0 s1 := outside0.set hLow0 le_rfl (by omega)
  have limit1 : s1.get base = some (.i64 limit) :=
    Locals.get_setLocal_same (bound base le_rfl (by omega)).1 (bound base le_rfl (by omega)).2
  change wp target _ Q initial s1 env
  simp only [wp_localGet_cons, limit1, wp_constI64_cons, wp_geUI64_cons]
  refine wp_iff_cons rfl ?_
  by_cases hLarge : (4294963200 : UInt64) ≤ limit
  · -- The limit leaves no room for the buffer: errno 61 and no bytes.
    have hLargeNat : ¬limit.toNat < 4294963200 := by
      rw [UInt64.le_iff_toNat_le] at hLarge
      simp only [UInt64.reduceToNat] at hLarge
      omega
    simp (config := { decide := true }) only [ge_iff_le, hLarge, ↓reduceIte]
    rw [readAllOverflowCode]
    refine wp_set_word (outside1.bounds hLow0 hHigh0 (i := base + 1) (by omega) (by omega)).1
      (outside1.bounds hLow0 hHigh0 (i := base + 1) (by omega) (by omega)).2 ?_
    let s2 := setLocal s1 (base + 1) (.i64 61)
    have outside2 : ReadAllOutside base s0 s2 := outside1.set hLow0 (by omega) (by omega)
    change wp target _ _ initial s2 env
    refine wp_set_word (outside2.bounds hLow0 hHigh0 (i := base + 2) (by omega) (by omega)).1
      (outside2.bounds hLow0 hHigh0 (i := base + 2) (by omega) (by omega)).2 ?_
    let s3 := setLocal s2 (base + 2) (.i64 0)
    have outside3 : ReadAllOutside base s0 s3 := outside2.set hLow0 (by omega) (by omega)
    change wp target _ _ initial s3 env
    refine wp_set_word (outside3.bounds hLow0 hHigh0 (i := base + 3) (by omega) (by omega)).1
      (outside3.bounds hLow0 hHigh0 (i := base + 3) (by omega) (by omega)).2 ?_
    let s4 := setLocal s3 (base + 3) (.i64 0)
    have outside4 : ReadAllOutside base s0 s4 := outside3.set hLow0 (by omega) (by omega)
    have hLow4 := (outside3.bounds hLow0 hHigh0 (i := base + 3) (by omega) (by omega)).1
    have hHigh4 := (outside3.bounds hLow0 hHigh0 (i := base + 3) (by omega) (by omega)).2
    have hLow3 := (outside2.bounds hLow0 hHigh0 (i := base + 2) (by omega) (by omega)).1
    have hHigh3 := (outside2.bounds hLow0 hHigh0 (i := base + 2) (by omega) (by omega)).2
    have hLow2 := (outside1.bounds hLow0 hHigh0 (i := base + 1) (by omega) (by omega)).1
    have hHigh2 := (outside1.bounds hLow0 hHigh0 (i := base + 1) (by omega) (by omega)).2
    have errno4 : s4.get (base + 1) = some (.i64 61) := by
      change (setLocal s3 (base + 3) _).get (base + 1) = _
      rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_setLocal_ne hLow3 (by omega)]
      exact Locals.get_setLocal_same hLow2 hHigh2
    have root4 : s4.get (base + 2) = some (.i64 0) := by
      change (setLocal s3 (base + 3) _).get (base + 2) = _
      rw [Locals.get_setLocal_ne hLow4 (by omega)]
      exact Locals.get_setLocal_same hLow3 hHigh3
    have length4 : s4.get (base + 3) = some (.i64 0) := Locals.get_setLocal_same hLow4 hHigh4
    change wp target [] _ initial s4 env
    rw [wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    refine wp_readAll_return (s := { s4 with values := values })
      (by simpa only [Locals.get_values] using errno4)
      (by simpa only [Locals.get_values] using root4)
      (by simpa only [Locals.get_values] using length4) ?_
    have exec : Exec (observedHost host) (readAll limit) initial.host []
        (.returned ⟨61, LeanExe.Bytes.empty⟩) initial.host := by
      simp only [readAll, hLargeNat, ↓reduceIte]
      exact .pure _ _
    refine hNext heap initial { s4 with values := values } 0 0 ⟨61, LeanExe.Bytes.empty⟩ [] exec
      ?_ (Bytes.Rep.empty heap _) (by omega) ((outside4.values _).frame hHigh0).values
    simpa only [Bytes.regions, ↓reduceIte] using
      Step.refl hHeap (fun region => regionsDisjoint region ABI.scratch)
  · -- The buffer and the read loop.
    have hSmall : limit.toNat < 4294963200 := by
      rw [UInt64.le_iff_toNat_le] at hLarge
      simp only [UInt64.reduceToNat] at hLarge
      omega
    have hCapacity := readAll_capacity_toNat hSmall
    simp (config := { decide := true }) only [ge_iff_le, hLarge, ↓reduceIte]
    rw [readAllValidCodeWith]
    simp only [List.cons_append, List.nil_append]
    refine wp_get_add limit1 ?_
    refine wp_alloc_frame_with (s := s1) (values := values) runtime layout profile hImports sourceHost
      hHeap (by omega) hCap (hRoom hSmall)
      (fun allowed final world => hResource allowed final world) ?_
    intro before hFits hStore hWorld
    obtain ⟨hAllocate, hBuffer, hRoomBuffer, hTop⟩ :=
      read_allocation_buffer hHeap (by omega) hFits hStore
    let root := FixedArrayAllocate.root heap.top (allocSize (limit + 4096)) heap.free
    let heap' := heap.allocate (allocSize (limit + 4096))
    have hLow2 := (outside1.bounds hLow0 hHigh0 (i := base + 2) (by omega) (by omega)).1
    have hHigh2 := (outside1.bounds hLow0 hHigh0 (i := base + 2) (by omega) (by omega)).2
    refine wp_localSet_local (s := s1) (vs := values) hLow2 hHigh2 ?_
    let s2 := setLocal s1 (base + 2) (.i64 root)
    have outside2 : ReadAllOutside base s0 s2 := outside1.set hLow0 (by omega) (by omega)
    change wp target _ _ before s2 env
    have hLow3 := (outside2.bounds hLow0 hHigh0 (i := base + 1) (by omega) (by omega)).1
    have hHigh3 := (outside2.bounds hLow0 hHigh0 (i := base + 1) (by omega) (by omega)).2
    refine wp_set_word hLow3 hHigh3 ?_
    let s3 := setLocal s2 (base + 1) (.i64 0)
    have outside3 : ReadAllOutside base s0 s3 := outside2.set hLow0 (by omega) (by omega)
    change wp target _ _ before s3 env
    have hLow4 := (outside3.bounds hLow0 hHigh0 (i := base + 3) (by omega) (by omega)).1
    have hHigh4 := (outside3.bounds hLow0 hHigh0 (i := base + 3) (by omega) (by omega)).2
    refine wp_set_word hLow4 hHigh4 ?_
    let s4 := setLocal s3 (base + 3) (.i64 0)
    have outside4 : ReadAllOutside base s0 s4 := outside3.set hLow0 (by omega) (by omega)
    change wp target _ _ before s4 env
    have hLow5 := (outside4.bounds hLow0 hHigh0 (i := base + 5) (by omega) (by omega)).1
    have hHigh5 := (outside4.bounds hLow0 hHigh0 (i := base + 5) (by omega) (by omega)).2
    refine wp_set_word hLow5 hHigh5 ?_
    let s5 := setLocal s4 (base + 5) (.i64 4096)
    have outside5 : ReadAllOutside base s0 s5 := outside4.set hLow0 (by omega) (by omega)
    change wp target _ _ before s5 env
    have get5 : ∀ j, j ≠ base + 5 → s5.get j = s4.get j := fun j hj =>
      Locals.get_setLocal_ne hLow5 hj
    have get4 : ∀ j, j ≠ base + 3 → s4.get j = s3.get j := fun j hj =>
      Locals.get_setLocal_ne hLow4 hj
    have get3 : ∀ j, j ≠ base + 1 → s3.get j = s2.get j := fun j hj =>
      Locals.get_setLocal_ne hLow3 hj
    have get2 : ∀ j, j ≠ base + 2 → s2.get j = s1.get j := fun j hj =>
      Locals.get_setLocal_ne hLow2 hj
    have hStart : Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase before) [block (PureTransport.erase before) root] :=
      hAllocate.mono (fun _ _ => True.intro) (fun _ member => member)
    have hTopCost : heap'.top.toNat ≤ heap.top.toNat + readAllCost limit := by
      rw [readAllCost_positive hSmall]
      exact hTop
    have facts : ReadAllFacts host base limit root initial heap heap' s0 LeanExe.Bytes.empty []
        (limit.toNat + 2) 0 before s5 := by
      refine ⟨?_, by simp only [LeanExe.Bytes.empty, ByteArray.size_empty]; omega,
        hBuffer.toEmpty, Nat.zero_le _, by rw [← hCapacity]; exact hRoomBuffer, hStart,
        outside5, rfl, ?_, ?_, ?_, Locals.get_setLocal_same hLow5 hHigh5⟩
      · rw [← hWorld]
        exact ReadAllRest.initial before.host hSmall
      · rw [get5 _ (by omega), get4 _ (by omega), get3 _ (by omega), get2 _ (by omega)]
        exact limit1
      · rw [get5 _ (by omega), get4 _ (by omega), get3 _ (by omega)]
        exact Locals.get_setLocal_same hLow2 hHigh2
      · rw [get5 _ (by omega)]
        exact Locals.get_setLocal_same hLow4 hHigh4
    rw [← List.append_nil (readAllLoopCode base)]
    refine wp_readAll_loop_with hImports hHost hLow0 hHigh0 ?_ ?_ facts
    · intro final si result trace exec step rep outside stack errnoLocal rootLocal lengthLocal
      rw [wp_nil]
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      refine wp_readAll_return (s := { si with values := values })
        (by simpa only [Locals.get_values] using errnoLocal)
        (by simpa only [Locals.get_values] using rootLocal)
        (by simpa only [Locals.get_values] using lengthLocal) ?_
      exact hNext heap' final { si with values := values } root _ result trace exec step rep
        hTopCost ((outside.values _).frame hHigh0).values
    · intro final message trace exec step
      exact hTrap heap' final root message trace exec step hTopCost

theorem wp_readAll {World : Type} {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {limit : UInt64} {s : Locals}
    {base : Nat} {values : List Value} {rest : Program} {Q : Assertion (Observed World)}
    {aborts : Bool}
    (hHost : env.Satisfies target (hostSpec host))
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hRoom : limit.toNat < 4294963200 → aborts = false →
      heap.Room (PureTransport.erase initial) source (allocSize (limit + 4096)))
    (hResource : aborts = true → ∀ final : Store (Observed World),
      final.host = initial.host → Q (.Trap final "unreachable"))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (finalLocals : Locals)
      (root length : UInt64) (result : LeanExe.Wasi.ReadResult) (trace : List Event),
      Exec (observedHost host) (readAll limit) initial.host trace (.returned result) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap' (PureTransport.erase final) root length result.bytes →
      heap'.top.toNat ≤ heap.top.toNat + readAllCost limit →
      Frame base s finalLocals →
      wp target rest Q final
        { finalLocals with values := .i64 length :: .i64 root :: .i64 result.errno :: values } env)
    (hTrap : ∀ (heap' : Heap) (final : Store (Observed World)) (root : UInt64)
      (message : String) (trace : List Event),
      Exec (observedHost host) (readAll limit) initial.host trace (.trapped message) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      heap'.top.toNat ≤ heap.top.toNat + readAllCost limit → Q (.Trap final message)) :
    wp target (readAllCode base ++ rest) Q initial { s with values := .i64 limit :: values }
      env := by
  layout_instance wp_readAll_with

end Verified.Wasi
