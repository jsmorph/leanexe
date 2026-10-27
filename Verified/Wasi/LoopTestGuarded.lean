import Verified.Wasi.LoopContext
import Verified.Wasi.Return

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem wp_loopTestGuarded {World : Type} {S : List Sig} {context : List Ty} {type : Ty}
    {source target : Wasm.Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
    {fits : Fits S} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {pool : Bytes.LiteralPool} {test : Expr S (type :: .word :: context) .bool}
    {env : Env context} {slots : List Slot} {liveIn live testLive : Nat → Bool}
    {state : type.denote} {index : UInt64} {words : List Value} {params : List Value}
    {heap currentHeap : Heap} {initial current : Store World} {locals currentLocals : Locals}
    {h base : Nat} {rest : Program} {Q : Assertion World}
    (runtime : Runtime source) (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    (spec : CodeSpec source funs flags bounds fits sourceHost params test
      (.cons state (.cons (t := .word) index env))
      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots) [] testLive pool)
    (form : Encoding.ProgramForm (test.code (pool := pool) h
      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      (base + 2 + type.width) testLive))
    (closed : Relocation.programClosed source.funcs.length (test.code (pool := pool) h
      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      (base + 2 + type.width) testLive) = true)
    (positions : currentLocals.positions = h) (parameters : currentLocals.params = params)
    (after : After env slots liveIn live base heap initial locals (.value type) state
      currentHeap current currentLocals words)
    (scratch : Holds.ApartFrom env slots live (PureTransport.erase current) currentLocals ABI.scratch)
    (static : pool.Static currentHeap (PureTransport.erase current))
    (held : LocalsHold currentLocals (base + 2) type.types words)
    (counter : currentLocals.get (base + 1) = some (.i64 index))
    (selected : ∀ i, (testLive (i + 2) || test.uses (i + 2)) = true → live i = true)
    (cap : (PureTransport.erase current).memoryCap source 0 ≤ 65535)
    (low : currentLocals.params.length ≤ base + 2 + type.width)
    (room : base + 2 + type.width + max test.width (copyWidth .bool) ≤ h)
    (place : test.placeArgs = true)
    (resource : (!(test.fits funs fits (.cons state (.cons (t := .word) index env))) || !decide
        (currentHeap.Within (PureTransport.erase current) source
          (returnCost funs flags bounds test (.cons state (.cons (t := .word) index env))
            (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots) [] testLive
            (PureTransport.erase current) currentLocals))) = true →
      ∀ final : Store World, final.host = current.host → Q (.Trap final "unreachable"))
    (next : ∀ finalHeap final finalLocals,
      After env slots liveIn live base heap initial locals (.value type) state
        finalHeap final finalLocals words →
      Frame (base + 2 + type.width) currentLocals finalLocals →
      final.host = current.host →
      (test.fits funs fits (.cons state (.cons (t := .word) index env)) = true →
        finalHeap.top.toNat ≤ currentHeap.top.toNat +
          test.allocs funs flags bounds
            ((⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots).map Slot.mode)
            [] testLive (.cons state (.cons (t := .word) index env))) →
      wp target rest Q final { finalLocals with
        values := .i64 (boolWord (test.denote funs (.cons state (.cons (t := .word) index env)))) ::
          currentLocals.values } targetHost) :
    wp target (Relocation.program (test.code (pool := pool) h
      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      (base + 2 + type.width) testLive) ++ rest) Q current currentLocals targetHost := by
  let testSlots : List Slot :=
    ⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots
  have noCoerce : coerceCode h .bool (test.mode (testSlots.map Slot.mode)) .owned
      (base + 2 + type.width) = [] := by simp [coerceCode, Ty.scalar]
  have testVars := loop_test_holds (live := fun i => testLive i || test.uses i)
    (after.holds.live_mono selected) held after.rep
    (after.apart.live_mono selected) counter
  have testSafe := loop_test_safe (env := env) (state := state) (index := index)
    (slots := slots) (base := base) (live := fun i => testLive i || test.uses i)
    (locals := currentLocals) static
  have execution := wp_return (targetHost := targetHost) runtime layout profile spec
    (by simpa only [noCoerce, List.append_nil, testSlots] using form)
    (by simpa only [noCoerce, List.append_nil, testSlots] using closed)
    positions parameters testVars after.step.at_ testSafe cap low room place
    (rest := rest) (Q := Q) (fun failure final same => resource failure final same)
    (fun finalHeap final finalLocals result tested same top => by
      have resultEq : result =
          [.i64 (boolWord (test.denote funs (.cons state (.cons (t := .word) index env))))] :=
        tested.rep
      subst result
      have frame : Frame base currentLocals finalLocals := tested.frame.mono (by omega)
      have retained := after.loopTest scratch (loop_test_step tested) frame
      have growth : test.fits funs fits (.cons state (.cons (t := .word) index env)) = true →
          finalHeap.top.toNat ≤ currentHeap.top.toNat +
            test.allocs funs flags bounds (testSlots.map Slot.mode) [] testLive
              (.cons state (.cons (t := .word) index env)) := by
        intro fitsTest
        have bound := top fitsTest
        have scalar : coerceCost .bool (test.mode (testSlots.map Slot.mode)) .owned
            (test.denote funs (.cons state (.cons (t := .word) index env))) = 0 := by
          simp [coerceCost, Ty.copyCost]
        dsimp only [testSlots] at scalar ⊢
        simpa only [returnCost, dyingPot_nil, Nat.zero_add, scalar, Nat.add_zero] using bound
      simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] using
        next finalHeap final finalLocals retained tested.frame same growth)
  simpa only [noCoerce, List.append_nil, testSlots] using execution

end Verified.Wasi
