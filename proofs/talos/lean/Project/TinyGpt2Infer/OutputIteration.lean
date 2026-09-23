import Project.TinyGpt2Infer.OutputLogitExec
import Project.TinyGpt2Infer.OutputCapacityExec
import Project.TinyGpt2Infer.OutputAppendExec
import Project.TinyGpt2Infer.OutputAdvanceExec
import Project.TinyGpt2.OutputModel

namespace Project.TinyGpt2Infer.Spec
open Wasm Project.TinyGpt2 Project.ProofKit ArrayPushLayout

structure OutputLoopLocals (pointer empty : UInt64) (x : Row) (root : UInt64)
    (count : Nat) (frame : Locals) : Prop extends OutputSaved pointer empty x frame where
  current : frame.get 23 = some (.i64 root)
  output : frame.get 24 = some (.i64 root)
  counter : frame.get 48 = some (.i64 (UInt64.ofNat count))
  owned : frame.get 69 = some (.i64 (if count = 0 then 0 else 1))

theorem output_iteration_shape : outputBody.drop 4 =
    (outputBody.drop 4).take 29 ++ (outputBody.drop 33).take 34 ++
      (outputBody.drop 67).take 64 ++ outputBody.drop 131 := by
  have hSplit (start count : Nat) : outputBody.drop start =
      (outputBody.drop start).take count ++ outputBody.drop (start + count) := by
    simpa only [List.drop_drop] using (List.take_append_drop count (outputBody.drop start)).symm
  calc
    outputBody.drop 4 = (outputBody.drop 4).take 29 ++ outputBody.drop 33 := hSplit 4 29
    _ = (outputBody.drop 4).take 29 ++
        ((outputBody.drop 33).take 34 ++ outputBody.drop 67) :=
      congrArg ((outputBody.drop 4).take 29 ++ ·) (hSplit 33 34)
    _ = (outputBody.drop 4).take 29 ++ ((outputBody.drop 33).take 34 ++
        ((outputBody.drop 67).take 64 ++ outputBody.drop 131)) :=
      congrArg (fun rest => (outputBody.drop 4).take 29 ++ ((outputBody.drop 33).take 34 ++ rest))
        (hSplit 67 64)
    _ = _ := by simp only [List.append_assoc]

theorem output_iteration_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (pointer empty : UInt64) (weights : Array UInt64) (x : Row) (start count : Nat)
    (hLocals : OutputLoopLocals pointer empty x (node start count).root count frame)
    (hState : OutputMemory.State start count initial)
    (hInput : UInt64Array.At initial (node start count).root (logitPrefix weights x count))
    (hWeights : UInt64Array.At initial pointer weights) (hSize : 2488 ≤ weights.size)
    (hCount : count < 256)
    (hFit : top start (count + 1) < 4294967296)
    (hMemory : top start (count + 1) ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap module 0)
    (Q : Assertion Unit)
    (hNext : ∀ (final : Store Unit) (finalFrame : Locals),
      OutputMemory.State start (count + 1) final →
      UInt64Array.At final (node start (count + 1)).root (logitPrefix weights x (count + 1)) →
      OutputLoopLocals pointer empty x (node start (count + 1)).root (count + 1) finalFrame →
      final.mem.pages = initial.mem.pages →
      (∀ address : Nat, address < start → final.mem.bytes address = initial.mem.bytes address) →
      final = { initial with mem := final.mem, globals := final.globals } →
      Q (.Break 0 final finalFrame)) :
    wp module (outputBody.drop 4) Q initial frame env := by
  have hToken : (UInt64.ofNat count).toNat = count := by
    apply UInt64.toNat_ofNat_of_lt'
    change count < 18446744073709551616
    omega
  rw [output_iteration_shape]
  simp only [List.append_assoc]
  apply output_logit_spec env initial frame pointer empty (node start count).root
    (UInt64.ofNat count) weights x hLocals.toOutputSaved hLocals.output hLocals.counter
    hWeights hSize (by rw [hToken]; exact hCount)
  let value := logit weights x (UInt64.ofNat count)
  let logged := outputLogitFrame frame pointer (node start count).root (UInt64.ofNat count) value x
  have hLogged : OutputSaved pointer empty x logged := outputLogitFrame_saved hLocals.toOutputSaved _ _ _
  obtain ⟨hValue, hOutput, hCurrent, _, hCounter, hOwned⟩ :=
    outputLogitFrame_get frame pointer (node start count).root (UInt64.ofNat count) value x
      hLocals.params hLocals.locals
  apply output_capacity_spec env initial logged pointer empty (node start count).root value
    (logitPrefix weights x count) x count hLogged hOutput hValue hInput
    (logitPrefix_size weights x count) hCount
  let capacityFrame := outputCapacityFrame logged (node start count).root value count
  have hCapacity : OutputSaved pointer empty x capacityFrame := outputCapacityFrame_saved hLogged _ _ _
  obtain ⟨hSource, hVal, hLength, hCopyCount, hNextLength, hNeed, hCur, _, hCtr, hOwn⟩ :=
    outputCapacityFrame_get logged (node start count).root value count hLogged.params hLogged.locals
  apply output_append_spec env initial capacityFrame pointer empty value x start count
    (logitPrefix weights x count) hCapacity hState hInput (logitPrefix_size weights x count)
    hSource hCopyCount hLength hVal hNextLength hNeed
    (hCur.trans (hCurrent.trans hLocals.current))
    (hOwn.trans (hOwned.trans hLocals.owned)) hFit hMemory hPages hCap
  intro final released hFinal hArray hReleased hCur' hOut' hCtr' hOwn' hPages' hBytes hStore
  have hCounter' : released.get 48 = some (.i64 (UInt64.ofNat count)) :=
    hCtr'.trans (hCtr.trans (hCounter.trans hLocals.counter))
  apply output_advance_spec env final released count hCount hReleased.params hReleased.locals
    hReleased.values hCounter' hReleased.step
  have hAdvanced := outputAdvanceFrame_saved hReleased count
  obtain ⟨hCur'', hOut'', hCtr'', hOwn''⟩ :=
    outputAdvanceFrame_get released count hReleased.params hReleased.locals
  apply hNext final (outputAdvanceFrame released count) hFinal
    (by simpa only [logitPrefix_succ] using hArray)
    ⟨hAdvanced, hCur''.trans hCur', hOut''.trans hOut', hCtr'', ?_⟩ hPages' hBytes hStore
  simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] using hOwn''.trans hOwn'

#print axioms output_iteration_spec
end Project.TinyGpt2Infer.Spec
