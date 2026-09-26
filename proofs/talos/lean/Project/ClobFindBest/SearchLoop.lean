import Project.ClobFindBest.SearchStep
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

namespace Project.ClobFindBest.SearchLoop
open Wasm Project.Common Project.Clob Project.ClobFindBest.Model Project.ClobFindBest.Helpers
  Project.ClobFindBest.SearchFrame Project.ClobFindBest.SearchProgram
  Project.ClobFindBest.SearchAdvance
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

structure Frame (s : Locals) (fuel owner ptr : UInt64) (taker : OrderL) (k : Nat)
    (best : Option Nat) (tag payload done : UInt64) : Prop where
  params : s.params = params fuel owner ptr taker k best
  locals : s.locals.length = 56
  values : s.values = []
  owner : s.locals[0]? = some (.i64 0)
  tag : s.locals[1]? = some (.i64 tag)
  payload : s.locals[2]? = some (.i64 payload)
  done : s.locals[3]? = some (.i64 done)

def Invariant (st0 : Store Unit) (owner ptr : UInt64) (os : List OrderL)
    (taker : OrderL) : AssertionF Unit := fun st s => st=st0 ∧
  ∃ k fuel tag payload done, k ≤ os.length ∧
    Frame s fuel owner ptr taker k (bestPrefixL os taker k) tag payload done ∧
    ((done=0 ∧ fuel=UInt64.ofNat (os.length+1-k)) ∨
      (done=1 ∧ k=os.length ∧ tag=optionTag (bestPrefixL os taker os.length) ∧
        payload=optionPayload (bestPrefixL os taker os.length)))

def measure (_ : Store Unit) (s : Locals) : Nat :=
  match s.params[0]?, s.locals[3]? with
  | some (Value.i64 fuel), some (Value.i64 done) => 2*fuel.toNat + (if done=0 then 1 else 0)
  | _, _ => 0

def entryFrame (owner ptr : UInt64) (os : List OrderL) (taker : OrderL) : Locals :=
  { params := params (UInt64.ofNat (os.length+1)) owner ptr taker 0 none
    locals := List.replicate 56 (.i64 0), values := [] }

theorem body_spec (m : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (eligibleId releaseId : Nat) (owner ptr : UInt64) (os : List OrderL) (taker : OrderL)
    (hLength : os.length < 4294967296) (hInput : OrdersAt st ptr os)
    (hEligible : ∀ k, k < os.length → TerminatesWith env m eligibleId st
      [.i64 os[k]!.oqty, .i64 os[k]!.oprice, .i64 os[k]!.oside,
        .i64 os[k]!.otrader, .i64 os[k]!.oid, .i64 taker.oqty, .i64 taker.oprice,
        .i64 taker.oside, .i64 taker.otrader, .i64 taker.oid]
      (fun st1 vs => vs = [.i64 (boolWord (eligibleL taker os[k]!))] ∧ st1=st))
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final, final.values = optionVals (findBestL os taker) → wp m rest Q st final env) :
    wp m (program eligibleId releaseId ++ rest) Q st (entryFrame owner ptr os taker) env := by
  have hHead := hInput.1.1
  have hHeadB := hInput.1.2
  have hHeadSafe := Nat.not_lt.mpr hHeadB
  have hLengthU : (UInt64.ofNat os.length).toNat = os.length := by u64_omega
  simp only [program, List.append_assoc, List.cons_append, List.nil_append]
  wp_run_with [entryFrame]
  apply wp_block_cons
  apply wp_loop_cons (Inv := Invariant st owner ptr os taker) (μ := measure)
  · refine ⟨rfl, 0, UInt64.ofNat (os.length+1), 0, 0, 0, Nat.zero_le _, ?_, Or.inl ⟨rfl, rfl⟩⟩
    constructor <;> simp [entryFrame, params, bestPrefixL]
  · rintro st1 s ⟨rfl, k, fuel, tag, payload, done, hk, hFrame, hState⟩
    have hP := hFrame.params
    have hL := hFrame.locals
    have hV := hFrame.values
    have hOwner := getElem_of_some hFrame.owner
    have hTag := getElem_of_some hFrame.tag
    have hPayload := getElem_of_some hFrame.payload
    have hDone := getElem_of_some hFrame.done
    rcases hState with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · have hFuelNe : UInt64.ofNat (os.length+1-k) ≠ 0 := by
        intro h
        have hz := congrArg UInt64.toNat h
        rw [toNat_ofNat_lt (by rw [size_eq]; omega)] at hz
        change os.length+1-k=0 at hz
        omega
      simp only [loop, SearchProgram.guard, List.cons_append, List.nil_append]
      wp_run_with [hP, params, hL, hV, hOwner, hTag, hPayload, hDone]
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp [hFuelNe])]
      wp_run_with [hP, params, hL, hV, hOwner, hTag, hPayload, hDone, hHead, hHeadSafe]
      refine wp_iff_cons rfl ?_
      by_cases hEnd : k=os.length
      · have hNotLt : ¬UInt64.ofNat k < UInt64.ofNat os.length := by simp [hEnd]
        rw [if_neg (by simp [hNotLt])]
        simp only [SearchProgram.done]
        wp_run_with [hP, params, hL, hV, hOwner, hTag, hPayload, hDone]
        subst k
        refine ⟨⟨rfl, os.length, UInt64.ofNat (os.length+1-os.length),
          optionTag (bestPrefixL os taker os.length), optionPayload (bestPrefixL os taker os.length),
          1, Nat.le_refl _, ?_, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩, ?_⟩
        · constructor <;> simp [List.length_set, hL, hOwner, params]
        · simp [measure, hP, params, hDone, hL]
      · have hklt : k < os.length := by omega
        have hkU : (UInt64.ofNat k).toNat = k := by u64_omega
        have hLt : UInt64.ofNat k < UInt64.ofNat os.length := by
          rw [UInt64.lt_iff_toNat_lt, hkU, hLengthU]; exact hklt
        rw [if_pos (by simp [hLt])]
        let checked : Locals :=
          { params := params (UInt64.ofNat (os.length+1-k)) owner ptr taker k (bestPrefixL os taker k)
            locals := s.locals.set 53 (.i64 ptr)
            values := [] }
        refine (by simpa only [checked, params, List.append_nil, List.append_assoc, List.cons_append, List.nil_append] using
          (SearchStep.step_spec m env st1 eligibleId releaseId checked (UInt64.ofNat (os.length+1-k))
            owner ptr os taker k (bestPrefixL os taker k)
            rfl (by simp [checked, hL]) rfl (by simp [checked, hL, hOwner]) hLength hklt
            (fun j h => bestPrefixL_some_lt os taker k j h) hInput (hEligible k hklt) _ [] (by
            intro final hFinal
            wp_run
            have hFuelNext : UInt64.ofNat (os.length+1-k)-1 =
                UInt64.ofNat (os.length+1-(k+1)) := by
              have hStep : UInt64.ofNat (os.length+1-k) =
                  UInt64.ofNat (os.length+1-(k+1))+1 := by
                apply UInt64.toNat.inj
                rw [toNat_ofNat_lt (by rw [size_eq]; omega), toNat_add_one,
                  toNat_ofNat_lt (by rw [size_eq]; omega)]
                · omega
                · rw [toNat_ofNat_lt (by rw [size_eq]; omega), size_eq]; omega
              rw [hStep]; simp
            have hFT : final.locals[1]? = some (.i64 tag) := by
              rw [hFinal.kept 1 (by omega) (by omega)]
              simp [checked, hL, hTag]
            have hFP : final.locals[2]? = some (.i64 payload) := by
              rw [hFinal.kept 2 (by omega) (by omega)]
              simp [checked, hL, hPayload]
            have hFD : final.locals[3]? = some (.i64 0) := by
              rw [hFinal.kept 3 (by omega) (by omega)]
              simp [checked, hL, hDone]
            constructor
            · refine ⟨rfl, k+1, UInt64.ofNat (os.length+1-(k+1)), tag, payload, 0,
                (by omega), ?_, Or.inl ⟨rfl, rfl⟩⟩
              refine ⟨?_, hFinal.locals, rfl, hFinal.owner, hFT, hFP, hFD⟩
              simpa only [hFuelNext, bestPrefixL] using hFinal.params
            · simp only [measure, hFinal.params, hP, params, List.getElem?_cons_zero,
                hFD, hFrame.done]
              rw [hFuelNext, toNat_ofNat_lt (by rw [size_eq]; omega),
                toNat_ofNat_lt (by rw [size_eq]; omega)]
              simp only [ite_true]
              omega)))
    · simp only [loop, SearchProgram.guard, List.cons_append, List.nil_append]
      wp_run_with [hP, params, hL, hV, hOwner, hTag, hPayload, hDone]
      refine wp_iff_cons rfl ?_
      by_cases hZero : fuel=0
      · rw [if_neg (by simp [hZero])]
        wp_run_with [hP, params, hL, hV, hOwner, hTag, hPayload, hDone, finish]
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run_with [hP, params, hL, hTag, hPayload]
        apply hNext
        simp [optionVals, findBestL_eq_prefix]
      · rw [if_pos (by simp [hZero])]
        wp_run_with [hP, params, hL, hV, hOwner, hTag, hPayload, hDone, finish]
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run_with [hP, params, hL, hTag, hPayload]
        apply hNext
        simp [optionVals, findBestL_eq_prefix]

#print axioms body_spec
end Project.ClobFindBest.SearchLoop
