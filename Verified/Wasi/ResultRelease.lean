import Verified.Wasi.ScratchContext
import Verified.ArgsCorrect

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem After.release {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {all middle live : Nat → Bool} {base : Nat}
    {heap heap1 heap2 : Heap} {initial intermediate final : Store World}
    {locals locals1 : Locals} {result : ResultTy} {value : result.denote} {words : List Value}
    (vars : Holds env slots all base heap (PureTransport.erase initial) locals)
    (scratch : Holds.ApartFrom env slots all (PureTransport.erase initial) locals ABI.scratch)
    (after : After env slots all middle base heap initial locals result value
      heap1 intermediate locals1 words)
    (middleSelected : ∀ i, middle i = true → all i = true)
    (liveSelected : ∀ i, live i = true → middle i = true)
    (release : Evolves env slots middle live base heap1 (PureTransport.erase intermediate)
      locals1 heap2 (PureTransport.erase final) locals1) :
    After env slots all live base heap initial locals result value heap2 final locals1 words := by
  have step := after.step.transBoth release.step
    (keep := fun region => Holds.KeepDying env slots all live (PureTransport.erase initial)
      locals region ∧ regionsDisjoint region ABI.scratch) (fun region kept => by
      refine ⟨⟨kept.1.mono (fun i hi dead => ⟨hi, ?_⟩), kept.2⟩, fun _ => ?_⟩
      · cases selected : live i with
        | false => rfl
        | true => rw [liveSelected i selected] at dead; exact nomatch dead
      · exact Holds.KeepDying.transfer_kept vars after.step after.frame
          (fun i hi _ => middleSelected i hi)
          (fun type x hi _ values held width block member =>
            ⟨vars.keepDying middleSelected hi held width block member,
              regionsDisjoint_symm (scratch type x (middleSelected _ hi)
                values held width block member)⟩)
          (kept.1.mono fun i hi dead => ⟨middleSelected i hi, dead⟩))
  cases result with
  | unit =>
      exact ⟨step.mono (fun _ h => h) (fun _ member => nomatch member), after.frame,
        release.holds, after.rep, trivial⟩
  | value type =>
      have keptValue : ∀ region ∈ type.regions .owned (PureTransport.erase intermediate) words value,
          Holds.KeepDying env slots middle live (PureTransport.erase intermediate) locals1 region := by
        intro region member other x hi _ owned values held width block blockMember
        have blockMember' : block ∈ other.regions (slots.getD x.index default).mode
            (PureTransport.erase intermediate) values (env.get x) := by
          rw [owned]; exact blockMember
        exact after.apart other x hi (Or.inr owned) values held width region member block blockMember'
      obtain ⟨rep, same, _⟩ := after.rep.step release.step keptValue
      refine ⟨step.mono (fun _ h => h) (fun block member => ?_), after.frame,
        release.holds, rep, ?_⟩
      · change block ∈ Mode.owned.fresh (PureTransport.erase final) type words value at member
        rw [Mode.fresh_congr same] at member
        exact List.mem_append_left _ member
      · exact Holds.Apart.transfer (after.holds.live_mono liveSelected)
          (after.apart.live_mono liveSelected) release.step (Frame.refl base locals1)
          (fun other x hi values held width => after.holds.keepDying liveSelected hi held width) same

end Verified.Wasi
