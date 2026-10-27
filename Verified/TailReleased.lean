import Verified.TailCorrect

namespace Verified

open Wasm LeanExe.Pipeline

theorem TailCodeSpec.released {S : List Sig} {Γ params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} {targetModes : List Mode}
    {body : TailBody S params result Γ} (hm : Runtime m)
    (spec : TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes body)
    {env : Env Γ} {slots : List Slot} {paid nextPaid : List Bool} {resultPaid : Bool}
    {L0 : Nat → Bool} {h stateBase resultBase base exitLabel nextLabel : Nat}
    {heap : Heap} {store : Store Unit} {s : Locals}
    (hh : s.positions = h) (hpv : s.params = pv)
    (hVars : Holds env slots L0 base heap store s) (hAt : heap.At store)
    (hSafe : pool.Safe env slots L0 heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535) (hLow : s.params.length ≤ stateBase)
    (hState : stateBase + widthSum params ≤ resultBase)
    (hResult : resultBase + result.width ≤ base)
    (hRoom : base + body.width targetModes ≤ h)
    (hPlace : body.placeArgs targetModes (slots.map Slot.mode) = true)
    (hPaid : resultPaid = true → body.paidResult flags (slots.map Slot.mode) paid = true)
    (hEntry : ∀ i, body.uses i = true → L0 i = true) {Q : Assertion Unit}
    (hTrap : TrapOK (!(body.fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid L0 (fun _ => false) +
        body.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env))) Q)
    (hNext : ∀ heap' store' s'
      (after : TailAfter env slots L0 targetModes stateBase resultBase heap store s
        (body.denote funs env) heap' store' s'),
      (body.fits funs fits env = true → heap'.top.toNat +
        tailPot targetModes nextPaid resultPaid store' after.words (body.denote funs env) ≤
          heap.top.toNat + dyingPot store s env slots paid L0 (fun _ => false) +
            body.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env) →
      Q (.Break ((body.denote funs env).elim (fun _ => nextLabel) (fun _ => exitLabel))
        store' { s' with values := s.values })) :
    wp m (releaseWhere Γ slots (fun i => L0 i && !body.uses i) ++
      body.code (pool := pool) targetModes h stateBase resultBase slots base exitLabel nextLabel)
      Q store s host := by
  refine wp_releaseWhere hm hVars hAt (fun i hi => by
      simp only [Bool.and_eq_true] at hi; exact hi.1)
    (fun heap1 store1 released hTop1 => ?_)
  have hLiveEq : (fun i => L0 i && !(L0 i && !body.uses i)) = body.uses := by
    funext i
    have hi := hEntry i
    cases h0 : L0 i <;> cases hb : body.uses i <;> simp_all
  rw [hLiveEq] at released
  have hPot := dyingPot_evolves (paid := paid) hVars released hEntry
    body.uses (fun _ => false) (fun _ hi => hi)
  have hPotLe : dyingPot store s env slots paid body.uses (fun _ => false) ≤
      dyingPot store s env slots paid L0 (fun _ => false) :=
    dyingPot_mono hEntry nofun
  have hBudget : TrapOK (!(body.fits funs fits env) ||
      (true && !decide (heap.Within store m
        (dyingPot store s env slots paid L0 (fun _ => false) +
          body.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env)))) Q := by
    simpa only [Bool.true_and] using hTrap
  refine spec env slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel
    heap1 store1 s hh hpv released.holds released.step.at_
    (hSafe.evolves hVars released hEntry)
    (by rw [released.step.cap m]; exact hCap) hLow hState hResult hRoom hPlace hPaid _
    (hBudget.part id (fun _ => rfl) (fun _ hw => hw.shift
      (heap1 := heap1) (store1 := store1) (c1 := 0)
      (by have ht := congrArg UInt64.toNat hTop1; omega)
      (by rw [hPot]; omega) (released.step.cap m)))
    (fun heap2 store2 s2 after hTop2 => ?_)
  refine hNext heap2 store2 s2 (TailAfter.prepend hVars released after hEntry (by omega))
    (fun hf => ?_)
  have h2 := hTop2 hf
  have h1 := congrArg UInt64.toNat hTop1
  rw [hPot] at h2
  change heap2.top.toNat +
    tailPot targetModes nextPaid resultPaid store2 after.words (body.denote funs env) ≤ _
  omega

#print axioms TailCodeSpec.released

end Verified
