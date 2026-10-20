import Verified.TailHeap

namespace Verified

open Wasm LeanExe.Pipeline

theorem tail_step_spec {S : List Sig} {params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m) (modes : List Mode)
    (body : TailBody S params result params)
    (bodySpec : TailCodeSpec m funs flags bounds fits host pv modes body)
    (place : body.placeArgs modes (entryModes params modes) = true)
    (pf : List Bool) (rf : Bool)
    (hPaid : rf = true → body.paidResult flags (entryModes params modes) pf = true)
    (h stateBase resultBase base exitLabel nextLabel : Nat) (env : Env params)
    (heap : Heap) (store : Store Unit) (s : Locals) (ws : List Value)
    (hh : s.positions = h) (hpv : s.params = pv)
    (hRep : Env.Rep (paramMode params modes) heap store ws env)
    (hSep : Separate store (Env.moves store (paramMode params modes) ws env)
      (Env.reads store (paramMode params modes) ws env))
    (hold : LocalsHold s stateBase (params.flatMap Ty.types) ws)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hLow : s.params.length ≤ stateBase) (hState : stateBase + widthSum params ≤ resultBase)
    (hResult : resultBase + result.width ≤ base) (hRoom : base + body.width modes ≤ h)
    (Q : Assertion Unit)
    (hTrap : TrapOK (!body.fits funs fits env ||
      ((body.aborts || !result.scalar || (paramModes params modes).any (· == .owned)) &&
        !decide (heap.Within store m (Env.argPot store
          (fun i => paidAt pf i && paramMode params modes i == .owned) ws env +
            body.allocs funs flags bounds modes pf (entryModes params modes) pf env)))) Q)
    (hNext : ∀ heap' store' s'
      (after : TailAfter env (paramSlots params modes stateBase) (fun _ => true) modes
        stateBase resultBase heap store s (body.denote funs env) heap' store' s'),
      (body.fits funs fits env = true →
        heap'.top.toNat + tailPot modes pf rf store' after.words (body.denote funs env) ≤
          heap.top.toNat + Env.argPot store
            (fun i => paidAt pf i && paramMode params modes i == .owned) ws env +
              body.allocs funs flags bounds modes pf (entryModes params modes) pf env) →
      Q (.Break ((body.denote funs env).elim (fun _ => nextLabel) (fun _ => exitLabel)) store'
        { s' with values := s.values })) :
    wp m (releaseWhere params (paramSlots params modes stateBase) (fun i => !body.usesFast i) ++
      body.code modes h stateBase resultBase (paramSlots params modes stateBase) base
        exitLabel nextLabel) Q store s host := by
  have vars0 := Holds.ofEnvRep hRep hSep hold
  have modesEq : (paramSlots params modes stateBase).map Slot.mode = entryModes params modes := by
    rw [entryModes, paramSlots_modes, paramSlots_modes]
  have potEq : env.pot store s (paramSlots params modes stateBase)
      (fun i => paidAt pf i && paramMode params modes i == .owned) =
      Env.argPot store (fun i => paidAt pf i && paramMode params modes i == .owned) ws env :=
    Env.pot_paramSlots modes stateBase _ ws env hRep.length (fun x => hold.var x)
  simp only [TailBody.usesFast_eq]
  refine wp_releaseWhere hm vars0 hAt (fun _ _ => rfl) fun heap1 store1 release top1 => ?_
  have release' := release.mono (live' := body.uses) (fun _ hi => by simp [hi])
  have potLe : dyingPot store1 s env (paramSlots params modes stateBase) pf body.uses
      (fun _ => false) ≤ Env.argPot store
        (fun i => paidAt pf i && paramMode params modes i == .owned) ws env := by
    rw [dyingPot_evolves vars0 release' (fun _ _ => rfl) _ _ (fun _ hi => hi), ← potEq]
    refine Env.pot_mono env _ _ _ fun i hi => ?_
    simp only [Bool.and_eq_true, beq_iff_eq] at hi ⊢
    exact ⟨hi.1.2, by rw [← paramSlots_getD_mode params modes stateBase]; exact hi.2⟩
  refine bodySpec env (paramSlots params modes stateBase) pf pf rf h stateBase resultBase base
    exitLabel nextLabel heap1 store1 s hh hpv (release'.holds.mono (by omega)) release'.step.at_
    (by rw [release'.step.cap m]; exact hCap) hLow hState hResult hRoom
    (by rw [modesEq]; exact place) (by rw [modesEq]; exact hPaid) _
    (hTrap.part (fun hd => hd)
      (fun ha => by
        rw [← Slot.any_map, paramSlots_modes] at ha
        simpa only [Bool.or_assoc, Bool.or_self] using ha)
      fun _ hw => hw.of_le (by rw [top1, modesEq]; omega) (release'.step.cap m))
    fun heap2 store2 s2 after2 top2 => ?_
  let final := TailAfter.prepend vars0 release' after2 (fun _ _ => rfl) (by omega)
  refine hNext heap2 store2 s2 final fun hf => ?_
  have ht := top2 hf
  rw [modesEq] at ht
  rw [top1] at ht
  exact ht.trans (by omega)

#print axioms tail_step_spec

end Verified
