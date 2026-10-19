import Verified.Correct
import Verified.TailPaid
import Verified.TailState
import Verified.TailLoop
import Verified.EnvStep

namespace Verified

open Wasm LeanExe.Pipeline

def TailRep {params : List Ty} {result : Ty} (modes : List Mode)
    (stateBase resultBase : Nat) (heap : Heap) (store : Store Unit) (s : Locals)
    (words : List Value) : Sum (Env params) result.denote → Prop
  | .inl state =>
    Env.Rep (paramMode params modes) heap store words state ∧
      Separate store (Env.moves (paramMode params modes) words state)
        (Env.reads (paramMode params modes) words state) ∧
      LocalsHold s stateBase (params.flatMap Ty.types) words
  | .inr value => result.Rep .owned heap store words value ∧ LocalsHold s resultBase result.types words

def tailFresh {params : List Ty} {result : Ty} (modes : List Mode) (store : Store Unit)
    (words : List Value) : Sum (Env params) result.denote → List (Nat × Nat)
  | .inl state => (Env.moves (paramMode params modes) words state).map (block store)
  | .inr value => result.blocks store words value

def tailPot {params : List Ty} {result : Ty} (modes : List Mode) (paid : List Bool) (resultPaid : Bool)
    (store : Store Unit) (words : List Value) : Sum (Env params) result.denote → Nat
  | .inl state =>
    Env.argPot store (fun i => paidAt paid i && paramMode params modes i == .owned) words state
  | .inr value => if resultPaid then result.pot store words value else 0

structure TailAfter {Γ params : List Ty} {result : Ty} (env : Env Γ) (slots : List Slot)
    (live : Nat → Bool) (modes : List Mode) (stateBase resultBase : Nat)
    (heap : Heap) (store : Store Unit) (s : Locals) (value : Sum (Env params) result.denote)
    (heap' : Heap) (store' : Store Unit) (s' : Locals) where
  words : List Value
  step : Step heap store (Holds.KeepDying env slots live (fun _ => false) store s)
    heap' store' (tailFresh modes store' words value)
  frame : Frame stateBase s s'
  rep : TailRep modes stateBase resultBase heap' store' s' words value

def TailAfter.congr {Γ params : List Ty} {result : Ty} {env : Env Γ} {slots : List Slot}
    {live : Nat → Bool} {modes : List Mode} {stateBase resultBase : Nat}
    {heap heap' : Heap} {store store' : Store Unit} {s s' : Locals}
    {value value' : Sum (Env params) result.denote} (eq : value = value')
    (a : TailAfter env slots live modes stateBase resultBase heap store s value heap' store' s') :
    TailAfter env slots live modes stateBase resultBase heap store s value' heap' store' s' :=
  ⟨a.words, by rw [← eq]; exact a.step, a.frame, by rw [← eq]; exact a.rep⟩

def TailAfter.prepend {Γ params : List Ty} {result : Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 : Nat → Bool} {modes : List Mode} {base stateBase resultBase : Nat}
    {heap heap1 heap2 : Heap} {store store1 store2 : Store Unit} {s s1 s2 : Locals}
    {value : Sum (Env params) result.denote}
    (h0 : Holds env slots L0 base heap store s)
    (e : Evolves env slots L0 L1 base heap store s heap1 store1 s1)
    (a : TailAfter env slots L1 modes stateBase resultBase heap1 store1 s1 value heap2 store2 s2)
    (hSub : ∀ i, L1 i = true → L0 i = true) (hBase : stateBase ≤ base) :
    TailAfter env slots L0 modes stateBase resultBase heap store s value heap2 store2 s2 :=
  ⟨a.words, e.step.trans a.step fun r hr =>
      ⟨hr.mono fun _ hi _ => ⟨hi, rfl⟩,
        fun _ => Holds.KeepDying.transfer h0 e.step e.frame hSub (fun _ hi _ => hi)
          (hr.mono fun i hi ho => ⟨hSub i hi, ho⟩)⟩,
    (e.frame.mono hBase).trans a.frame, a.rep⟩

def tailTrapFlag {S : List Sig} {Γ params : List Ty} {result : Ty}
    (m : Module) (body : TailBody S params result Γ) (modes : List Mode) (slots : List Slot)
    (heap : Heap) (store : Store Unit) (cost : Nat) (fits : Bool) : Bool :=
  !fits || ((body.aborts || !result.scalar ||
    (paramModes params modes).any (· == .owned) || slots.any (·.mode == .owned)) &&
      !decide (heap.Within store m cost))

def TailCodeSpec {S : List Sig} {Γ params : List Ty} {result : Ty}
    (m : Module) (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (fits : Fits S)
    (host : HostEnv Unit) (pv : List Value) (targetModes : List Mode)
    (body : TailBody S params result Γ) : Prop :=
  ∀ (env : Env Γ) (slots : List Slot) (paid : List Bool) (nextPaid : List Bool) (resultPaid : Bool)
    (h stateBase resultBase base exitLabel nextLabel : Nat)
    (heap : Heap) (store : Store Unit) (s : Locals),
    s.half = h → s.params = pv →
    Holds env slots body.uses base heap store s → heap.At store → store.memoryCap m 0 ≤ 65535 →
    s.params.length ≤ stateBase → stateBase + widthSum params ≤ resultBase →
    resultBase + result.width ≤ base → base + body.width targetModes ≤ h →
    body.placeArgs targetModes (slots.map Slot.mode) = true →
    (resultPaid = true → body.paidResult flags (slots.map Slot.mode) paid = true) →
    ∀ (Q : Assertion Unit),
    TrapOK (tailTrapFlag m body targetModes slots heap store
      (dyingPot store s env slots paid body.uses (fun _ => false) +
        body.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env)
      (body.fits funs fits env)) Q →
    (∀ heap' store' s' (after : TailAfter env slots body.uses targetModes stateBase resultBase
        heap store s (body.denote funs env) heap' store' s'),
      (body.fits funs fits env = true →
        heap'.top.toNat + tailPot targetModes nextPaid resultPaid store' after.words
            (body.denote funs env) ≤
          heap.top.toNat + dyingPot store s env slots paid body.uses (fun _ => false) +
            body.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env) →
      Q (.Break ((body.denote funs env).elim (fun _ => nextLabel) (fun _ => exitLabel)) store'
        { s' with values := s.values })) →
    wp m (body.code targetModes h stateBase resultBase slots base exitLabel nextLabel) Q store s host

theorem tail_ret_spec {S : List Sig} {Γ params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m) (targetModes : List Mode)
    (value : Expr S Γ result)
    (valueSpec : ∀ env slots paid live,
      CodeSpec m funs flags bounds fits host pv value env slots paid live) :
    TailCodeSpec m funs flags bounds fits host pv targetModes (.ret (params := params) value) := by
  intro env slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel heap
    store s hh hpv hVars hAt hCap hLow hState hResult hRoom hPlace hPaid Q hTrap hNext
  have hWidth : value.width ≤ max value.width (copyWidth result) := Nat.le_max_left ..
  have hCopy : copyWidth result ≤ max value.width (copyWidth result) := Nat.le_max_right ..
  simp only [TailBody.width] at hRoom
  simp only [TailBody.placeArgs] at hPlace
  simp only [TailBody.paidResult] at hPaid
  simp only [tailTrapFlag, TailBody.aborts, TailBody.fits, TailBody.allocs, TailBody.uses] at hTrap
  simp only [TailBody.code, List.append_assoc]
  refine valueSpec env slots paid (fun _ => false) h base heap store s hh hpv
    (by simpa [TailBody.uses] using hVars) hAt hCap (by omega) (by omega) hPlace _ _
    (hTrap.part id (fun ha => by
      simp only [Bool.or_eq_true] at ha ⊢
      tauto) fun _ hw => hw.mono (by simp only [Bool.false_or]; omega))
    fun heap1 store1 s1 ws1 after1 hTop1 => ?_
  have after1' : After env slots value.uses (fun _ => false) base heap store s result
      (value.mode (slots.map Slot.mode)) (value.denote funs env) heap1 store1 s1 ws1 := by
    simpa only [Bool.false_or] using after1
  refine After.coerce hm after1' (fun _ => rfl) (Nat.le_refl _)
    (by rw [after1'.frame.params]; omega) (after1'.frame.half.trans hh) (by omega)
    (by rw [after1'.step.cap m]; exact hCap)
    (fun hs _ hScalar => hTrap.alloc (by simp [hScalar]) fun hd hw =>
      hw.of_le (by
        have ht := hTop1 (fits_of_not hd)
        simp only [Bool.false_or] at ht
        simp only [coerceCost, hs, and_self, hScalar, ↓reduceIte]
        omega) (after1'.step.cap m))
    fun heap2 store2 s2 ws2 after2 hTop2 hSame2 => ?_
  refine wp_storeCode ws2 h resultBase result.types s2 s.values after2.rep.typed
    (after2.frame.half.trans hh) (by rw [after2.frame.params]; omega)
    (by rw [Ty.types_length, after2.frame.half, hh]; omega) fun s3 frame3 hold3 _ => ?_
  rw [wp_br_cons]
  refine hNext heap2 store2 s3
    ⟨ws2, after2.step,
      (after2.frame.mono (by omega)).trans (frame3.mono (by omega)), after2.rep, hold3⟩ ?_
  intro hf
  have ht := hTop1 hf
  simp only [Bool.false_or] at ht
  have hPot := pot_keep (P := resultPaid)
    (Q := value.paid flags (slots.map Slot.mode) paid (fun _ => false))
    (a := result.pot store2 ws2 (value.denote funs env))
    (b := result.pot store1 ws1 (value.denote funs env)) hPaid fun hp => by
      obtain ⟨rfl, rfl⟩ := hSame2 (Expr.mode_of_paid value (hPaid hp))
      rfl
  simp only [TailBody.fits, TailBody.uses, TailBody.allocs, TailBody.denote, tailPot]
  omega

#print axioms tail_ret_spec

end Verified
