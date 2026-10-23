import LeanExe.Wasi.Prefix

namespace LeanExe.Wasi

inductive PrefixAdvance {World : Type} (host : Host World) :
    {α : Type} → Action α → World → List Event → Action α → World → Prop where
  | read_reject {capacity : UInt64} {next : ReadResult → Action α} {world}
      (capacityBound : 2 ^ 32 ≤ capacity.toNat) :
      PrefixAdvance host (.read capacity next) world [] (next ⟨61, Bytes.empty⟩) world
  | read_return {capacity : UInt64} {next : ReadResult → Action α}
      {world after errno committed}
      (capacityBound : capacity.toNat < 2 ^ 32)
      (reply : host.read world capacity (.returned errno committed) after) :
      PrefixAdvance host (.read capacity next) world [.read capacity (.returned errno committed)]
        (next (readResult errno committed)) after
  | write_return {output : Output} {bytes : Bytes} {next : WriteResult → Action α}
      {world after errno committed}
      (reply : host.write world output bytes (.returned errno committed) after) :
      PrefixAdvance host (.write output bytes next) world [.write output bytes (.returned errno committed)]
        (next (writeResult errno committed)) after
  | loop {count : UInt64} {state : σ} {test : UInt64 → σ → Bool}
      {step : UInt64 → σ → Action σ} {next : σ → Action α} {world} :
      PrefixAdvance host (.loop count state test step next) world []
        (resumeLoop test step next count.toNat 0 state) world

namespace PrefixAdvance

theorem toPrefix {World : Type} {host : Host World} {action residual : Action α}
    {world trace after} (advance : PrefixAdvance host action world trace residual after) :
    Prefix host action world trace residual after := by
  cases advance with
  | read_reject bound => exact .read_reject bound
  | read_return bound reply => exact .read_return bound reply
  | write_return reply => exact .write_return reply
  | loop => exact .loop

theorem bind {World : Type} {host : Host World} {action residual : Action α}
    {next : α → Action β} {world trace after}
    (advance : PrefixAdvance host action world trace residual after) :
    PrefixAdvance host (Action.bind action next) world trace
      (Action.bind residual next) after := by
  cases advance with
  | read_reject bound => exact .read_reject bound
  | read_return bound reply => exact .read_return bound reply
  | write_return reply => exact .write_return reply
  | loop =>
      rw [resumeLoop_bind]
      exact .loop

end PrefixAdvance

inductive PrefixProgress {World : Type} (host : Host World) :
    {α : Type} → Action α → World → List Event → Action α → World → Prop where
  | refl (action : Action α) (world : World) :
      PrefixProgress host action world [] action world
  | advance {action residual : Action α} {world trace after}
      (step : PrefixAdvance host action world trace residual after) :
      PrefixProgress host action world trace residual after
  | trans {action middle residual : Action α} {world after final first rest}
      (head : PrefixProgress host action world first middle after)
      (tail : PrefixProgress host middle after rest residual final) :
      PrefixProgress host action world (first ++ rest) residual final

namespace PrefixProgress

theorem bind {World : Type} {host : Host World} {action residual : Action α}
    {next : α → Action β} {world trace after}
    (progress : PrefixProgress host action world trace residual after) :
    PrefixProgress host (Action.bind action next) world trace
      (Action.bind residual next) after := by
  induction progress with
  | refl => exact .refl _ _
  | advance step => exact .advance step.bind
  | trans _ _ head tail => exact .trans head tail

theorem toPrefix {World : Type} {host : Host World} {action residual : Action α}
    {world trace after} (progress : PrefixProgress host action world trace residual after) :
    Prefix host action world trace residual after := by
  induction progress with
  | refl => exact .refl _ _
  | advance step => exact step.toPrefix
  | trans _ _ head tail => exact .trans head tail

end PrefixProgress

theorem Prefix.progress {World : Type} {host : Host World} {action residual : Action α}
    {world trace after} (hPrefix : Prefix host action world trace residual after) :
    PrefixProgress host action world trace residual after := by
  induction hPrefix with
  | refl => exact .refl _ _
  | read_reject bound => exact .advance (.read_reject bound)
  | read_return bound reply => exact .advance (.read_return bound reply)
  | write_return reply => exact .advance (.write_return reply)
  | loop => exact .advance .loop
  | bind _ ih => exact ih.bind
  | trans _ _ head tail => exact .trans head tail

theorem Prefix.progress_iff {World : Type} {host : Host World} {action residual : Action α}
    {world trace after} :
    Prefix host action world trace residual after ↔
      PrefixProgress host action world trace residual after :=
  ⟨Prefix.progress, PrefixProgress.toPrefix⟩

end LeanExe.Wasi
