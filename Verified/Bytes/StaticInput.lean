import Verified.Bytes.StaticEnv

namespace Verified.Bytes.LiteralPool

open Wasm LeanExe.Pipeline LeanExe.Runtime

def Input {α : Type} [Represent α] (pool : LiteralPool) (heap : Heap) (store : Store Unit)
    (words : List Value) (value : α) : Prop :=
  pool.Static heap store ∧
    ∀ region ∈ pool.regions, Apart store (Represent.moves store words value) region

namespace Input

theorem empty (base : Nat) {α : Type} {_ : Represent α} (heap : Heap) (store : Store Unit)
    (words : List Value) (value : α) : Input ⟨base, []⟩ heap store words value :=
  ⟨Static.empty _ _ _, by simp [regions, payload]⟩

theorem params {pool : LiteralPool} {Γ : List Ty} {env : Env Γ} {modes : List Mode}
    {heap : Heap} {store : Store Unit} {s : Locals} {words : List Value} {base : Nat}
    (h : @Input (Env Γ) (Env.represent Γ modes) pool heap store words env)
    (hRep : Env.Rep (paramMode Γ modes) heap store words env)
    (hWords : ∀ {t : Ty} (x : Var Γ t),
      LocalsHold s (base + x.offset) t.types ((words.drop x.offset).take t.width)) :
    Safe pool env (paramSlots Γ modes base) (fun _ => true) heap store s :=
  Safe.params h.1 hRep h.2 hWords

end Input
end Verified.Bytes.LiteralPool
