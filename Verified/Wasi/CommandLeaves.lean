import Verified.Wasi.CommandCodeSpec
import Verified.Wasi.CompilerFacts
import Verified.Wasi.ReturnCommand
import Verified.Wasi.ReadCommand
import Verified.Wasi.WriteCommand
import Verified.Wasi.ExitCommand

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem command_unit_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} :
    CommandCodeSpec source target pure effects pool (.unit (context := context)) := by
  intro World host targetHost depth env slots live h base heap initial locals
    _ _ _ _ vars at_ _ _ _ _ _ _ _ _
  simp only [Command.uses, Bool.or_false] at vars
  simpa only [Command.uses, Bool.or_false, Command.denote] using
    wp_command_unit (host := host) (h := h) (pool := pool) (targetHost := targetHost) at_ vars

theorem command_ret_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty} {type : Ty}
    (facts : CompilerFacts source target pure effects pool) (sourceHost : HostEnv Unit)
    (value : Expr pureSigs context type) :
    CommandCodeSpec source target pure effects pool (.ret value) := by
  intro World host targetHost depth env slots live h base heap initial locals
    _ _ depthParam positions vars at_ safe _ cap low room ready covered place
  have fragment := ready _ (List.mem_singleton_self _)
  have spec := value.code_spec source pure.funs pure.flags (pure.callBounds depth)
    (pure.callFits depth) sourceHost facts.runtime (Calls.at facts.calls depth) covered
    (fun _ => depthParam) env slots [] live
  exact wp_command_ret facts.runtime facts.layout facts.profile spec fragment.1 fragment.2
    positions rfl vars at_ safe cap low room place (fun _ => rfl)

theorem command_write_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFacts source target pure effects pool) (sourceHost : HostEnv Unit)
    (output : Output) (bytes : Var context .bytes) :
    CommandCodeSpec source target pure effects pool (.write output bytes) := by
  intro World host targetHost depth env slots live h base heap initial locals
    valid _ _ positions vars at_ _ scratch _ _ _ ready _ _
  have fragment := ready _ (List.mem_singleton_self _)
  obtain ⟨typeIndex, lookup⟩ := facts.write_function output
  exact wp_command_write (sourceHost := sourceHost) facts.runtime facts.layout facts.profile
    facts.imports lookup valid at_ positions vars scratch fragment.1 fragment.2

theorem command_read_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFacts source target pure effects pool) (sourceHost : HostEnv Unit)
    (capacity : Expr pureSigs context .word) :
    CommandCodeSpec source target pure effects pool (.read capacity) := by
  intro World host targetHost depth env slots live h base heap initial locals
    valid _ depthParam positions vars at_ safe scratch cap low room ready covered place
  have fragment := ready _ (List.mem_singleton_self _)
  have spec := capacity.code_spec source pure.funs pure.flags (pure.callBounds depth)
    (pure.callFits depth) sourceHost facts.runtime (Calls.at facts.calls depth) covered
    (fun _ => depthParam) env slots [] live
  have noCoerce : coerceCode h .word (capacity.mode (slots.map Slot.mode)) .owned base = [] := by
    simp [coerceCode, Ty.scalar]
  obtain ⟨typeIndex, lookup⟩ := facts.read
  exact wp_command_read facts.runtime facts.layout facts.profile facts.imports lookup valid spec
    (by simpa only [noCoerce, List.append_nil] using fragment.1)
    (by simpa only [noCoerce, List.append_nil] using fragment.2)
    positions rfl vars scratch at_ safe cap low
    (by simpa only [Command.width, copyWidth, Ty.scalar, ite_true, Nat.max_zero] using room) place
    (fun _ => rfl) (fun _ _ _ _ _ _ _ impossible => Bool.noConfusion impossible)

theorem command_exit_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty} {result : ResultTy}
    (facts : CompilerFacts source target pure effects pool) (sourceHost : HostEnv Unit)
    (status : Expr pureSigs context .word) :
    CommandCodeSpec source target pure effects pool (.exit (result := result) status) := by
  intro World host targetHost depth env slots live h base heap initial locals
    valid _ depthParam positions vars at_ safe _ cap low room ready covered place
  have fragment := ready _ (List.mem_singleton_self _)
  have spec := status.code_spec source pure.funs pure.flags (pure.callBounds depth)
    (pure.callFits depth) sourceHost facts.runtime (Calls.at facts.calls depth) covered
    (fun _ => depthParam) env slots [] live
  have noCoerce : coerceCode h .word (status.mode (slots.map Slot.mode)) .owned base = [] := by
    simp [coerceCode, Ty.scalar]
  exact wp_command_exit facts.runtime facts.layout facts.profile facts.imports valid spec
    (by simpa only [noCoerce, List.append_nil] using fragment.1)
    (by simpa only [noCoerce, List.append_nil] using fragment.2)
    positions rfl vars at_ safe cap low room place (fun _ => rfl)

end Verified.Wasi
