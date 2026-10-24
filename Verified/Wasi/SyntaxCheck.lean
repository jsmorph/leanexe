import LeanExe.Encoding.FormCheck
import Verified.Wasi.ProgramCorrect

namespace Verified.Wasi

open Wasm

def checkFragment (bound : Nat) (code : Program) : Bool :=
  Encoding.checkProgramForm code && Relocation.programClosed bound code

theorem checkFragment_sound {bound : Nat} {code : Program}
    (accepted : checkFragment bound code = true) :
    Encoding.ProgramForm code ∧ Relocation.programClosed bound code = true := by
  simp only [checkFragment, Bool.and_eq_true] at accepted
  exact ⟨Encoding.checkProgramForm_sound accepted.1, accepted.2⟩

theorem checkFragment_complete {bound : Nat} {code : Program}
    (ready : Encoding.ProgramForm code ∧ Relocation.programClosed bound code = true) :
    checkFragment bound code = true := by
  simp only [checkFragment, Bool.and_eq_true]
  exact ⟨Encoding.checkProgramForm_complete ready.1, ready.2⟩

def Relocation.checkProfile (source : Module) : Bool :=
  source.funcs.all fun function => checkFragment source.funcs.length function.body

theorem Relocation.checkProfile_sound {source : Module}
    (accepted : Relocation.checkProfile source = true) : Relocation.Profile source := by
  intro function member
  exact checkFragment_sound (List.all_eq_true.mp accepted function member)

theorem Relocation.checkProfile_complete {source : Module} (profile : Relocation.Profile source) :
    Relocation.checkProfile source = true :=
  List.all_eq_true.mpr fun function member => checkFragment_complete (profile function member)

def Command.checkReady (source : Module) (h : Nat) (slots : List Slot) (base : Nat)
    (live : Nat → Bool) (pool : Bytes.LiteralPool)
    (command : Command pureSigs effectSigs context result) : Bool :=
  (command.fragments h slots base live pool).all (checkFragment source.funcs.length)

theorem Command.checkReady_sound {source : Module} {h : Nat} {slots : List Slot} {base : Nat}
    {live : Nat → Bool} {pool : Bytes.LiteralPool} {command : Command pureSigs effectSigs context result}
    (accepted : command.checkReady source h slots base live pool = true) :
    command.Ready source h slots base live pool := by
  intro fragment member
  exact checkFragment_sound (List.all_eq_true.mp accepted fragment member)

theorem Command.checkReady_complete {source : Module} {h : Nat} {slots : List Slot} {base : Nat}
    {live : Nat → Bool} {pool : Bytes.LiteralPool} {command : Command pureSigs effectSigs context result}
    (ready : command.Ready source h slots base live pool) :
    command.checkReady source h slots base live pool = true :=
  List.all_eq_true.mpr fun fragment member => checkFragment_complete (ready fragment member)

def EffectFunc.checkReady (source : Module) (pool : Bytes.LiteralPool)
    (function : EffectFunc pureSigs effectSigs) : Bool :=
  checkFragment source.funcs.length (releaseWhere function.params
    (paramSlots function.params function.modes 1) (fun i => !function.body.uses i)) &&
    (function.body.checkReady source function.positions (paramSlots function.params function.modes 1)
      (1 + widthSum function.params) (fun _ => false) pool && function.body.placeArgs)

theorem EffectFunc.checkReady_sound {source : Module} {pool : Bytes.LiteralPool}
    {function : EffectFunc pureSigs effectSigs} (accepted : function.checkReady source pool = true) :
    function.Ready source pool := by
  simp only [EffectFunc.checkReady, Bool.and_eq_true] at accepted
  obtain ⟨form, closed⟩ := checkFragment_sound accepted.1
  exact ⟨form, closed, Command.checkReady_sound accepted.2.1, accepted.2.2⟩

theorem EffectFunc.checkReady_complete {source : Module} {pool : Bytes.LiteralPool}
    {function : EffectFunc pureSigs effectSigs} (ready : function.Ready source pool) :
    function.checkReady source pool = true := by
  obtain ⟨form, closed, body, place⟩ := ready
  simp only [EffectFunc.checkReady, Bool.and_eq_true]
  exact ⟨checkFragment_complete ⟨form, closed⟩, Command.checkReady_complete body, place⟩

def EffectProg.checkReady (source : Module) (pool : Bytes.LiteralPool) :
    {effectSigs : List EffectSig} → EffectProg pureSigs effectSigs → Bool
  | _, .nil => true
  | _, .cons function rest => function.checkReady source pool && rest.checkReady source pool

theorem EffectProg.checkReady_sound {source : Module} {pool : Bytes.LiteralPool}
    (program : EffectProg pureSigs effectSigs) :
    program.checkReady source pool = true → program.Ready source pool := by
  induction program with
  | nil => intro _; trivial
  | cons function rest ih =>
    intro accepted
    simp only [EffectProg.checkReady, Bool.and_eq_true] at accepted
    exact ⟨EffectFunc.checkReady_sound accepted.1, ih accepted.2⟩

theorem EffectProg.checkReady_complete {source : Module} {pool : Bytes.LiteralPool}
    (program : EffectProg pureSigs effectSigs) :
    program.Ready source pool → program.checkReady source pool = true := by
  induction program with
  | nil => intro _; rfl
  | cons function rest ih =>
    intro ready
    simp only [EffectProg.checkReady, Bool.and_eq_true]
    exact ⟨EffectFunc.checkReady_complete ready.1, ih ready.2⟩

end Verified.Wasi
