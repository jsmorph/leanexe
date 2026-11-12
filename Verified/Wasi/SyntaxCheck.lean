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

def Command.checkReadyWith (calls : List LeanExe.Wasi.Call) (source : Module) (h : Nat)
    (slots : List Slot) (base : Nat) (live : Nat → Bool) (pool : Bytes.LiteralPool)
    (command : Command pureSigs effectSigs context result) : Bool :=
  (command.fragments h slots base live pool).all (checkFragment source.funcs.length) &&
    command.callsReady calls

def Command.checkReady (source : Module) (h : Nat) (slots : List Slot) (base : Nat)
    (live : Nat → Bool) (pool : Bytes.LiteralPool)
    (command : Command pureSigs effectSigs context result) : Bool :=
  command.checkReadyWith [] source h slots base live pool

theorem Command.checkReadyWith_sound {calls : List LeanExe.Wasi.Call} {source : Module} {h : Nat}
    {slots : List Slot} {base : Nat} {live : Nat → Bool} {pool : Bytes.LiteralPool}
    {command : Command pureSigs effectSigs context result}
    (accepted : command.checkReadyWith calls source h slots base live pool = true) :
    command.ReadyWith calls source h slots base live pool := by
  simp only [Command.checkReadyWith, Bool.and_eq_true] at accepted
  exact ⟨fun fragment member => checkFragment_sound (List.all_eq_true.mp accepted.1 fragment member),
    accepted.2⟩

theorem Command.checkReady_sound {source : Module} {h : Nat} {slots : List Slot} {base : Nat}
    {live : Nat → Bool} {pool : Bytes.LiteralPool} {command : Command pureSigs effectSigs context result}
    (accepted : command.checkReady source h slots base live pool = true) :
    command.Ready source h slots base live pool :=
  Command.checkReadyWith_sound accepted

theorem Command.checkReadyWith_complete {calls : List LeanExe.Wasi.Call} {source : Module}
    {h : Nat} {slots : List Slot} {base : Nat} {live : Nat → Bool} {pool : Bytes.LiteralPool}
    {command : Command pureSigs effectSigs context result}
    (ready : command.ReadyWith calls source h slots base live pool) :
    command.checkReadyWith calls source h slots base live pool = true := by
  simp only [Command.checkReadyWith, Bool.and_eq_true]
  exact ⟨List.all_eq_true.mpr fun fragment member => checkFragment_complete (ready.1 fragment member),
    ready.2⟩

theorem Command.checkReady_complete {source : Module} {h : Nat} {slots : List Slot} {base : Nat}
    {live : Nat → Bool} {pool : Bytes.LiteralPool} {command : Command pureSigs effectSigs context result}
    (ready : command.Ready source h slots base live pool) :
    command.checkReady source h slots base live pool = true :=
  Command.checkReadyWith_complete ready

def EffectFunc.checkReadyWith (calls : List LeanExe.Wasi.Call) (source : Module)
    (pool : Bytes.LiteralPool) (function : EffectFunc pureSigs effectSigs) : Bool :=
  checkFragment source.funcs.length (releaseWhere function.params
    (paramSlots function.params function.modes 1) (fun i => !function.body.uses i)) &&
    (function.body.checkReadyWith calls source function.positions
      (paramSlots function.params function.modes 1) (1 + widthSum function.params)
      (fun _ => false) pool && function.body.placeArgs)

def EffectFunc.checkReady (source : Module) (pool : Bytes.LiteralPool)
    (function : EffectFunc pureSigs effectSigs) : Bool :=
  function.checkReadyWith [] source pool

theorem EffectFunc.checkReadyWith_sound {calls : List LeanExe.Wasi.Call} {source : Module}
    {pool : Bytes.LiteralPool} {function : EffectFunc pureSigs effectSigs}
    (accepted : function.checkReadyWith calls source pool = true) :
    function.ReadyWith calls source pool := by
  simp only [EffectFunc.checkReadyWith, Bool.and_eq_true] at accepted
  obtain ⟨form, closed⟩ := checkFragment_sound accepted.1
  exact ⟨form, closed, Command.checkReadyWith_sound accepted.2.1, accepted.2.2⟩

theorem EffectFunc.checkReady_sound {source : Module} {pool : Bytes.LiteralPool}
    {function : EffectFunc pureSigs effectSigs} (accepted : function.checkReady source pool = true) :
    function.Ready source pool :=
  EffectFunc.checkReadyWith_sound accepted

theorem EffectFunc.checkReadyWith_complete {calls : List LeanExe.Wasi.Call} {source : Module}
    {pool : Bytes.LiteralPool} {function : EffectFunc pureSigs effectSigs}
    (ready : function.ReadyWith calls source pool) :
    function.checkReadyWith calls source pool = true := by
  obtain ⟨form, closed, body, place⟩ := ready
  simp only [EffectFunc.checkReadyWith, Bool.and_eq_true]
  exact ⟨checkFragment_complete ⟨form, closed⟩, Command.checkReadyWith_complete body, place⟩

theorem EffectFunc.checkReady_complete {source : Module} {pool : Bytes.LiteralPool}
    {function : EffectFunc pureSigs effectSigs} (ready : function.Ready source pool) :
    function.checkReady source pool = true :=
  EffectFunc.checkReadyWith_complete ready

def EffectProg.checkReadyWith (calls : List LeanExe.Wasi.Call) (source : Module)
    (pool : Bytes.LiteralPool) :
    {effectSigs : List EffectSig} → EffectProg pureSigs effectSigs → Bool
  | _, .nil => true
  | _, .cons function rest =>
    function.checkReadyWith calls source pool && rest.checkReadyWith calls source pool

def EffectProg.checkReady (source : Module) (pool : Bytes.LiteralPool) :
    {effectSigs : List EffectSig} → EffectProg pureSigs effectSigs → Bool :=
  fun program => program.checkReadyWith [] source pool

theorem EffectProg.checkReadyWith_sound {calls : List LeanExe.Wasi.Call} {source : Module}
    {pool : Bytes.LiteralPool} (program : EffectProg pureSigs effectSigs) :
    program.checkReadyWith calls source pool = true → program.ReadyWith calls source pool := by
  induction program with
  | nil => intro _; trivial
  | cons function rest ih =>
    intro accepted
    simp only [EffectProg.checkReadyWith, Bool.and_eq_true] at accepted
    exact ⟨EffectFunc.checkReadyWith_sound accepted.1, ih accepted.2⟩

theorem EffectProg.checkReady_sound {source : Module} {pool : Bytes.LiteralPool}
    (program : EffectProg pureSigs effectSigs) :
    program.checkReady source pool = true → program.Ready source pool :=
  EffectProg.checkReadyWith_sound program

theorem EffectProg.checkReadyWith_complete {calls : List LeanExe.Wasi.Call} {source : Module}
    {pool : Bytes.LiteralPool} (program : EffectProg pureSigs effectSigs) :
    program.ReadyWith calls source pool → program.checkReadyWith calls source pool = true := by
  induction program with
  | nil => intro _; rfl
  | cons function rest ih =>
    intro ready
    simp only [EffectProg.checkReadyWith, Bool.and_eq_true]
    exact ⟨EffectFunc.checkReadyWith_complete ready.1, ih ready.2⟩

theorem EffectProg.checkReady_complete {source : Module} {pool : Bytes.LiteralPool}
    (program : EffectProg pureSigs effectSigs) :
    program.Ready source pool → program.checkReady source pool = true :=
  EffectProg.checkReadyWith_complete program

end Verified.Wasi
