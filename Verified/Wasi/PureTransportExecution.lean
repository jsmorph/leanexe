import Verified.Wasi.PureInstructions

namespace Verified.Wasi.PureTransport

open Wasm

def InstructionAt (World : Type) (source target : Module) (fuel : Nat)
    (inst : Instruction) : Prop :=
  ∀ (initial : Store Unit) (world : World) (locals : Locals)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World),
    execOne fuel target (restore world initial) locals (Relocation.instruction inst) targetHost =
        liftContinuation world (execOne fuel source initial locals inst sourceHost) ∧
      NoReturnCall (execOne fuel source initial locals inst sourceHost)

def ProgramAt (World : Type) (source target : Module) (fuel : Nat) (code : Program) : Prop :=
  ∀ (initial : Store Unit) (world : World) (locals : Locals)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World),
    exec fuel target (restore world initial) locals (Relocation.program code) targetHost =
        liftContinuation world (exec fuel source initial locals code sourceHost) ∧
      NoReturnCall (exec fuel source initial locals code sourceHost)

def EntryAt (World : Type) (source target : Module) (fuel index : Nat) : Prop :=
  ∀ (initial : Store Unit) (world : World) (args : List Value)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World),
    run fuel target (3 + index) (restore world initial) args targetHost =
      liftResult world (run fuel source index initial args sourceHost)

theorem program_at_of_instruction {World : Type} {source target : Module} {fuel : Nat}
    (hOne : ∀ inst, Encoding.InstructionForm inst →
      Relocation.instructionClosed source.funcs.length inst = true →
      InstructionAt World source target fuel inst) :
    ∀ code, Encoding.ProgramForm code →
      Relocation.programClosed source.funcs.length code = true →
      ProgramAt World source target fuel code := by
  intro code
  induction code with
  | nil =>
      intro _ _ initial world locals sourceHost targetHost
      simp only [Relocation.program, exec, liftContinuation, NoReturnCall, and_self]
  | cons head tail ih =>
      intro hForm hClosed initial world locals sourceHost targetHost
      cases hForm with
      | cons _ _ hHead hTail =>
        simp only [Relocation.programClosed, Bool.and_eq_true] at hClosed
        obtain ⟨hHeadEq, hHeadNoTail⟩ :=
          hOne head hHead hClosed.1 initial world locals sourceHost targetHost
        simp only [Relocation.program, exec]
        rw [hHeadEq]
        cases hExec : execOne fuel source initial locals head sourceHost with
        | Fallthrough store locals' => exact ih hTail hClosed.2 store world locals' sourceHost targetHost
        | Break label store locals' => exact ⟨rfl, trivial⟩
        | Return store values => exact ⟨rfl, trivial⟩
        | Trap store message => exact ⟨rfl, trivial⟩
        | Invalid message => exact ⟨rfl, trivial⟩
        | OutOfFuel => exact ⟨rfl, trivial⟩
        | ReturnCall entry store values => simp only [hExec, NoReturnCall] at hHeadNoTail
        | Throwing tag values store locals' => exact ⟨rfl, trivial⟩

theorem entry_at_of_program {World : Type} {source target : Module} {fuel : Nat}
    (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    (hCode : ∀ code, Encoding.ProgramForm code →
      Relocation.programClosed source.funcs.length code = true →
      ProgramAt World source target fuel code) :
    ∀ index, index < source.funcs.length → EntryAt World source target fuel index := by
  intro index hIndex initial world args sourceHost targetHost
  have hFunction : source.funcs[index]? = some source.funcs[index] :=
    List.getElem?_eq_getElem hIndex
  obtain ⟨hForm, hClosed⟩ := profile _ (List.mem_of_getElem? hFunction)
  exact run_frame_at layout.sourceImports layout.targetImports hFunction
    (layout.functions hFunction) (Relocation.function_shape _)
    fuel initial world args sourceHost targetHost
    (fun locals => (hCode _ hForm hClosed initial world locals sourceHost targetHost).1)
    (fun locals => (hCode _ hForm hClosed initial world locals sourceHost targetHost).2)

theorem block_at {World : Type} {source target : Module} {fuel : Nat}
    (types : List ValueType) (body : Program)
    (hBody : ProgramAt World source target fuel body) :
    InstructionAt World source target (fuel + 1) (.block 0 types.length body [] types) := by
  intro initial world locals sourceHost targetHost
  obtain ⟨hBodyEq, hBodyNoTail⟩ := hBody initial world locals sourceHost targetHost
  simp only [Relocation.instruction, execOne.eq_def]
  rw [hBodyEq]
  cases hExec : exec fuel source initial locals body sourceHost with
  | Fallthrough store locals' => exact ⟨rfl, trivial⟩
  | Break label store locals' => cases label <;> exact ⟨rfl, trivial⟩
  | Return store values => exact ⟨rfl, trivial⟩
  | Trap store message => exact ⟨rfl, trivial⟩
  | Invalid message => exact ⟨rfl, trivial⟩
  | OutOfFuel => exact ⟨rfl, trivial⟩
  | ReturnCall entry store values => simp only [hExec, NoReturnCall] at hBodyNoTail
  | Throwing tag values store locals' => exact ⟨rfl, trivial⟩

theorem loop_at {World : Type} {source target : Module} {fuel : Nat}
    (types : List ValueType) (body : Program)
    (hBody : ProgramAt World source target fuel body)
    (hRepeat : InstructionAt World source target fuel (.loop 0 types.length body [] types)) :
    InstructionAt World source target (fuel + 1) (.loop 0 types.length body [] types) := by
  intro initial world locals sourceHost targetHost
  obtain ⟨hBodyEq, hBodyNoTail⟩ := hBody initial world locals sourceHost targetHost
  simp only [Relocation.instruction, execOne_loop_succ]
  rw [hBodyEq]
  cases hExec : exec fuel source initial locals body sourceHost with
  | Fallthrough store locals' => exact ⟨rfl, trivial⟩
  | Break label store locals' =>
      cases label with
      | zero =>
          simpa only [Relocation.instruction, liftContinuation] using
            hRepeat store world
              { locals' with values := locals'.values.take 0 ++ locals.values.drop 0 }
              sourceHost targetHost
      | succ label => exact ⟨rfl, trivial⟩
  | Return store values => exact ⟨rfl, trivial⟩
  | Trap store message => exact ⟨rfl, trivial⟩
  | Invalid message => exact ⟨rfl, trivial⟩
  | OutOfFuel => exact ⟨rfl, trivial⟩
  | ReturnCall entry store values => simp only [hExec, NoReturnCall] at hBodyNoTail
  | Throwing tag values store locals' => exact ⟨rfl, trivial⟩

theorem iff_to_block {State : Type} {m : Module} {store : Store State} {locals : Locals}
    {host : HostEnv State} {condition : UInt32} {values : List Value}
    {fuel ps rs : Nat} {yes no : Program} {pts rts : List ValueType}
    (hValues : locals.values = .i32 condition :: values) :
    execOne (fuel + 1) m store locals (.iff ps rs yes no pts rts) host =
      execOne (fuel + 1) m store { locals with values := values }
        (.block ps rs (if condition ≠ 0 then yes else no) pts rts) host := by
  simp only [execOne.eq_def, hValues]

theorem iff_at {World : Type} {source target : Module} {fuel : Nat}
    (types : List ValueType) (yes no : Program)
    (hYes : InstructionAt World source target (fuel + 1) (.block 0 types.length yes [] types))
    (hNo : InstructionAt World source target (fuel + 1) (.block 0 types.length no [] types)) :
    InstructionAt World source target (fuel + 1) (.iff 0 types.length yes no [] types) := by
  intro initial world locals sourceHost targetHost
  simp only [Relocation.instruction]
  cases hValues : locals.values with
  | nil => simp only [execOne.eq_def, hValues, liftContinuation, NoReturnCall, and_self]
  | cons value values =>
      cases value with
      | i32 condition =>
          simp only [iff_to_block (host := targetHost) hValues,
            iff_to_block (host := sourceHost) hValues]
          by_cases hCondition : condition ≠ 0
          · simpa only [if_pos hCondition, Relocation.instruction] using
              hYes initial world { locals with values := values } sourceHost targetHost
          · simpa only [if_neg hCondition, Relocation.instruction] using
              hNo initial world { locals with values := values } sourceHost targetHost
      | _ => simp only [execOne.eq_def, hValues, liftContinuation, NoReturnCall, and_self]

theorem call_at {World : Type} {source target : Module} {fuel index : Nat}
    (hRun : EntryAt World source target fuel index) :
    InstructionAt World source target (fuel + 1) (.call index) := by
  intro initial world locals sourceHost targetHost
  simp only [Relocation.instruction, execOne.eq_def]
  rw [hRun initial world locals.values sourceHost targetHost]
  cases run fuel source index initial locals.values sourceHost <;> exact ⟨rfl, trivial⟩

theorem transport_fuel {World : Type} {source target : Module}
    (layout : Relocation.Layout source target) (profile : Relocation.Profile source) :
    ∀ fuel,
      (∀ inst, Encoding.InstructionForm inst →
        Relocation.instructionClosed source.funcs.length inst = true →
        InstructionAt World source target fuel inst) ∧
      (∀ code, Encoding.ProgramForm code →
        Relocation.programClosed source.funcs.length code = true →
        ProgramAt World source target fuel code) ∧
      (∀ index, index < source.funcs.length → EntryAt World source target fuel index) := by
  intro fuel
  induction fuel with
  | zero =>
      have hOne : ∀ inst, Encoding.InstructionForm inst →
          Relocation.instructionClosed source.funcs.length inst = true →
          InstructionAt World source target 0 inst := by
        intro inst _ _ initial world locals sourceHost targetHost
        simp only [execOne.eq_def, liftContinuation, NoReturnCall, and_self]
      have hCode := program_at_of_instruction hOne
      exact ⟨hOne, hCode, entry_at_of_program layout profile hCode⟩
  | succ fuel ih =>
      obtain ⟨ihOne, ihCode, ihRun⟩ := ih
      have hOne : ∀ inst, Encoding.InstructionForm inst →
          Relocation.instructionClosed source.funcs.length inst = true →
          InstructionAt World source target (fuel + 1) inst := by
        intro inst hForm hClosed
        by_cases hAtomic : atomic inst = true
        · intro initial world locals sourceHost targetHost
          rw [relocate_atomic hForm hAtomic]
          exact atomic_transport layout.memory64 layout.memoryCap hForm hAtomic
            (fuel + 1) initial world locals sourceHost targetHost
        · cases hForm with
          | call index bound =>
              have hIndex : index < source.funcs.length := of_decide_eq_true
                (by simpa only [Relocation.instructionClosed] using hClosed)
              exact call_at (ihRun index hIndex)
          | block types body hTypes hBody =>
              exact block_at types body (ihCode body hBody hClosed)
          | loop types body hTypes hBody =>
              exact loop_at types body (ihCode body hBody hClosed)
                (ihOne _ (.loop types body hTypes hBody) hClosed)
          | iff types yes no hTypes hYes hNo =>
              simp only [Relocation.instructionClosed, Bool.and_eq_true] at hClosed
              exact iff_at types yes no
                (block_at types yes (ihCode yes hYes hClosed.1))
                (block_at types no (ihCode no hNo hClosed.2))
          | _ => simp [atomic] at hAtomic
      have hCode := program_at_of_instruction hOne
      exact ⟨hOne, hCode, entry_at_of_program layout profile hCode⟩

theorem code_transport {World : Type} {source target : Module}
    (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    {code : Program} (hForm : Encoding.ProgramForm code)
    (hClosed : Relocation.programClosed source.funcs.length code = true) :
    CodeTransport World source target code (Relocation.program code) := by
  intro fuel initial world locals sourceHost targetHost
  exact ((transport_fuel layout profile fuel).2.1 code hForm hClosed
    initial world locals sourceHost targetHost).1

theorem entry_transport {World : Type} {source target : Module}
    (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length) :
    ∀ fuel, EntryAt World source target fuel index :=
  fun fuel => (transport_fuel layout profile fuel).2.2 index hIndex

end Verified.Wasi.PureTransport
