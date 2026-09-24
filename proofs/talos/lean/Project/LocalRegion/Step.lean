import Project.LocalRegion.Control

namespace Project.LocalRegion
open Wasm Project.FunctionRegion
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

macro "relate_atomic" frame:ident hFrame:ident : tactic => `(tactic|
  (simp only [renameInstruction, execOne.eq_def, Frame.values $frame $hFrame]
   repeat' (first
     | split
     | exact Continuations.next _ _ _ (Frame.stack $frame $hFrame _)
     | exact Continuations.branch _ _ _ _ (Frame.stack $frame $hFrame _)
     | exact Continuations.branch _ _ _ _ $hFrame
     | exact Continuations.thrown _ _ _ _ _ (Frame.stack $frame $hFrame _)
     | exact Continuations.exhausted
     | apply Continuations.invalid
     | apply Continuations.trap
     | apply Continuations.returned)))

theorem execOne_succ
    (frame : Frame slots localDomain)
    (hMemory : source.memory = target.memory)
    (hOne : ∀ (env : HostEnv α) st s t inst,
      frame.Related s t → PortableInstruction callDomain inst →
      AllowedInstruction localDomain inst →
      Continuations frame.Related (execOne fuel source st s inst env)
        (execOne fuel target st t (renameInstruction calls slots inst) env))
    (hExec : ∀ (env : HostEnv α) st s t program,
      frame.Related s t → PortableProgram callDomain program →
      AllowedProgram localDomain program →
      Continuations frame.Related (exec fuel source st s program env)
        (exec fuel target st t (renameProgram calls slots program) env))
    (hRun : ∀ (env : HostEnv α) st args id,
      callDomain id → run fuel target (calls id) st args env =
        run fuel source id st args env)
    (env : HostEnv α) (st : Store α) (s t : Locals) (inst : Instruction)
    (hFrame : frame.Related s t)
    (hPortable : PortableInstruction callDomain inst)
    (hAllowed : AllowedInstruction localDomain inst) :
    Continuations frame.Related (execOne (fuel + 1) source st s inst env)
      (execOne (fuel + 1) target st t (renameInstruction calls slots inst) env) := by
  cases hPortable with
  | localGet i =>
      simp only [renameInstruction, execOne.eq_def, frame.read hFrame hAllowed,
        frame.values hFrame]
      cases hGet : s.get i
      · exact .invalid _
      · exact .next _ _ _ (frame.stack hFrame _)
  | localSet i =>
      simp only [renameInstruction, execOne.eq_def, frame.values hFrame]
      cases hValues : s.values with
      | nil => exact .invalid _
      | cons value rest =>
          have hWrite := frame.write hFrame hAllowed value
          cases hs : s.set? i value <;> cases ht : t.set? (slots i) value <;>
            rw [hs, ht] at hWrite <;> cases hWrite
          · simp only [hs, ht]; exact .invalid _
          · simp only [hs, ht]; exact .next _ _ _ (frame.stack (by assumption) _)
  | localTee i =>
      simp only [renameInstruction, execOne.eq_def, frame.values hFrame]
      cases hValues : s.values with
      | nil => exact .invalid _
      | cons value rest =>
          have hWrite := frame.write hFrame hAllowed value
          cases hs : s.set? i value <;> cases ht : t.set? (slots i) value <;>
            rw [hs, ht] at hWrite <;> cases hWrite
          · simp only [hs, ht]; exact .invalid _
          · simp only [hs, ht]; exact .next _ _ _ (by assumption)
  | globalGet => relate_atomic frame hFrame
  | globalSet => relate_atomic frame hFrame
  | const32 => relate_atomic frame hFrame
  | const64 => relate_atomic frame hFrame
  | eqI32 => relate_atomic frame hFrame
  | addI64 => relate_atomic frame hFrame
  | subI64 => relate_atomic frame hFrame
  | mulI64 => relate_atomic frame hFrame
  | divUI64 => relate_atomic frame hFrame
  | remUI64 => relate_atomic frame hFrame
  | andI64 => relate_atomic frame hFrame
  | orI64 => relate_atomic frame hFrame
  | shlI64 => relate_atomic frame hFrame
  | shrUI64 => relate_atomic frame hFrame
  | f32ReinterpretI32 => relate_atomic frame hFrame
  | i32ReinterpretF32 => relate_atomic frame hFrame
  | f32Add => relate_atomic frame hFrame
  | f32Sub => relate_atomic frame hFrame
  | f32Mul => relate_atomic frame hFrame
  | f32Div => relate_atomic frame hFrame
  | f32Sqrt => relate_atomic frame hFrame
  | f64ReinterpretI64 => relate_atomic frame hFrame
  | i64ReinterpretF64 => relate_atomic frame hFrame
  | f64Add => relate_atomic frame hFrame
  | f64Sub => relate_atomic frame hFrame
  | f64Mul => relate_atomic frame hFrame
  | f64Div => relate_atomic frame hFrame
  | f64Sqrt => relate_atomic frame hFrame
  | eqI64 => relate_atomic frame hFrame
  | neI64 => relate_atomic frame hFrame
  | eqz => relate_atomic frame hFrame
  | leUI64 => relate_atomic frame hFrame
  | ltUI64 => relate_atomic frame hFrame
  | geUI64 => relate_atomic frame hFrame
  | wrapI64 => relate_atomic frame hFrame
  | extendUI32 => relate_atomic frame hFrame
  | load32 => relate_atomic frame hFrame
  | store32 => relate_atomic frame hFrame
  | load64 => relate_atomic frame hFrame
  | store64 => relate_atomic frame hFrame
  | unreachable => relate_atomic frame hFrame
  | ret => relate_atomic frame hFrame
  | br => relate_atomic frame hFrame
  | brIf => relate_atomic frame hFrame
  | memorySize =>
      simp only [renameInstruction, execOne.eq_def, Module.memIs64, hMemory]
      split <;> exact .next _ _ _ (by simpa only [frame.values hFrame] using frame.stack hFrame _)
  | memoryGrow =>
      have hCap : st.memoryCap target 0 = st.memoryCap source 0 := by
        simp [Store.memoryCap, Module.memoryCap, hMemory]
      simp only [renameInstruction, execOne.eq_def, hCap, frame.values hFrame]
      repeat' (first
        | split
        | exact Continuations.next _ _ _ (frame.stack hFrame _)
        | apply Continuations.invalid
        | apply Continuations.trap)
  | block params results body paramTypes resultTypes hBody =>
      simp only [renameInstruction, execOne.eq_def, frame.values hFrame]
      exact exitBlock_related frame results (s.values.drop params)
        (hExec env st s t body hFrame hBody hAllowed)
  | loop params results body paramTypes resultTypes hBody =>
      simp only [renameInstruction, execOne_loop_succ]
      have h := hExec env st s t body hFrame hBody hAllowed
      generalize exec fuel source st s body env = leftResult at h ⊢
      generalize exec fuel target st t (renameProgram calls slots body) env = rightResult at h ⊢
      cases h with
      | next st' s' t' h' =>
          simpa only [frame.values hFrame, frame.values h'] using
            Continuations.next st' _ _ (frame.stack h' _)
      | branch k st' s' t' h' =>
          cases k with
          | zero =>
              simp only [frame.values hFrame, frame.values h']
              exact hOne env st' _ _ _ (frame.stack h' _) (.loop _ _ _ _ _ hBody) hAllowed
          | succ k => exact .branch _ _ _ _ h'
      | returned => exact .returned _ _
      | trap => exact .trap _ _
      | invalid => exact .invalid _
      | exhausted => exact .exhausted
      | tail => exact .tail _ _ _
      | thrown _ _ _ _ _ h' => exact .thrown _ _ _ _ _ h'
  | branch params results yes no paramTypes resultTypes hYes hNo =>
      simp only [renameInstruction, execOne.eq_def, frame.values hFrame]
      cases hValues : s.values with
      | nil => exact .invalid _
      | cons value values =>
          cases value with
          | i32 condition =>
              by_cases hCondition : condition ≠ 0
              · simp only [if_pos hCondition]
                exact exitBlock_related frame results (values.drop params)
                  (hExec env st _ _ yes (frame.stack hFrame values) hYes hAllowed.1)
              · simp only [if_neg hCondition]
                exact exitBlock_related frame results (values.drop params)
                  (hExec env st _ _ no (frame.stack hFrame values) hNo hAllowed.2)
          | _ => exact .invalid _
  | call id hDomain =>
      simp only [renameInstruction, execOne.eq_def, frame.values hFrame,
        hRun env st s.values id hDomain]
      cases run fuel source id st s.values env
      · exact .next _ _ _ (frame.stack hFrame _)
      · exact .trap _ _
      · exact .invalid _
      · exact .exhausted
      · exact .thrown _ _ _ _ _ hFrame

end Project.LocalRegion
