import Project.Beck.ExecutionJobAccepted

namespace Project.Beck.Execution

open Wasm Project.ProofKit LeanExe.Examples.Beck

theorem jobReadFrame_reconstruct (frame : Locals) (count categories members : Nat)
    (wordsPointer incidencePointer rowPointer internal : UInt64) (state : ParseState) (tail : JobTail)
    (params : frame.params = jobParams count categories wordsPointer incidencePointer state)
    (locals : frame.locals.length = 60) (values : frame.values = [])
    (r8 : frame.get 8 = some (.i64 internal)) (r9 : frame.get 9 = some (.i64 0)) (r15 : frame.get 15 = some (.i64 0))
    (r16 : frame.get 16 = some (.i64 members.toUInt64)) (r17 : frame.get 17 = some (.i64 (state.position + 1).toUInt64))
    (r29 : frame.get 29 = some (.i64 rowPointer))
    (tailReads : ∀ index : Fin 17, frame.get (index.val + 51) = some (.i64 (tail index))) :
    frame = jobReadFrame count categories members wordsPointer incidencePointer rowPointer internal state
      (fun k => frame.locals[k.val]!) tail := by
  have paramsLength : frame.params.length = 8 := by simp [params, jobParams]
  have a := job_local_read frame 8 (.i64 members.toUInt64) paramsLength locals (by decide) r16
  have b := job_local_read frame 9 (.i64 (state.position + 1).toUInt64) paramsLength locals (by decide) r17
  have c := job_local_read frame 21 (.i64 rowPointer) paramsLength locals (by decide) r29
  have fixed : jobReadSaved members (state.position + 1) rowPointer (fun k => frame.locals[k.val]!) =
      (fun k => frame.locals[k.val]!) := by
    funext k
    by_cases h8 : k.val = 8
    · simp [jobReadSaved, h8, a]
    by_cases h9 : k.val = 9
    · simp [jobReadSaved, h9, b]
    by_cases h21 : k.val = 21
    · simp [jobReadSaved, h21, c]
    simp [jobReadSaved, h8, h9, h21]
  rw [jobReadFrame, fixed]
  exact jobFrame_reconstruct frame count categories wordsPointer incidencePointer internal state tail params locals values r8 r9 r15 tailReads

theorem jobReadFrame_wp (env : HostEnv Unit) (initial : Store Unit) (frame : Locals) (count categories members : Nat)
    (wordsPointer incidencePointer rowPointer internal : UInt64) (state : ParseState) (tail : JobTail)
    (Q : Assertion Unit) (program : Wasm.Program)
    (next : ∀ saved tail, wp Project.Beck.«module» program Q initial
      (jobReadFrame count categories members wordsPointer incidencePointer rowPointer internal state saved tail) env)
    (params : frame.params = jobParams count categories wordsPointer incidencePointer state)
    (locals : frame.locals.length = 60) (values : frame.values = [])
    (r8 : frame.get 8 = some (.i64 internal)) (r9 : frame.get 9 = some (.i64 0)) (r15 : frame.get 15 = some (.i64 0))
    (r16 : frame.get 16 = some (.i64 members.toUInt64)) (r17 : frame.get 17 = some (.i64 (state.position + 1).toUInt64))
    (r29 : frame.get 29 = some (.i64 rowPointer))
    (tailReads : ∀ index : Fin 17, frame.get (index.val + 51) = some (.i64 (tail index))) :
    wp Project.Beck.«module» program Q initial frame env := by
  rw [jobReadFrame_reconstruct frame count categories members wordsPointer incidencePointer rowPointer internal state tail
    params locals values r8 r9 r15 r16 r17 r29 tailReads]
  exact next _ tail

#print axioms jobReadFrame_reconstruct

end Project.Beck.Execution
