import Project.ProofKit.Frame
import Interpreter.Wasm.Wp.Loop

namespace Project.ProofKit.RangeFoldLoop

open Wasm

def body (indexLocal stopLocal : Nat) (stepCode : Wasm.Program) : Wasm.Program :=
  [.localGet indexLocal, .localGet stopLocal, .geUI64, .br_if 1] ++ stepCode ++ [.br 0]

def program (indexLocal stopLocal : Nat) (stepCode : Wasm.Program) : Wasm.Program :=
  [.block 0 0 [.loop 0 0 (body indexLocal stopLocal stepCode)]]

def Ready (indexLocal stopLocal count index : Nat) (frame : Locals) : Prop :=
  frame.values = [] ∧
  frame.get indexLocal = some (.i64 (UInt64.ofNat index)) ∧
  frame.get stopLocal = some (.i64 (UInt64.ofNat count))

def measure (indexLocal count : Nat) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get indexLocal with
  | some (.i64 index) => count - index.toNat
  | _ => count

theorem program_spec (indexLocal stopLocal : Nat) (stepCode : Wasm.Program)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (count : Nat) (P : Nat → Locals → Prop)
    (hcount : count < UInt64.size)
    (hready : Ready indexLocal stopLocal count 0 frame) (hP : P 0 frame)
    (hstep : ∀ index next, index < count →
      Ready indexLocal stopLocal count index next → P index next →
      ∀ (Q : Assertion Unit) rest,
      (∀ result, Ready indexLocal stopLocal count (index + 1) result →
        P (index + 1) result → wp module_ rest Q initial result env) →
      wp module_ (stepCode ++ rest) Q initial next env)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hdone : ∀ result, Ready indexLocal stopLocal count count result →
      P count result → wp module_ rest Q initial result env) :
    wp module_ (program indexLocal stopLocal stepCode ++ rest) Q initial frame env := by
  let Inv : AssertionF Unit := fun current next => current = initial ∧
    ∃ index, index ≤ count ∧ Ready indexLocal stopLocal count index next ∧ P index next
  have hentry := hready.1
  simp only [program, List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := Inv) (μ := measure indexLocal count)
  · exact ⟨rfl, 0, Nat.zero_le _, hready, hP⟩
  · rintro current next ⟨rfl, index, hindex, hready, hP⟩
    have hindex64 : index < UInt64.size := lt_of_le_of_lt hindex hcount
    simp only [body, List.cons_append, List.nil_append, wp_localGet_cons,
      Frame.withValues_get, hready.1, hready.2.1, hready.2.2,
      wp_geUI64_cons, wp_br_if_cons]
    by_cases hlast : index = count
    · subst index
      rw [ite_eq_left (show UInt64.ofNat count ≥ UInt64.ofNat count by simp)]
      simp [hentry]
      have hempty : ({ next with values := [] } : Locals) = next :=
        Frame.ext _ _ rfl rfl hready.1.symm
      simpa only [hempty] using hdone next hready hP
    · have hlt : index < count := by omega
      have hguard : ¬ UInt64.ofNat count ≤ UInt64.ofNat index := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hcount,
          UInt64.toNat_ofNat_of_lt' hindex64]
        omega
      simp only [ge_iff_le, hguard, ite_false]
      have hempty : ({ next with values := [] } : Locals) = next :=
        Frame.ext _ _ rfl rfl hready.1.symm
      rw [hempty]
      apply hstep index next hlt hready hP
      intro result hresult hPresult
      simp only [wp_br_cons, hresult.1, List.take_zero, List.drop_zero, List.nil_append]
      have hresultEmpty : ({ result with values := [] } : Locals) = result :=
        Frame.ext _ _ rfl rfl hresult.1.symm
      change Inv current { result with values := [] } ∧
        measure indexLocal count current { result with values := [] } < measure indexLocal count current next
      rw [hresultEmpty]
      refine ⟨⟨rfl, index + 1, by omega, hresult, hPresult⟩, ?_⟩
      simp only [measure, hresult.2.1, hready.2.1,
        UInt64.toNat_ofNat_of_lt' (show index + 1 < UInt64.size by omega),
        UInt64.toNat_ofNat_of_lt' hindex64]
      omega

#print axioms program_spec

end Project.ProofKit.RangeFoldLoop
