import Project.EulerConservative.Rejection

namespace Project.EulerConservative.Execution
open Wasm
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def resultValues (rho momentum energy : UInt64) : List Wasm.Value :=
  let out := Model.sideCheckedBits rho momentum energy
  [.i64 out.energyFlux, .i64 out.momentumFlux, .i64 out.massFlux,
    .i64 out.speed, .i64 out.pressure, .i64 out.velocity, .i64 out.status]

macro "side_fp_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [boolWord, Wasm.f64Add, Wasm.f64Sub, Wasm.f64Mul, Wasm.f64Div, Wasm.f64Sqrt, List.set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
        reduceIte, ite_true, ite_false, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
    | refine wp_iff_cons rfl ?_
      simp [boolWord, *])

theorem sideCheckedBits_exact_in_module {m : Wasm.Module}
    (layout : HelperLayout m) (hside : m.funcs[5]? = some func5Def)
    (env : HostEnv Unit) (initial : Store Unit) (rho momentum energy : UInt64) :
    TerminatesWith env m 5 initial [.i64 energy, .i64 momentum, .i64 rho]
      (fun final values => final = initial ∧ values = resultValues rho momentum energy) := by
  let velocity := Wasm.IEEE64.div momentum rho
  let transport := Wasm.IEEE64.mul momentum velocity
  let halfKinetic := Wasm.IEEE64.mul 0x3FE0000000000000 transport
  let internal := Wasm.IEEE64.sub energy halfKinetic
  let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
  let pressureOverDensity := Wasm.IEEE64.div pressure rho
  let radicand := Wasm.IEEE64.mul 0x3FF6666666666666 pressureOverDensity
  let soundSpeed := Wasm.IEEE64.sqrt radicand
  let speed := Wasm.IEEE64.add (Model.absBits velocity) soundSpeed
  let momentumFlux := Wasm.IEEE64.add transport pressure
  let enthalpy := Wasm.IEEE64.add energy pressure
  let energyFlux := Wasm.IEEE64.mul velocity enthalpy
  refine TerminatesWith.of_wp_entry_for (f := func5Def)
    (by simpa [layout.noImports] using hside) ?_ (by simp [layout.noImports])
  change wp m func5 _ initial (func5Def.toLocals [.i64 rho, .i64 momentum, .i64 energy]) env
  unfold func5
  wp_run [func5Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  refine wp_call_tw (stateGuard_exact layout env initial rho momentum energy) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases h0 : Model.stateGuard rho momentum energy
  · side_fp_peel
    refine wp_call_tw (rejectedSide_exact layout env initial) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    side_fp_peel
    simp [resultValues, Model.sideCheckedBits, Model.rejectedSide, *]
  · side_fp_peel
    refine wp_call_tw (finiteBits_exact layout env initial velocity) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    cases h1 : Model.finiteBits velocity
    · side_fp_peel
      refine wp_call_tw (rejectedSide_exact layout env initial) ?_
      rintro st values ⟨hst, rfl⟩
      subst st
      side_fp_peel
      simp [resultValues, Model.sideCheckedBits, Model.rejectedSide, velocity, *]
    · side_fp_peel
      refine wp_call_tw (finiteBits_exact layout env initial transport) ?_
      rintro st values ⟨hst, rfl⟩
      subst st
      cases h2 : Model.finiteBits transport
      · side_fp_peel
        refine wp_call_tw (rejectedSide_exact layout env initial) ?_
        rintro st values ⟨hst, rfl⟩
        subst st
        side_fp_peel
        simp [resultValues, Model.sideCheckedBits, Model.rejectedSide, velocity, transport, *]
      · side_fp_peel
        refine wp_call_tw (finiteBits_exact layout env initial halfKinetic) ?_
        rintro st values ⟨hst, rfl⟩
        subst st
        cases h3 : Model.finiteBits halfKinetic
        · side_fp_peel
          refine wp_call_tw (rejectedSide_exact layout env initial) ?_
          rintro st values ⟨hst, rfl⟩
          subst st
          side_fp_peel
          simp [resultValues, Model.sideCheckedBits, Model.rejectedSide, velocity, transport, halfKinetic, *]
        · side_fp_peel
          refine wp_call_tw (positiveBits_exact layout env initial internal) ?_
          rintro st values ⟨hst, rfl⟩
          subst st
          cases h4 : Model.positiveBits internal
          · side_fp_peel
            refine wp_call_tw (rejectedSide_exact layout env initial) ?_
            rintro st values ⟨hst, rfl⟩
            subst st
            side_fp_peel
            simp [resultValues, Model.sideCheckedBits, Model.rejectedSide, velocity, transport, halfKinetic, internal, *]
          · side_fp_peel
            refine wp_call_tw (positiveBits_exact layout env initial pressure) ?_
            rintro st values ⟨hst, rfl⟩
            subst st
            cases h5 : Model.positiveBits pressure
            · side_fp_peel
              refine wp_call_tw (rejectedSide_exact layout env initial) ?_
              rintro st values ⟨hst, rfl⟩
              subst st
              side_fp_peel
              simp [resultValues, Model.sideCheckedBits, Model.rejectedSide, velocity, transport, halfKinetic, internal, pressure, *]
            · side_fp_peel
              refine wp_call_tw (positiveBits_exact layout env initial pressureOverDensity) ?_
              rintro st values ⟨hst, rfl⟩
              subst st
              cases h6 : Model.positiveBits pressureOverDensity
              · side_fp_peel
                refine wp_call_tw (rejectedSide_exact layout env initial) ?_
                rintro st values ⟨hst, rfl⟩
                subst st
                side_fp_peel
                simp [resultValues, Model.sideCheckedBits, Model.rejectedSide, velocity, transport, halfKinetic, internal, pressure, pressureOverDensity, *]
              · side_fp_peel
                refine wp_call_tw (positiveBits_exact layout env initial radicand) ?_
                rintro st values ⟨hst, rfl⟩
                subst st
                cases h7 : Model.positiveBits radicand
                · side_fp_peel
                  refine wp_call_tw (rejectedSide_exact layout env initial) ?_
                  rintro st values ⟨hst, rfl⟩
                  subst st
                  side_fp_peel
                  simp [resultValues, Model.sideCheckedBits, Model.rejectedSide, velocity, transport, halfKinetic, internal, pressure, pressureOverDensity, radicand, *]
                · side_fp_peel
                  refine wp_call_tw (absBits_exact layout env initial velocity) ?_
                  rintro st values ⟨hst, rfl⟩
                  subst st
                  side_fp_peel
                  refine wp_call_tw (positiveBits_exact layout env initial soundSpeed) ?_
                  rintro st values ⟨hst, rfl⟩
                  subst st
                  cases h8 : Model.positiveBits soundSpeed
                  · side_fp_peel
                    refine wp_call_tw (rejectedSide_exact layout env initial) ?_
                    rintro st values ⟨hst, rfl⟩
                    subst st
                    side_fp_peel
                    simp [resultValues, Model.sideCheckedBits, Model.rejectedSide, velocity, transport, halfKinetic, internal, pressure, pressureOverDensity, radicand, soundSpeed, *]
                  · side_fp_peel
                    refine wp_call_tw (positiveBits_exact layout env initial speed) ?_
                    rintro st values ⟨hst, rfl⟩
                    subst st
                    cases h9 : Model.positiveBits speed
                    · side_fp_peel
                      refine wp_call_tw (rejectedSide_exact layout env initial) ?_
                      rintro st values ⟨hst, rfl⟩
                      subst st
                      side_fp_peel
                      simp [resultValues, Model.sideCheckedBits, Model.rejectedSide, velocity, transport, halfKinetic, internal, pressure, pressureOverDensity, radicand, soundSpeed, speed, *]
                    · side_fp_peel
                      refine wp_call_tw (finiteBits_exact layout env initial momentumFlux) ?_
                      rintro st values ⟨hst, rfl⟩
                      subst st
                      cases h10 : Model.finiteBits momentumFlux
                      · side_fp_peel
                        refine wp_call_tw (rejectedSide_exact layout env initial) ?_
                        rintro st values ⟨hst, rfl⟩
                        subst st
                        side_fp_peel
                        simp [resultValues, Model.sideCheckedBits, Model.rejectedSide, velocity, transport, halfKinetic, internal, pressure, pressureOverDensity, radicand, soundSpeed, speed, momentumFlux, *]
                      · side_fp_peel
                        refine wp_call_tw (finiteBits_exact layout env initial enthalpy) ?_
                        rintro st values ⟨hst, rfl⟩
                        subst st
                        cases h11 : Model.finiteBits enthalpy
                        · side_fp_peel
                          refine wp_call_tw (rejectedSide_exact layout env initial) ?_
                          rintro st values ⟨hst, rfl⟩
                          subst st
                          side_fp_peel
                          simp [resultValues, Model.sideCheckedBits, Model.rejectedSide, velocity, transport, halfKinetic, internal, pressure, pressureOverDensity, radicand, soundSpeed, speed, momentumFlux, enthalpy, *]
                        · side_fp_peel
                          refine wp_call_tw (finiteBits_exact layout env initial energyFlux) ?_
                          rintro st values ⟨hst, rfl⟩
                          subst st
                          cases h12 : Model.finiteBits energyFlux
                          · side_fp_peel
                            refine wp_call_tw (rejectedSide_exact layout env initial) ?_
                            rintro st values ⟨hst, rfl⟩
                            subst st
                            side_fp_peel
                            simp [resultValues, Model.sideCheckedBits, Model.rejectedSide, velocity, transport, halfKinetic, internal, pressure, pressureOverDensity, radicand, soundSpeed, speed, momentumFlux, enthalpy, energyFlux, *]
                          · side_fp_peel
                            simp [resultValues, Model.sideCheckedBits, velocity, transport, halfKinetic, internal, pressure, pressureOverDensity, radicand, soundSpeed, speed, momentumFlux, enthalpy, energyFlux, *]

#print axioms sideCheckedBits_exact_in_module
end Project.EulerConservative.Execution
