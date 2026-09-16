import Project.EulerCertificate.BoundaryPadded
import Project.EulerCertificate.FluxExecution
import Project.EulerCertificate.VectorExecution

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerRiemann
open Project.EulerRiemann.Traversal (Cell)
open Project.EulerRiemann.Execution (stateValues boolWord)
open Project.EulerReconstruction.Execution (facesValues)
open Project.EulerCertificateFlux.Execution (boundsValues vectorValues)

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

macro "boundary_face_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [stateValues, facesValues, vectorValues, boundsValues, List.set,
        List.cons_append, List.nil_append, List.getElem?_cons_zero,
        List.getElem?_cons_succ, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
    | (try simp only [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      conv => arg 2; simp [*, -UInt64.ofNat_add])

macro "boundary_face_call" call:term : tactic => `(tactic|
  (refine wp_call_tw $call ?_
   rintro final values ⟨hFinal, rfl⟩
   subst final
   boundary_face_peel))

theorem boundary_face_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (trials : UInt64) (axis : Bool) (owner pointer : UInt64)
    (grid : Array Cell) (line k : Nat)
    (hn : 2 ≤ n ∧ n ≤ 800) (hSize : grid.size = n * n)
    (hl : line < n) (hk : k ≤ n) (hGrid : Memory.GridAt initial pointer grid) :
    TerminatesWith env Project.EulerCertificate.«module» 170 initial
      [.i64 (UInt64.ofNat k), .i64 (UInt64.ofNat line), .i64 pointer, .i64 owner,
        .i64 (boolWord axis), .i64 trials, .i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧
        values = vectorValues (Boundary.face n trials.toNat axis grid line k)) := by
  have aCall := boundary_padded_exact env initial n axis owner pointer grid line k
    hn hSize hl (by omega) hGrid
  have bCall := boundary_padded_exact env initial n axis owner pointer grid line (k + 1)
    hn hSize hl (by omega) hGrid
  have cCall := boundary_padded_exact env initial n axis owner pointer grid line (k + 2)
    hn hSize hl (by omega) hGrid
  have dCall := boundary_padded_exact env initial n axis owner pointer grid line (k + 3)
    hn hSize hl (by omega) hGrid
  generalize ha : Boundary.padded n axis grid line k = a at aCall
  generalize hb : Boundary.padded n axis grid line (k + 1) = b at bCall
  generalize hc : Boundary.padded n axis grid line (k + 2) = c at cCall
  generalize hd : Boundary.padded n axis grid line (k + 3) = d at dCall
  have leftCall := reconstruct_exact env initial trials a b c
  have rightCall := reconstruct_exact env initial trials b c d
  generalize hLeft : Reconstruction.reconstruct trials.toNat a b c = left at leftCall
  generalize hRight : Reconstruction.reconstruct trials.toNat b c d = right at rightCall
  have fluxCall := selected_flux_exact env initial left.right right.left
  dsimp only [Project.EulerOutwardFlux.Execution.fluxValues] at fluxCall
  generalize hFlux : OutwardNumerics.fluxCheckedBits left.right.density left.right.mx
    left.right.my left.right.energy right.left.density right.left.mx right.left.my
    right.left.energy = flux at fluxCall
  have interfaceCall := flux_interface_exact env initial flux.alpha left.right right.left
  generalize hInterface : Flux.interface flux.alpha left.right right.left = interval at interfaceCall
  have orientCall := vector_orient_exact env initial axis interval
  generalize hOut : Vectors.orient axis interval = out at orientCall
  have hNat (j : Nat) (hj : j ≤ 3) : (UInt64.ofNat (k + j)).toNat = k + j :=
    UInt64.toNat_ofNat_of_lt' (by change k + j < 18446744073709551616; omega)
  have hkNat : (UInt64.ofNat k).toNat = k := by simpa using hNat 0 (by decide)
  have hAdd1 : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := (UInt64.ofNat_add k 1).symm
  have hAdd2 : UInt64.ofNat k + 2 = UInt64.ofNat (k + 2) := (UInt64.ofNat_add k 2).symm
  have hAdd3 : UInt64.ofNat k + 3 = UInt64.ofNat (k + 3) := (UInt64.ofNat_add k 3).symm
  have hGuard (j : Nat) (hj : j ≤ 3) : ¬ UInt64.ofNat (k + j) < UInt64.ofNat k := by
    simp only [UInt64.lt_iff_toNat_lt, hNat j hj, hkNat]
    omega
  have hGuard1 := hGuard 1 (by decide)
  have hGuard2 := hGuard 2 (by decide)
  have hGuard3 := hGuard 3 (by decide)
  simp only [Boundary.face, ha, hb, hc, hd, hLeft, hRight, hFlux, hInterface, hOut]
  refine TerminatesWith.of_wp_entry_for (f := func170Def) rfl ?_ (by decide)
  change wp Project.EulerCertificate.«module» func170 _ initial
    (func170Def.toLocals [.i64 (UInt64.ofNat n), .i64 trials, .i64 (boolWord axis),
      .i64 owner, .i64 pointer, .i64 (UInt64.ofNat line), .i64 (UInt64.ofNat k)]) env
  unfold func170
  wp_run [func170Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  boundary_face_call aCall
  boundary_face_call bCall
  boundary_face_call cCall
  boundary_face_call dCall
  boundary_face_call leftCall
  boundary_face_call rightCall
  boundary_face_call fluxCall
  boundary_face_call interfaceCall
  boundary_face_call orientCall
  simp

theorem boundary_line_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (trials : UInt64) (axis : Bool) (owner pointer : UInt64)
    (grid : Array Cell) (line : Nat)
    (hn : 2 ≤ n ∧ n ≤ 800) (hSize : grid.size = n * n)
    (hl : line < n) (hGrid : Memory.GridAt initial pointer grid) :
    TerminatesWith env Project.EulerCertificate.«module» 172 initial
      [.i64 (UInt64.ofNat line), .i64 pointer, .i64 owner,
        .i64 (boolWord axis), .i64 trials, .i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧
        values = vectorValues (Boundary.line n trials.toNat axis grid line)) := by
  have leftCall := boundary_face_exact env initial n trials axis owner pointer grid line 0
    hn hSize hl (by omega) hGrid
  have rightCall := boundary_face_exact env initial n trials axis owner pointer grid line n
    hn hSize hl (by omega) hGrid
  generalize hLeft : Boundary.face n trials.toNat axis grid line 0 = left at leftCall
  generalize hRight : Boundary.face n trials.toNat axis grid line n = right at rightCall
  have subCall := vector_sub_exact env initial left right
  generalize hSub : Vectors.sub left right = out at subCall
  simp only [Boundary.line, hLeft, hRight, hSub]
  refine TerminatesWith.of_wp_entry_for (f := func172Def) rfl ?_ (by decide)
  change wp Project.EulerCertificate.«module» func172 _ initial
    (func172Def.toLocals [.i64 (UInt64.ofNat n), .i64 trials, .i64 (boolWord axis),
      .i64 owner, .i64 pointer, .i64 (UInt64.ofNat line)]) env
  unfold func172
  wp_run [func172Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  boundary_face_call leftCall
  boundary_face_call rightCall
  boundary_face_call subCall
  simp

#print axioms boundary_face_exact
#print axioms boundary_line_exact
end Project.EulerCertificate.Execution
