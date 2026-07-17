import Project.ClobPostOnly.Program
import Project.ClobFindBest.Model
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Call

/-!
# Search helpers used by `postOnly`

The generated `postOnly` artifact contains the four pure helpers used by its
`findBest` call.  Each theorem states a helper directly over `OrderL` values
and preserves the store.  These statements match the earlier search proof at
the new artifact's function indices.
-/

namespace Project.ClobPostOnly.SearchHelpers

open Wasm Project.Clob Project.ClobPostOnly Project.ClobFindBest.Model

set_option maxHeartbeats 64000000

def boolWord (p : Prop) [Decidable p] : UInt64 :=
  if p then 1 else 0

macro "po_step" : tactic => `(tactic|
  (refine wp_iff_cons rfl ?_;
   repeat (split <;> try (exfalso; simp_all; done));
   wp_run;
   simp only [List.cons_append, List.nil_append, List.append_nil,
     List.append_eq, List.append, List.take, List.drop]))

theorem func7_spec (env : HostEnv Unit) (st : Store Unit) (side : UInt64) :
    TerminatesWith (m := «module») (id := 7) (initial := st) (env := env)
      [.i64 side]
      (fun st' vs => vs = [.i64 (boolWord (side = 0))] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func7Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func7 _ st
      { params := [.i64 side], locals := [.i64 0], values := [] } env
    unfold func7
    wp_run
    by_cases h : side = 0 <;>
      (po_step; po_step; po_step; simp [h, boolWord, func7Def])

theorem func9_spec (env : HostEnv Unit) (st : Store Unit)
    (taker maker : OrderL) :
    TerminatesWith (m := «module») (id := 9) (initial := st) (env := env)
      [.i64 maker.oqty, .i64 maker.oprice, .i64 maker.oside,
       .i64 maker.otrader, .i64 maker.oid,
       .i64 taker.oqty, .i64 taker.oprice, .i64 taker.oside,
       .i64 taker.otrader, .i64 taker.oid]
      (fun st' vs =>
        vs = [.i64 (boolWord (crossesL taker maker))] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func9Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func9 _ st
      { params := [.i64 taker.oid, .i64 taker.otrader, .i64 taker.oside,
          .i64 taker.oprice, .i64 taker.oqty, .i64 maker.oid,
          .i64 maker.otrader, .i64 maker.oside, .i64 maker.oprice,
          .i64 maker.oqty],
        locals := [.i64 0], values := [] } env
    unfold func9
    wp_run
    by_cases hs : taker.oside = 0
    · by_cases hp : maker.oprice ≤ taker.oprice <;>
        (po_step; po_step; po_step; po_step;
          simp [hs, hp, boolWord, func9Def])
    · by_cases hp : taker.oprice ≤ maker.oprice <;>
        (po_step; po_step; po_step; po_step;
          simp [hp, boolWord, func9Def])

theorem func10_spec (env : HostEnv Unit) (st : Store Unit)
    (taker maker : OrderL) :
    TerminatesWith (m := «module») (id := 10) (initial := st) (env := env)
      [.i64 maker.oqty, .i64 maker.oprice, .i64 maker.oside,
       .i64 maker.otrader, .i64 maker.oid,
       .i64 taker.oqty, .i64 taker.oprice, .i64 taker.oside,
       .i64 taker.otrader, .i64 taker.oid]
      (fun st' vs =>
        vs = [.i64 (boolWord (eligibleL taker maker))] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func10Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func10 _ st
      { params := [.i64 taker.oid, .i64 taker.otrader, .i64 taker.oside,
          .i64 taker.oprice, .i64 taker.oqty, .i64 maker.oid,
          .i64 maker.otrader, .i64 maker.oside, .i64 maker.oprice,
          .i64 maker.oqty],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func10
    wp_run
    refine wp_call_tw (func7_spec env st taker.oside) ?_
    rintro st1 vs ⟨rfl, rfl⟩
    have hop : boolWord (taker.oside = 0) = oppositeSideL taker.oside := by
      simp [boolWord, oppositeSideL]
    simp only [hop]
    wp_run
    by_cases hs : maker.oside = oppositeSideL taker.oside
    · by_cases ht : maker.otrader = taker.otrader
      · po_step
        po_step
        po_step
        po_step
        po_step
        simp [eligibleL, hs, ht, boolWord, oppositeSideL, func10Def]
      · po_step
        po_step
        po_step
        po_step
        refine wp_call_tw (func9_spec env st1 taker maker) ?_
        rintro st2 vs ⟨rfl, rfl⟩
        by_cases hc : crossesL taker maker
        · simp only [boolWord, if_pos hc]
          wp_run
          po_step
          simp [hs, func10Def]
        · simp only [boolWord, if_neg hc]
          wp_run
          po_step
          simp [hs, func10Def]
    · po_step
      po_step
      po_step
      po_step
      simp [func10Def, boolWord]
      intro hside
      exact (hs hside).elim

theorem func11_spec (env : HostEnv Unit) (st : Store Unit)
    (taker candidate incumbent : OrderL) :
    TerminatesWith (m := «module») (id := 11) (initial := st) (env := env)
      [.i64 incumbent.oqty, .i64 incumbent.oprice, .i64 incumbent.oside,
       .i64 incumbent.otrader, .i64 incumbent.oid,
       .i64 candidate.oqty, .i64 candidate.oprice, .i64 candidate.oside,
       .i64 candidate.otrader, .i64 candidate.oid,
       .i64 taker.oqty, .i64 taker.oprice, .i64 taker.oside,
       .i64 taker.otrader, .i64 taker.oid]
      (fun st' vs =>
        vs = [.i64 (boolWord (betterPriceL taker candidate incumbent))] ∧
        st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func11Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func11 _ st
      { params := [.i64 taker.oid, .i64 taker.otrader, .i64 taker.oside,
          .i64 taker.oprice, .i64 taker.oqty, .i64 candidate.oid,
          .i64 candidate.otrader, .i64 candidate.oside,
          .i64 candidate.oprice, .i64 candidate.oqty, .i64 incumbent.oid,
          .i64 incumbent.otrader, .i64 incumbent.oside,
          .i64 incumbent.oprice, .i64 incumbent.oqty],
        locals := [.i64 0], values := [] } env
    unfold func11
    wp_run
    by_cases hs : taker.oside = 0
    · by_cases hp : candidate.oprice < incumbent.oprice <;>
        (po_step; po_step; po_step; po_step;
          simp [hs, hp, boolWord, func11Def])
    · by_cases hp : incumbent.oprice < candidate.oprice <;>
        (po_step; po_step; po_step; po_step;
          simp [hp, boolWord, func11Def])

end Project.ClobPostOnly.SearchHelpers
