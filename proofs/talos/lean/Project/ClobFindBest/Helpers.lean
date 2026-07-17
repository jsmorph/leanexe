import Project.ClobFindBest.Program
import Project.ClobFindBest.Model
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Call

/-!
# Scalar helpers used by `findBest`

The generated search calls four pure helpers for side selection, crossing,
eligibility, and price comparison.  Each theorem states the helper directly
over `OrderL` values and preserves the store.
-/

namespace Project.ClobFindBest.Helpers

open Wasm Project.Clob Project.ClobFindBest Project.ClobFindBest.Model

set_option maxHeartbeats 64000000

def boolWord (p : Prop) [Decidable p] : UInt64 :=
  if p then 1 else 0

macro "fb_step" : tactic => `(tactic|
  (refine wp_iff_cons rfl ?_;
   repeat (split <;> try (exfalso; simp_all; done));
   wp_run;
   simp only [List.cons_append, List.nil_append, List.append_nil,
     List.append_eq, List.append, List.take, List.drop]))

theorem func1_spec (env : HostEnv Unit) (st : Store Unit) (side : UInt64) :
    TerminatesWith (m := «module») (id := 1) (initial := st) (env := env)
      [.i64 side]
      (fun st' vs => vs = [.i64 (boolWord (side = 0))] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func1 _ st
      { params := [.i64 side], locals := [.i64 0], values := [] } env
    unfold func1
    wp_run
    by_cases h : side = 0 <;>
      (fb_step; fb_step; fb_step; simp [h, boolWord, func1Def])

theorem func4_spec (env : HostEnv Unit) (st : Store Unit)
    (taker maker : OrderL) :
    TerminatesWith (m := «module») (id := 4) (initial := st) (env := env)
      [.i64 maker.oqty, .i64 maker.oprice, .i64 maker.oside,
       .i64 maker.otrader, .i64 maker.oid,
       .i64 taker.oqty, .i64 taker.oprice, .i64 taker.oside,
       .i64 taker.otrader, .i64 taker.oid]
      (fun st' vs =>
        vs = [.i64 (boolWord (crossesL taker maker))] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func4Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func4 _ st
      { params := [.i64 taker.oid, .i64 taker.otrader, .i64 taker.oside,
          .i64 taker.oprice, .i64 taker.oqty, .i64 maker.oid,
          .i64 maker.otrader, .i64 maker.oside, .i64 maker.oprice,
          .i64 maker.oqty],
        locals := [.i64 0], values := [] } env
    unfold func4
    wp_run
    by_cases hs : taker.oside = 0
    · by_cases hp : maker.oprice ≤ taker.oprice <;>
        (fb_step; fb_step; fb_step; fb_step;
          simp [hs, hp, boolWord, func4Def])
    · by_cases hp : taker.oprice ≤ maker.oprice <;>
        (fb_step; fb_step; fb_step; fb_step;
          simp [hp, boolWord, func4Def])

theorem func5_spec (env : HostEnv Unit) (st : Store Unit)
    (taker maker : OrderL) :
    TerminatesWith (m := «module») (id := 5) (initial := st) (env := env)
      [.i64 maker.oqty, .i64 maker.oprice, .i64 maker.oside,
       .i64 maker.otrader, .i64 maker.oid,
       .i64 taker.oqty, .i64 taker.oprice, .i64 taker.oside,
       .i64 taker.otrader, .i64 taker.oid]
      (fun st' vs =>
        vs = [.i64 (boolWord (eligibleL taker maker))] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func5Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func5 _ st
      { params := [.i64 taker.oid, .i64 taker.otrader, .i64 taker.oside,
          .i64 taker.oprice, .i64 taker.oqty, .i64 maker.oid,
          .i64 maker.otrader, .i64 maker.oside, .i64 maker.oprice,
          .i64 maker.oqty],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func5
    wp_run
    refine wp_call_tw (func1_spec env st taker.oside) ?_
    rintro st1 vs ⟨rfl, rfl⟩
    have hop : boolWord (taker.oside = 0) = oppositeSideL taker.oside := by
      simp [boolWord, oppositeSideL]
    simp only [hop]
    wp_run
    by_cases hs : maker.oside = oppositeSideL taker.oside
    · by_cases ht : maker.otrader = taker.otrader
      · fb_step
        fb_step
        fb_step
        fb_step
        fb_step
        simp [eligibleL, hs, ht, boolWord, oppositeSideL, func5Def]
      · fb_step
        fb_step
        fb_step
        fb_step
        refine wp_call_tw (func4_spec env st1 taker maker) ?_
        rintro st2 vs ⟨rfl, rfl⟩
        by_cases hc : crossesL taker maker
        · simp only [boolWord, if_pos hc]
          wp_run
          fb_step
          simp [hs, func5Def]
        · simp only [boolWord, if_neg hc]
          wp_run
          fb_step
          simp [hs, func5Def]
    · fb_step
      fb_step
      fb_step
      fb_step
      simp [func5Def, boolWord]
      intro hside
      exact (hs hside).elim

theorem func6_spec (env : HostEnv Unit) (st : Store Unit)
    (taker candidate incumbent : OrderL) :
    TerminatesWith (m := «module») (id := 6) (initial := st) (env := env)
      [.i64 incumbent.oqty, .i64 incumbent.oprice, .i64 incumbent.oside,
       .i64 incumbent.otrader, .i64 incumbent.oid,
       .i64 candidate.oqty, .i64 candidate.oprice, .i64 candidate.oside,
       .i64 candidate.otrader, .i64 candidate.oid,
       .i64 taker.oqty, .i64 taker.oprice, .i64 taker.oside,
       .i64 taker.otrader, .i64 taker.oid]
      (fun st' vs =>
        vs = [.i64 (boolWord (betterPriceL taker candidate incumbent))] ∧
        st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func6Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func6 _ st
      { params := [.i64 taker.oid, .i64 taker.otrader, .i64 taker.oside,
          .i64 taker.oprice, .i64 taker.oqty, .i64 candidate.oid,
          .i64 candidate.otrader, .i64 candidate.oside,
          .i64 candidate.oprice, .i64 candidate.oqty, .i64 incumbent.oid,
          .i64 incumbent.otrader, .i64 incumbent.oside,
          .i64 incumbent.oprice, .i64 incumbent.oqty],
        locals := [.i64 0], values := [] } env
    unfold func6
    wp_run
    by_cases hs : taker.oside = 0
    · by_cases hp : candidate.oprice < incumbent.oprice <;>
        (fb_step; fb_step; fb_step; fb_step;
          simp [hs, hp, boolWord, func6Def])
    · by_cases hp : incumbent.oprice < candidate.oprice <;>
        (fb_step; fb_step; fb_step; fb_step;
          simp [hp, boolWord, func6Def])

end Project.ClobFindBest.Helpers
