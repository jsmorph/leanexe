import Project.ClobQuote.Program
import Project.Clob
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop
import Interpreter.Wasm.Wp.Call

/-!
# Specification for `quote`

The export folds `quoteStep` over an array of five-slot orders and returns
the six quote fields.  `func9` is the compiled `quoteStep`: a pure branch
tree over the eleven scalar arguments that assigns all six output fields in
the selected branch.  The export `func10` reads the array length, loops over
the elements, loads five fields per element, and calls `func9` to advance the
accumulator.

Value-list conventions: `TerminatesWith` argument lists and result lists are
top-of-stack first, so arguments appear reversed relative to the WASM
parameter order and the six results run from `askQty` down to `hasBid`.
-/

set_option maxHeartbeats 64000000

namespace Project.ClobQuote.Step

open Wasm Project.Common Project.Clob Project.ClobQuote

/-- The six-field quote accumulator. -/
structure QuoteL where
  hasBid : UInt64
  bidPrice : UInt64
  bidQty : UInt64
  hasAsk : UInt64
  askPrice : UInt64
  askQty : UInt64

/-- The source `quoteStep` restated over the model types. -/
def quoteStepL (q : QuoteL) (o : OrderL) : QuoteL :=
  if o.oside = 0 then
    if q.hasBid = 0 then
      { q with hasBid := 1, bidPrice := o.oprice, bidQty := o.oqty }
    else if q.bidPrice < o.oprice then
      { q with bidPrice := o.oprice, bidQty := o.oqty }
    else if o.oprice = q.bidPrice then
      { q with bidQty := q.bidQty + o.oqty }
    else q
  else
    if q.hasAsk = 0 then
      { q with hasAsk := 1, askPrice := o.oprice, askQty := o.oqty }
    else if o.oprice < q.askPrice then
      { q with askPrice := o.oprice, askQty := o.oqty }
    else if o.oprice = q.askPrice then
      { q with askQty := q.askQty + o.oqty }
    else q

def qInit : QuoteL := ⟨0, 0, 0, 0, 0, 0⟩

def quoteFold (os : List OrderL) : QuoteL :=
  os.foldl quoteStepL qInit

/-- The six quote fields as a result list, top of stack first. -/
def quoteVals (q : QuoteL) : List Value :=
  [.i64 q.askQty, .i64 q.askPrice, .i64 q.hasAsk,
   .i64 q.bidQty, .i64 q.bidPrice, .i64 q.hasBid]

/-- Normalize value lists back to cons form after a branch step. -/
macro "wp_norm" : tactic => `(tactic|
  simp only [List.cons_append, List.nil_append, List.append_nil,
    List.append_eq, List.append, List.take, List.drop])

/-- Resolve one compiled branch point: peel the `iff`, decide every `ite`
in its condition from the case hypotheses, and advance to the next branch
point. -/
macro "wp_step" : tactic => `(tactic|
  (refine wp_iff_cons rfl ?_;
   repeat (split <;> try (exfalso; simp_all; done));
   wp_run; wp_norm))

macro "wp_bool" : tactic => `(tactic| (wp_step; wp_step))

macro "wp_then" : tactic => `(tactic|
  (refine wp_iff_cons rfl ?_;
   rw [if_pos (by simp_all)];
   wp_run; try wp_norm))

macro "wp_else" : tactic => `(tactic|
  (refine wp_iff_cons rfl ?_;
   rw [if_neg (by simp_all)];
   wp_run; try wp_norm))

/-- `func9` computes `quoteStepL`: the eleven arguments are the six
accumulator fields and the five order fields, and the six results are the
fields of the advanced accumulator.  The store is untouched. -/
theorem func9_spec (env : HostEnv Unit) (st : Store Unit)
    (q1 q2 q3 q4 q5 q6 oid otr osd opr oqt : UInt64) :
    TerminatesWith (m := «module») (id := 9) (initial := st) (env := env)
      [.i64 oqt, .i64 opr, .i64 osd, .i64 otr, .i64 oid,
       .i64 q6, .i64 q5, .i64 q4, .i64 q3, .i64 q2, .i64 q1]
      (fun st' vs =>
        vs = quoteVals (quoteStepL ⟨q1, q2, q3, q4, q5, q6⟩
          ⟨oid, otr, osd, opr, oqt⟩) ∧
        st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func9Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func9 _ st
      { params := [.i64 q1, .i64 q2, .i64 q3, .i64 q4, .i64 q5, .i64 q6,
          .i64 oid, .i64 otr, .i64 osd, .i64 opr, .i64 oqt],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func9
    wp_run
    by_cases hs : osd = 0
    · subst hs
      wp_bool
      wp_then
      by_cases hb : q1 = 0
      · subst hb
        wp_bool
        wp_then
        norm_num [func9Def, quoteVals, quoteStepL]
      · by_cases hlt : q2 < opr
        · wp_bool
          wp_else
          wp_then
          norm_num [func9Def, quoteVals, quoteStepL, hb, hlt]
        · by_cases heq : opr = q2
          · wp_bool
            wp_else
            wp_else
            wp_bool
            wp_then
            norm_num [func9Def, quoteVals, quoteStepL, hb, hlt, heq]
          · wp_bool
            wp_else
            wp_else
            wp_bool
            wp_else
            norm_num [func9Def, quoteVals, quoteStepL, hb, hlt, heq]
    · wp_bool
      wp_else
      by_cases ha : q4 = 0
      · subst ha
        wp_bool
        wp_then
        norm_num [func9Def, quoteVals, quoteStepL, hs]
      · by_cases hlt : opr < q5
        · wp_bool
          wp_else
          wp_then
          norm_num [func9Def, quoteVals, quoteStepL, hs, ha, hlt]
        · by_cases heq : opr = q5
          · wp_bool
            wp_else
            wp_else
            wp_bool
            wp_then
            norm_num [func9Def, quoteVals, quoteStepL, hs, ha, hlt, heq]
          · wp_bool
            wp_else
            wp_else
            wp_bool
            wp_else
            norm_num [func9Def, quoteVals, quoteStepL, hs, ha, hlt, heq]

end Project.ClobQuote.Step
