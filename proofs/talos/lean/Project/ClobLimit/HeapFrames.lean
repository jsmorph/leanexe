import Project.ClobLimit.HeapStep

namespace Project.ClobLimit.HeapFrames
open Wasm Project.Clob Project.ClobFindBest.Model Project.LocalRegion
open Project.ClobLimit.HeapProgram

def searchLocals (base : Locals) (owner book : UInt64) (taker : OrderL)
    (result : Option Nat) : List Value :=
  let ls := base.locals.set 8 (.i64 owner)
  let ls := ls.set 9 (.i64 book)
  let ls := ls.set 10 (.i64 taker.oid)
  let ls := ls.set 11 (.i64 taker.otrader)
  let ls := ls.set 12 (.i64 taker.oside)
  let ls := ls.set 13 (.i64 taker.oprice)
  let ls := ls.set 14 (.i64 taker.oqty)
  let ls := ls.set 16 (.i64 (optionPayload result))
  ls.set 15 (.i64 (optionTag result))

def searchFrame (base : Locals) (owner book : UInt64) (taker : OrderL)
    (result : Option Nat) : Locals :=
  { base with locals := searchLocals base owner book taker result, values := [] }

theorem search_related (s t : Locals) (h : layout.Related s t)
    (owner book : UInt64) (taker : OrderL) (result : Option Nat) :
    layout.Related (ClobMatchFuel.Iteration.searchFrame s owner book taker result)
      (searchFrame t owner book taker result) := by
  have hp := h.sourceParams
  have ht := h.targetParams
  change s.params.length = 9 at hp
  change t.params.length = 11 at ht
  have h0 := layout.frame.stack h []
  have h1 := layout.update_related h0 (i := 25) (by simp [Domain]) (.i64 owner)
  have h2 := layout.update_related h1 (i := 26) (by simp [Domain]) (.i64 book)
  have h3 := layout.update_related h2 (i := 27) (by simp [Domain]) (.i64 taker.oid)
  have h4 := layout.update_related h3 (i := 28) (by simp [Domain]) (.i64 taker.otrader)
  have h5 := layout.update_related h4 (i := 29) (by simp [Domain]) (.i64 taker.oside)
  have h6 := layout.update_related h5 (i := 30) (by simp [Domain]) (.i64 taker.oprice)
  have h7 := layout.update_related h6 (i := 31) (by simp [Domain]) (.i64 taker.oqty)
  have h8 := layout.update_related h7 (i := 33) (by simp [Domain]) (.i64 (optionPayload result))
  have h9 := layout.update_related h8 (i := 32) (by simp [Domain]) (.i64 (optionTag result))
  simpa [update, slots, hp, ht, searchFrame, searchLocals,
    ClobMatchFuel.Iteration.searchFrame, ClobMatchFuel.Iteration.searchLocals] using h9

def completeSource (s : Locals) (bookOwner tradesOwner : Value)
    (book trades remaining : UInt64) : Locals :=
  let s := { s with values := [] }
  let s := update s 73 bookOwner
  let s := update s 21 (.i64 book)
  let s := update s 75 tradesOwner
  let s := update s 22 (.i64 trades)
  let s := update s 23 (.i64 remaining)
  update s 24 (.i64 1)

def completeTarget (t : Locals) (bookOwner tradesOwner : Value)
    (book trades remaining : UInt64) : Locals :=
  { t with
    locals := (((((t.locals.set 2 bookOwner).set 3 (.i64 book)).set 4 tradesOwner).set 5
      (.i64 trades)).set 6 (.i64 remaining)).set 7 (.i64 1)
    values := [] }

theorem complete_related (s t : Locals) (h : layout.Related s t)
    (bookOwner tradesOwner : Value) (book trades remaining : UInt64) :
    layout.Related (completeSource s bookOwner tradesOwner book trades remaining)
      (completeTarget t bookOwner tradesOwner book trades remaining) := by
  have ht := h.targetParams
  change t.params.length = 11 at ht
  have h0 := layout.frame.stack h []
  have h1 := layout.update_related h0 (i := 73) (by simp [Domain]) bookOwner
  have h2 := layout.update_related h1 (i := 21) (by simp [Domain]) (.i64 book)
  have h3 := layout.update_related h2 (i := 75) (by simp [Domain]) tradesOwner
  have h4 := layout.update_related h3 (i := 22) (by simp [Domain]) (.i64 trades)
  have h5 := layout.update_related h4 (i := 23) (by simp [Domain]) (.i64 remaining)
  have h6 := layout.update_related h5 (i := 24) (by simp [Domain]) (.i64 1)
  simpa [completeSource, completeTarget, update, slots, ht] using h6

theorem complete_result (s : Locals) (bookOwner tradesOwner : Value)
    (book trades remaining : UInt64)
    (hp : s.params.length = 9) (hl : s.locals.length = 86) :
    ClobMatchFuel.LoopControl.CompletedResultAt
      (completeSource s bookOwner tradesOwner book trades remaining) book trades remaining := by
  simp [completeSource, update, hp, hl, ClobMatchFuel.LoopControl.CompletedResultAt]

theorem complete_fuel (s : Locals) (bookOwner tradesOwner : Value)
    (book trades remaining : UInt64) (hp : s.params.length = 9) :
    (completeSource s bookOwner tradesOwner book trades remaining).get 0 = s.get 0 := by
  simp [completeSource, update, hp, Locals.get]

set_option Elab.async false in
theorem read_spec (env : HostEnv Unit) (st : Store Unit) (source target : Locals)
    (owner book : UInt64) (taker : OrderL) (os : List OrderL) (i : Nat)
    (h : layout.Related source target)
    (hBook : source.locals[6]? = some (.i64 book))
    (hi : i < os.length) (hLength : os.length < 4294967296)
    (hOrders : OrdersAt st book os) :
    wp Project.ClobLimit.«module» readProg
      (fun c => match c with
        | .Fallthrough st1 t => st1 = st ∧ layout.Related
            (ClobMatchFuel.Iteration.quantityFrame source owner book taker i os[i]!) t
        | _ => False)
      st (searchFrame target owner book taker (some i)) env := by
  have hp := h.sourceParams
  have hl := h.sourceLocals
  change source.params.length = 9 at hp
  change source.locals.length = 86 at hl
  let s := ClobMatchFuel.Iteration.searchFrame source owner book taker (some i)
  let final := ClobMatchFuel.SelectedMaker.cacheFrame s book i os[i]!
  let P : Assertion Unit := fun c => match c with
    | .Fallthrough st1 s1 => st1 = st ∧ s1 = final
    | _ => False
  have hSource : wp Project.ClobMatchFuel.«module» ClobMatchFuel.SelectedMaker.readProg P st s env := by
    simpa only [List.append_nil] using
      (ClobMatchFuel.SelectedMaker.read_spec env st s book os i
        (by simpa [s, ClobMatchFuel.Iteration.searchFrame] using hp)
        (by simp [s, ClobMatchFuel.Iteration.searchFrame,
          ClobMatchFuel.Iteration.searchLocals, hl]) rfl
        (by simpa [s, ClobMatchFuel.Iteration.searchFrame,
          ClobMatchFuel.Iteration.searchLocals, hl] using hBook)
        (by simp [s, ClobMatchFuel.Iteration.searchFrame,
          ClobMatchFuel.Iteration.searchLocals, hl, optionPayload]) hLength hi hOrders P []
        (by simp [wp_simp, P, final]))
  refine wp_transport layout.frame SearchRegion.searchShift env st s _ _
    (search_related source target h owner book taker (some i)) ?_ ?_ P _ ?_ hSource
  · prove_portable
  · repeat' (first | exact True.intro | apply And.intro)
    all_goals simp [AllowedInstruction, Domain]
  · intro a b hAB hP
    cases hAB <;> simp only [P] at hP
    rcases hP with ⟨rfl, rfl⟩
    exact ⟨rfl, by assumption⟩

#print axioms search_related
#print axioms read_spec
end Project.ClobLimit.HeapFrames
