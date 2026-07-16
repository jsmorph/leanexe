import Project.ClobMatchFuel.ReleaseFrame
import Interpreter.Wasm.Wp.Call

/-!
# Consumed-array release block

The common matching branch conditionally releases its prior book and trade
roots after producing replacements.  The first theorem isolates the generated
alias guards and two calls from the fixed-array memory semantics.
-/

namespace Project.ClobMatchFuel.ReleaseOld

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame
  Project.ClobMatchFuel.ReleaseFrame

def releaseOldValuesProg : Wasm.Program :=
  [
  .localGet 19,
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 1 [
    .localGet 19,
    .localGet 44,
    .eqI64,
    .eqz
  ] [
    .const 0
  ],
  .iff 0 1 [
    .localGet 19,
    .localGet 46,
    .eqI64,
    .eqz
  ] [
    .const 0
  ],
  .iff 0 0 [
    .localGet 19,
    .call 18
  ] [],
  .localGet 20,
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 1 [
    .localGet 20,
    .localGet 19,
    .eqI64,
    .eqz
  ] [
    .const 0
  ],
  .iff 0 1 [
    .localGet 20,
    .localGet 44,
    .eqI64,
    .eqz
  ] [
    .const 0
  ],
  .iff 0 1 [
    .localGet 20,
    .localGet 46,
    .eqI64,
    .eqz
  ] [
    .const 0
  ],
  .iff 0 0 [
    .localGet 20,
    .call 18
  ] []
  ]

set_option Elab.async false in
theorem releaseOldValuesProg_calls
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (oldBook oldTrades newBook newTrades : UInt64)
    (bookPost : Store Unit → Prop)
    (tradePost : Store Unit → Store Unit → Prop)
    (hOldBookLocal : base.get 19 = some (.i64 oldBook))
    (hOldTradesLocal : base.get 20 = some (.i64 oldTrades))
    (hNewBookLocal : base.get 44 = some (.i64 newBook))
    (hNewTradesLocal : base.get 46 = some (.i64 newTrades))
    (hValues : base.values = [])
    (hOldBookNonzero : oldBook ≠ 0)
    (hOldBookNewBook : oldBook ≠ newBook)
    (hOldBookNewTrades : oldBook ≠ newTrades)
    (hOldTradesNonzero : oldTrades ≠ 0)
    (hOldTradesOldBook : oldTrades ≠ oldBook)
    (hOldTradesNewBook : oldTrades ≠ newBook)
    (hOldTradesNewTrades : oldTrades ≠ newTrades)
    (hReleaseBook :
      TerminatesWith (m := «module») (id := 18) (initial := st) (env := env)
        [.i64 oldBook] (fun st1 vs => vs = [] ∧ bookPost st1))
    (hReleaseTrades : ∀ st1, bookPost st1 →
      TerminatesWith (m := «module») (id := 18) (initial := st1) (env := env)
        [.i64 oldTrades] (fun st2 vs => vs = [] ∧ tradePost st1 st2))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 st2, bookPost st1 → tradePost st1 st2 →
      wp «module» rest Q st2 base env) :
    wp «module» (releaseOldValuesProg ++ rest) Q st base env := by
  rcases base with ⟨params, locals, values⟩
  dsimp only at hValues
  subst values
  simp only [releaseOldValuesProg, List.cons_append, List.nil_append]
  simp_all only [wp_simp, Locals.get]
  refine wp_iff_cons
    (s := { params, locals, values := [.i32 1] })
    (c := 1) (vs := []) rfl ?_
  rw [if_pos (by decide)]
  simp_all only [wp_simp, Locals.get]
  try simp
  refine wp_iff_cons
    (s := { params, locals, values := [.i32 1] })
    (c := 1) (vs := []) rfl ?_
  rw [if_pos (by decide)]
  simp_all only [wp_simp, Locals.get]
  try simp
  refine wp_iff_cons
    (s := { params, locals, values := [.i32 1] })
    (c := 1) (vs := []) rfl ?_
  rw [if_pos (by decide)]
  simp_all only [wp_simp, Locals.get]
  try simp
  refine wp_call_tw hReleaseBook ?_
  rintro st1 vs ⟨rfl, hBookPost⟩
  simp_all only [wp_simp]
  refine wp_iff_cons
    (s := { params, locals, values := [.i32 1] })
    (c := 1) (vs := []) rfl ?_
  rw [if_pos (by decide)]
  simp_all only [wp_simp, Locals.get]
  try simp
  refine wp_iff_cons
    (s := { params, locals, values := [.i32 1] })
    (c := 1) (vs := []) rfl ?_
  rw [if_pos (by decide)]
  simp_all only [wp_simp, Locals.get]
  try simp
  refine wp_iff_cons
    (s := { params, locals, values := [.i32 1] })
    (c := 1) (vs := []) rfl ?_
  rw [if_pos (by decide)]
  simp_all only [wp_simp, Locals.get]
  try simp
  refine wp_iff_cons
    (s := { params, locals, values := [.i32 1] })
    (c := 1) (vs := []) rfl ?_
  rw [if_pos (by decide)]
  simp_all only [wp_simp, Locals.get]
  try simp
  refine wp_call_tw (hReleaseTrades st1 hBookPost) ?_
  rintro st2 vs ⟨rfl, hTradePost⟩
  wp_run
  try simp
  exact hDone st1 st2 hBookPost hTradePost

end Project.ClobMatchFuel.ReleaseOld
