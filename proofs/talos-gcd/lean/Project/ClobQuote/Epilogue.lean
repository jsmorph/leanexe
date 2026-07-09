import Project.ClobQuote.Program
import Project.Common
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block

/-!
# The loop-body epilogue of `func10`, in segments

The instructions after `call 9` inside the export's loop body, cut into
five segment lemmas so each symbolic walk stays short: store the six call
results, copy them twice, write them into the accumulator locals with the
flag updates, and take the not-taken `br_if` plus the index increment and
the back edge.  Each lemma is generic in the continuation and binds only
the frame slots it mentions, so the export proof composes them with
`refine` and discharges only the final `Break 0` obligation.
-/

namespace Project.ClobQuote.Spec

open Wasm Project.Common Project.ClobQuote

set_option maxHeartbeats 400000000
set_option linter.unusedVariables false

macro "wp_walk" : tactic => `(tactic|
  simp only [wp_simp, Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    ValueType.zero, List.headD, List.set, Nat.reduceAdd, Nat.reduceLT,
    Nat.reduceLeDiff, Nat.reduceSub])

theorem epilogueA {env : HostEnv Unit} {st : Store Unit}
    {Q : Assertion Unit} {rest : Program} {p0 : UInt64}
    {L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12
     L13 L14 L15 L16 L17 L18 L19 L20 L21 L22 L23 L24
     L25 L26 L27 L28 L29 L30 L31 L32 L33 L34 L35 L36
     L37 L38 L39 L40 L41 L42 L43 L44 L45 L46 L47 L48
     L49 L50 L51 L52 L53 L54 L55 L56 L57 L58 L59 w1
     w2 w3 w4 w5 w6 : UInt64}
    (hNext : wp «module» rest Q st
      { params := [.i64 p0],
        locals := [.i64 L1, .i64 L2, .i64 L3, .i64 L4, .i64 L5, .i64 L6,
          .i64 L7, .i64 L8, .i64 L9, .i64 L10, .i64 L11, .i64 L12,
          .i64 L13, .i64 L14, .i64 L15, .i64 L16, .i64 L17, .i64 L18,
          .i64 L19, .i64 L20, .i64 L21, .i64 L22, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 L29, .i64 L30,
          .i64 L31, .i64 L32, .i64 L33, .i64 L34, .i64 L35, .i64 L36,
          .i64 L37, .i64 L38, .i64 L39, .i64 L40, .i64 L41, .i64 L42,
          .i64 L43, .i64 L44, .i64 L45, .i64 L46, .i64 L47, .i64 L48,
          .i64 L49, .i64 L50, .i64 L51, .i64 L52, .i64 L53, .i64 L54,
          .i64 L55, .i64 L56, .i64 L57, .i64 L58, .i64 L59],
        values := [] }
      env) :
    wp «module»
      (.localSet 28 :: .localSet 27 :: .localSet 26 :: .localSet 25 ::
       .localSet 24 :: .localSet 23 :: rest)
      Q st
      { params := [.i64 p0],
        locals := [.i64 L1, .i64 L2, .i64 L3, .i64 L4, .i64 L5, .i64 L6,
          .i64 L7, .i64 L8, .i64 L9, .i64 L10, .i64 L11, .i64 L12,
          .i64 L13, .i64 L14, .i64 L15, .i64 L16, .i64 L17, .i64 L18,
          .i64 L19, .i64 L20, .i64 L21, .i64 L22, .i64 L23, .i64 L24,
          .i64 L25, .i64 L26, .i64 L27, .i64 L28, .i64 L29, .i64 L30,
          .i64 L31, .i64 L32, .i64 L33, .i64 L34, .i64 L35, .i64 L36,
          .i64 L37, .i64 L38, .i64 L39, .i64 L40, .i64 L41, .i64 L42,
          .i64 L43, .i64 L44, .i64 L45, .i64 L46, .i64 L47, .i64 L48,
          .i64 L49, .i64 L50, .i64 L51, .i64 L52, .i64 L53, .i64 L54,
          .i64 L55, .i64 L56, .i64 L57, .i64 L58, .i64 L59],
        values := [.i64 w1, .i64 w2, .i64 w3, .i64 w4, .i64 w5, .i64 w6] }
      env := by
  wp_walk
  exact hNext

theorem epilogueB {env : HostEnv Unit} {st : Store Unit}
    {Q : Assertion Unit} {rest : Program} {p0 : UInt64}
    {L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12
     L13 L14 L15 L16 L17 L18 L19 L20 L21 L22 L29 L30
     L31 L32 L33 L34 L35 L36 L37 L38 L39 L40 L41 L42
     L43 L44 L45 L46 L47 L48 L49 L50 L51 L52 L53 L54
     L55 L56 L57 L58 L59 w1 w2 w3 w4 w5 w6 : UInt64}
    (hNext : wp «module» rest Q st
      { params := [.i64 p0],
        locals := [.i64 L1, .i64 L2, .i64 L3, .i64 L4, .i64 L5, .i64 L6,
          .i64 L7, .i64 L8, .i64 L9, .i64 L10, .i64 L11, .i64 L12,
          .i64 L13, .i64 L14, .i64 L15, .i64 L16, .i64 L17, .i64 L18,
          .i64 L19, .i64 L20, .i64 L21, .i64 L22, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 L35, .i64 L36,
          .i64 L37, .i64 L38, .i64 L39, .i64 L40, .i64 L41, .i64 L42,
          .i64 L43, .i64 L44, .i64 L45, .i64 L46, .i64 L47, .i64 L48,
          .i64 L49, .i64 L50, .i64 L51, .i64 L52, .i64 L53, .i64 L54,
          .i64 L55, .i64 L56, .i64 L57, .i64 L58, .i64 L59],
        values := [] }
      env) :
    wp «module»
      (.localGet 23 :: .localSet 29 :: .localGet 24 :: .localSet 30 :: .localGet 25 :: .localSet 31 :: .localGet 26 :: .localSet 32 :: .localGet 27 :: .localSet 33 :: .localGet 28 :: .localSet 34 :: rest)
      Q st
      { params := [.i64 p0],
        locals := [.i64 L1, .i64 L2, .i64 L3, .i64 L4, .i64 L5, .i64 L6,
          .i64 L7, .i64 L8, .i64 L9, .i64 L10, .i64 L11, .i64 L12,
          .i64 L13, .i64 L14, .i64 L15, .i64 L16, .i64 L17, .i64 L18,
          .i64 L19, .i64 L20, .i64 L21, .i64 L22, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 L29, .i64 L30,
          .i64 L31, .i64 L32, .i64 L33, .i64 L34, .i64 L35, .i64 L36,
          .i64 L37, .i64 L38, .i64 L39, .i64 L40, .i64 L41, .i64 L42,
          .i64 L43, .i64 L44, .i64 L45, .i64 L46, .i64 L47, .i64 L48,
          .i64 L49, .i64 L50, .i64 L51, .i64 L52, .i64 L53, .i64 L54,
          .i64 L55, .i64 L56, .i64 L57, .i64 L58, .i64 L59],
        values := [] }
      env := by
  wp_walk
  exact hNext

theorem epilogueC {env : HostEnv Unit} {st : Store Unit}
    {Q : Assertion Unit} {rest : Program} {p0 : UInt64}
    {L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12
     L13 L14 L15 L16 L17 L18 L19 L20 L21 L22 L35 L36
     L37 L38 L39 L40 L41 L42 L43 L44 L45 L46 L47 L48
     L49 L50 L51 L52 L53 L54 L55 L56 L57 L58 L59 w1
     w2 w3 w4 w5 w6 : UInt64}
    (hNext : wp «module» rest Q st
      { params := [.i64 p0],
        locals := [.i64 L1, .i64 L2, .i64 L3, .i64 L4, .i64 L5, .i64 L6,
          .i64 L7, .i64 L8, .i64 L9, .i64 L10, .i64 L11, .i64 L12,
          .i64 L13, .i64 L14, .i64 L15, .i64 L16, .i64 L17, .i64 L18,
          .i64 L19, .i64 L20, .i64 L21, .i64 L22, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 L35, .i64 L36,
          .i64 L37, .i64 L38, .i64 L39, .i64 L40, .i64 L41, .i64 L42,
          .i64 L43, .i64 L44, .i64 L45, .i64 L46, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 L53, .i64 L54,
          .i64 L55, .i64 L56, .i64 L57, .i64 L58, .i64 L59],
        values := [] }
      env) :
    wp «module»
      (.localGet 29 :: .localSet 47 :: .localGet 30 :: .localSet 48 :: .localGet 31 :: .localSet 49 :: .localGet 32 :: .localSet 50 :: .localGet 33 :: .localSet 51 :: .localGet 34 :: .localSet 52 :: rest)
      Q st
      { params := [.i64 p0],
        locals := [.i64 L1, .i64 L2, .i64 L3, .i64 L4, .i64 L5, .i64 L6,
          .i64 L7, .i64 L8, .i64 L9, .i64 L10, .i64 L11, .i64 L12,
          .i64 L13, .i64 L14, .i64 L15, .i64 L16, .i64 L17, .i64 L18,
          .i64 L19, .i64 L20, .i64 L21, .i64 L22, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 L35, .i64 L36,
          .i64 L37, .i64 L38, .i64 L39, .i64 L40, .i64 L41, .i64 L42,
          .i64 L43, .i64 L44, .i64 L45, .i64 L46, .i64 L47, .i64 L48,
          .i64 L49, .i64 L50, .i64 L51, .i64 L52, .i64 L53, .i64 L54,
          .i64 L55, .i64 L56, .i64 L57, .i64 L58, .i64 L59],
        values := [] }
      env := by
  wp_walk
  exact hNext

theorem epilogueD {env : HostEnv Unit} {st : Store Unit}
    {Q : Assertion Unit} {rest : Program} {p0 : UInt64}
    {L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12
     L13 L14 L15 L16 L17 L18 L19 L20 L21 L22 L35 L36
     L37 L38 L39 L40 L41 L42 L43 L44 L45 L46 L53 L54
     L55 L56 L57 L58 L59 w1 w2 w3 w4 w5 w6 : UInt64}
    (hNext : wp «module» rest Q st
      { params := [.i64 p0],
        locals := [.i64 w6, .i64 w5, .i64 w4, .i64 w3, .i64 w2, .i64 w1,
          .i64 L7, .i64 L8, .i64 L9, .i64 L10, .i64 L11, .i64 L12,
          .i64 L13, .i64 L14, .i64 L15, .i64 L16, .i64 L17, .i64 L18,
          .i64 L19, .i64 L20, .i64 L21, .i64 L22, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 L35, .i64 L36,
          .i64 L37, .i64 L38, .i64 L39, .i64 L40, .i64 L41, .i64 L42,
          .i64 L43, .i64 L44, .i64 L45, .i64 0, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 1, .i64 L54,
          .i64 L55, .i64 L56, .i64 L57, .i64 L58, .i64 L59],
        values := [] }
      env) :
    wp «module»
      (.constI64 0 :: .localSet 46 :: .localGet 47 :: .localSet 1 :: .localGet 48 :: .localSet 2 :: .localGet 49 :: .localSet 3 :: .localGet 50 :: .localSet 4 :: .localGet 51 :: .localSet 5 :: .localGet 52 :: .localSet 6 :: .constI64 1 :: .localSet 53 :: rest)
      Q st
      { params := [.i64 p0],
        locals := [.i64 L1, .i64 L2, .i64 L3, .i64 L4, .i64 L5, .i64 L6,
          .i64 L7, .i64 L8, .i64 L9, .i64 L10, .i64 L11, .i64 L12,
          .i64 L13, .i64 L14, .i64 L15, .i64 L16, .i64 L17, .i64 L18,
          .i64 L19, .i64 L20, .i64 L21, .i64 L22, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 L35, .i64 L36,
          .i64 L37, .i64 L38, .i64 L39, .i64 L40, .i64 L41, .i64 L42,
          .i64 L43, .i64 L44, .i64 L45, .i64 L46, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 L53, .i64 L54,
          .i64 L55, .i64 L56, .i64 L57, .i64 L58, .i64 L59],
        values := [] }
      env := by
  wp_walk
  exact hNext

theorem epilogueE {env : HostEnv Unit} {st : Store Unit}
    {Q : Assertion Unit} {p0 : UInt64}
    {L7 L8 L9 L10 L11 L12 L13 L14 L15 L16 L17 L18
     L19 L20 L21 L22 L35 L36 L37 L38 L39 L40 L41 L42
     L43 L44 L45 L54 L55 L56 L57 L58 L59 w1 w2 w3
     w4 w5 w6 : UInt64}
    (hBr : Q (Continuation.Break 0 st
      { params := [.i64 p0],
        locals := [.i64 w6, .i64 w5, .i64 w4, .i64 w3, .i64 w2, .i64 w1,
          .i64 L7, .i64 L8, .i64 L9, .i64 L10, .i64 L11, .i64 L12,
          .i64 L13, .i64 L14, .i64 L15, .i64 L16, .i64 L17, .i64 L18,
          .i64 L19, .i64 L20, .i64 L21, .i64 L22, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 L35, .i64 L36,
          .i64 L37, .i64 L38, .i64 L39, .i64 L40, .i64 L41, .i64 L42,
          .i64 (L43 + 1), .i64 L44, .i64 L45, .i64 0, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 1, .i64 L54,
          .i64 L55, .i64 L56, .i64 L57, .i64 L58, .i64 L59],
        values := [] })) :
    wp «module»
      (.localGet 46 :: .constI64 0 :: .neI64 :: .br_if 1 ::
       .localGet 43 :: .constI64 1 :: .addI64 :: .localSet 43 ::
       [.br 0])
      Q st
      { params := [.i64 p0],
        locals := [.i64 w6, .i64 w5, .i64 w4, .i64 w3, .i64 w2, .i64 w1,
          .i64 L7, .i64 L8, .i64 L9, .i64 L10, .i64 L11, .i64 L12,
          .i64 L13, .i64 L14, .i64 L15, .i64 L16, .i64 L17, .i64 L18,
          .i64 L19, .i64 L20, .i64 L21, .i64 L22, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 L35, .i64 L36,
          .i64 L37, .i64 L38, .i64 L39, .i64 L40, .i64 L41, .i64 L42,
          .i64 L43, .i64 L44, .i64 L45, .i64 0, .i64 w6, .i64 w5,
          .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 1, .i64 L54,
          .i64 L55, .i64 L56, .i64 L57, .i64 L58, .i64 L59],
        values := [] }
      env := by
  wp_walk
  rw [if_neg (by simp)]
  try wp_walk
  exact hBr

end Project.ClobQuote.Spec
