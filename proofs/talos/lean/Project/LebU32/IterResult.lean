import Project.LebU32.Defs

/-!
# Final-byte iteration result

The final-byte branch exports its semantic state through a named value.  The
weakest-precondition proof carries only `Nonempty PosResult` at fallthrough,
while a shallow consequence proof applies the caller's continuation.  This
boundary keeps the continuation and the generated instruction suffix out of
the same elaboration goal.
-/

namespace Project.LebU32.Spec

open Wasm

def posAllocTail : Program :=
  [Instruction.localGet 28, Instruction.localGet 26,
    Instruction.addI64, Instruction.wrapI64, Instruction.localGet 27,
    Instruction.wrapI64, Instruction.store8 0, Instruction.localGet 28,
    Instruction.localSet 12, Instruction.localGet 12,
    Instruction.localSet 5, Instruction.localGet 12,
    Instruction.localSet 6, Instruction.localGet 11,
    Instruction.constI64 1, Instruction.addI64, Instruction.localSet 7,
    Instruction.constI64 1, Instruction.localSet 8]

structure PosResult (st : Store Unit) (n g0 g2 : UInt64) (m0 : Nat)
    (st' : Store Unit) (s' : Locals) where
  k : Nat
  v : UInt64
  written : List UInt8
  done : Bool
  e : Nat → UInt64
  split : lebList 10 n = written ++
    (if done then [] else lebList (10 - k) v)
  writtenLength : written.length = k
  indexBound : k ≤ (lebList 10 n).length
  frame :
    if done then
      { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } =
        lFrame (UInt64.ofNat (11 - k)) (e 1) (e 2) (e 3) (e 4)
          (bufPtr g0 k) (bufPtr g0 k) (UInt64.ofNat k) 1 e
    else
      { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } =
        lFrame (UInt64.ofNat (10 - k)) v (bufPtr g0 k) (bufPtr g0 k)
          (UInt64.ofNat k) 0 0 0 0 e
  bytes : ∀ i : Nat, i < k →
    st'.mem.bytes (objBase g0 (k - 1) + 48 + i) = written[i]!
  globalsLength : st'.globals.globals.length = st.globals.globals.length
  global0 : st'.globals.globals[0]? =
    some (.i64 (g0 + UInt64.ofNat (56 * k)))
  global1 : st'.globals.globals[1]? = some (.i64 0)
  global2 : st'.globals.globals[2]? =
    some (.i64 (g2 + UInt64.ofNat k))
  global3 : st'.globals.globals[3]? = st.globals.globals[3]?
  global4 : st'.globals.globals[4]? = st.globals.globals[4]?
  global5 : st'.globals.globals[5]? = st.globals.globals[5]?
  pages : st'.mem.pages = st.mem.pages
  below : ∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st.mem.bytes a
  measure : lMeasure st'
    { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } < m0

def posPOST (st : Store Unit) (n g0 g2 : UInt64) (m0 : Nat)
    (POST : Assertion Unit) : Assertion Unit := fun cont =>
  match cont with
  | .Fallthrough st' s' => Nonempty (PosResult st n g0 g2 m0 st' s')
  | other => POST other

end Project.LebU32.Spec
