import LeanExe.WGSL.Statement
import LeanExe.WGSL.SourceBounds

/-! Execution of the parsed statement subset. Arithmetic is an explicit scalar
interpretation. Indexing and loop counters use wrapping UInt32 operations;
local lookup, buffer access and exhausted loop budgets can fail. -/
namespace LeanExe.WGSL.Statement
open Source

inductive Error where
  | localSlot (slot : Nat)
  | loadA (address : Nat)
  | loadB (address : Nat)
  | storeC (address : Nat)
  | loopBudget
  deriving Repr, BEq, DecidableEq

structure Memory where
  a : WordBuffer
  b : WordBuffer
  sizeA : Nat
  sizeB : Nat

/-- Local scopes are stacks. A missing local is an execution error. -/
def readLocal (words : List UInt32) (slot : Nat) : Except Error UInt32 :=
  match words[slot]? with
  | some value => .ok value
  | none => .error (.localSlot slot)

def Prim.run (ar : ScalarArithmetic) (memory : Memory) (row col : UInt32)
    (indices words : List UInt32) : Prim → Except Error UInt32
  | .literal w => .ok w
  | .copy n => readLocal words n
  | .loadA i =>
      let address := (i.word row col indices).toNat
      if address < memory.sizeA then .ok (memory.a address) else .error (.loadA address)
  | .loadB i =>
      let address := (i.word row col indices).toNat
      if address < memory.sizeB then .ok (memory.b address) else .error (.loadB address)
  | .add a b => do pure (ar.add (← readLocal words a) (← readLocal words b))
  | .mul a b => do pure (ar.mul (← readLocal words a) (← readLocal words b))

/-- Test the u32 counter before each iteration, execute the body, assign its
result to the accumulator, increment the counter, and test again. `fuel` bounds
body executions; reaching the limit while the condition remains true is an
error, not a successful return. -/
def loopRun (body : UInt32 → UInt32 → Except Error UInt32) (limit : UInt32) :
    Nat → UInt32 → UInt32 → Except Error UInt32
  | fuel, counter, acc =>
      if counter < limit then
        match fuel with
        | 0 => .error .loopBudget
        | fuel + 1 => do
            let value ← body counter acc
            loopRun body limit fuel (counter + 1) value
      else .ok acc

def Code.run (ar : ScalarArithmetic) (memory : Memory) (row col : UInt32)
    (indices words : List UInt32) : Code → Except Error UInt32
  | .finish n => readLocal words n
  | .bind value next => do
      let word ← value.run ar memory row col indices words
      next.run ar memory row col indices (word :: words)
  | .loop count initial body next => do
      let acc ← readLocal words initial
      let result ← loopRun
        (fun k value => body.run ar memory row col (k :: indices) (value :: words))
        (UInt32.ofNat count) count 0 acc
      next.run ar memory row col indices (result :: words)

def AccessValid (shape : Shape) (ranges : List Nat) (size : Nat) (i : Source.Index) : Prop :=
  match i.bound shape ranges with
  | .error _ => False
  | .ok bound => bound < size

instance (shape ranges size i) : Decidable (AccessValid shape ranges size i) := by
  unfold AccessValid
  split <;> infer_instance

def Prim.Valid (shape : Shape) (ranges : List Nat) (words : Nat) : Prim → Prop
  | .literal _ => True
  | .copy n => n < words
  | .loadA i => AccessValid shape ranges shape.elementsA i
  | .loadB i => AccessValid shape ranges shape.elementsB i
  | .add a b | .mul a b => a < words ∧ b < words

instance (shape ranges words p) : Decidable (Prim.Valid shape ranges words p) := by
  cases p <;> simp only [Prim.Valid] <;> infer_instance

def Code.Valid (shape : Shape) (ranges : List Nat) (words : Nat) : Code → Prop
  | .finish n => n < words
  | .bind value next => value.Valid shape ranges words ∧ next.Valid shape ranges (words + 1)
  | .loop count initial body next =>
      count ≤ 65535 ∧ initial < words ∧
      body.Valid shape ((count - 1) :: ranges) (words + 1) ∧
      next.Valid shape ranges (words + 1)

instance codeValidDecidable (shape ranges words) (code : Code) :
    Decidable (code.Valid shape ranges words) :=
  match code with
  | .finish _ => inferInstanceAs (Decidable (_ < _))
  | .bind value next =>
      @instDecidableAnd _ _ (inferInstanceAs (Decidable (value.Valid shape ranges words)))
        (codeValidDecidable shape ranges (words + 1) next)
  | .loop count initial body next =>
      letI := codeValidDecidable shape ((count - 1) :: ranges) (words + 1) body
      letI := codeValidDecidable shape ranges (words + 1) next
      inferInstanceAs (Decidable (count ≤ 65535 ∧ initial < words ∧
        body.Valid shape ((count - 1) :: ranges) (words + 1) ∧
        next.Valid shape ranges (words + 1)))

end LeanExe.WGSL.Statement
