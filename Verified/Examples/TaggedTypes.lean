import Verified.Reflect.Command

namespace Verified.Examples.TaggedTypes

open LeanExe.Pipeline

/-- Arithmetic terms over words.  `zero` is null, and the other constructors are records whose
slot 0 holds the constructor's index. -/
inductive Term where
  | zero
  | lit (n : UInt64)
  | neg (a : Term)
  | add (a b : Term)
  | mul (a b : Term)

/-- `Term` as records: `zero` is the null pointer, and each other constructor a record of its
index followed by its fields. -/
def Term.encode : Term → Node
  | .zero => .null
  | .lit n => .record [.word 1, .word n]
  | .neg a => .record [.word 2, .child a.encode]
  | .add a b => .record [.word 3, .child a.encode, .child b.encode]
  | .mul a b => .record [.word 4, .child a.encode, .child b.encode]

instance : Encode Term := ⟨Term.encode⟩

def keep (t : Term) : Term := t

def lit (n : UInt64) : Term := .lit n

def add (a b : Term) : Term := .add a b

def double (t : Term) : Term := .add t t

def eval : Term → UInt64
  | .zero => 0
  | .lit n => n
  | .neg a => 0 - eval a
  | .add a b => eval a + eval b
  | .mul a b => eval a * eval b

def size : Term → UInt64
  | .zero => 0
  | .lit _ => 1
  | .neg a => 1 + size a
  | .add a b => 1 + size a + size b
  | .mul a b => 1 + size a + size b

def swap : Term → Term
  | .zero => .zero
  | .lit n => .lit n
  | .neg a => .neg a
  | .add a b => .add b a
  | .mul a b => .mul b a

def right : Term → Term
  | .zero => .zero
  | .lit _ => .zero
  | .neg a => a
  | .add _ b => b
  | .mul _ b => b

def spine (acc : UInt64) (t : Term) : UInt64 :=
  match t with
  | .zero => acc
  | .lit n => acc + n
  | .neg a => spine (acc + 1) a
  | .add _ b => spine (acc + 2) b
  | .mul _ b => spine (acc + 3) b

verified_compile compiled := [keep, lit, add, double, eval, size, swap, right, spine]

#print axioms compiled.keep.implements
#print axioms compiled.eval.implements
#print axioms compiled.swap.implements
#print axioms compiled.spine.implements

end Verified.Examples.TaggedTypes
