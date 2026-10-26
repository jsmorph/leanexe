import Verified.Examples.TaggedTypes
import TestSupport.Host
import TestSupport.Records

namespace Verified.Examples.TaggedTypes

open TestSupport.Host

/-- The depth of the deepest call of a recursion over `t` that recurses into every child, the
root's call at depth 0. -/
def Term.height : Term → Nat
  | .zero | .lit _ => 0
  | .neg a => 1 + a.height
  | .add a b | .mul a b => 1 + max a.height b.height

/-- `n` negations of a literal. -/
def Term.negChain : Nat → Term
  | 0 => .lit 5
  | n + 1 => .neg (Term.negChain n)

/-- `n` additions, each of a literal and the rest. -/
def Term.addChain : Nat → Term
  | 0 => .zero
  | n + 1 => .add (.lit (UInt64.ofNat n)) (Term.addChain n)

/-- A term of at most `n` constructors and `fuel` levels whose shape and words follow the
arbitrary words from `seed`. -/
def Term.arbitraryWith : Nat → Nat → Nat → Term
  | 0, _, _ | _, 0, _ => .zero
  | fuel + 1, n + 1, seed =>
    let left := (rw (seed + 1)).toNat % (n + 1)
    match (rw seed).toNat % 4 with
    | 0 => .lit (rw (seed + 7))
    | 1 => .neg (Term.arbitraryWith fuel n (2 * seed + 1))
    | 2 => .add (Term.arbitraryWith fuel left (2 * seed + 1))
      (Term.arbitraryWith fuel (n - left) (2 * seed + 2))
    | _ => .mul (Term.arbitraryWith fuel left (2 * seed + 1))
      (Term.arbitraryWith fuel (n - left) (2 * seed + 2))

/-- A term of at most `n` constructors from `seed`.  Each level takes at least one constructor,
so `n` levels suffice. -/
def Term.arbitrary (n seed : Nat) : Term := Term.arbitraryWith n n seed

def cases : IO Unit := do
  let terms := [Term.zero, .lit 0, .lit maxU, .neg .zero, .neg (.lit maxU),
      .add .zero (.lit 3), .mul (.lit 3) .zero, Term.negChain 998, Term.negChain 999,
      Term.negChain 1000, Term.addChain 999, Term.addChain 1000, Term.addChain 4096] ++
    (List.range 20).map fun i => Term.arbitrary (10 * i) i
  for n in [0, 7, maxU] do
    IO.println s!"taggedtypes|lit|records-u64|{u n}|{records (lit n)}|1|1"
  for t in terms do
    let n := (size t).toNat
    let arg := recordsArg t
    IO.println s!"taggedtypes|keep|records-u64|{arg}|{records (keep t)}|{n}|{n}"
    IO.println s!"taggedtypes|double|records-u64|{arg}|{records (double t)}|{2 * n + 1}|{2 * n + 1}"
    IO.println s!"taggedtypes|swap|records-u64|{arg}|{records (swap t)}|{n}|{n}"
    let rest := (size (right t)).toNat
    IO.println s!"taggedtypes|right|records-u64|{arg}|{records (right t)}|{rest}|{n}"
    for acc in [0, maxU] do
      IO.println s!"taggedtypes|spine|i64|{u acc} {arg}|{spine acc t}|{n}|{n}"
    if t.height < 1000 then
      IO.println s!"taggedtypes|eval|i64|{arg}|{eval t}|{n}|{n}"
      IO.println s!"taggedtypes|size|i64|{arg}|{size t}|{n}|{n}"
    else
      IO.println s!"taggedtypes|eval|i64|{arg}|trap"
      IO.println s!"taggedtypes|size|i64|{arg}|trap"
  for a in terms.take 8 do
    for b in terms.take 8 do
      let n := (size a).toNat + (size b).toNat + 1
      let args := s!"{recordsArg a} {recordsArg b}"
      IO.println s!"taggedtypes|add|records-u64|{args}|{records (add a b)}|{n}|{n}"

end Verified.Examples.TaggedTypes
