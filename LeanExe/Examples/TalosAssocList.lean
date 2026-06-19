namespace LeanExe
namespace Examples.TalosAssocList

def lookup : List (UInt64 × UInt64) → UInt64 → UInt64
  | [], _ => 0
  | (k, v) :: rest, key =>
      if k == key then
        v
      else
        lookup rest key

def sample : List (UInt64 × UInt64) :=
  [(7, 70), (2, 20), (9, 90), (2, 22)]

def lookupDemo (key : UInt64) : UInt64 :=
  lookup sample key

end Examples.TalosAssocList
end LeanExe
