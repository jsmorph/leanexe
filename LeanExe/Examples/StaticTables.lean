namespace LeanExe.Examples.StaticTables

def first : Array UInt64 := #[0, 65, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF]
def second : Array UInt64 := #[7, 11]
def empty : Array UInt64 := #[]

def lookup (i : Nat) : UInt64 := first[i]!
def provedLookup (i : Nat) : UInt64 :=
  first[i % 4]'(by simpa [first] using Nat.mod_lt i (by decide : 0 < 4))
def lookupSecond (i : Nat) : UInt64 := second[i]!
def lookupEmpty (i : Nat) : UInt64 := empty[i]!

def changed (i : Nat) (x : UInt64) : Array UInt64 := first.set! i x

def afterChange (i : Nat) (x : UInt64) : UInt64 :=
  let a := first.set! i x
  a[i]! + first[i]!

def output : ByteArray := ByteArray.empty.push first[1]!.toUInt8

end LeanExe.Examples.StaticTables
