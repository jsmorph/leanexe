namespace LeanExe.Examples.IntMap

def capacityNat : Nat :=
  256

def capacity : UInt64 :=
  256

def tableWords : Nat :=
  512

def empty : Array UInt64 :=
  Array.replicate tableWords 0

def hash (key : UInt64) : UInt64 :=
  key % capacity

def probe (key attempt : UInt64) : UInt64 :=
  (hash key + attempt) % capacity

def keyIndex (slot : UInt64) : UInt64 :=
  slot * 2

def valueIndex (slot : UInt64) : UInt64 :=
  slot * 2 + 1

def getKey (table : Array UInt64) (slot : UInt64) : UInt64 :=
  table[(keyIndex slot).toNat]!

def getValue (table : Array UInt64) (slot : UInt64) : UInt64 :=
  table[(valueIndex slot).toNat]!

def setSlot (table : Array UInt64) (slot key value : UInt64) : Array UInt64 :=
  (Array.set! table (keyIndex slot).toNat key).set! (valueIndex slot).toNat value

def slotAvailable (table : Array UInt64) (key attempt : UInt64) : Bool :=
  getKey table (probe key attempt) == 0 || getKey table (probe key attempt) == key

def shouldInsert (table : Array UInt64) (key attempt done : UInt64) : Bool :=
  done == 0 && slotAvailable table key attempt

def insertFuel : Nat → UInt64 → UInt64 → UInt64 → UInt64 → Array UInt64 → Array UInt64
  | 0, _, _, _, _, table => table
  | fuel + 1, key, value, attempt, done, table =>
      insertFuel fuel key value (attempt + 1)
        (if shouldInsert table key attempt done then 1 else done)
        (if shouldInsert table key attempt done then
          setSlot table (probe key attempt) key value
        else
          table)

def insert (key value : UInt64) (table : Array UInt64) : Array UInt64 :=
  insertFuel capacityNat key value 0 0 table

def slotMatches (table : Array UInt64) (key attempt found : UInt64) : Bool :=
  found == 0 && getKey table (probe key attempt) == key

def lookupFuel : Nat → UInt64 → UInt64 → UInt64 → Array UInt64 → UInt64 → UInt64
  | 0, _, _, _, _, result => result
  | fuel + 1, key, attempt, found, table, result =>
      lookupFuel fuel key (attempt + 1)
        (if slotMatches table key attempt found then 1 else found)
        table
        (if slotMatches table key attempt found then
          getValue table (probe key attempt)
        else
          result)

def lookup (key : UInt64) (table : Array UInt64) : UInt64 :=
  lookupFuel capacityNat key 0 0 table 0

def buildFuel : Nat → UInt64 → Array UInt64 → Array UInt64
  | 0, _, table => table
  | fuel + 1, key, table =>
      buildFuel fuel (key + 1) (insert key (key * 10 + 7) table)

def build : Array UInt64 :=
  buildFuel 100 1 empty

def checksumFuel : Nat → UInt64 → Array UInt64 → UInt64 → UInt64
  | 0, _, _, acc => acc
  | fuel + 1, key, table, acc =>
      checksumFuel fuel (key + 1) table (acc + lookup key table)

def checksum : UInt64 :=
  checksumFuel 100 1 build 0

def query (key : UInt64) : UInt64 :=
  lookup key build

end LeanExe.Examples.IntMap
