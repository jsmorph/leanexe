namespace LeanExe.Examples.IntMap

def capacityNat : Nat :=
  256

def capacity : UInt64 :=
  256

structure Slot where
  key : UInt64
  value : UInt64
  deriving Inhabited

structure Table where
  slots : Array Slot

def emptySlot : Slot :=
  { key := 0, value := 0 }

def empty : Table :=
  { slots := Array.replicate capacityNat emptySlot }

def hash (key : UInt64) : UInt64 :=
  key % capacity

def probe (key attempt : UInt64) : UInt64 :=
  (hash key + attempt) % capacity

def getSlot (table : Table) (slot : UInt64) : Slot :=
  table.slots[slot.toNat]!

def getKey (table : Table) (slot : UInt64) : UInt64 :=
  (getSlot table slot).key

def getValue (table : Table) (slot : UInt64) : UInt64 :=
  (getSlot table slot).value

def setSlot (table : Table) (slot key value : UInt64) : Table :=
  { slots := table.slots.set! slot.toNat { key := key, value := value } }

def slotAvailable (table : Table) (key attempt : UInt64) : Bool :=
  getKey table (probe key attempt) == 0 || getKey table (probe key attempt) == key

def shouldInsert (table : Table) (key attempt done : UInt64) : Bool :=
  done == 0 && slotAvailable table key attempt

def insertFuel : Nat → UInt64 → UInt64 → UInt64 → UInt64 → Table → Table
  | 0, _, _, _, _, table => table
  | fuel + 1, key, value, attempt, done, table =>
      insertFuel fuel key value (attempt + 1)
        (if shouldInsert table key attempt done then 1 else done)
        (if shouldInsert table key attempt done then
          setSlot table (probe key attempt) key value
        else
          table)

def insert (key value : UInt64) (table : Table) : Table :=
  insertFuel capacityNat key value 0 0 table

def slotMatches (table : Table) (key attempt found : UInt64) : Bool :=
  found == 0 && getKey table (probe key attempt) == key

def lookupFuel : Nat → UInt64 → UInt64 → UInt64 → Table → UInt64 → UInt64
  | 0, _, _, _, _, result => result
  | fuel + 1, key, attempt, found, table, result =>
      lookupFuel fuel key (attempt + 1)
        (if slotMatches table key attempt found then 1 else found)
        table
        (if slotMatches table key attempt found then
          getValue table (probe key attempt)
        else
          result)

def lookup (key : UInt64) (table : Table) : UInt64 :=
  lookupFuel capacityNat key 0 0 table 0

def buildFuel : Nat → UInt64 → Table → Table
  | 0, _, table => table
  | fuel + 1, key, table =>
      buildFuel fuel (key + 1) (insert key (key * 10 + 7) table)

def build : Table :=
  buildFuel 100 1 empty

def checksumFuel : Nat → UInt64 → Table → UInt64 → UInt64
  | 0, _, _, acc => acc
  | fuel + 1, key, table, acc =>
      checksumFuel fuel (key + 1) table (acc + lookup key table)

def checksum : UInt64 :=
  checksumFuel 100 1 build 0

def query (key : UInt64) : UInt64 :=
  lookup key build

end LeanExe.Examples.IntMap
