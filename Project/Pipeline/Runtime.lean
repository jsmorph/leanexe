import Project.Runtime.FreeList
import Project.ProofKit.Array

namespace Project.Pipeline

open Wasm Project.Runtime Project.ProofKit

/-- The allocator state held in globals 0 through 5: the bump pointer `top`, the
free list, and the allocation, retain, release, and free counters. -/
structure Heap where
  top : UInt64
  free : List FreeNode
  allocs : UInt64
  retains : UInt64
  releases : UInt64
  frees : UInt64

def Heap.globals (heap : Heap) : List Value :=
  [.i64 heap.top, .i64 (freeHead heap.free), .i64 heap.allocs, .i64 heap.retains,
    .i64 heap.releases, .i64 heap.frees]

/-- The allocator invariant.  The globals hold `heap`, the free list is laid out
in memory, every free block lies between the heap base at 4096 and `top`, `top`
lies inside memory, and memory has at most 65,536 pages. -/
structure Heap.At (heap : Heap) (store : Store Unit) : Prop where
  globals : store.globals.globals = heap.globals
  freeList : FreeListAt store.mem heap.free
  base : 4096 ≤ heap.top.toNat
  top : heap.top.toNat ≤ store.mem.pages * 65536
  pages : store.mem.pages ≤ 65536
  above : ∀ node ∈ heap.free, 4096 + 48 ≤ node.root.toNat
  below : ∀ node ∈ heap.free, node.root.toNat + node.capacity.toNat ≤ heap.top.toNat

/-- The length word and elements of `words` at `ptr`, below `top` and outside
every free block, so that no allocation can overwrite them. -/
structure Heap.Borrowed (heap : Heap) (store : Store Unit) (ptr : UInt64)
    (words : Array UInt64) : Prop where
  values : UInt64Array.At store ptr words
  below : ptr.toNat + 8 * (words.size + 1) ≤ heap.top.toNat
  separate : ∀ node ∈ heap.free,
    regionsDisjoint (ptr.toNat, 8 * (words.size + 1)) node.region

def objectMagic : UInt64 := 5501223100278326855

/-- The payload capacity recorded in the header of the object at `ptr`. -/
def capacityAt (store : Store Unit) (ptr : UInt64) : Nat :=
  (store.mem.read64 (ptr - 32).toUInt32).toNat

/-- A runtime array object at payload pointer `ptr` holding `words`, with
reference count one, element width one, and no child pointers.  The object,
header included, lies inside the 32-bit address space, below `top`, and outside
every free block. -/
structure Heap.Owned (heap : Heap) (store : Store Unit) (ptr : UInt64)
    (words : Array UInt64) : Prop where
  values : UInt64Array.At store ptr words
  base : 4096 + 48 ≤ ptr.toNat
  magic : store.mem.read64 (ptr - 48).toUInt32 = objectMagic
  count : store.mem.read64 (ptr - 40).toUInt32 = 1
  capacity : 8 * (words.size + 1) ≤ capacityAt store ptr
  kind : store.mem.read64 (ptr - 24).toUInt32 = 2
  width : store.mem.read64 (ptr - 16).toUInt32 = 1
  childMask : store.mem.read64 (ptr - 8).toUInt32 = 0
  address : ptr.toNat + capacityAt store ptr < 4294967296
  below : ptr.toNat + capacityAt store ptr ≤ heap.top.toNat
  separate : ∀ node ∈ heap.free,
    regionsDisjoint node.region (ptr.toNat - 48, 48 + capacityAt store ptr)

/-- The allocator can advance `top` by `bytes` without passing the 32-bit address
limit or the growth cap of memory 0 in module `m`. -/
structure Heap.Room (heap : Heap) (store : Store Unit) (m : Module) (bytes : Nat) : Prop where
  address : heap.top.toNat + bytes < 4294967296
  cap : heap.top.toNat + bytes ≤ store.memoryCap m 0 * 65536

end Project.Pipeline
