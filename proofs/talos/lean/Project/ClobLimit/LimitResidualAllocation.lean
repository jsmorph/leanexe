import Project.ClobLimit.MatchOutput
import Project.ProofKit.FixedArrayAllocate

namespace Project.ClobLimit.LimitResidualAllocation

open Wasm Project.Clob Project.ClobLimit Project.Runtime Project.ProofKit
  Project.ClobLimit.MatchInvariant Project.ClobMatchFuel.Allocation

def need (ctx : Context) : UInt64 := orderArrayBytesU (ctx.result.book.length + 1)

def root (ctx : Context) (data : MatchOutput.OutputData) : UInt64 :=
  FixedArrayAllocate.root data.g0 (need ctx) data.nodes

def capacity (ctx : Context) (data : MatchOutput.OutputData) : UInt64 :=
  match takeFirstFitFrom 0 (need ctx) data.nodes with
  | some choice => choice.node.capacity
  | none => need ctx

def heap (ctx : Context) (data : MatchOutput.OutputData) : UInt64 :=
  match takeFirstFitFrom 0 (need ctx) data.nodes with
  | some _ => data.g0
  | none => data.g0 + 48 + need ctx

def nodes (ctx : Context) (data : MatchOutput.OutputData) : List FreeNode :=
  match takeFirstFitFrom 0 (need ctx) data.nodes with
  | some choice => choice.remaining
  | none => data.nodes

def allocated (st : Store Unit) (ctx : Context) (data : MatchOutput.OutputData) : Store Unit :=
  FixedArrayAllocateNone.counted
    (FixedArrayAllocate.allocated st data.g0 (need ctx) 5 data.nodes) ctx.expectedG2

def store (st : Store Unit) (ctx : Context) (data : MatchOutput.OutputData) : Store Unit :=
  { allocated st ctx data with
    mem := (allocated st ctx data).mem.write64 (root ctx data).toUInt32
      (UInt64.ofNat (ctx.result.book.length + 1)) }

end Project.ClobLimit.LimitResidualAllocation
