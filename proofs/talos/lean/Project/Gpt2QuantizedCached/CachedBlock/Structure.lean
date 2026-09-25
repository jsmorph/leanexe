import Project.Gpt2QuantizedCached.CachedBlock.Qkv

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm

def attentionSuccess : Program :=
  match (normalizedSuccess[140]? : Option Instruction) with
  | some (.iff _ _ _ body _ _) => body
  | _ => []

def normalized2Success : Program :=
  match (attentionSuccess[205]? : Option Instruction) with
  | some (.iff _ _ _ body _ _) => body
  | _ => []

def activatedSuccess : Program :=
  match (normalized2Success[125]? : Option Instruction) with
  | some (.iff _ _ _ body _ _) => body
  | _ => []

end Project.Gpt2QuantizedCached.CachedBlock
