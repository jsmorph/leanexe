import Project.ProofKit.WordArrayPushFrame

namespace Project.ProofKit.WordArrayPush
open Wasm

def prepared (s : Scratch) (length : Nat) : Scratch :=
  { s with
    length := UInt64.ofNat length
    count := UInt64.ofNat length
    nextLength := UInt64.ofNat (length + 1) }

macro "wp_push_frame" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (discharger := decide) only [wp_simp, Frame.withValues_get,
    frame_get, frame_set, frame_set_values, frame_values, frame_with_empty,
    Scratch.words, Scratch.write, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.add_zero, Nat.reduceAdd, UInt64.mul_one, ite_false, $ts,*])

theorem prepare_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (s : Scratch) (input : Array UInt64)
    (ha : UInt64Array.At store s.source input) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store (frame params saved tail (prepared s input.size)) env) :
    wp module_ (prepare (params.length + saved.length) ++ rest) Q store
      (frame params saved tail s) env := by
  simp only [prepare, List.cons_append, List.nil_append]
  have hSource := frame_get params saved tail s 0 (by decide)
  simp only [Nat.add_zero, Scratch.words, List.getElem?_cons_zero] at hSource
  wp_push_frame [hSource, ha.pointerAddress_eq, show 2^32 = 4294967296 by decide,
    UInt32.toNat_zero, UInt32.add_zero, Nat.not_lt.mpr ha.lengthBound, ha.lengthRead]
  simpa only [prepared, UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl] using hNext

#print axioms prepare_spec
end Project.ProofKit.WordArrayPush
