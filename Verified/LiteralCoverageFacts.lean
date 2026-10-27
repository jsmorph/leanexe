import Verified.LiteralCoverage

namespace Verified

variable {S : List Sig} {Γ : List Ty} {pool : Bytes.LiteralPool}

theorem Expr.covered_bin {op : BinOp} {left right : Expr S Γ .word}
    (h : (Expr.bin op left right).Covered pool) : left.Covered pool ∧ right.Covered pool :=
  List.append_subset.mp h

theorem Expr.covered_cmp {op : CmpOp} {left right : Expr S Γ .word}
    (h : (Expr.cmp op left right).Covered pool) : left.Covered pool ∧ right.Covered pool :=
  List.append_subset.mp h

theorem Expr.covered_and {left right : Expr S Γ .bool}
    (h : (Expr.and left right).Covered pool) : left.Covered pool ∧ right.Covered pool :=
  List.append_subset.mp h

theorem Expr.covered_or {left right : Expr S Γ .bool}
    (h : (Expr.or left right).Covered pool) : left.Covered pool ∧ right.Covered pool :=
  List.append_subset.mp h

theorem Expr.covered_pair {s t : Ty} {first : Expr S Γ s} {second : Expr S Γ t}
    (h : (Expr.pair first second).Covered pool) : first.Covered pool ∧ second.Covered pool :=
  List.append_subset.mp h

theorem Expr.covered_mk {a b : Elem} {first : Expr S Γ (.elem a)} {second : Expr S Γ (.elem b)}
    (h : (Expr.mk first second).Covered pool) : first.Covered pool ∧ second.Covered pool :=
  List.append_subset.mp h

theorem Expr.covered_ite {t : Ty} {cond : Expr S Γ .bool} {yes no : Expr S Γ t}
    (h : (Expr.ite cond yes no).Covered pool) :
    cond.Covered pool ∧ yes.Covered pool ∧ no.Covered pool := by
  simpa only [Expr.Covered, Expr.literals, List.append_subset, and_assoc] using h

theorem Expr.covered_letE {s t : Ty} {value : Expr S Γ s} {body : Expr S (s :: Γ) t}
    (h : (Expr.letE value body).Covered pool) : value.Covered pool ∧ body.Covered pool :=
  List.append_subset.mp h

theorem Expr.covered_letPair {s t u : Ty} {value : Expr S Γ (.pair s t)}
    {body : Expr S (t :: s :: Γ) u} (h : (Expr.letPair value body).Covered pool) :
    value.Covered pool ∧ body.Covered pool := List.append_subset.mp h

theorem Expr.covered_loop {t : Ty} {count : Expr S Γ .word} {init : Expr S Γ t}
    {cond : Expr S (t :: Γ) .bool} {body : Expr S (t :: .word :: Γ) t}
    (h : (Expr.loop count init cond body).Covered pool) :
    count.Covered pool ∧ init.Covered pool ∧ cond.Covered pool ∧ body.Covered pool := by
  simpa only [Expr.Covered, Expr.literals, List.append_subset, and_assoc] using h

theorem Expr.covered_fold {e : Elem} {t : Ty} {x : Var Γ (.array e)} {init : Expr S Γ t}
    {body : Expr S (.elem e :: t :: .word :: Γ) t}
    (h : (Expr.fold x init body).Covered pool) : init.Covered pool ∧ body.Covered pool :=
  List.append_subset.mp h

theorem Expr.covered_call {g : Sig} {func : FVar S g}
    {args : (i : Fin g.params.length) → Expr S Γ (g.params.get i)}
    (h : (Expr.call func args).Covered pool) : ∀ i, (args i).Covered pool :=
  literals_args_subset.mp h

theorem Expr.covered_treeNode {shape : TreeShape} {r : Fin shape.records}
    {reuse : Option (Var Γ (.treeHeader shape r))}
    {words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i)}
    {children : Fin (shape.children r) → Expr S Γ (.tree shape)}
    (h : (Expr.treeNode r reuse words children).Covered pool) :
    (∀ i, (words i).Covered pool) ∧ (∀ i, (children i).Covered pool) := by
  have parts := List.append_subset.mp h
  exact ⟨literals_args_subset.mp parts.1, literals_args_subset.mp parts.2⟩

theorem Expr.covered_treeCase {shape : TreeShape} {t : Ty} {x : Var Γ (.tree shape)}
    {empty : shape.hasNull = true → Expr S Γ t}
    {nodes : (r : Fin shape.records) → Expr S (shape.context r Γ) t}
    (h : (Expr.treeCase x empty nodes).Covered pool) :
    (∀ hn, (empty hn).Covered pool) ∧ ∀ r, (nodes r).Covered pool := by
  have parts := List.append_subset.mp h
  refine ⟨fun hn => ?_, literals_args_subset.mp parts.2⟩
  have hEmpty := parts.1
  rw [dif_pos hn] at hEmpty
  exact hEmpty

theorem Expr.covered_listFold {e : Elem} {captures : List Ty}
    {args : (i : Fin (ListFold.params e captures).length) →
      Expr S Γ ((ListFold.params e captures).get i)}
    {body : Expr S (ListFold.context e captures) (.elem e)}
    (h : (Expr.listFold args body).Covered pool) :
    (∀ i, (args i).Covered pool) ∧ body.Covered pool := by
  have parts := List.append_subset.mp h
  exact ⟨literals_args_subset.mp parts.1, parts.2⟩

theorem Expr.covered_build {e : Elem} {count : Expr S Γ .word}
    {elem : Expr S (.word :: Γ) (.elem e)} (h : (Expr.build count elem).Covered pool) :
    count.Covered pool ∧ elem.Covered pool := List.append_subset.mp h

theorem Expr.covered_bytesBuild {count : Expr S Γ .word} {elem : Expr S (.word :: Γ) .word}
    (h : (Expr.bytesBuild count elem).Covered pool) : count.Covered pool ∧ elem.Covered pool :=
  List.append_subset.mp h

theorem Expr.covered_set {e : Elem} {x : Var Γ (.array e)} {index : Expr S Γ .word}
    {value : Expr S Γ (.elem e)} (h : (Expr.set x index value).Covered pool) :
    index.Covered pool ∧ value.Covered pool := List.append_subset.mp h

theorem Expr.covered_insertAt {e : Elem} {x : Var Γ (.array e)} {index : Expr S Γ .word}
    {value : Expr S Γ (.elem e)} (h : (Expr.insertAt x index value).Covered pool) :
    index.Covered pool ∧ value.Covered pool := List.append_subset.mp h

theorem Expr.covered_not {value : Expr S Γ .bool}
    (h : (Expr.not value).Covered pool) : value.Covered pool := h

theorem Expr.covered_bytesGet {x : Var Γ .bytes} {index : Expr S Γ .word}
    (h : (Expr.bytesGet x index).Covered pool) : index.Covered pool := h

theorem Expr.covered_get {e : Elem} {x : Var Γ (.array e)} {index : Expr S Γ .word}
    (h : (Expr.get x index).Covered pool) : index.Covered pool := h

theorem Expr.covered_eraseAt {e : Elem} {x : Var Γ (.array e)} {index : Expr S Γ .word}
    (h : (Expr.eraseAt x index).Covered pool) : index.Covered pool := h

theorem Expr.covered_push {e : Elem} {x : Var Γ (.array e)} {value : Expr S Γ (.elem e)}
    (h : (Expr.push x value).Covered pool) : value.Covered pool := h

theorem Expr.covered_fbin {op : FBinOp} {left right : Expr S Γ .float}
    (h : (Expr.fbin op left right).Covered pool) : left.Covered pool ∧ right.Covered pool :=
  List.append_subset.mp h

theorem Expr.covered_fcmp {op : FCmpOp} {left right : Expr S Γ .float}
    (h : (Expr.fcmp op left right).Covered pool) : left.Covered pool ∧ right.Covered pool :=
  List.append_subset.mp h

theorem Expr.covered_fbin32 {op : FBinOp} {left right : Expr S Γ .float32}
    (h : (Expr.fbin32 op left right).Covered pool) : left.Covered pool ∧ right.Covered pool :=
  List.append_subset.mp h

theorem Expr.covered_fcmp32 {op : FCmpOp} {left right : Expr S Γ .float32}
    (h : (Expr.fcmp32 op left right).Covered pool) : left.Covered pool ∧ right.Covered pool :=
  List.append_subset.mp h

theorem Expr.covered_funary {op : FUnOp} {value : Expr S Γ .float}
    (h : (Expr.funary op value).Covered pool) : value.Covered pool := h

theorem Expr.covered_funary32 {op : F32UnOp} {value : Expr S Γ .float32}
    (h : (Expr.funary32 op value).Covered pool) : value.Covered pool := h

theorem Expr.covered_toFloat {op : ToFloat} {value : Expr S Γ .word}
    (h : (Expr.toFloat op value).Covered pool) : value.Covered pool := h

theorem Expr.covered_toWord {op : ToWord} {value : Expr S Γ .float}
    (h : (Expr.toWord op value).Covered pool) : value.Covered pool := h

theorem Expr.covered_toFloat32 {op : ToFloat32} {value : Expr S Γ .word}
    (h : (Expr.toFloat32 op value).Covered pool) : value.Covered pool := h

theorem Expr.covered_toWord32 {op : ToWord32} {value : Expr S Γ .float32}
    (h : (Expr.toWord32 op value).Covered pool) : value.Covered pool := h

end Verified
