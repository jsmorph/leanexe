import Verified.Source

namespace Verified

abbrev FunRenaming (S T : List Sig) := {g : Sig} → FVar S g → FVar T g

def Expr.renameFuns {S T : List Sig} (ρ : FunRenaming S T) :
    {Γ : List Ty} → {t : Ty} → Expr S Γ t → Expr T Γ t
  | _, _, .word n => .word n
  | _, _, .bool b => .bool b
  | _, _, .var x => .var x
  | _, _, .treeNil shape => .treeNil shape
  | _, _, .treeNode reuse words children =>
    .treeNode reuse (fun i => (words i).renameFuns ρ) (fun i => (children i).renameFuns ρ)
  | _, _, .treeCase x empty node => .treeCase x (empty.renameFuns ρ) (node.renameFuns ρ)
  | _, _, .bin op a b => .bin op (a.renameFuns ρ) (b.renameFuns ρ)
  | _, _, .cmp op a b => .cmp op (a.renameFuns ρ) (b.renameFuns ρ)
  | _, _, .not a => .not (a.renameFuns ρ)
  | _, _, .and a b => .and (a.renameFuns ρ) (b.renameFuns ρ)
  | _, _, .or a b => .or (a.renameFuns ρ) (b.renameFuns ρ)
  | _, _, .ite c a b => .ite (c.renameFuns ρ) (a.renameFuns ρ) (b.renameFuns ρ)
  | _, _, .letE a b => .letE (a.renameFuns ρ) (b.renameFuns ρ)
  | _, _, .call f args => .call (ρ f) (fun i => (args i).renameFuns ρ)
  | _, _, .pair a b => .pair (a.renameFuns ρ) (b.renameFuns ρ)
  | _, _, .letPair a b => .letPair (a.renameFuns ρ) (b.renameFuns ρ)
  | _, _, .loop n a c b =>
    .loop (n.renameFuns ρ) (a.renameFuns ρ) (c.renameFuns ρ) (b.renameFuns ρ)
  | _, _, .fold x a b => .fold x (a.renameFuns ρ) (b.renameFuns ρ)
  | _, _, .listFold args body => .listFold (fun i => (args i).renameFuns ρ) (body.renameFuns ρ)
  | _, _, .size x => .size x
  | _, _, .bytesEmpty => .bytesEmpty
  | _, _, .bytesLiteral bytes => .bytesLiteral bytes
  | _, _, .bytesSize x => .bytesSize x
  | _, _, .bytesGet x index => .bytesGet x (index.renameFuns ρ)
  | _, _, .bytesBuild count elem => .bytesBuild (count.renameFuns ρ) (elem.renameFuns ρ)
  | _, _, .leSize x i => .leSize x i
  | _, _, .get x i => .get x (i.renameFuns ρ)
  | _, _, .build n e => .build (n.renameFuns ρ) (e.renameFuns ρ)
  | _, _, .set x i v => .set x (i.renameFuns ρ) (v.renameFuns ρ)
  | _, _, .push x v => .push x (v.renameFuns ρ)
  | _, _, .append x y => .append x y
  | _, _, .insertAt x i v => .insertAt x (i.renameFuns ρ) (v.renameFuns ρ)
  | _, _, .eraseAt x i => .eraseAt x (i.renameFuns ρ)
  | _, _, .float n => .float n
  | _, _, .float32 n => .float32 n
  | _, _, .fbin op a b => .fbin op (a.renameFuns ρ) (b.renameFuns ρ)
  | _, _, .funary op a => .funary op (a.renameFuns ρ)
  | _, _, .fcmp op a b => .fcmp op (a.renameFuns ρ) (b.renameFuns ρ)
  | _, _, .toFloat op a => .toFloat op (a.renameFuns ρ)
  | _, _, .toWord op a => .toWord op (a.renameFuns ρ)
  | _, _, .fbin32 op a b => .fbin32 op (a.renameFuns ρ) (b.renameFuns ρ)
  | _, _, .funary32 op a => .funary32 op (a.renameFuns ρ)
  | _, _, .fcmp32 op a b => .fcmp32 op (a.renameFuns ρ) (b.renameFuns ρ)
  | _, _, .toFloat32 op a => .toFloat32 op (a.renameFuns ρ)
  | _, _, .toWord32 op a => .toWord32 op (a.renameFuns ρ)
  | _, _, .mk a b => .mk (a.renameFuns ρ) (b.renameFuns ρ)
  | _, _, .proj x p => .proj x p

theorem Expr.denote_renameFuns {S T : List Sig} (ρ : FunRenaming S T)
    (funs : Funs S) (target : Funs T)
    (h : ∀ {g : Sig} (f : FVar S g) env, target.get (ρ f) env = funs.get f env)
    (e : Expr S Γ t) (env : Env Γ) :
    (e.renameFuns ρ).denote target env = e.denote funs env := by
  induction e with
  | call f args ih =>
    simp only [Expr.renameFuns, Expr.denote, h]
    congr 2
    funext i
    exact ih i env
  | listFold args body ha hb =>
    simp only [Expr.renameFuns, Expr.denote]
    have hbody : (body.renameFuns ρ).denote target = body.denote funs := funext hb
    rw [hbody]
    congr 2
    funext i
    exact ha i env
  | _ => simp_all [Expr.renameFuns, Expr.denote]

theorem Expr.denote_weakenFuns {g : Sig} (e : Expr S Γ t) (M : Env g.params → g.result.denote)
    (funs : Funs S) (env : Env Γ) :
    (e.renameFuns (fun f => .there f)).denote (.cons M funs) env = e.denote funs env :=
  e.denote_renameFuns _ funs (.cons M funs) (fun _ _ => rfl) env

#print axioms Expr.denote_renameFuns

end Verified
