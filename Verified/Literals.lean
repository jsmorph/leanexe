import Verified.Source
import Verified.Bytes.LiteralPool

namespace Verified

namespace Bytes.LiteralPool

def empty : LiteralPool := ⟨4096, []⟩

end Bytes.LiteralPool

def Expr.literals : {Γ : List Ty} → {t : Ty} → Expr S Γ t → List Bytes.Literal
  | _, _, .bytesLiteral bytes => if bytes = [] then [] else [bytes]
  | _, _, .bin _ left right | _, _, .cmp _ left right
  | _, _, .fbin _ left right | _, _, .fcmp _ left right
  | _, _, .fbin32 _ left right | _, _, .fcmp32 _ left right
  | _, _, .and left right | _, _, .or left right
  | _, _, .mk left right | _, _, .pair left right => left.literals ++ right.literals
  | _, _, .not value | _, _, .funary _ value | _, _, .funary32 _ value
  | _, _, .toFloat _ value | _, _, .toWord _ value
  | _, _, .toFloat32 _ value | _, _, .toWord32 _ value => value.literals
  | _, _, .ite cond yes no => cond.literals ++ yes.literals ++ no.literals
  | _, _, .letE value body | _, _, .letPair value body => value.literals ++ body.literals
  | _, _, .call _ args => (List.ofFn fun i => (args i).literals).flatten
  | _, _, .loop count init cond body =>
    count.literals ++ init.literals ++ cond.literals ++ body.literals
  | _, _, .fold _ init body => init.literals ++ body.literals
  | _, _, .listFold args body =>
    (List.ofFn fun i => (args i).literals).flatten ++ body.literals
  | _, _, .get _ index | _, _, .bytesGet _ index | _, _, .eraseAt _ index => index.literals
  | _, _, .build count elem | _, _, .bytesBuild count elem => count.literals ++ elem.literals
  | _, _, .set _ index value | _, _, .insertAt _ index value => index.literals ++ value.literals
  | _, _, .push _ value => value.literals
  | _, _, .treeNode _ _ words children =>
    (List.ofFn fun i => (words i).literals).flatten ++
      (List.ofFn fun i => (children i).literals).flatten
  | _, _, .treeCase (shape := shape) _ empty nodes =>
    (if h : shape.hasNull = true then (empty h).literals else []) ++
      (List.ofFn fun r => (nodes r).literals).flatten
  | _, _, .word _ | _, _, .bool _ | _, _, .float _ | _, _, .float32 _
  | _, _, .var _ | _, _, .treeNil _ _ | _, _, .size _ | _, _, .bytesEmpty
  | _, _, .bytesSize _ | _, _, .leSize _ _ | _, _, .append _ _ | _, _, .proj _ _ => []

def Expr.Covered (expr : Expr S Γ t) (pool : Bytes.LiteralPool) : Prop :=
  expr.literals ⊆ pool.values

def TailBody.literals : {Γ : List Ty} → TailBody S params result Γ → List Bytes.Literal
  | _, .ret value => value.literals
  | _, .next args => (List.ofFn fun i => (args i).literals).flatten
  | _, .ite cond yes no => cond.literals ++ yes.literals ++ no.literals
  | _, .letE value body | _, .letPair value body => value.literals ++ body.literals
  | _, .treeCase (shape := shape) _ empty nodes =>
    (if h : shape.hasNull = true then (empty h).literals else []) ++
      (List.ofFn fun r => (nodes r).literals).flatten

def TailBody.Covered (body : TailBody S params result Γ) (pool : Bytes.LiteralPool) : Prop :=
  body.literals ⊆ pool.values

def Prog.literals : {S : List Sig} → Prog S → List Bytes.Literal
  | _, .nil => []
  | _, .cons func rest => rest.literals ++ func.body.literals
  | _, .consRec func rest => rest.literals ++ func.body.literals
  | _, .consTail func rest => rest.literals ++ func.body.literals

def Prog.Covered (prog : Prog S) (pool : Bytes.LiteralPool) : Prop :=
  prog.literals ⊆ pool.values

def Prog.literalPool (prog : Prog S) (base : Nat) : Bytes.LiteralPool :=
  ⟨base, prog.literals.eraseDups⟩

theorem Prog.covered_literalPool (prog : Prog S) (base : Nat) :
    prog.Covered (prog.literalPool base) := by
  intro bytes hBytes
  exact List.mem_eraseDups.mpr hBytes

theorem literals_args_subset {n : Nat} {args : Fin n → List Bytes.Literal}
    {values : List Bytes.Literal} :
    (List.ofFn args).flatten ⊆ values ↔ ∀ i, args i ⊆ values := by
  constructor
  · intro h i bytes hBytes
    exact h (List.mem_flatten.mpr ⟨args i, List.mem_ofFn.mpr ⟨i, rfl⟩, hBytes⟩)
  · intro h bytes hBytes
    obtain ⟨arg, hArg, hBytes⟩ := List.mem_flatten.mp hBytes
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hArg
    exact h i hBytes

end Verified
