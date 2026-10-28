import Verified.Literals
import Verified.Rename
import Verified.FunRename

namespace Verified

theorem literals_args_congr {n : Nat} {first second : Fin n → List Bytes.Literal}
    (h : ∀ i, first i = second i) :
    (List.ofFn first).flatten = (List.ofFn second).flatten :=
  congrArg List.flatten (congrArg List.ofFn (funext h))

theorem literals_append3_congr {a b c x y z : List Bytes.Literal}
    (ha : a = x) (hb : b = y) (hc : c = z) : a ++ b ++ c = x ++ y ++ z := by
  rw [ha, hb, hc]

theorem literals_append4_congr {a b c d x y z w : List Bytes.Literal}
    (ha : a = x) (hb : b = y) (hc : c = z) (hd : d = w) :
    a ++ b ++ c ++ d = x ++ y ++ z ++ w := by
  rw [ha, hb, hc, hd]

theorem Expr.literals_rename (expr : Expr S Γ t) (renameVars : Renaming Γ Δ) :
    (expr.rename renameVars).literals = expr.literals := by
  induction expr generalizing Δ with
  | call func args ih => exact literals_args_congr fun i => ih i renameVars
  | treeNode r reuse words arrays buffers children ihWords ihArrays ihBuffers ihChildren =>
    exact congrArg₂ List.append (congrArg₂ List.append (congrArg₂ List.append
      (literals_args_congr fun i => ihWords i renameVars)
      (literals_args_congr fun i => ihArrays i renameVars))
      (literals_args_congr fun i => ihBuffers i renameVars))
      (literals_args_congr fun i => ihChildren i renameVars)
  | listFold args body ihArgs ihBody =>
    exact congrArg₂ List.append (literals_args_congr fun i => ihArgs i renameVars)
      (Eq.refl body.literals)
  | treeCase x empty nodes ihEmpty ihNodes =>
    exact congrArg₂ List.append (dite_congr rfl (fun h => ihEmpty h renameVars) (fun _ => rfl))
      (literals_args_congr fun r => ihNodes r _)
  | bin op left right ihLeft ihRight =>
    exact congrArg₂ List.append (ihLeft renameVars) (ihRight renameVars)
  | cmp op left right ihLeft ihRight =>
    exact congrArg₂ List.append (ihLeft renameVars) (ihRight renameVars)
  | and left right ihLeft ihRight =>
    exact congrArg₂ List.append (ihLeft renameVars) (ihRight renameVars)
  | or left right ihLeft ihRight =>
    exact congrArg₂ List.append (ihLeft renameVars) (ihRight renameVars)
  | pair first second ihFirst ihSecond =>
    exact congrArg₂ List.append (ihFirst renameVars) (ihSecond renameVars)
  | mk first second ihFirst ihSecond =>
    exact congrArg₂ List.append (ihFirst renameVars) (ihSecond renameVars)
  | ite cond yes no ihCond ihYes ihNo =>
    exact literals_append3_congr (ihCond renameVars) (ihYes renameVars) (ihNo renameVars)
  | letE value body ihValue ihBody =>
    exact congrArg₂ List.append (ihValue renameVars) (ihBody renameVars.lift)
  | letPair value body ihValue ihBody =>
    exact congrArg₂ List.append (ihValue renameVars)
      (ihBody (Renaming.lift (Renaming.lift renameVars)))
  | loop count init cond body ihCount ihInit ihCond ihBody =>
    exact literals_append4_congr (ihCount renameVars) (ihInit renameVars)
      (ihCond renameVars.lift) (ihBody (Renaming.lift (Renaming.lift renameVars)))
  | fold x init body ihInit ihBody =>
    exact congrArg₂ List.append (ihInit renameVars)
      (ihBody (Renaming.lift (Renaming.lift (Renaming.lift renameVars))))
  | bytesBuild count elem ihCount ihElem =>
    exact congrArg₂ List.append (ihCount renameVars) (ihElem renameVars.lift)
  | build count elem ihCount ihElem =>
    exact congrArg₂ List.append (ihCount renameVars) (ihElem renameVars.lift)
  | set x index value ihIndex ihValue =>
    exact congrArg₂ List.append (ihIndex renameVars) (ihValue renameVars)
  | insertAt x index value ihIndex ihValue =>
    exact congrArg₂ List.append (ihIndex renameVars) (ihValue renameVars)
  | not value ih => exact ih renameVars
  | funary op value ih => exact ih renameVars
  | funary32 op value ih => exact ih renameVars
  | toFloat op value ih => exact ih renameVars
  | toWord op value ih => exact ih renameVars
  | toFloat32 op value ih => exact ih renameVars
  | toWord32 op value ih => exact ih renameVars
  | bytesGet x index ih => exact ih renameVars
  | get x index ih => exact ih renameVars
  | eraseAt x index ih => exact ih renameVars
  | push x value ih => exact ih renameVars
  | fbin op left right ihLeft ihRight =>
    exact congrArg₂ List.append (ihLeft renameVars) (ihRight renameVars)
  | fcmp op left right ihLeft ihRight =>
    exact congrArg₂ List.append (ihLeft renameVars) (ihRight renameVars)
  | fbin32 op left right ihLeft ihRight =>
    exact congrArg₂ List.append (ihLeft renameVars) (ihRight renameVars)
  | fcmp32 op left right ihLeft ihRight =>
    exact congrArg₂ List.append (ihLeft renameVars) (ihRight renameVars)
  | _ => rfl

theorem Expr.literals_renameFuns (expr : Expr S Γ t)
    (renameFuncs : {g : Sig} → FVar S g → FVar T g) :
    (expr.renameFuns renameFuncs).literals = expr.literals := by
  induction expr with
  | call func args ih => exact literals_args_congr ih
  | treeNode r reuse words arrays buffers children ihWords ihArrays ihBuffers ihChildren =>
    exact congrArg₂ List.append (congrArg₂ List.append (congrArg₂ List.append
      (literals_args_congr ihWords) (literals_args_congr ihArrays)) (literals_args_congr ihBuffers))
      (literals_args_congr ihChildren)
  | listFold args body ihArgs ihBody =>
    exact congrArg₂ List.append (literals_args_congr ihArgs) ihBody
  | treeCase x empty nodes ihEmpty ihNodes =>
    exact congrArg₂ List.append (dite_congr rfl (fun h => ihEmpty h) (fun _ => rfl))
      (literals_args_congr ihNodes)
  | bin op left right ihLeft ihRight => exact congrArg₂ List.append ihLeft ihRight
  | cmp op left right ihLeft ihRight => exact congrArg₂ List.append ihLeft ihRight
  | and left right ihLeft ihRight => exact congrArg₂ List.append ihLeft ihRight
  | or left right ihLeft ihRight => exact congrArg₂ List.append ihLeft ihRight
  | pair first second ihFirst ihSecond => exact congrArg₂ List.append ihFirst ihSecond
  | mk first second ihFirst ihSecond => exact congrArg₂ List.append ihFirst ihSecond
  | ite cond yes no ihCond ihYes ihNo => exact literals_append3_congr ihCond ihYes ihNo
  | letE value body ihValue ihBody => exact congrArg₂ List.append ihValue ihBody
  | letPair value body ihValue ihBody => exact congrArg₂ List.append ihValue ihBody
  | loop count init cond body ihCount ihInit ihCond ihBody =>
    exact literals_append4_congr ihCount ihInit ihCond ihBody
  | fold x init body ihInit ihBody => exact congrArg₂ List.append ihInit ihBody
  | bytesBuild count elem ihCount ihElem => exact congrArg₂ List.append ihCount ihElem
  | build count elem ihCount ihElem => exact congrArg₂ List.append ihCount ihElem
  | set x index value ihIndex ihValue => exact congrArg₂ List.append ihIndex ihValue
  | insertAt x index value ihIndex ihValue => exact congrArg₂ List.append ihIndex ihValue
  | not value ih => exact ih
  | funary op value ih => exact ih
  | funary32 op value ih => exact ih
  | toFloat op value ih => exact ih
  | toWord op value ih => exact ih
  | toFloat32 op value ih => exact ih
  | toWord32 op value ih => exact ih
  | bytesGet x index ih => exact ih
  | get x index ih => exact ih
  | eraseAt x index ih => exact ih
  | push x value ih => exact ih
  | fbin op left right ihLeft ihRight => exact congrArg₂ List.append ihLeft ihRight
  | fcmp op left right ihLeft ihRight => exact congrArg₂ List.append ihLeft ihRight
  | fbin32 op left right ihLeft ihRight => exact congrArg₂ List.append ihLeft ihRight
  | fcmp32 op left right ihLeft ihRight => exact congrArg₂ List.append ihLeft ihRight
  | _ => rfl

theorem literals_args_eq_nil {n : Nat} {args : Fin n → List Bytes.Literal} :
    (List.ofFn args).flatten = [] ↔ ∀ i, args i = [] := by
  constructor
  · intro h i
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro bytes hBytes
    have hMember := List.mem_flatten.mpr
      ⟨args i, List.mem_ofFn.mpr ⟨i, rfl⟩, hBytes⟩
    rw [h] at hMember
    exact nomatch hMember
  · intro h
    simp only [show args = (fun _ => []) from funext h, List.ofFn_const]
    simp

end Verified
