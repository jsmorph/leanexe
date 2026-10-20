import Verified.Rename

namespace Verified

def Args.vars {S : List Sig} {Γ : List Ty} :
    (ps : List Ty) → Renaming ps Γ → Args S Γ ps
  | [], _ => .nil
  | _ :: ps, vars => .cons (.var (vars .here)) (Args.vars ps fun x => vars (.there x))

namespace ListFold

def nextArgs {S : List Sig} (e : Elem) (captures : List Ty) :
    Args S (.elem e :: context e captures) (params e captures) :=
  .cons (.var (.there (.there (.there .here))))
    (.cons (.var .here)
      (Args.vars captures fun x => .there (.there (.there (.there (.there (.there x)))))))

def tailBody {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (context e captures) (.elem e)) :
    TailBody S (params e captures) (.elem e) (params e captures) :=
  .treeCase .here (.ret (.var (.there .here))) (.letE body (.next (nextArgs e captures).get))

def meaning {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (context e captures) (.elem e)) (funs : Funs S) :
    Env (params e captures) → e.denote :=
  denoteWith (body.denote funs)

end ListFold
end Verified
