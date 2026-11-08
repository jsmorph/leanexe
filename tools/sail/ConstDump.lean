import THE_MODULE_NAME

/-!
Writes `consts.txt` in the current directory: for every constant whose name contains the module's
root name, other than the auxiliary matchers, the name and hashes of its type and value, with that
name component replaced by `M` in constant and projection names and each reference to a matcher
replaced by the hash of the matcher's own type and value.  Two builds of translations with
different module names and different matcher numbering then compare line by line after
`LC_ALL=C sort`.  Substitute the module name for THE_MODULE_NAME and run it with `lake env lean`
in the built project.
-/

open Lean Meta

def root : String := "THE_MODULE_NAME"

def rename (n : Name) : Name :=
  n.componentsRev.foldr (init := Name.anonymous) fun c acc =>
    match c with
    | .str _ s => Name.mkStr acc (s.replace root "M")
    | .num _ k => Name.mkNum acc k
    | .anonymous => acc

def mentions (n : Name) : Bool :=
  n.components.any fun c => match c with
    | .str _ s => (s.splitOn root).length > 1
    | _ => false

partial def norm (env : Environment) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls =>
      if (Match.Extension.getMatcherInfo? env n).isSome then
        match env.find? n with
        | some c =>
          let h := hash (norm env c.type, (c.value?.map (norm env)).getD (.bvar 0))
          some (.const (Name.mkSimple s!"matcher_{h}") ls)
        | none => some (.const (rename n) ls)
      else some (.const (rename n) ls)
    | .proj s i b => some (.proj (rename s) i (norm env b))
    | _ => none

#eval show CoreM Unit from do
  let env ← getEnv
  let mut lines : Array String := #[]
  for (n, c) in env.constants.toList do
    if mentions n && (Match.Extension.getMatcherInfo? env n).isNone then
      let v := match c.value? with
        | some v => toString (hash (norm env v))
        | none => "-"
      lines := lines.push s!"{rename n} {hash (norm env c.type)} {v}"
  IO.FS.writeFile "consts.txt" (String.intercalate "\n" (lines.qsort (· < ·)).toList ++ "\n")
