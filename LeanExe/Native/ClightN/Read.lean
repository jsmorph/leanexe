import Lean

/-!
The Lean half of the read-back that `clightn/check.sh` compares with the neutral specification
(`clightn/README.md`).  `dump` writes to the file that the environment variable `CLIGHTN_OUT`
names one S-expression per line, with every argument explicit and the full name of every
constant:

* `(relation R TYPE (ctors C ...) safe)` for each inductive type `R` directly in the namespace
  `ClightN.Spec`, and `(ctor C TYPE)` for each of its constructors;
* `(equation E VALUE TYPE)` for each definition `E` there whose name starts with `eqn_`;
* `(constant C VALUE TYPE)` for each definition `C` there whose name starts with `cst_`;
* `(statement S VALUE TYPE)` for each definition `S` there whose name starts with `stmt_`, and
  `(proof P TYPE (axioms A ...))` for the theorem `P` of the same name without `stmt_` in the
  namespace `ClightN.Proof`, or `(no-proof P)` or `(not-theorem P)`;
* `(other D)` for each other declaration directly in `ClightN.Spec`.

A bound variable prints as `v<k>`, where `k` is its depth, a product whose variable the body
does not use prints as `(-> A B)`, and a string literal prints in double quotes.
-/

namespace ClightN.Read

open Lean Elab Command

partial def sx (ctx : Array String) (e : Expr) : Except String String :=
  match e with
  | .bvar i =>
      if i < ctx.size then pure ctx[ctx.size - 1 - i]! else throw "loose bound variable"
  | .const n _ => pure n.toString
  | .sort .zero => pure "Prop"
  | .sort _ => throw "a sort other than Prop"
  | .lit (.natVal k) => pure s!"(lit {k})"
  | .lit (.strVal s) =>
      if s.all fun c => c.isAlphanum || c == '_' then pure s!"\"{s}\""
      else throw s!"a string with characters outside the language: {s}"
  | .mdata _ b => sx ctx b
  | .app .. => do
      let fs ← sx ctx e.getAppFn
      let as ← e.getAppArgs.mapM (sx ctx)
      pure ("(" ++ " ".intercalate (fs :: as.toList) ++ ")")
  | .forallE _ t b _ => do
      let ts ← sx ctx t
      if b.hasLooseBVar 0 then
        let x := s!"v{ctx.size}"
        pure s!"(forall (({x} {ts})) {← sx (ctx.push x) b})"
      else
        pure s!"(-> {ts} {← sx (ctx.push "_") b})"
  | .lam _ t b _ => do
      let x := s!"v{ctx.size}"
      pure s!"(fun (({x} {← sx ctx t})) {← sx (ctx.push x) b})"
  | e => throw s!"unexpected term {e}"

def term (e : Expr) : CommandElabM String :=
  match sx #[] e with
  | .ok s => pure s
  | .error msg => throwError "read: {msg}"

def dump : CommandElabM Unit := do
  let some path ← IO.getEnv "CLIGHTN_OUT" | throwError "read: CLIGHTN_OUT is not set"
  let env ← getEnv
  let spec := `ClightN.Spec
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    if n.getPrefix == spec && !n.isInternal then acc.push n else acc
  let mut lines : Array String := #[]
  for n in names.qsort (fun a b => a.toString < b.toString) do
    match env.find? n with
    | some (.inductInfo ii) =>
        let ctors := " ".intercalate (ii.ctors.map toString)
        let safe := if ii.isUnsafe then "unsafe" else "safe"
        lines := lines.push s!"(relation {n} {← term ii.type} (ctors {ctors}) {safe})"
        for c in ii.ctors do
          let some ci := env.find? c | throwError "read: no constructor {c}"
          lines := lines.push s!"(ctor {c} {← term ci.type})"
    | some (.defnInfo di) =>
        match n with
        | .str _ s =>
            if s.startsWith "eqn_" then
              lines := lines.push s!"(equation {n} {← term di.value} {← term di.type})"
            else if s.startsWith "cst_" then
              lines := lines.push s!"(constant {n} {← term di.value} {← term di.type})"
            else if s.startsWith "stmt_" then
              lines := lines.push s!"(statement {n} {← term di.value} {← term di.type})"
              let p := `ClightN.Proof ++ Name.mkSimple (s.drop 5).toString
              match env.find? p with
              | some (.thmInfo ti) =>
                  let axs := " ".intercalate ((← collectAxioms p).toList.map toString)
                  lines := lines.push s!"(proof {p} {← term ti.type} (axioms {axs}))"
              | some _ => lines := lines.push s!"(not-theorem {p})"
              | none => lines := lines.push s!"(no-proof {p})"
            else
              lines := lines.push s!"(other {n})"
        | _ => lines := lines.push s!"(other {n})"
    | _ => lines := lines.push s!"(other {n})"
  IO.FS.writeFile path ("\n".intercalate lines.toList ++ "\n")

end ClightN.Read
