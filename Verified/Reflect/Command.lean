import Verified.Correct
import Verified.Reflect.Lemmas
import LeanExe.Encoding.RoundTrip

/-! The reflector.  `verified_compile p := [f, g, …]` reads the listed Lean definitions, writes
each as a source function, and proves its equation `denote (reflect f) = f` from the lemmas of
`Verified.Reflect.Lemmas`, composed term by term.  It adds the program `p.program`, the module
`p.module := compile p.prog`, in which the `k`-th definition is function `2 + k`, and for each
definition `f` the source function `p.f.func`, the equation `p.f.denote_eq`, and the theorem
`p.f.implements` that the module computes `f`.  `p.bytes` states that the module's bytes decode
to a module that computes every listed definition.

The reflector is meta code and is not trusted: Lean's kernel checks every equation it builds.  A
definition's parameters and result are `UInt64` or `Bool`.  Its body may use literals and other
closed terms, its parameters, `let`, the word operations `+`, `-`, `*`, `/`, `%`, `&&&`, `|||`,
`^^^`, `<<<`, and `>>>`, the comparisons `==`, `!=`, `<`, `≤`, `>`, `≥`, `=`, and `≠` as
`Bool` values, `!`, `&&`, and `||`, and `if` on a `Bool` or on a comparison. -/

namespace Verified.Reflect

open Lean Meta Elab Command Term

def tyOf (type : Lean.Expr) : MetaM Ty := do
  let type ← whnfR type
  if type.isConstOf ``UInt64 then return .word
  if type.isConstOf ``Bool then return .bool
  throwError "verified_compile: the type {type} is neither UInt64 nor Bool"

def tyExpr : Ty → Lean.Expr
  | .word => mkConst ``Ty.word
  | .bool => mkConst ``Ty.bool

def listExpr (α : Lean.Expr) : List Lean.Expr → Lean.Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) α
  | x :: xs => mkApp3 (mkConst ``List.cons [Level.zero]) α x (listExpr α xs)

def ctxExpr (Γ : List Ty) : Lean.Expr := listExpr (mkConst ``Ty) (Γ.map tyExpr)

def sigExpr (params : List Ty) (result : Ty) : Lean.Expr :=
  mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkApp (mkConst ``List [Level.zero])
    (mkConst ``Ty)) (mkConst ``Ty) (ctxExpr params) (tyExpr result)

/-- The functions an expression may call, the Lean functions they mean, the variables in scope
with their types, variable 0 first, and the environment of their values. -/
structure Ctx where
  sigs : Lean.Expr
  funs : Lean.Expr
  vars : List (Lean.Expr × Ty)
  env : Lean.Expr

def Ctx.ctx (c : Ctx) : Lean.Expr := ctxExpr (c.vars.map (·.2))

/-- `Expr.denote funs e env`. -/
def denoteExpr (c : Ctx) (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``Expr.denote #[c.funs, e, c.env]

/-- The proof by `rfl` that `e` means `lean`. -/
def rflProof (c : Ctx) (e lean : Lean.Expr) : MetaM Lean.Expr := do
  mkExpectedTypeHint (← mkEqRefl lean) (← mkEq (← denoteExpr c e) lean)

def binOp? : Name → Option Lean.Expr
  | ``HAdd.hAdd => some (mkConst ``BinOp.add)
  | ``HSub.hSub => some (mkConst ``BinOp.sub)
  | ``HMul.hMul => some (mkConst ``BinOp.mul)
  | ``HDiv.hDiv => some (mkConst ``BinOp.div)
  | ``HMod.hMod => some (mkConst ``BinOp.rem)
  | ``HAnd.hAnd => some (mkConst ``BinOp.and)
  | ``HOr.hOr => some (mkConst ``BinOp.or)
  | ``HXor.hXor => some (mkConst ``BinOp.xor)
  | ``HShiftLeft.hShiftLeft => some (mkConst ``BinOp.shl)
  | ``HShiftRight.hShiftRight => some (mkConst ``BinOp.shr)
  | _ => none

/-- A comparison of words as a `Prop`: its operation and its operands, with `>` and `≥` as `<`
and `≤` on swapped operands. -/
def comparison? (p : Lean.Expr) : MetaM (Option (CmpOp × Lean.Expr × Lean.Expr)) := do
  let p := p.consumeMData
  let isWord (α : Lean.Expr) : MetaM Bool := return (← whnfR α).isConstOf ``UInt64
  match p.getAppFnArgs with
  | (``LT.lt, #[α, _, a, b]) => if ← isWord α then return some (.lt, a, b) else return none
  | (``LE.le, #[α, _, a, b]) => if ← isWord α then return some (.le, a, b) else return none
  | (``GT.gt, #[α, _, a, b]) => if ← isWord α then return some (.lt, b, a) else return none
  | (``GE.ge, #[α, _, a, b]) => if ← isWord α then return some (.le, b, a) else return none
  | (``Eq, #[α, a, b]) => if ← isWord α then return some (.eq, a, b) else return none
  | (``Ne, #[α, a, b]) => if ← isWord α then return some (.ne, a, b) else return none
  | _ => return none

def cmpExpr : CmpOp → Lean.Expr
  | .eq => mkConst ``CmpOp.eq
  | .ne => mkConst ``CmpOp.ne
  | .lt => mkConst ``CmpOp.lt
  | .le => mkConst ``CmpOp.le

def iteLemma : CmpOp → Name
  | .eq => ``ite_eqP_eq
  | .ne => ``ite_ne_eq
  | .lt => ``ite_lt_eq
  | .le => ``ite_le_eq

/-- The source expression for the Lean term `e`, with the proof that it means `e`, and its
type. -/
partial def reflect (c : Ctx) (e : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Ty) := do
  let e := e.consumeMData.headBeta
  if e.isFVar then
    let some i := c.vars.findIdx? (·.1 == e)
      | throwError "verified_compile: {e} is not a variable in scope"
    let some (_, t) := c.vars[i]? | throwError "verified_compile: variable index {i}"
    let proof ← mkEqRefl (mkApp (mkConst ``Option.some [Level.zero]) (mkConst ``Ty) |>.app
      (tyExpr t))
    let x ← mkAppOptM ``Var.ofIndex #[some (tyExpr t), some c.ctx, some (toExpr i), some proof]
    let src ← mkAppOptM ``Expr.var #[some c.sigs, some c.ctx, some (tyExpr t), some x]
    return (src, ← rflProof c src e, t)
  if !e.hasFVar && !e.hasLooseBVars then
    let t ← tyOf (← inferType e)
    let src ← match t with
      | .word => mkAppOptM ``Expr.word #[some c.sigs, some c.ctx, some e]
      | .bool => mkAppOptM ``Expr.bool #[some c.sigs, some c.ctx, some e]
    return (src, ← rflProof c src e, t)
  if let .letE _ type value body _ := e then
    let s ← tyOf type
    let (vs, hv, _) ← reflect c value
    return ← withLocalDeclD `x type fun x => do
      let env' ← mkAppOptM ``Env.cons #[some c.ctx, some (tyExpr s), some x, some c.env]
      let c' : Ctx := { c with vars := (x, s) :: c.vars, env := env' }
      let (bs, hb, t) ← reflect c' (body.instantiate1 x)
      let hb ← mkLambdaFVars #[x] hb
      let src ← mkAppM ``Expr.letE #[vs, bs]
      return (src, ← mkAppM ``letE_eq #[hv, hb], t)
  let (fn, args) := e.getAppFnArgs
  if let some op := binOp? fn then
    if args.size == 6 then
      let (ls, hl, _) ← reflect c args[4]!
      let (rs, hr, _) ← reflect c args[5]!
      return (← mkAppM ``Expr.bin #[op, ls, rs], ← mkAppM ``bin_eq #[op, hl, hr], .word)
  match fn, args with
  | ``Decidable.decide, #[p, _] =>
    let some (op, a, b) ← comparison? p
      | throwError "verified_compile: unsupported decision {p}"
    reflectCmp op a b
  | ``BEq.beq, #[_, _, a, b] => reflectCmp .eq a b
  | ``bne, #[_, _, a, b] => reflectCmp .ne a b
  | ``not, #[a] =>
    let (s, h, _) ← reflect c a
    return (← mkAppM ``Expr.not #[s], ← mkAppM ``not_eq #[h], .bool)
  | ``and, #[a, b] =>
    let (ls, hl, _) ← reflect c a
    let (rs, hr, _) ← reflect c b
    return (← mkAppM ``Expr.and #[ls, rs], ← mkAppM ``and_eq #[hl, hr], .bool)
  | ``or, #[a, b] =>
    let (ls, hl, _) ← reflect c a
    let (rs, hr, _) ← reflect c b
    return (← mkAppM ``Expr.or #[ls, rs], ← mkAppM ``or_eq #[hl, hr], .bool)
  | ``ite, #[_, p, _, a, b] =>
    let (as, ha, t) ← reflect c a
    let (bs, hb, _) ← reflect c b
    match (p.consumeMData).getAppFnArgs with
    | (``Eq, #[α, cond, tru]) =>
      if (← whnfR α).isConstOf ``Bool && tru.isConstOf ``Bool.true then
        let (cs, hc, _) ← reflect c cond
        return (← mkAppM ``Expr.ite #[cs, as, bs], ← mkAppM ``ite_eq #[hc, ha, hb], t)
    | _ => pure ()
    let some (op, l, r) ← comparison? p
      | throwError "verified_compile: unsupported condition {p}"
    let (ls, hl, _) ← reflect c l
    let (rs, hr, _) ← reflect c r
    let cond ← mkAppM ``Expr.cmp #[cmpExpr op, ls, rs]
    return (← mkAppM ``Expr.ite #[cond, as, bs], ← mkAppM (iteLemma op) #[hl, hr, ha, hb], t)
  | _, _ => throwError "verified_compile: unsupported term {e}"
where
  reflectCmp (op : CmpOp) (a b : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Ty) := do
    let (ls, hl, _) ← reflect c a
    let (rs, hr, _) ← reflect c b
    return (← mkAppM ``Expr.cmp #[cmpExpr op, ls, rs], ← mkAppM ``cmp_eq #[cmpExpr op, hl, hr],
      .bool)

/-- `Env.cons v₀ (… (Env.cons vₙ Env.nil))` for the variables `vars`. -/
def envExpr : List (Lean.Expr × Ty) → MetaM Lean.Expr
  | [] => return mkConst ``Env.nil
  | (x, t) :: rest => do
    mkAppOptM ``Env.cons
      #[some (ctxExpr (rest.map (·.2))), some (tyExpr t), some x, some (← envExpr rest)]

/-- What the reflector learns from one definition. -/
structure Reflected where
  name : Name
  params : List Ty
  result : Ty
  deriving Inhabited

def addDefinition (name : Name) (type value : Lean.Expr) : CoreM Unit :=
  addAndCompile <| .defnDecl <|
    mkDefinitionValEx name [] type value (.regular 1) .safe [name]

def addTheorem (name : Name) (type value : Lean.Expr) : CoreM Unit :=
  addDecl <| .thmDecl { name, levelParams := [], type, value }

/-- Reflects definition `name` as a function that may call the functions `sigs`, meaning
`funs`, and adds `base.func` and `base.denote_eq`. -/
def reflectDefinition (base name : Name) (sigs funs : Lean.Expr) : MetaM Reflected := do
  let info ← getConstInfoDefn name
  unless info.levelParams.isEmpty do
    throwError "verified_compile: {name} has universe parameters"
  lambdaTelescope (← instantiateMVars info.value) fun params body => do
    let types ← params.toList.mapM fun p => do tyOf (← inferType p)
    let result ← tyOf (← inferType body)
    let vars := params.toList.zip types
    let env ← envExpr vars
    let (src, proof, _) ← reflect ⟨sigs, funs, vars, env⟩ body
    let funcType := mkApp (mkConst ``Func) sigs
    let func ← mkAppOptM ``Func.mk #[some sigs, some (toExpr name.getString!),
      some (ctxExpr types), some (tyExpr result), some src]
    addDefinition (base ++ `func) funcType func
    let lhs ← mkAppM ``Func.denote #[mkConst (base ++ `func), funs, env]
    let eqType ← mkForallFVars params (← mkEq lhs (mkAppN (mkConst name) params))
    addTheorem (base ++ `denote_eq) eqType (← mkLambdaFVars params proof)
    return ⟨name, types, result⟩

def tyStx : Ty → CommandElabM Term
  | .word => `(UInt64)
  | .bool => `(Bool)

/-- The argument type of a definition: its parameter types as a right-nested product, or `Unit`
for none. -/
def argType : List Ty → CommandElabM Term
  | [] => `(Unit)
  | [t] => tyStx t
  | t :: ts => do `($(← tyStx t) × $(← argType ts))

/-- The components of `x : argType params`, in order. -/
def argProjs (x : Term) : Nat → CommandElabM (List Term)
  | 0 => return []
  | 1 => return [x]
  | n + 2 => do return (← `($x.1)) :: (← argProjs (← `($x.2)) (n + 1))

def envStx : List Term → CommandElabM Term
  | [] => `(Verified.Env.nil)
  | x :: xs => do `(Verified.Env.cons $x $(← envStx xs))

/-- `FVar.there (… (FVar.there FVar.here))` with `k` applications of `there`. -/
def fvarStx : Nat → CommandElabM Term
  | 0 => `(Verified.FVar.here)
  | k + 1 => do `(Verified.FVar.there $(← fvarStx k))

syntax (name := verifiedCompile) "verified_compile " ident " := " "[" ident,* "]" : command

@[command_elab verifiedCompile]
def elabVerifiedCompile : CommandElab
  | `(verified_compile $target := [$sources,*]) => do
    let names ← sources.getElems.mapM fun s => liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
    let base := (← getCurrNamespace) ++ target.getId
    let reflected ← liftTermElabM do
      let mut sigs : List (List Ty × Ty) := []
      let mut prog := Lean.mkConst ``Prog.nil
      let mut out : Array Reflected := #[]
      for name in names do
        let sigsExpr := listExpr (Lean.mkConst ``Sig) (sigs.map fun (p, r) => sigExpr p r)
        let funs ← mkAppM ``Prog.funs #[prog]
        let r ← reflectDefinition (base ++ Name.mkSimple name.getString!) name sigsExpr funs
        prog ← mkAppM ``Prog.cons #[Lean.mkConst (base ++ Name.mkSimple name.getString! ++ `func),
          prog]
        sigs := (r.params, r.result) :: sigs
        out := out.push r
      let sigsExpr := listExpr (Lean.mkConst ``Sig) (sigs.map fun (p, r) => sigExpr p r)
      addDefinition (base ++ `program) (mkApp (Lean.mkConst ``Prog) sigsExpr) prog
      addDefinition (base ++ `module) (Lean.mkConst ``Wasm.Module)
        (← mkAppM ``compile #[Lean.mkConst (base ++ `program)])
      return out
    let progId := mkIdent (base ++ `program)
    let moduleId := mkIdent (base ++ `module)
    let n := reflected.size
    let mut claims : Array Term := #[]
    let mut proofs : Array Term := #[]
    for k in [0:n] do
      let r := reflected[k]!
      let simple := Name.mkSimple r.name.getString!
      let fnId := mkIdent r.name
      let implId := mkIdent (target.getId ++ simple ++ `implements)
      let eqId := mkIdent (base ++ simple ++ `denote_eq)
      let x := mkIdent `x
      let α ← argType r.params
      let projs ← argProjs x r.params.length
      let fvar ← fvarStx (n - 1 - k)
      let index := Syntax.mkNumLit (toString (2 + k))
      let lean ← `(fun ($x : $α) => $fnId $(projs.toArray)*)
      let envFn ← `(fun ($x : $α) => $(← envStx projs))
      elabCommand (← `(theorem $implId :
          LeanExe.Pipeline.ImplementsPureA false $moduleId $index $lean := by
          have h := (Verified.Prog.correct $progId $fvar).1
          have hComp : Verified.Funs.get (Verified.Prog.funs $progId) $fvar ∘ $envFn = $lean := by
            funext $x
            exact $eqId $(projs.toArray)*
          rw [← hComp]
          exact Verified.ImplementsPureA.comap h _ fun _ => rfl))
      claims := claims.push
        (← `(LeanExe.Pipeline.ImplementsPureA false $(mkIdent `m) $index $lean))
      proofs := proofs.push implId
    let bytesId := mkIdent (target.getId ++ `bytes)
    let m := mkIdent `m
    let conj ← claims.pop.foldrM (fun c acc => `($c ∧ $acc)) claims.back!
    let impls ← proofs.pop.foldrM (fun p acc => `(⟨$p, $acc⟩)) proofs.back!
    elabCommand (← `(theorem $bytesId : ∃ bytes, Wasm.Encoding.encode $moduleId = .ok bytes ∧
        ∃ $m:ident, Wasm.Encoding.decode bytes = .ok $m ∧ $conj := by
      obtain ⟨bytes, success, decoded⟩ :=
        Wasm.Encoding.round_trip $moduleId (by decide) (by decide +kernel)
      exact ⟨bytes, success, $moduleId, decoded, $impls⟩))
  | _ => throwUnsupportedSyntax

end Verified.Reflect
