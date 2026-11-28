module

public import Demos.Scheme.Semantics.Expand
public import Demos.Scheme.Semantics.Read

@[expose] public section

/-! The source machine of the reference semantics: values, stores, continuation frames, and one
deterministic step function whose clauses are the rules.

Values follow the domains of §7.2.2.  A pair denotes two locations and a mutability flag
(Ep = L × L × T), and a vector or a string denotes the locations of its elements with the flag
(Ev, Es).  A vector and a string also carry an identity location, since §6.2 leaves `eqv?` of two
empty vectors or strings unspecified and the profile makes every vector and string a distinct
object.  A procedure carries the identity location of §7.2's F = L × (E* → K → C) and its
behavior: a closure, a standard procedure, or an escape procedure that holds a continuation.

A store is a list of values, and a location is in use exactly when it is below the list's length,
so the allocator `alloc` meets §7.2's axiom for `new`.  An environment maps variables to
locations, and the top-level environment maps symbols to locations (§5.2.1).  A continuation is a
list of frames, each of which records the pending work of one rule with the values it holds, and
no rule changes a frame, so an escape procedure that holds a continuation resumes the work as it
was when `call-with-current-continuation` captured it.

The rules evaluate an operator before its operands and the operands from left to right (§4.1.3),
bind fresh locations for a call's arguments and fresh pairs for a rest list (§4.1.4), and pass a
call in tail position, the last expression of a body, and an arm of `if` the continuation of their
context. -/

namespace Demos.Scheme.Semantics

open Numeric

/-- Locations (§7.2.2's L). -/
abbrev Loc := Nat

mutual

/-- Values (§7.2.2's expressed values E). -/
inductive Val where
  | bool (b : Bool)
  | int (n : Int)
  | char (c : UInt8)
  | sym (s : Sym)
  | nil
  | unspecified
  | undefined
  | pair (car cdr : Loc) (mutable : Bool)
  | vec (tag : Loc) (elems : List Loc) (mutable : Bool)
  | str (tag : Loc) (chars : List Loc) (mutable : Bool)
  | proc (tag : Loc) (p : Proc)

/-- The behavior of a procedure. -/
inductive Proc where
  | closure (fixed : List Var) (rest : Option Var) (body : List Expr) (last : Expr)
      (env : List (Var × Loc))
  | prim (p : Prim)
  | escape (k : List Frame)

/-- The frames of a continuation. -/
inductive Frame where
  /-- The operator of a call is under evaluation. -/
  | fn (args : List Expr) (env : List (Var × Loc))
  /-- An operand is under evaluation, after the operator `f` and the operands `done`. -/
  | arg (f : Val) (done : List Val) (rest : List Expr) (env : List (Var × Loc))
  /-- The test of an `if` is under evaluation. -/
  | branch (t e : Expr) (env : List (Var × Loc))
  /-- A command of a body is under evaluation. -/
  | seq (cmds : List Expr) (last : Expr) (env : List (Var × Loc))
  /-- The expression of a `set!` is under evaluation. -/
  | assign (x : Var) (env : List (Var × Loc))
  /-- The expression of a top-level definition is under evaluation. -/
  | define (x : Sym)
  /-- The rest of the program: the forms of the current datum and the expanded later data. -/
  | top (pending : List TopForm) (rest : List (Except SyntaxError (List TopForm)))
  /-- A call of `map`'s procedure is under evaluation, with the remaining lists and the earlier
  results. -/
  | map (f : Val) (lists : List Val) (done : List Val)
  /-- A call of `for-each`'s procedure is under evaluation, with the remaining lists. -/
  | forEach (f : Val) (lists : List Val)

end

instance : Inhabited Val := ⟨.unspecified⟩

/-- Environments (§7.2.2's U). -/
abbrev Env := List (Var × Loc)

/-- A store and the top-level environment. -/
structure State where
  store : List Val
  globals : List (Sym × Loc)

/-- The errors that the rules signal. -/
inductive RunError where
  | unbound (s : Sym)
  | undefinedVariable
  | notProcedure
  | arity
  | wrongType
  | immutable
  | divideByZero
  | index
  deriving DecidableEq, Repr

/-- The faults that end a run. -/
inductive Fault where
  | read (e : ReadError) (pos : Nat)
  | syntax (e : SyntaxError)
  | error (e : RunError)
  | restriction (r : Restriction)
  deriving DecidableEq, Repr

/-- The configurations of the machine. -/
inductive Config where
  | eval (e : Expr) (env : Env) (k : List Frame) (s : State)
  | apply (f : Val) (args : List Val) (k : List Frame) (s : State)
  | ret (v : Val) (k : List Frame) (s : State)
  | halt (v : Val) (s : State)
  | fault (f : Fault)

namespace State

/-- The value at a location. -/
def read (s : State) (l : Loc) : Val := s.store.getD l .undefined

def write (s : State) (l : Loc) (v : Val) : State := { s with store := s.store.set l v }

/-- A fresh location holding `v` (§7.2's `new` and `update`). -/
def alloc (s : State) (v : Val) : Loc × State := (s.store.length, { s with store := s.store ++ [v] })

/-- Fresh locations holding the values, in order. -/
def allocAll (s : State) : List Val → List Loc × State
  | [] => ([], s)
  | v :: vs =>
    let (l, s) := s.alloc v
    let (ls, s) := s.allocAll vs
    (l :: ls, s)

/-- The location of a top-level variable. -/
def global (s : State) (x : Sym) : Option Loc := s.globals.lookup x

/-- A fresh pair (§7.2's `cons`). -/
def cons (s : State) (a d : Val) (m : Bool) : Val × State :=
  let (la, s) := s.alloc a
  let (ld, s) := s.alloc d
  (.pair la ld m, s)

/-- A list of fresh mutable pairs with the values and the tail `t`. -/
def listTail (s : State) : List Val → Val → Val × State
  | [], t => (t, s)
  | v :: vs, t =>
    let (r, s) := s.listTail vs t
    s.cons v r true

/-- A proper list of fresh mutable pairs with the values. -/
def list (s : State) (vs : List Val) : Val × State := s.listTail vs .nil

/-- The elements of a proper list, with at most `fuel` pairs. -/
def elemsAux (s : State) : Nat → Val → Option (List Val)
  | _, .nil => some []
  | fuel + 1, .pair a d _ => (s.elemsAux fuel (s.read d)).map (s.read a :: ·)
  | _, _ => none

/-- The elements of a proper list, or `none` for any other value, a circular list included. -/
def elems? (s : State) (v : Val) : Option (List Val) := s.elemsAux (s.store.length + 1) v

/-- The pairs of a proper list, first first. -/
def pairsAux (s : State) : Nat → Val → Option (List Val)
  | _, .nil => some []
  | fuel + 1, p@(.pair _ d _) => (s.pairsAux fuel (s.read d)).map (p :: ·)
  | _, _ => none

def pairs? (s : State) (v : Val) : Option (List Val) := s.pairsAux (s.store.length + 1) v

mutual

/-- The object of a datum in fresh locations, with the mutability flag `m`. -/
def ofDatum (s : State) (m : Bool) : Datum → Val × State
  | .bool b => (.bool b, s)
  | .int n => (.int n, s)
  | .char c => (.char c, s)
  | .sym x => (.sym x, s)
  | .nil => (.nil, s)
  | .str cs =>
    let (tag, s) := s.alloc .unspecified
    let (ls, s) := s.allocAll (cs.map Val.char)
    (.str tag ls m, s)
  | .pair a d =>
    let (va, s) := s.ofDatum m a
    let (vd, s) := s.ofDatum m d
    s.cons va vd m
  | .vec elems =>
    let (tag, s) := s.alloc .unspecified
    let (ls, s) := s.ofElems m elems
    (.vec tag ls m, s)

/-- The locations of the objects of a vector's elements. -/
def ofElems (s : State) (m : Bool) : Datum → List Loc × State
  | .pair a d =>
    let (v, s) := s.ofDatum m a
    let (l, s) := s.alloc v
    let (ls, s) := s.ofElems m d
    (l :: ls, s)
  | _ => ([], s)

end

end State

mutual

/-- The expression with each compound literal replaced by the location of its object, which the
store holds immutable (§3.5, §4.1.2).  The literal then denotes one object at every evaluation. -/
def allocExpr (s : State) : Expr → Expr × State
  | .const (.datum d) =>
    if d.compound then
      let (v, s) := s.ofDatum false d
      let (l, s) := s.alloc v
      (.const (.lit l), s)
    else (.const (.datum d), s)
  | .const k => (.const k, s)
  | .var x => (.var x, s)
  | .app f args =>
    let (f, s) := allocExpr s f
    let (args, s) := allocExprs s args
    (.app f args, s)
  | .lam fs r body last =>
    let (body, s) := allocExprs s body
    let (last, s) := allocExpr s last
    (.lam fs r body last, s)
  | .ite c t e =>
    let (c, s) := allocExpr s c
    let (t, s) := allocExpr s t
    let (e, s) := allocExpr s e
    (.ite c t e, s)
  | .set x e =>
    let (e, s) := allocExpr s e
    (.set x e, s)

def allocExprs (s : State) : List Expr → List Expr × State
  | [] => ([], s)
  | e :: es =>
    let (e, s) := allocExpr s e
    let (es, s) := allocExprs s es
    (e :: es, s)

end

def allocTops (s : State) : List TopForm → List TopForm × State
  | [] => ([], s)
  | .expr e :: fs =>
    let (e, s) := allocExpr s e
    let (fs, s) := allocTops s fs
    (.expr e :: fs, s)
  | .define x e :: fs =>
    let (e, s) := allocExpr s e
    let (fs, s) := allocTops s fs
    (.define x e :: fs, s)

/-- The identity location of a standard procedure: the position of its first name in
`primNames`. -/
def primTag (p : Prim) : Loc := (primNames.findIdx? (·.2 == p)).getD 0

/-- The value of a standard procedure. -/
def primVal (p : Prim) : Val := .proc (primTag p) (.prim p)

/-- The initial state: the identity locations of the standard procedures, then the location of
each name of `primNames`, which holds its procedure. -/
def initState : State :=
  let n := primNames.length
  { store := List.replicate n .unspecified ++ primNames.map (fun (_, p) => primVal p)
    globals := (List.range n).zip primNames |>.map fun (i, (name, _)) => (name, n + i) }

def isFalse : Val → Bool
  | .bool false => true
  | _ => false

def isProc : Val → Bool
  | .proc .. => true
  | _ => false

def isPairVal : Val → Bool
  | .pair .. => true
  | _ => false

def isNilVal : Val → Bool
  | .nil => true
  | _ => false

/-- `eqv?` (§6.2, §7.2's `eqv`): atoms by value, pairs by their two locations, and vectors,
strings, and procedures by their identity locations. -/
def eqv : Val → Val → Bool
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .char a, .char b => a == b
  | .sym a, .sym b => a == b
  | .nil, .nil | .unspecified, .unspecified | .undefined, .undefined => true
  | .pair a d _, .pair a' d' _ => a == a' && d == d'
  | .vec t _ _, .vec t' _ _ | .str t _ _, .str t' _ _ | .proc t _, .proc t' _ => t == t'
  | _, _ => false

/-- An exact integer result under the profile's restriction (§6.5.3). -/
def numResult (P : Profile) (n : Int) : Except Fault Val :=
  if P.representable n then .ok (.int n) else .error (.restriction .range)

/-- The numeric layer applied to values: a type predicate accepts any object, and every other
procedure requires numbers. -/
def applyNumeric (P : Profile) (op : Op) (args : List Val) : Except Fault Val :=
  if op.isPredicate then
    match args with
    | [.int _] => .ok (.bool true)
    | _ => .ok (.bool false)
  else
    let ints := args.filterMap fun | .int n => some n | _ => none
    if ints.length != args.length then .error (.error .wrongType)
    else match eval op ints with
      | .int n => numResult P n
      | .bool b => .ok (.bool b)
      | .divideByZero => .error (.error .divideByZero)
      | .notInteger => .error (.restriction .notInteger)
      | .arity => .error (.error .arity)

/-- The value after the operations of a `c…r` path. -/
def cxrWalk (s : State) : List Bool → Val → Except Fault Val
  | [], v => .ok v
  | b :: bs, .pair a d _ => cxrWalk s bs (s.read (if b then a else d))
  | _ :: _, _ => .error (.error .wrongType)

/-- The first pair of `ps` whose car meets `test`, or `#f`. -/
def memFind (s : State) (test : Val → Bool) : List Val → Val
  | [] => .bool false
  | p@(.pair a _ _) :: ps => if test (s.read a) then p else memFind s test ps
  | _ :: ps => memFind s test ps

/-- The first element of an association list whose car meets `test`, or `#f`. -/
def assFind (s : State) (test : Val → Bool) : List Val → Val
  | [] => .bool false
  | p@(.pair a _ _) :: ps => if test (s.read a) then p else assFind s test ps
  | _ :: ps => assFind s test ps

/-- A standard procedure other than `apply`, `map`, `for-each`, and
`call-with-current-continuation`, applied to arguments that meet its arity (§6). -/
def applySimple (P : Profile) (p : Prim) (args : List Val) (s : State) :
    Except Fault (Val × State) :=
  let pure (v : Val) : Except Fault (Val × State) := .ok (v, s)
  let wrong : Except Fault (Val × State) := .error (.error .wrongType)
  match p, args with
  | .not, [v] => pure (.bool (isFalse v))
  | .isBoolean, [v] => pure (.bool (match v with | .bool _ => true | _ => false))
  | .eq, [a, b] | .eqv, [a, b] => pure (.bool (eqv a b))
  | .isPair, [v] => pure (.bool (isPairVal v))
  | .cons, [a, b] => .ok (s.cons a b true)
  | .car, [.pair a _ _] => pure (s.read a)
  | .cdr, [.pair _ d _] => pure (s.read d)
  | .setCar, [.pair a _ m, v] => if m then .ok (.unspecified, s.write a v) else
      .error (.error .immutable)
  | .setCdr, [.pair _ d m, v] => if m then .ok (.unspecified, s.write d v) else
      .error (.error .immutable)
  | .cxr path, [v] => (cxrWalk s path v).map (·, s)
  | .isNull, [v] => pure (.bool (isNilVal v))
  | .isList, [v] => pure (.bool (s.elems? v).isSome)
  | .list, vs => .ok (s.list vs)
  | .length, [v] =>
    match s.elems? v with
    | some xs => (numResult P xs.length).map (·, s)
    | none => wrong
  | .append, vs =>
    match vs.reverse with
    | [] => pure .nil
    | last :: firstsRev =>
      match firstsRev.reverse.mapM s.elems? with
      | some xss => .ok (s.listTail xss.flatten last)
      | none => wrong
  | .reverse, [v] =>
    match s.elems? v with
    | some xs => .ok (s.list xs.reverse)
    | none => wrong
  | .listRef, [v, .int k] =>
    match s.elems? v with
    | some xs => if 0 ≤ k ∧ k < xs.length then pure (xs.getD k.toNat .undefined)
        else .error (.error .index)
    | none => wrong
  | .memq, [x, v] | .memv, [x, v] =>
    match s.pairs? v with
    | some ps => pure (memFind s (eqv x) ps)
    | none => wrong
  | .assq, [x, v] | .assv, [x, v] =>
    match s.elems? v with
    | some ps => if ps.all isPairVal then pure (assFind s (eqv x) ps) else wrong
    | none => wrong
  | .num op, vs => (applyNumeric P op vs).map (·, s)
  | .isProcedure, [v] => pure (.bool (isProc v))
  | .isVector, [v] => pure (.bool (match v with | .vec .. => true | _ => false))
  | .listToVector, [v] =>
    match s.elems? v with
    | some xs =>
      let (tag, s) := s.alloc .unspecified
      let (ls, s) := s.allocAll xs
      .ok (.vec tag ls true, s)
    | none => wrong
  | _, _ => wrong

/-- The location of a variable: its binding in the environment, or else its top-level
binding (§3.1). -/
def varLoc (ρ : Env) (s : State) (x : Var) : Option Loc :=
  match ρ.lookup x with
  | some l => some l
  | none =>
    match x with
    | .id y => s.global y
    | .temp _ => none

def unboundError (x : Var) : Fault :=
  .error (.unbound (match x with | .id y => y | .temp _ => []))

/-- The environment of a call: the formals bound to fresh locations that hold the arguments, and
the rest variable to a fresh list of the surplus arguments (§4.1.4), or `none` when the number of
arguments does not fit the formals. -/
def bindArgs : List Var → Option Var → List Val → Env → State → Option (Env × State)
  | [], none, [], ρ, s => some (ρ, s)
  | [], some r, vs, ρ, s =>
    let (lst, s) := s.list vs
    let (l, s) := s.alloc lst
    some ((r, l) :: ρ, s)
  | x :: xs, r, v :: vs, ρ, s =>
    let (l, s) := s.alloc v
    (bindArgs xs r vs ρ s).map fun (ρ', s') => ((x, l) :: ρ', s')
  | _, _, _, _, _ => none

/-- The evaluation of a body: its commands in order, then its last expression with the body's
continuation. -/
def enterBody (body : List Expr) (last : Expr) (ρ : Env) (k : List Frame) (s : State) : Config :=
  match body with
  | [] => .eval last ρ k s
  | c :: cs => .eval c ρ (.seq cs last ρ :: k) s

def carOf (s : State) : Val → Val
  | .pair a _ _ => s.read a
  | _ => .undefined

def cdrOf (s : State) : Val → Val
  | .pair _ d _ => s.read d
  | _ => .undefined

/-- The next call of `map`'s procedure on the cars of the lists, or the list of the results when
every list has ended (§6.9).  Lists that end at different elements, or a list that ends in another
object, signal an error. -/
def mapNext (f : Val) (lists : List Val) (done : List Val) (k : List Frame) (s : State) :
    Config :=
  if lists.all isPairVal then
    .apply f (lists.map (carOf s)) (.map f (lists.map (cdrOf s)) done :: k) s
  else if lists.all isNilVal then
    let (v, s) := s.list done
    .ret v k s
  else .fault (.error .wrongType)

/-- The next call of `for-each`'s procedure, from the first elements to the last (§6.9). -/
def forEachNext (f : Val) (lists : List Val) (k : List Frame) (s : State) : Config :=
  if lists.all isPairVal then
    .apply f (lists.map (carOf s)) (.forEach f (lists.map (cdrOf s)) :: k) s
  else if lists.all isNilVal then .ret .unspecified k s
  else .fault (.error .wrongType)

/-- A call of a standard procedure whose arguments meet its arity.  `apply` calls its procedure
with the elements of its list (§6.9, §7.2's `apply`), `call-with-current-continuation` calls its
procedure with a fresh escape procedure that holds the current continuation (§6.9, §7.2's
`cwcc`), and `map` and `for-each` call their procedure on the elements in order. -/
def applyPrim (P : Profile) (p : Prim) (args : List Val) (k : List Frame) (s : State) : Config :=
  match p, args with
  | .apply, [f, lst] =>
    if !isProc f then .fault (.error .wrongType) else
    match s.elems? lst with
    | some xs => .apply f xs k s
    | none => .fault (.error .wrongType)
  | .callcc, [f] =>
    if !isProc f then .fault (.error .wrongType) else
    let (tag, s) := s.alloc .unspecified
    .apply f [.proc tag (.escape k)] k s
  | .map, f :: lists => if !isProc f then .fault (.error .wrongType) else mapNext f lists [] k s
  | .forEach, f :: lists =>
    if !isProc f then .fault (.error .wrongType) else forEachNext f lists k s
  | _, _ =>
    match applySimple P p args s with
    | .ok (v, s) => .ret v k s
    | .error f => .fault f

/-- One rule of the machine.  `halt` and `fault` are final. -/
def step (P : Profile) : Config → Config
  | .eval e ρ k s =>
    match e with
    | .const c =>
      match c with
      | .datum d =>
        let (v, s) := s.ofDatum false d
        .ret v k s
      | .lit l => .ret (s.read l) k s
      | .undefined => .ret .undefined k s
      | .unspecified => .ret .unspecified k s
      | .prim p => .ret (primVal p) k s
    | .var x =>
      match varLoc ρ s x with
      | some l =>
        match s.read l with
        | .undefined => .fault (.error .undefinedVariable)
        | v => .ret v k s
      | none => .fault (unboundError x)
    | .app f args => .eval f ρ (.fn args ρ :: k) s
    | .lam fs r body last =>
      let (tag, s) := s.alloc .unspecified
      .ret (.proc tag (.closure fs r body last ρ)) k s
    | .ite c t e => .eval c ρ (.branch t e ρ :: k) s
    | .set x e => .eval e ρ (.assign x ρ :: k) s
  | .ret v k s =>
    match k with
    | [] => .halt v s
    | .fn args ρ :: k =>
      match args with
      | [] => .apply v [] k s
      | a :: as => .eval a ρ (.arg v [] as ρ :: k) s
    | .arg f done rest ρ :: k =>
      match rest with
      | [] => .apply f (done ++ [v]) k s
      | a :: as => .eval a ρ (.arg f (done ++ [v]) as ρ :: k) s
    | .branch t e ρ :: k => if isFalse v then .eval e ρ k s else .eval t ρ k s
    | .seq cmds last ρ :: k => enterBody cmds last ρ k s
    | .assign x ρ :: k =>
      match varLoc ρ s x with
      | some l => .ret .unspecified k (s.write l v)
      | none => .fault (unboundError x)
    | .define x :: k =>
      match s.global x with
      | some l => .ret .unspecified k (s.write l v)
      | none =>
        let (l, s) := s.alloc v
        .ret .unspecified k { s with globals := (x, l) :: s.globals }
    | .top pending rest :: k =>
      match pending with
      | .expr e :: tfs => .eval e [] (.top tfs rest :: k) s
      | .define x e :: tfs => .eval e [] (.define x :: .top tfs rest :: k) s
      | [] =>
        match rest with
        | [] => .halt v s
        | .error e :: _ => .fault (.syntax e)
        | .ok tfs :: rest => .ret v (.top tfs rest :: k) s
    | .map f lists done :: k => mapNext f lists (done ++ [v]) k s
    | .forEach f lists :: k => forEachNext f lists k s
  | .apply f args k s =>
    match f with
    | .proc _ (.closure fs r body last ρ) =>
      match bindArgs fs r args ρ s with
      | some (ρ', s') => enterBody body last ρ' k s'
      | none => .fault (.error .arity)
    | .proc _ (.prim p) =>
      if p.arity.accepts args.length then applyPrim P p args k s else .fault (.error .arity)
    | .proc _ (.escape k') =>
      match args with
      | [v] => .ret v k' s
      | _ => .fault (.error .arity)
    | _ => .fault (.error .notProcedure)
  | c => c

/-- The configuration after `n` rules, or the final configuration that an earlier rule
reached. -/
def run (P : Profile) : Nat → Config → Config
  | 0, c => c
  | n + 1, c =>
    match c with
    | .halt .. | .fault .. => c
    | _ => run P n (step P c)

/-- The rules lead from `c` to `c'`. -/
def Steps (P : Profile) (c c' : Config) : Prop := ∃ n, run P n c = c'

/-- The data of a program, each expanded with its literals allocated, or its syntax error. -/
def prepare : List Datum → State → List (Except SyntaxError (List TopForm)) × State
  | [], s => ([], s)
  | d :: ds, s =>
    match expandTop d with
    | .ok tfs =>
      let (tfs, s) := allocTops s tfs
      let (rest, s) := prepare ds s
      (.ok tfs :: rest, s)
    | .error e =>
      let (rest, s) := prepare ds s
      (.error e :: rest, s)

/-- The initial configuration of the program whose bytes are `src`: the program is read whole,
and each datum's forms run in order. -/
def start (P : Profile) (src : List UInt8) : Config :=
  match readProgram P src with
  | .error (.error e pos) => .fault (.read e pos)
  | .error (.restriction r) => .fault (.restriction r)
  | .ok ds =>
    let (forms, s) := prepare ds initState
    .ret .unspecified [.top [] forms] s

end Demos.Scheme.Semantics
