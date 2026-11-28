module

public import Demos.Scheme.Semantics.Outcome

@[expose] public section

/-! A transcription of the formal semantics of R4RS, §7.2 (printed pages 34 to 36 of the PDF).

The domain equations of §7.2.2 have no direct encoding as Lean types.  In
φ ∈ F = L × (E* → K → C), with K = E* → C, C = S → A, and S = L → (E × T), the domain E occurs
to the left of function arrows, and Lean admits only strictly positive inductive types.  Mathlib
supplies ω-complete partial orders and least fixed points of continuous maps, and no solution of
a recursive domain equation.  The transcription therefore defunctionalizes the equations: each
λ-abstraction of §7.2.3 and §7.2.4 whose value lies in F's function part, in K, in C, in an
argument of `single` (E → C), or in an argument of `tievals` (L* → C) is a constructor of the code
types `Fn`, `K`, `Theta`, `Psi`, or `Tie`, whose fields are the abstraction's free variables.  The
semantic functions E, E*, and C and the auxiliary functions in continuation-passing style become
the clauses of one function `step` over configurations and the functions that it calls, such as
`send`, `hold`, `applicate`, `twoarg`, and `auxStep`, one for each equation and each abstraction,
since every right-hand side of §7.2 is a tail call.  A configuration `.E e ρ κ σ` is
`E[[e]] ρ κ σ`, `.K κ εs σ` is `κ ε* σ`, and `.Fn φ εs κ σ` is `φ ε* κ σ`.  Each clause of `step`
cites its equation and page.

The report leaves parts of the semantics to the implementation, to its prose, or to nothing, and
the transcription supplies each as follows.

| Part | Clause | Rule of the transcription |
|---|---|---|
| `K`, the meaning of constants | p. 34: "Definition of K deliberately omitted." | `ofDatum`: an atom denotes its value, and each occurrence of a quoted compound datum denotes an object that the initial store holds with the flag false (§3.5, §4.1.2). |
| `new` | p. 35, implementation-dependent | `new σ = #σ`, which meets the axiom of p. 34 (`new_unallocated`) and never reports `error`. |
| `wrong` | p. 35, implementation-dependent | The answer `wrong x`. |
| `permute`, `unpermute` | p. 35, implementation-dependent | The identity, which selects the profile's order of §4.1.3. |
| A, the answers | p. 34, no definition | The values with the store, or `wrong x`. |
| The initial environment, store, and continuation | none | `rho0` binds the names of the procedures that §7.2.4 defines, `+`, `<`, `list`, `cons`, `car`, `cdr`, `set-car!`, `eqv?`, `apply`, `call-with-current-continuation`, and `call/cc`, to locations of `sigma0` that hold them, and the initial continuation `K.top` gives the answer.  The first locations of `sigma0`, one for each name, hold `unspecified` as the procedures' identity locations; `call/cc` has the identity location of `call-with-current-continuation`, so its own stays unused. |
| `cdr` | p. 36: "[similar to car]" | `car`'s equation with the second location of the pair and the error "non-pair argument to cdr". |
| `eqv` on vectors and strings | p. 36: "…" | By analogy with pairs: the sequences of locations are equal. |
| U = Ide → L | p. 34 | The environments are finite, and a variable that an environment does not bind is the answer `wrong "unbound variable"`, outside the class of programs of p. 34. |
| An empty program | p. 34 | The unspecified value, since `(lambda () )` has no body. |
| A variable that a program defines twice | p. 34 | It is one variable of I*, since `(lambda (x x) …)` is an error (§4.1.4), and its definitions are assignments to it. |
| A constant that names a standard procedure that §7.2.4 does not define, such as §7.3's `<memv>` | none | No meaning: `ofExpr` returns `none`. |
| `unspecified` | p. 35: "any expressed value other than undefined may be used" | The value `unspecified` of M. |
| R, the numbers | p. 34 | `Int`, with no range: the profile's restriction is an implementation restriction outside §7.2, so `add` returns results outside the fixnum range.  The front end that `start` uses, the reference reader, reads numerals under the fixnum profile. |
| Locations outside the store | none | `read` gives `undefined` off the store, and `update` beyond the next location marks the locations between in use.  Neither arises, since `new σ = #σ`; nor do the defaults of `K.app`, `extendsEnv`, and `takefirst` for sequences shorter than their equations require. |

A vector or string here is its sequence of locations, as Ev = L* × T states, so two empty vectors
are `eqv`, where the reference semantics's profile makes them distinct objects, which §6.2
permits.  `answerDatum` observes an answer of one value as its datum, and no datum for a
procedure, for `unspecified`, or for an answer of several values or of `wrong`. -/

namespace Demos.Scheme.Report

open Demos.Scheme.Semantics

/-- Locations (L). -/
abbrev L := Nat

/-- Identifiers (Ide): the variables of the core syntax, identifiers and the temporaries of
§7.3's rules. -/
abbrev Ide := Var

/-- M = {false, true, null, undefined, unspecified} (§7.2.2, p. 34). -/
inductive M where
  | false | true | null | undefined | unspecified
  deriving DecidableEq, Repr

/-- The procedures that §7.2.4 defines (pp. 35–36). -/
inductive Aux where
  | list | cons | less | add | car | cdr | setcar | eqv | apply | valueslist | cwcc
  deriving DecidableEq, Repr

mutual

/-- The abstract syntax of §7.2.1 (p. 34), with each constant K already replaced by its value
`K[[K]]`. -/
inductive Exp where
  /-- K -/
  | const (ε : E)
  /-- I -/
  | var (i : Ide)
  /-- (E0 E*) -/
  | app (e0 : Exp) (es : List Exp)
  /-- (lambda (I*) Γ* E0) -/
  | lam (is : List Ide) (cs : List Exp) (e0 : Exp)
  /-- (lambda (I* . I) Γ* E0) -/
  | lamRest (is : List Ide) (i : Ide) (cs : List Exp) (e0 : Exp)
  /-- (lambda I Γ* E0) -/
  | lamVar (i : Ide) (cs : List Exp) (e0 : Exp)
  /-- (if E0 E1 E2) -/
  | ite (e0 e1 e2 : Exp)
  /-- (if E0 E1) -/
  | it (e0 e1 : Exp)
  /-- (set! I E) -/
  | set (i : Ide) (e : Exp)

/-- Expressed values, E = Q + H + R + Ep + Ev + Es + M + F (§7.2.2, p. 34). -/
inductive E where
  | q (s : Sym)
  | h (c : UInt8)
  | r (n : Int)
  /-- Ep = L × L × T -/
  | ep (car cdr : L) (mutable : Bool)
  /-- Ev = L* × T -/
  | ev (ls : List L) (mutable : Bool)
  /-- Es = L* × T -/
  | es (ls : List L) (mutable : Bool)
  | m (x : M)
  /-- F = L × (E* → K → C), with the function part as a code. -/
  | f (α : L) (φ : Fn)

/-- The functions E* → K → C of procedure values. -/
inductive Fn where
  /-- `λε*κ′ . #ε* = #I* → tievals (…) ε*, wrong …` of E[[(lambda (I*) Γ* E0)]] (p. 35). -/
  | closure (is : List Ide) (cs : List Exp) (e0 : Exp) (ρ : List (Ide × L))
  /-- `λε*κ′ . #ε* ≥ #I* → tievalsrest (…) ε* (#I*), wrong …` of
  E[[(lambda (I* . I) Γ* E0)]] (p. 35). -/
  | closureRest (is : List Ide) (i : Ide) (cs : List Exp) (e0 : Exp) (ρ : List (Ide × L))
  /-- `λε*κ′ . κε*` of `cwcc` (p. 36). -/
  | escape (κ : K)
  /-- A procedure of §7.2.4. -/
  | aux (a : Aux)

/-- Expression continuations, K = E* → C. -/
inductive K where
  /-- `single ψ` (p. 35). -/
  | single (ψ : Psi)
  /-- `λε* . ((λε* . applicate (ε* ↓ 1) (ε* † 1) κ) (unpermute ε*))` of E[[(E0 E*)]]
  (p. 35). -/
  | app (κ : K)
  /-- `λε* . κ (⟨ε0⟩ § ε*)` of E*[[E0 E*]] (p. 35). -/
  | prepend (ε0 : E) (κ : K)
  /-- `λε* . C[[Γ*]]ρθ` of C[[Γ0 Γ*]] (p. 35). -/
  | cmd (cs : List Exp) (ρ : List (Ide × L)) (θ : Theta)
  /-- `λε* . valueslist ε* (λε* . car⟨ε⟩(single(λε . κ(⟨ε⟩ § ε*))))` of `valueslist`
  (p. 36). -/
  | valuesCdr (ε : E) (κ : K)
  /-- `λε* . car⟨ε⟩(single(λε . κ(⟨ε⟩ § ε*)))` of `valueslist` (p. 36). -/
  | valuesCar (ε : E) (κ : K)
  /-- `λε* . applicate ε1 ε* κ` of `apply` (p. 36). -/
  | applyArgs (ε1 : E) (κ : K)
  /-- The initial continuation, which gives the answer. -/
  | top

/-- The functions E → C that `single` takes. -/
inductive Psi where
  /-- `λε . ε = undefined → wrong "undefined variable", send ε κ` of E[[I]] (p. 35). -/
  | var (κ : K)
  /-- `λε . truish ε → E[[E1]]ρκ, E[[E2]]ρκ` of E[[(if E0 E1 E2)]] (p. 35). -/
  | ite (e1 e2 : Exp) (ρ : List (Ide × L)) (κ : K)
  /-- `λε . truish ε → E[[E1]]ρκ, send unspecified κ` of E[[(if E0 E1)]] (p. 35). -/
  | it (e1 : Exp) (ρ : List (Ide × L)) (κ : K)
  /-- `λε . assign (lookup ρ I) ε (send unspecified κ)` of E[[(set! I E)]] (p. 35). -/
  | assign (i : Ide) (ρ : List (Ide × L)) (κ : K)
  /-- `λε0 . E*[[E*]] ρ (λε* . κ (⟨ε0⟩ § ε*))` of E*[[E0 E*]] (p. 35). -/
  | evlis (es : List Exp) (ρ : List (Ide × L)) (κ : K)
  /-- `λε . cons⟨ε* ↓ 1, ε⟩κ` of `list` (p. 36), with `ε* ↓ 1` as `ε1`. -/
  | listCons (ε1 : E) (κ : K)
  /-- `λε . tievals ψ ((takefirst ε* ν) § ⟨ε⟩)` of `tievalsrest` (p. 35), with
  `takefirst ε* ν` as `firsts`. -/
  | rest (ψ : Tie) (firsts : List E)
  /-- `λε . κ(⟨ε⟩ § ε*)` of `valueslist` (p. 36). -/
  | valuesCons (εs : List E) (κ : K)

/-- Command continuations, C = S → A. -/
inductive Theta where
  /-- `E[[E0]]ρ′κ′` as the command continuation of C[[Γ*]]ρ′ in the lambda equations
  (p. 35). -/
  | body (e0 : Exp) (ρ : List (Ide × L)) (κ : K)
  /-- `send ε κ`, the command continuation of `assign` in E[[(set! I E)]] and `setcar`
  (pp. 35–36). -/
  | send (ε : E) (κ : K)

/-- The functions L* → C that `tievals` takes. -/
inductive Tie where
  /-- `λα* . (λρ′ . C[[Γ*]]ρ′ (E[[E0]]ρ′κ′)) (extends ρ I* α*)` of the lambda equations
  (p. 35). -/
  | bind (is : List Ide) (cs : List Exp) (e0 : Exp) (ρ : List (Ide × L)) (κ' : K)
  /-- `λα* . ψ(⟨new σ | L⟩ § α*)` of `tievals` (p. 35), with `new σ | L` as `α`. -/
  | prepend (α : L) (ψ : Tie)

end

instance : Inhabited E := ⟨.m .unspecified⟩

/-- Environments, U = Ide → L, as finite maps. -/
abbrev U := List (Ide × L)

/-- Stores, S = L → (E × T): location `α` holds `σ[α]` and is in use when `α < #σ`. -/
abbrev S := List E

/-- Answers. -/
inductive A where
  | values (εs : List E) (σ : S)
  | wrong (x : String)

/-- The configurations: a semantic function or a code applied to its arguments, or an answer. -/
inductive Conf where
  /-- E[[e]] ρ κ σ -/
  | E (e : Exp) (ρ : U) (κ : K) (σ : S)
  /-- E*[[es]] ρ κ σ -/
  | Es (es : List Exp) (ρ : U) (κ : K) (σ : S)
  /-- C[[cs]] ρ θ σ -/
  | C (cs : List Exp) (ρ : U) (θ : Theta) (σ : S)
  /-- κ ε* σ -/
  | K (κ : K) (εs : List E) (σ : S)
  /-- ψ ε σ -/
  | Psi (ψ : Psi) (ε : E) (σ : S)
  /-- θ σ -/
  | Theta (θ : Theta) (σ : S)
  /-- φ ε* κ σ -/
  | Fn (φ : Fn) (εs : List E) (κ : K) (σ : S)
  /-- ψ α* σ -/
  | Tie (ψ : Tie) (αs : List L) (σ : S)
  /-- tievals ψ ε* σ -/
  | Tievals (ψ : Tie) (εs : List E) (σ : S)
  | Answer (a : A)

/-! ## Auxiliary functions (§7.2.4, pp. 35–36) -/

/-- `σ α ↓ 1`. -/
def read (σ : S) (α : L) : E := σ.getD α (.m .undefined)

/-- `new σ`, implementation-dependent (p. 35): the first location after those in use. -/
def new (σ : S) : L := σ.length

/-- `update = λαεσ . σ[⟨ε, true⟩/α]` (p. 35). -/
def update (α : L) (ε : E) (σ : S) : S :=
  if α < σ.length then σ.set α ε
  else σ ++ List.replicate (α - σ.length) (.m .undefined) ++ [ε]

/-- The axiom of p. 34: if `new σ ∈ L`, then `σ (new σ | L) ↓ 2 = false`, the location is not in
use. -/
theorem new_unallocated (σ : S) : ¬ new σ < σ.length := Nat.lt_irrefl _

/-- `lookup = λρI . ρI` (p. 35), on a finite environment. -/
def lookup (ρ : U) (i : Ide) : Option L := ρ.lookup i

/-- `extends = λρI*α* . #I* = 0 → ρ, extends (ρ[(α* ↓ 1)/(I* ↓ 1)]) (I* † 1) (α* † 1)`
(p. 35). -/
def extendsEnv : U → List Ide → List L → U
  | ρ, i :: is, α :: αs => extendsEnv ((i, α) :: ρ) is αs
  | ρ, _, _ => ρ

/-- `wrong : X → C`, implementation-dependent (p. 35). -/
def wrong (x : String) : Conf := .Answer (.wrong x)

/-- `send = λεκ . κ⟨ε⟩` (p. 35). -/
def send (ε : E) (κ : K) (σ : S) : Conf := .K κ [ε] σ

/-- `hold = λακσ . send (σα ↓ 1)κσ` (p. 35). -/
def hold (α : L) (κ : K) (σ : S) : Conf := send (read σ α) κ σ

/-- `assign = λαεθσ . θ(update αεσ)` (p. 35). -/
def assign (α : L) (ε : E) (θ : Theta) (σ : S) : Conf := .Theta θ (update α ε σ)

/-- `dropfirst = λln . n = 0 → l, dropfirst (l † 1)(n − 1)` (p. 35). -/
def dropfirst : List E → Nat → List E
  | l, 0 => l
  | l, n + 1 => dropfirst (l.drop 1) n

/-- `takefirst = λln . n = 0 → ⟨⟩, ⟨l ↓ 1⟩ § (takefirst (l † 1)(n − 1))` (p. 35). -/
def takefirst : List E → Nat → List E
  | _, 0 => []
  | l, n + 1 => l.take 1 ++ takefirst (l.drop 1) n

/-- `truish = λε . ε = false → false, true` (p. 35). -/
def truish : E → Bool
  | .m .false => false
  | _ => true

/-- `permute`, implementation-dependent (p. 35): the identity. -/
def permute (es : List Exp) : List Exp := es

/-- `unpermute`, the inverse of `permute` (p. 35). -/
def unpermute (εs : List E) : List E := εs

/-- `applicate = λεε*κ . ε ∈ F → (ε | F ↓ 2)ε*κ, wrong "bad procedure"` (p. 35). -/
def applicate (ε : E) (εs : List E) (κ : K) (σ : S) : Conf :=
  match ε with
  | .f _ φ => .Fn φ εs κ σ
  | _ => wrong "bad procedure"

/-- `onearg = λζε*κ . #ε* = 1 → ζ(ε* ↓ 1)κ, wrong "wrong number of arguments"` (p. 35). -/
def onearg (ζ : E → K → S → Conf) (εs : List E) (κ : K) (σ : S) : Conf :=
  match εs with
  | [ε] => ζ ε κ σ
  | _ => wrong "wrong number of arguments"

/-- `twoarg = λζε*κ . #ε* = 2 → ζ(ε* ↓ 1)(ε* ↓ 2)κ, wrong "wrong number of arguments"`
(p. 35). -/
def twoarg (ζ : E → E → K → S → Conf) (εs : List E) (κ : K) (σ : S) : Conf :=
  match εs with
  | [ε1, ε2] => ζ ε1 ε2 κ σ
  | _ => wrong "wrong number of arguments"

/-- `tievalsrest = λψε*ν . list (dropfirst ε*ν) (single(λε . tievals ψ ((takefirst ε*ν) § ⟨ε⟩)))`
(p. 35). -/
def tievalsrest (ψ : Tie) (εs : List E) (ν : Nat) (σ : S) : Conf :=
  .Fn (.aux .list) (dropfirst εs ν) (.single (.rest ψ (takefirst εs ν))) σ

def bool (b : Bool) : E := .m (if b then .true else .false)

/-- `eqv` (p. 36), with the elided clauses of vectors and strings by analogy with pairs. -/
def eqvE : E → E → E
  | .m a, .m b => bool (a == b)
  | .q a, .q b => bool (a == b)
  | .h a, .h b => bool (a == b)
  | .r a, .r b => bool (a == b)
  | .ep a d _, .ep a' d' _ => bool (a == a' && d == d')
  | .ev ls _, .ev ls' _ => bool (ls == ls')
  | .es ls _, .es ls' _ => bool (ls == ls')
  | .f α _, .f α' _ => bool (α == α')
  | _, _ => bool false

/-- The procedures of §7.2.4 applied to their arguments (p. 36). -/
def auxStep : Aux → List E → K → S → Conf
  -- list = λε*κ . #ε* = 0 → send null κ, list (ε* † 1)(single(λε . cons⟨ε* ↓ 1, ε⟩κ)) (p. 36)
  | .list, [], κ, σ => send (.m .null) κ σ
  | .list, ε :: rest, κ, σ => .Fn (.aux .list) rest (.single (.listCons ε κ)) σ
  -- cons = twoarg (λε1ε2κσ . new σ ∈ L → (λσ′ . new σ′ ∈ L →
  --   send (⟨new σ | L, new σ′ | L, true⟩ in E) κ (update (new σ′ | L) ε2 σ′), …)
  --   (update (new σ | L) ε1 σ), …) (p. 36)
  | .cons, εs, κ, σ => twoarg (fun ε1 ε2 κ σ =>
      let σ' := update (new σ) ε1 σ
      send (.ep (new σ) (new σ') true) κ (update (new σ') ε2 σ')) εs κ σ
  -- less = twoarg (λε1ε2κ . (ε1 ∈ R ∧ ε2 ∈ R) → send (ε1 | R < ε2 | R → true, false)κ,
  --   wrong "non-numeric argument to <") (p. 36)
  | .less, εs, κ, σ => twoarg (fun ε1 ε2 κ σ =>
      match ε1, ε2 with
      | .r a, .r b => send (bool (decide (a < b))) κ σ
      | _, _ => wrong "non-numeric argument to <") εs κ σ
  -- add = twoarg (λε1ε2κ . (ε1 ∈ R ∧ ε2 ∈ R) → send ((ε1 | R + ε2 | R) in E)κ,
  --   wrong "non-numeric argument to +") (p. 36)
  | .add, εs, κ, σ => twoarg (fun ε1 ε2 κ σ =>
      match ε1, ε2 with
      | .r a, .r b => send (.r (a + b)) κ σ
      | _, _ => wrong "non-numeric argument to +") εs κ σ
  -- car = onearg (λεκ . ε ∈ Ep → hold (ε | Ep ↓ 1)κ, wrong "non-pair argument to car") (p. 36)
  | .car, εs, κ, σ => onearg (fun ε κ σ =>
      match ε with
      | .ep a _ _ => hold a κ σ
      | _ => wrong "non-pair argument to car") εs κ σ
  -- cdr : E* → K → C [similar to car] (p. 36)
  | .cdr, εs, κ, σ => onearg (fun ε κ σ =>
      match ε with
      | .ep _ d _ => hold d κ σ
      | _ => wrong "non-pair argument to cdr") εs κ σ
  -- setcar = twoarg (λε1ε2κ . ε1 ∈ Ep → (ε1 | Ep ↓ 3) → assign (ε1 | Ep ↓ 1) ε2
  --   (send unspecified κ), wrong "immutable argument to set-car!",
  --   wrong "non-pair argument to set-car!") (p. 36)
  | .setcar, εs, κ, σ => twoarg (fun ε1 ε2 κ σ =>
      match ε1 with
      | .ep a _ m => if m then assign a ε2 (.send (.m .unspecified) κ) σ
          else wrong "immutable argument to set-car!"
      | _ => wrong "non-pair argument to set-car!") εs κ σ
  -- eqv = twoarg (λε1ε2κ . … ) (p. 36)
  | .eqv, εs, κ, σ => twoarg (fun ε1 ε2 κ σ => send (eqvE ε1 ε2) κ σ) εs κ σ
  -- apply = twoarg (λε1ε2κ . ε1 ∈ F → valueslist ⟨ε2⟩(λε* . applicate ε1 ε*κ),
  --   wrong "bad procedure argument to apply") (p. 36)
  | .apply, εs, κ, σ => twoarg (fun ε1 ε2 κ σ =>
      match ε1 with
      | .f .. => .Fn (.aux .valueslist) [ε2] (.applyArgs ε1 κ) σ
      | _ => wrong "bad procedure argument to apply") εs κ σ
  -- valueslist = onearg (λεκ . ε ∈ Ep → cdr⟨ε⟩(λε* . valueslist ε* (λε* . car⟨ε⟩(single(λε .
  --   κ(⟨ε⟩ § ε*))))), ε = null → κ⟨⟩, wrong "non-list argument to values-list") (p. 36)
  | .valueslist, εs, κ, σ => onearg (fun ε κ σ =>
      match ε with
      | .ep .. => .Fn (.aux .cdr) [ε] (.valuesCdr ε κ) σ
      | .m .null => .K κ [] σ
      | _ => wrong "non-list argument to values-list") εs κ σ
  -- cwcc = onearg (λεκ . ε ∈ F → (λσ . new σ ∈ L → applicate ε ⟨⟨new σ | L, λε*κ′ . κε*⟩ in E⟩
  --   κ (update (new σ | L) unspecified σ), wrong "out of memory" σ),
  --   wrong "bad procedure argument") (p. 36)
  | .cwcc, εs, κ, σ => onearg (fun ε κ σ =>
      match ε with
      | .f .. => applicate ε [.f (new σ) (.escape κ)] κ (update (new σ) (.m .unspecified) σ)
      | _ => wrong "bad procedure argument") εs κ σ

/-! ## The semantic functions (§7.2.3, pp. 34–35) and the codes -/

/-- One clause of the equations. -/
def step : Conf → Conf
  -- E[[K]] = λρκ . send (K[[K]]) κ (p. 34)
  | .E (.const ε) _ κ σ => send ε κ σ
  -- E[[I]] = λρκ . hold (lookup ρ I) (single(λε . ε = undefined → wrong "undefined variable",
  --   send ε κ)) (p. 35)
  | .E (.var i) ρ κ σ =>
    match lookup ρ i with
    | some α => hold α (.single (.var κ)) σ
    | none => wrong "unbound variable"
  -- E[[(E0 E*)]] = λρκ . E*(permute(⟨E0⟩ § E*)) ρ (λε* . ((λε* . applicate (ε* ↓ 1) (ε* † 1) κ)
  --   (unpermute ε*))) (p. 35)
  | .E (.app e0 es) ρ κ σ => .Es (permute (e0 :: es)) ρ (.app κ) σ
  -- E[[(lambda (I*) Γ* E0)]] = λρκ . λσ . new σ ∈ L → send (⟨new σ | L, λε*κ′ . …⟩ in E) κ
  --   (update (new σ | L) unspecified σ), wrong "out of memory" σ (p. 35)
  | .E (.lam is cs e0) ρ κ σ =>
    send (.f (new σ) (.closure is cs e0 ρ)) κ (update (new σ) (.m .unspecified) σ)
  -- E[[(lambda (I* . I) Γ* E0)]] = λρκ . λσ . new σ ∈ L → send (⟨new σ | L, λε*κ′ . …⟩ in E) κ
  --   (update (new σ | L) unspecified σ), wrong "out of memory" σ (p. 35)
  | .E (.lamRest is i cs e0) ρ κ σ =>
    send (.f (new σ) (.closureRest is i cs e0 ρ)) κ (update (new σ) (.m .unspecified) σ)
  -- E[[(lambda I Γ* E0)]] = E[[(lambda (. I) Γ* E0)]] (p. 35)
  | .E (.lamVar i cs e0) ρ κ σ => .E (.lamRest [] i cs e0) ρ κ σ
  -- E[[(if E0 E1 E2)]] = λρκ . E[[E0]] ρ (single (λε . truish ε → E[[E1]]ρκ, E[[E2]]ρκ))
  --   (p. 35)
  | .E (.ite e0 e1 e2) ρ κ σ => .E e0 ρ (.single (.ite e1 e2 ρ κ)) σ
  -- E[[(if E0 E1)]] = λρκ . E[[E0]] ρ (single (λε . truish ε → E[[E1]]ρκ,
  --   send unspecified κ)) (p. 35)
  | .E (.it e0 e1) ρ κ σ => .E e0 ρ (.single (.it e1 ρ κ)) σ
  -- E[[(set! I E)]] = λρκ . E[[E]] ρ (single(λε . assign (lookup ρ I) ε (send unspecified κ)))
  --   (p. 35)
  | .E (.set i e) ρ κ σ => .E e ρ (.single (.assign i ρ κ)) σ
  -- E*[[ ]] = λρκ . κ⟨⟩ (p. 35)
  | .Es [] _ κ σ => .K κ [] σ
  -- E*[[E0 E*]] = λρκ . E[[E0]] ρ (single(λε0 . E*[[E*]] ρ (λε* . κ (⟨ε0⟩ § ε*)))) (p. 35)
  | .Es (e0 :: es) ρ κ σ => .E e0 ρ (.single (.evlis es ρ κ)) σ
  -- C[[ ]] = λρθ . θ (p. 35)
  | .C [] _ θ σ => .Theta θ σ
  -- C[[Γ0 Γ*]] = λρθ . E[[Γ0]] ρ (λε* . C[[Γ*]]ρθ) (p. 35)
  | .C (c :: cs) ρ θ σ => .E c ρ (.cmd cs ρ θ) σ
  -- single = λψε* . #ε* = 1 → ψ(ε* ↓ 1), wrong "wrong number of return values" (p. 35)
  | .K (.single ψ) εs σ =>
    match εs with
    | [ε] => .Psi ψ ε σ
    | _ => wrong "wrong number of return values"
  -- λε* . ((λε* . applicate (ε* ↓ 1) (ε* † 1) κ) (unpermute ε*)) of E[[(E0 E*)]] (p. 35)
  | .K (.app κ) εs σ =>
    let εs := unpermute εs
    applicate (εs.headD (.m .unspecified)) (εs.drop 1) κ σ
  -- λε* . κ (⟨ε0⟩ § ε*) of E*[[E0 E*]] (p. 35)
  | .K (.prepend ε0 κ) εs σ => .K κ (ε0 :: εs) σ
  -- λε* . C[[Γ*]]ρθ of C[[Γ0 Γ*]] (p. 35)
  | .K (.cmd cs ρ θ) _ σ => .C cs ρ θ σ
  -- λε* . valueslist ε* (λε* . car⟨ε⟩(single(λε . κ(⟨ε⟩ § ε*)))) of valueslist (p. 36)
  | .K (.valuesCdr ε κ) εs σ => .Fn (.aux .valueslist) εs (.valuesCar ε κ) σ
  -- λε* . car⟨ε⟩(single(λε . κ(⟨ε⟩ § ε*))) of valueslist (p. 36)
  | .K (.valuesCar ε κ) εs σ => .Fn (.aux .car) [ε] (.single (.valuesCons εs κ)) σ
  -- λε* . applicate ε1 ε*κ of apply (p. 36)
  | .K (.applyArgs ε1 κ) εs σ => applicate ε1 εs κ σ
  -- The initial continuation: the answer.
  | .K .top εs σ => .Answer (.values εs σ)
  -- λε . ε = undefined → wrong "undefined variable", send ε κ of E[[I]] (p. 35)
  | .Psi (.var κ) ε σ =>
    match ε with
    | .m .undefined => wrong "undefined variable"
    | _ => send ε κ σ
  -- λε . truish ε → E[[E1]]ρκ, E[[E2]]ρκ of E[[(if E0 E1 E2)]] (p. 35)
  | .Psi (.ite e1 e2 ρ κ) ε σ => if truish ε then .E e1 ρ κ σ else .E e2 ρ κ σ
  -- λε . truish ε → E[[E1]]ρκ, send unspecified κ of E[[(if E0 E1)]] (p. 35)
  | .Psi (.it e1 ρ κ) ε σ => if truish ε then .E e1 ρ κ σ else send (.m .unspecified) κ σ
  -- λε . assign (lookup ρ I) ε (send unspecified κ) of E[[(set! I E)]] (p. 35)
  | .Psi (.assign i ρ κ) ε σ =>
    match lookup ρ i with
    | some α => assign α ε (.send (.m .unspecified) κ) σ
    | none => wrong "unbound variable"
  -- λε0 . E*[[E*]] ρ (λε* . κ (⟨ε0⟩ § ε*)) of E*[[E0 E*]] (p. 35)
  | .Psi (.evlis es ρ κ) ε0 σ => .Es es ρ (.prepend ε0 κ) σ
  -- λε . cons⟨ε* ↓ 1, ε⟩κ of list (p. 36)
  | .Psi (.listCons ε1 κ) ε σ => .Fn (.aux .cons) [ε1, ε] κ σ
  -- λε . tievals ψ ((takefirst ε* ν) § ⟨ε⟩) of tievalsrest (p. 35)
  | .Psi (.rest ψ firsts) ε σ => .Tievals ψ (firsts ++ [ε]) σ
  -- λε . κ(⟨ε⟩ § ε*) of valueslist (p. 36)
  | .Psi (.valuesCons εs κ) ε σ => .K κ (ε :: εs) σ
  -- E[[E0]]ρ′κ′ as a command continuation (p. 35)
  | .Theta (.body e0 ρ κ) σ => .E e0 ρ κ σ
  -- send ε κ as a command continuation (pp. 35–36)
  | .Theta (.send ε κ) σ => send ε κ σ
  -- tievals = λψε*σ . #ε* = 0 → ψ⟨⟩σ, new σ ∈ L → tievals (λα* . ψ(⟨new σ | L⟩ § α*)) (ε* † 1)
  --   (update (new σ | L) (ε* ↓ 1) σ), wrong "out of memory" σ (p. 35)
  | .Tievals ψ [] σ => .Tie ψ [] σ
  | .Tievals ψ (ε :: εs) σ => .Tievals (.prepend (new σ) ψ) εs (update (new σ) ε σ)
  -- λα* . ψ(⟨new σ | L⟩ § α*) of tievals (p. 35)
  | .Tie (.prepend α ψ) αs σ => .Tie ψ (α :: αs) σ
  -- λα* . (λρ′ . C[[Γ*]]ρ′ (E[[E0]]ρ′κ′)) (extends ρ I* α*) of the lambda equations (p. 35)
  | .Tie (.bind is cs e0 ρ κ') αs σ =>
    let ρ' := extendsEnv ρ is αs
    .C cs ρ' (.body e0 ρ' κ') σ
  -- λε*κ′ . #ε* = #I* → tievals (…) ε*, wrong "wrong number of arguments"
  --   of E[[(lambda (I*) Γ* E0)]] (p. 35)
  | .Fn (.closure is cs e0 ρ) εs κ' σ =>
    if εs.length = is.length then .Tievals (.bind is cs e0 ρ κ') εs σ
    else wrong "wrong number of arguments"
  -- λε*κ′ . #ε* ≥ #I* → tievalsrest (…) ε* (#I*), wrong "too few arguments"
  --   of E[[(lambda (I* . I) Γ* E0)]], with extends ρ (I* § ⟨I⟩) α* (p. 35)
  | .Fn (.closureRest is i cs e0 ρ) εs κ' σ =>
    if εs.length ≥ is.length then tievalsrest (.bind (is ++ [i]) cs e0 ρ κ') εs is.length σ
    else wrong "too few arguments"
  -- λε*κ′ . κε* of cwcc (p. 36)
  | .Fn (.escape κ) εs _ σ => .K κ εs σ
  -- (ε | F ↓ 2) ε* κ for a procedure of §7.2.4 (p. 36)
  | .Fn (.aux a) εs κ σ => auxStep a εs κ σ
  -- An answer is final.
  | .Answer a => .Answer a

/-- The configuration after `n` clauses, or the answer that an earlier clause reached. -/
def run : Nat → Conf → Conf
  | 0, c => c
  | n + 1, c =>
    match c with
    | .Answer _ => c
    | _ => run n (step c)

/-! ## Constants, the initial environment, and programs -/

/-- `K` for a datum, which the report omits (p. 34): an atom denotes its value, and a compound
datum denotes an object in fresh locations with the flag false, since constants are immutable
(§3.5). -/
def ofDatum (σ : S) : Datum → E × S
  | .bool b => (bool b, σ)
  | .int n => (.r n, σ)
  | .char c => (.h c, σ)
  | .sym s => (.q s, σ)
  | .nil => (.m .null, σ)
  | .str cs =>
    let σ' := cs.foldl (fun σ c => σ ++ [E.h c]) σ
    (.es ((List.range cs.length).map (σ.length + ·)) false, σ')
  | .pair a d =>
    let (εa, σ) := ofDatum σ a
    let (εd, σ) := ofDatum σ d
    let σ' := update (new σ) εa σ
    (.ep (new σ) (new σ') false, update (new σ') εd σ')
  | .vec elems =>
    let (ls, σ) := ofElems σ elems
    (.ev ls false, σ)
where
  ofElems (σ : S) : Datum → List L × S
    | .pair a d =>
      let (ε, σ) := ofDatum σ a
      let l := new σ
      let (ls, σ) := ofElems (update l ε σ) d
      (l :: ls, σ)
    | _ => ([], σ)

/-- The names of the procedures of §7.2.4 in the initial environment, with `call/cc` as a second
name of `cwcc`. -/
def auxNames : List (Sym × Aux) :=
  [("+", .add), ("<", .less), ("list", .list), ("cons", .cons), ("car", .car), ("cdr", .cdr),
    ("set-car!", .setcar), ("eqv?", .eqv), ("apply", .apply),
    ("call-with-current-continuation", .cwcc), ("call/cc", .cwcc)].map fun (n, a) => (bytes n, a)

/-- The identity location of a procedure of §7.2.4: the position of its first name. -/
def auxTag (a : Aux) : L := (auxNames.findIdx? (·.2 == a)).getD 0

def auxVal (a : Aux) : E := .f (auxTag a) (.aux a)

/-- The initial store: the identity locations of the procedures, then a location for each name
that holds its procedure. -/
def sigma0 : S :=
  List.replicate auxNames.length (.m .unspecified) ++ auxNames.map fun (_, a) => auxVal a

/-- The initial environment. -/
def rho0 : U := (List.range auxNames.length).zip auxNames |>.map fun (i, (n, _)) =>
  (.id n, auxNames.length + i)

/-- The value of a constant of the core syntax: `K` of a datum, §7.3's `<undefined>` and the
unspecified value, and the procedures `cons` and `list` that quasiquotation names, which §7.2.4
defines, or `none` for another procedure, such as §7.3's `<memv>`. -/
def constVal (σ : S) : Const → Option (E × S)
  | .datum d => some (ofDatum σ d)
  | .lit _ => none
  | .undefined => some (.m .undefined, σ)
  | .unspecified => some (.m .unspecified, σ)
  | .prim .cons => some (auxVal .cons, σ)
  | .prim .list => some (auxVal .list, σ)
  | .prim _ => none

mutual

/-- The abstract syntax of §7.2.1 of a core expression, with each constant replaced by its value
and each compound literal allocated in the store. -/
def ofExpr (σ : S) : Expr → Option (Exp × S)
  | .const k => (constVal σ k).map fun (ε, σ) => (.const ε, σ)
  | .var x => some (.var x, σ)
  | .app f args => do
    let (f, σ) ← ofExpr σ f
    let (args, σ) ← ofExprs σ args
    pure (.app f args, σ)
  | .lam fs r body last => do
    let (body, σ) ← ofExprs σ body
    let (last, σ) ← ofExpr σ last
    match fs, r with
    | _, none => pure (.lam fs body last, σ)
    | [], some i => pure (.lamVar i body last, σ)
    | _, some i => pure (.lamRest fs i body last, σ)
  | .ite c t e => do
    let (c, σ) ← ofExpr σ c
    let (t, σ) ← ofExpr σ t
    let (e, σ) ← ofExpr σ e
    pure (.ite c t e, σ)
  | .set x e => do
    let (e, σ) ← ofExpr σ e
    pure (.set x e, σ)

def ofExprs (σ : S) : List Expr → Option (List Exp × S)
  | [] => some ([], σ)
  | e :: es => do
    let (e, σ) ← ofExpr σ e
    let (es, σ) ← ofExprs σ es
    pure (e :: es, σ)

end

/-- The variables that the definitions of a program define, each once, in order. -/
def defined : List TopForm → List Ide → List Ide
  | [], acc => acc
  | .define x _ :: fs, acc => defined fs (if acc.contains (.id x) then acc else acc ++ [.id x])
  | .expr _ :: fs, acc => defined fs acc

/-- P′: the program's forms with each definition replaced by an assignment (p. 34). -/
def assignments : List TopForm → List Expr
  | [] => []
  | .define x e :: fs => .set (.id x) e :: assignments fs
  | .expr e :: fs => e :: assignments fs

/-- The whole-program translation of p. 34: `E[[((lambda (I*) P′) ⟨undefined⟩ …)]]`, with the
unspecified value for an empty program. -/
def program (tops : List TopForm) : Expr :=
  let is := defined tops []
  match (assignments tops).reverse with
  | [] => .const .unspecified
  | last :: cmdsRev =>
    .app (.lam is none cmdsRev.reverse last) (is.map fun _ => .const .undefined)

/-- The configuration `E[[P]] rho0 κ₀ sigma0` of the program whose bytes are `src`, under the
reader and the expander of the reference semantics, or `none` for a read or syntax error or a
constant outside §7.2. -/
def start (src : List UInt8) : Option Conf :=
  match readProgram Numeric.fixnum src with
  | .error _ => none
  | .ok ds =>
    match ds.mapM expandTop with
    | .error _ => none
    | .ok tops => (ofExpr sigma0 (program tops.flatten)).map fun (e, σ) => .E e rho0 .top σ

mutual

/-- The datum of an expressed value. -/
def externE (σ : S) : Nat → E → Option Datum
  | 0, _ => none
  | fuel + 1, ε =>
    match ε with
    | .m .true => some (.bool true)
    | .m .false => some (.bool false)
    | .m .null => some .nil
    | .r n => some (.int n)
    | .h c => some (.char c)
    | .q s => some (.sym s)
    | .es ls _ => some (.str (ls.map fun l => match read σ l with | .h c => c | _ => 0))
    | .ep a d _ =>
      match externE σ fuel (read σ a), externE σ fuel (read σ d) with
      | some x, some y => some (.pair x y)
      | _, _ => none
    | .ev ls _ => (externElems σ fuel (ls.map (read σ))).map .vec
    | _ => none

def externElems (σ : S) : Nat → List E → Option Datum
  | 0, _ => none
  | _ + 1, [] => some .nil
  | fuel + 1, ε :: εs =>
    match externE σ fuel ε, externElems σ fuel εs with
    | some x, some y => some (.pair x y)
    | _, _ => none

end

/-- The datum of the single value of an answer. -/
def answerDatum : Conf → Option Datum
  | .Answer (.values [ε] σ) => externE σ (σ.length + 2) ε
  | _ => none

/-- The datum of the answer that `n` clauses give the program whose bytes are `src`. -/
def answerOf (n : Nat) (src : List UInt8) : Option Datum :=
  (start src).bind fun c => answerDatum (run n c)

end Demos.Scheme.Report
