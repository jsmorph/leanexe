import LeanExe.Native.Clight.Clight

/-!
A printer of Clight programs as C text, for the programs the translator and the differential
tests produce: globals of scalar or array type, functions whose parameters and temporaries are
scalars or pointers, and the statements and expressions of `Clight.lean` other than `Sswitch`,
`Slabel`, `Sgoto`, `Efield`, `Esizeof`, and `Ealignof`.  `Sloop s1 s2` prints only when `s2` is
`Sskip`, as `for (;;)`.  Every subexpression is parenthesized, integer constants carry the
suffix of their type, and floating-point constants print as hexadecimal literals, which C reads
exactly; a NaN or infinite constant has no literal and is an error.  The printer is not
verified: `clightgen` reads its output back for comparison.

The printer writes the forms that `clightgen` produces so that they come back unchanged.  A
sequence nested as the first part of a sequence prints as a block, since C's blocks nest to the
right.  `Sloop (Ssequence Sskip s) Sskip` prints as `for (;;) { s }`, from which `clightgen`
restores the `Sskip`.  A call through a temporary `t` that `isCall` accepts, `Scall (some t) f
args` followed by `Sset x (Etempvar t)`, prints as `x = f(args);`, and `t` is not declared;
`clightgen` creates such a temporary for every call whose result is stored.  A store to a volatile
lvalue, `Sbuiltin None (EF_vstore chunk) tys [Eaddrof l ty, e]`, the form that SimplExpr gives
it, prints as the assignment `l = e;`, and a volatile type prints with the qualifier `volatile`.
A global without initialization data prints as an `extern` declaration.  `gname` names the
globals and functions, and `tname` the temporaries.
-/

namespace LeanExe.Native

open LClight

/-- Lowercase hexadecimal digits of `n`, with at least `width` digits. -/
def hexDigits (n width : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (width - s.length) '0') ++ s

/-- `volatile ` for a volatile type, and nothing otherwise. -/
def volatileQual (a : attr) : String := if a.attr_volatile then "volatile " else ""

def ctype : type → Except String String
  | .Tvoid => pure "void"
  | .Tint .I8 .Signed a => pure (volatileQual a ++ "signed char")
  | .Tint .I8 .Unsigned a => pure (volatileQual a ++ "unsigned char")
  | .Tint .I16 .Signed a => pure (volatileQual a ++ "short")
  | .Tint .I16 .Unsigned a => pure (volatileQual a ++ "unsigned short")
  | .Tint .I32 .Signed a => pure (volatileQual a ++ "int")
  | .Tint .I32 .Unsigned a => pure (volatileQual a ++ "unsigned int")
  | .Tint .IBool _ a => pure (volatileQual a ++ "_Bool")
  | .Tlong .Signed a => pure (volatileQual a ++ "long long")
  | .Tlong .Unsigned a => pure (volatileQual a ++ "unsigned long long")
  | .Tfloat .F32 a => pure (volatileQual a ++ "float")
  | .Tfloat .F64 a => pure (volatileQual a ++ "double")
  | .Tpointer t _ => do pure ((← ctype t) ++ " *")
  | _ => throw "a type the printer does not declare"

/-- An exact hexadecimal literal for a finite binary64 value. -/
def doubleLiteral (f : float) : Except String String :=
  let sign := if Wasm.IEEE64.sign f then "-" else ""
  let e := Wasm.IEEE64.exponent f
  let frac := Wasm.IEEE64.fraction f
  if e == 0x7FF then throw "a NaN or infinite double constant"
  else if e == 0 then pure s!"({sign}0x0.{hexDigits frac 13}p-1022)"
  else
    let p : Int := (e : Int) - 1023
    let ps := if p < 0 then s!"{p}" else s!"+{p}"
    pure s!"({sign}0x1.{hexDigits frac 13}p{ps})"

/-- An exact hexadecimal literal for a finite binary32 value. -/
def floatLiteral (f : float32) : Except String String :=
  let sign := if Wasm.IEEE32.sign f then "-" else ""
  let e := Wasm.IEEE32.exponent f
  let frac := Wasm.IEEE32.fraction f * 2
  if e == 0xFF then throw "a NaN or infinite float constant"
  else if e == 0 then pure s!"({sign}0x0.{hexDigits frac 6}p-126f)"
  else
    let p : Int := (e : Int) - 127
    let ps := if p < 0 then s!"{p}" else s!"+{p}"
    pure s!"({sign}0x1.{hexDigits frac 6}p{ps}f)"

def binop : binary_operation → String
  | .Oadd => "+" | .Osub => "-" | .Omul => "*" | .Odiv => "/" | .Omod => "%"
  | .Oand => "&" | .Oor => "|" | .Oxor => "^" | .Oshl => "<<" | .Oshr => ">>"
  | .Oeq => "==" | .One => "!=" | .Olt => "<" | .Ogt => ">" | .Ole => "<=" | .Oge => ">="

section

variable (gname tname : ident → String) (isCall : ident → Bool)

def cexpr : expr → Except String String
  | .Econst_int i ty =>
      match ty with
      | .Tint .I32 .Unsigned _ => pure s!"{i.toNat}U"
      | .Tint .I32 .Signed _ => pure s!"((int){i.toNat}U)"
      | _ => throw "an int constant of a type other than int or unsigned int"
  | .Econst_long i ty =>
      match ty with
      | .Tlong .Unsigned _ => pure s!"{i.toNat}ULL"
      | .Tlong .Signed _ => pure s!"((long long){i.toNat}ULL)"
      | _ => throw "a long constant of a type other than long long"
  | .Econst_float f _ => doubleLiteral f
  | .Econst_single f _ => floatLiteral f
  | .Evar id _ => pure (gname id)
  | .Etempvar id _ => pure (tname id)
  | .Ederef a _ => do pure s!"(*{← cexpr a})"
  | .Eaddrof a _ => do pure s!"(&{← cexpr a})"
  | .Eunop op a _ => do
      let s ← cexpr a
      match op with
      | .Onotbool => pure s!"(!{s})"
      | .Onotint => pure s!"(~{s})"
      | .Oneg => pure s!"(-{s})"
      | .Oabsfloat => pure s!"__builtin_fabs({s})"
  | .Ebinop op a1 a2 _ => do pure s!"({← cexpr a1} {binop op} {← cexpr a2})"
  | .Ecast a ty => do pure s!"(({← ctype ty}){← cexpr a})"
  | .Efield _ _ _ => throw "Efield"
  | .Esizeof _ _ => throw "Esizeof"
  | .Ealignof _ _ => throw "Ealignof"

def cargs (al : List expr) : Except String String := do
  let parts ← al.mapM (cexpr gname tname)
  pure (", ".intercalate parts)

def builtinName : external_function → Except String String
  | .EF_builtin n _ => pure n
  | _ => throw "an external call other than a built-in"

def indent (depth : Nat) : String := String.ofList (List.replicate (2 * depth) ' ')

/-- The call `Scall (some t) f args` followed by `Sset x (Etempvar t)`, for a temporary `t` that
`isCall` accepts: `x`, `f`, and `args`. -/
def callPair? : statement → Option (ident × expr × List expr)
  | .Ssequence (.Scall (some t) a al) (.Sset x (.Etempvar t' _)) =>
      if isCall t && t == t' then some (x, a, al) else none
  | _ => none

/-- The C text of a statement.  It is `partial`: its recursion is structural, but the matches
that recognize `clightgen`'s forms hide that from Lean's checker. -/
partial def cstmt (depth : Nat) : statement → Except String String
  | .Sskip => pure s!"{indent depth};\n"
  | .Sassign a1 a2 => do
      pure s!"{indent depth}{← cexpr gname tname a1} = {← cexpr gname tname a2};\n"
  | .Sset id a => do pure s!"{indent depth}{tname id} = {← cexpr gname tname a};\n"
  | .Scall optid a al => do
      let lhs := match optid with
        | some id => s!"{tname id} = "
        | none => ""
      pure s!"{indent depth}{lhs}{← cexpr gname tname a}({← cargs gname tname al});\n"
  | .Sbuiltin none (.EF_vstore _) _ [.Eaddrof a _, e] => do
      pure s!"{indent depth}{← cexpr gname tname a} = {← cexpr gname tname e};\n"
  | .Sbuiltin optid ef _ al => do
      let lhs := match optid with
        | some id => s!"{tname id} = "
        | none => ""
      pure s!"{indent depth}{lhs}{← builtinName ef}({← cargs gname tname al});\n"
  | .Ssequence s1 s2 =>
      match callPair? isCall (.Ssequence s1 s2) with
      | some (x, a, al) => do
          pure s!"{indent depth}{tname x} = {← cexpr gname tname a}({← cargs gname tname al});\n"
      | none => do
          let first ← match s1 with
            | .Ssequence _ _ =>
                match callPair? isCall s1 with
                | some _ => cstmt depth s1
                | none => do
                    pure (s!"{indent depth}\{\n" ++ (← cstmt (depth + 1) s1) ++ s!"{indent depth}}\n")
            | _ => cstmt depth s1
          pure (first ++ (← cstmt depth s2))
  | .Sifthenelse a s1 s2 => do
      let c ← cexpr gname tname a
      let thn ← cstmt (depth + 1) s1
      match s2 with
      | .Sskip => pure (s!"{indent depth}if ({c}) \{\n" ++ thn ++ s!"{indent depth}}\n")
      | _ =>
          pure (s!"{indent depth}if ({c}) \{\n" ++ thn ++ s!"{indent depth}} else \{\n" ++
            (← cstmt (depth + 1) s2) ++ s!"{indent depth}}\n")
  | .Sloop s1 s2 => do
      match s2 with
      | .Sskip =>
          let body ← match s1 with
            | .Ssequence .Sskip b => cstmt (depth + 1) b
            | _ => cstmt (depth + 1) s1
          pure (s!"{indent depth}for (;;) \{\n" ++ body ++ s!"{indent depth}}\n")
      | _ => throw "a loop with a statement after its body"
  | .Sbreak => pure s!"{indent depth}break;\n"
  | .Scontinue => pure s!"{indent depth}continue;\n"
  | .Sreturn none => pure s!"{indent depth}return;\n"
  | .Sreturn (some a) => do pure s!"{indent depth}return {← cexpr gname tname a};\n"
  | .Sswitch _ _ => throw "Sswitch"
  | .Slabel _ _ => throw "Slabel"
  | .Sgoto _ => throw "Sgoto"

def cparams (params : List (ident × type)) : Except String String := do
  if params.isEmpty then pure "void"
  else
    let parts ← params.mapM fun (id, ty) => do pure s!"{← ctype ty} {tname id}"
    pure (", ".intercalate parts)

/-- The declaration of function `id`. -/
def cprototype (id : ident) (f : function) : Except String String := do
  pure s!"{← ctype f.fn_return} {gname id}({← cparams tname f.fn_params});\n"

def cfunction (id : ident) (f : function) : Except String String := do
  let decls ← (f.fn_temps.filter fun (t, _) => !isCall t).mapM fun (t, ty) => do
    pure s!"  {← ctype ty} {tname t};\n"
  pure (s!"{← ctype f.fn_return} {gname id}({← cparams tname f.fn_params}) \{\n" ++
    String.join decls ++ (← cstmt gname tname isCall 1 f.fn_body) ++ "}\n")

def cinit (ty : type) : init_data → Except String String
  | .Init_int8 n => pure s!"{n.toNat}"
  | .Init_int16 n => pure s!"{n.toNat}"
  | .Init_int32 n => pure s!"{n.toNat}U"
  | .Init_int64 n => pure s!"{n.toNat}ULL"
  | .Init_float32 f => floatLiteral f
  | .Init_float64 f => doubleLiteral f
  | .Init_space _ => throw s!"space inside an initializer of {repr ty}"
  | .Init_addrof _ _ => throw "an address in an initializer"

def cglobal (id : ident) (v : globvar type) : Except String String := do
  let qual := if v.gvar_readonly then "const " else ""
  match v.gvar_info, v.gvar_init with
  | .Tarray elt n _, [.Init_space _] => pure s!"{qual}{← ctype elt} {gname id}[{n}];\n"
  | .Tarray elt n _, init => do
      let items ← init.mapM (cinit elt)
      let body := ", ".intercalate items
      pure s!"{qual}{← ctype elt} {gname id}[{n}] = \{{body}};\n"
  | ty, [.Init_space _] => pure s!"{qual}{← ctype ty} {gname id};\n"
  | ty, [] => pure s!"extern {qual}{← ctype ty} {gname id};\n"
  | ty, [d] => pure s!"{qual}{← ctype ty} {gname id} = {← cinit ty d};\n"
  | _, _ => throw "a scalar global with several initializers"

/-- The definitions of `p`: the variables with their initializers, then a declaration of each
function, then the functions with their bodies.  External functions print nothing: the
built-ins need no declaration. -/
def cprogram (p : program function) : Except String String := do
  let vars ← p.prog_defs.mapM fun (id, g) =>
    match g with
    | .Gvar v => cglobal gname id v
    | _ => pure ""
  let protos ← p.prog_defs.mapM fun (id, g) =>
    match g with
    | .Gfun (.Internal f) => cprototype gname tname id f
    | _ => pure ""
  let funs ← p.prog_defs.mapM fun (id, g) =>
    match g with
    | .Gfun (.Internal f) => cfunction gname tname isCall id f
    | _ => pure ""
  pure (String.join vars ++ String.join protos ++ String.join funs)

end

end LeanExe.Native
