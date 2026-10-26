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
-/

namespace LeanExe.Native

open LClight

/-- Lowercase hexadecimal digits of `n`, with at least `width` digits. -/
def hexDigits (n width : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (width - s.length) '0') ++ s

def ctype : type → Except String String
  | .Tvoid => pure "void"
  | .Tint .I8 .Signed _ => pure "signed char"
  | .Tint .I8 .Unsigned _ => pure "unsigned char"
  | .Tint .I16 .Signed _ => pure "short"
  | .Tint .I16 .Unsigned _ => pure "unsigned short"
  | .Tint .I32 .Signed _ => pure "int"
  | .Tint .I32 .Unsigned _ => pure "unsigned int"
  | .Tint .IBool _ _ => pure "_Bool"
  | .Tlong .Signed _ => pure "long long"
  | .Tlong .Unsigned _ => pure "unsigned long long"
  | .Tfloat .F32 _ => pure "float"
  | .Tfloat .F64 _ => pure "double"
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

variable (name : ident → String)

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
  | .Evar id _ => pure (name id)
  | .Etempvar id _ => pure (name id)
  | .Ederef a _ => do pure s!"(*{← cexpr a})"
  | .Eaddrof a _ => do pure s!"(&{← cexpr a})"
  | .Eunop op a _ => do
      let s ← cexpr a
      match op with
      | .Onotbool => pure s!"(!{s})"
      | .Onotint => pure s!"(~{s})"
      | .Oneg => pure s!"(-{s})"
      | .Oabsfloat => throw "Oabsfloat"
  | .Ebinop op a1 a2 _ => do pure s!"({← cexpr a1} {binop op} {← cexpr a2})"
  | .Ecast a ty => do pure s!"(({← ctype ty}){← cexpr a})"
  | .Efield _ _ _ => throw "Efield"
  | .Esizeof _ _ => throw "Esizeof"
  | .Ealignof _ _ => throw "Ealignof"

def cargs (al : List expr) : Except String String := do
  let parts ← al.mapM (cexpr name)
  pure (", ".intercalate parts)

def builtinName : external_function → Except String String
  | .EF_builtin n _ => pure n
  | _ => throw "an external call other than a built-in"

def indent (depth : Nat) : String := String.ofList (List.replicate (2 * depth) ' ')

def cstmt (depth : Nat) : statement → Except String String
  | .Sskip => pure s!"{indent depth};\n"
  | .Sassign a1 a2 => do pure s!"{indent depth}{← cexpr name a1} = {← cexpr name a2};\n"
  | .Sset id a => do pure s!"{indent depth}{name id} = {← cexpr name a};\n"
  | .Scall optid a al => do
      let lhs := match optid with
        | some id => s!"{name id} = "
        | none => ""
      pure s!"{indent depth}{lhs}{← cexpr name a}({← cargs name al});\n"
  | .Sbuiltin optid ef _ al => do
      let lhs := match optid with
        | some id => s!"{name id} = "
        | none => ""
      pure s!"{indent depth}{lhs}{← builtinName ef}({← cargs name al});\n"
  | .Ssequence s1 s2 => do pure ((← cstmt depth s1) ++ (← cstmt depth s2))
  | .Sifthenelse a s1 s2 => do
      pure (s!"{indent depth}if ({← cexpr name a}) \{\n" ++ (← cstmt (depth + 1) s1) ++
        s!"{indent depth}} else \{\n" ++ (← cstmt (depth + 1) s2) ++ s!"{indent depth}}\n")
  | .Sloop s1 s2 => do
      match s2 with
      | .Sskip =>
          pure (s!"{indent depth}for (;;) \{\n" ++ (← cstmt (depth + 1) s1) ++
            s!"{indent depth}}\n")
      | _ => throw "a loop with a statement after its body"
  | .Sbreak => pure s!"{indent depth}break;\n"
  | .Scontinue => pure s!"{indent depth}continue;\n"
  | .Sreturn none => pure s!"{indent depth}return;\n"
  | .Sreturn (some a) => do pure s!"{indent depth}return {← cexpr name a};\n"
  | .Sswitch _ _ => throw "Sswitch"
  | .Slabel _ _ => throw "Slabel"
  | .Sgoto _ => throw "Sgoto"

def cparams (params : List (ident × type)) : Except String String := do
  if params.isEmpty then pure "void"
  else
    let parts ← params.mapM fun (id, ty) => do pure s!"{← ctype ty} {name id}"
    pure (", ".intercalate parts)

def cfunction (id : ident) (f : function) : Except String String := do
  let decls ← f.fn_temps.mapM fun (t, ty) => do pure s!"  {← ctype ty} {name t};\n"
  pure (s!"{← ctype f.fn_return} {name id}({← cparams name f.fn_params}) \{\n" ++
    String.join decls ++ (← cstmt name 1 f.fn_body) ++ "}\n")

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
  | .Tarray elt n _, [.Init_space _] => pure s!"{qual}{← ctype elt} {name id}[{n}];\n"
  | .Tarray elt n _, init => do
      let items ← init.mapM (cinit elt)
      let body := ", ".intercalate items
      pure s!"{qual}{← ctype elt} {name id}[{n}] = \{{body}};\n"
  | ty, [.Init_space _] => pure s!"{qual}{← ctype ty} {name id};\n"
  | ty, [d] => pure s!"{qual}{← ctype ty} {name id} = {← cinit ty d};\n"
  | _, _ => throw "a scalar global with several initializers"

/-- The definitions of `p` in order, functions with their bodies and variables with their
initializers.  External functions print nothing: the built-ins need no declaration. -/
def cprogram (p : program function) : Except String String := do
  let parts ← p.prog_defs.mapM fun (id, g) =>
    match g with
    | .Gvar v => cglobal name id v
    | .Gfun (.Internal f) => cfunction name id f
    | .Gfun (.External _ _ _ _) => pure ""
  pure (String.join parts)

end

end LeanExe.Native
