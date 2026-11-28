module

public import Demos.Scheme.Semantics.Datum

@[expose] public section

/-! The codes of the executable interpreter's keywords, standard procedures, and fixed texts, and
the entries of its table of names.  An entry of the table is six words: a code, a length in bytes,
and the bytes packed eight to a word, the lowest byte first, so a name has at most 32 bytes.  The
code of a keyword is its position in §2.1's list, from 1; that of a standard procedure is its
machine code; and a text has code 0, or 1000 when its irritant is a keyword, 1001 when it is a
symbol, and 1002 when it is an offset.  `entries` defines the table, and `Names.names` is its
literal. -/

namespace Demos.Scheme.Machine

open Demos.Scheme.Semantics (bytes)

/-- The keywords of §2.1, in the order of their codes from 1. -/
def keywordList : List String :=
  ["=>", "and", "begin", "case", "cond", "define", "delay", "do", "else", "if", "lambda", "let",
    "let*", "letrec", "or", "quasiquote", "quote", "set!", "unquote", "unquote-splicing"]

def KW_ARROW : UInt64 := 1
def KW_AND : UInt64 := 2
def KW_BEGIN : UInt64 := 3
def KW_CASE : UInt64 := 4
def KW_COND : UInt64 := 5
def KW_DEFINE : UInt64 := 6
def KW_DELAY : UInt64 := 7
def KW_DO : UInt64 := 8
def KW_ELSE : UInt64 := 9
def KW_IF : UInt64 := 10
def KW_LAMBDA : UInt64 := 11
def KW_LET : UInt64 := 12
def KW_LETSTAR : UInt64 := 13
def KW_LETREC : UInt64 := 14
def KW_OR : UInt64 := 15
def KW_QUASIQUOTE : UInt64 := 16
def KW_QUOTE : UInt64 := 17
def KW_SET : UInt64 := 18
def KW_UNQUOTE : UInt64 := 19
def KW_UNQUOTE_SPLICING : UInt64 := 20

/-! The codes of the standard procedures.  A composition of `car`s and `cdr`s has the code
`256 + p`, where `p` is 1 followed by the bits of its letters from left to right, 1 for `a`, so the
lowest bit names the operation that applies first. -/

def P_NOT : UInt64 := 64
def P_ISBOOLEAN : UInt64 := 65
def P_EQ : UInt64 := 66
def P_EQV : UInt64 := 67
def P_ISPAIR : UInt64 := 68
def P_CONS : UInt64 := 69
def P_CAR : UInt64 := 70
def P_CDR : UInt64 := 71
def P_SETCAR : UInt64 := 72
def P_SETCDR : UInt64 := 73
def P_ISNULL : UInt64 := 74
def P_ISLIST : UInt64 := 75
def P_LIST : UInt64 := 76
def P_LENGTH : UInt64 := 77
def P_APPEND : UInt64 := 78
def P_REVERSE : UInt64 := 79
def P_LISTREF : UInt64 := 80
def P_MEMQ : UInt64 := 81
def P_MEMV : UInt64 := 82
def P_ASSQ : UInt64 := 83
def P_ASSV : UInt64 := 84
def P_ISPROCEDURE : UInt64 := 85
def P_APPLY : UInt64 := 86
def P_MAP : UInt64 := 87
def P_FOREACH : UInt64 := 88
def P_CALLCC : UInt64 := 89
def P_ISVECTOR : UInt64 := 90
def P_LISTTOVECTOR : UInt64 := 91

/-- The numeric procedures have the codes from `P_NUM`, in the order of
`Demos.Scheme.Semantics.Numeric.Op`'s constructors. -/
def P_NUM : UInt64 := 100
def N_ISNUMBER : UInt64 := 100
def N_ISCOMPLEX : UInt64 := 101
def N_ISREAL : UInt64 := 102
def N_ISRATIONAL : UInt64 := 103
def N_ISINTEGER : UInt64 := 104
def N_ISEXACT : UInt64 := 105
def N_ISINEXACT : UInt64 := 106
def N_EQ : UInt64 := 107
def N_LT : UInt64 := 108
def N_GT : UInt64 := 109
def N_LE : UInt64 := 110
def N_GE : UInt64 := 111
def N_ISZERO : UInt64 := 112
def N_ISPOSITIVE : UInt64 := 113
def N_ISNEGATIVE : UInt64 := 114
def N_ISODD : UInt64 := 115
def N_ISEVEN : UInt64 := 116
def N_MAX : UInt64 := 117
def N_MIN : UInt64 := 118
def N_ADD : UInt64 := 119
def N_MUL : UInt64 := 120
def N_SUB : UInt64 := 121
def N_DIV : UInt64 := 122
def N_ABS : UInt64 := 123
def N_QUOTIENT : UInt64 := 124
def N_REMAINDER : UInt64 := 125
def N_MODULO : UInt64 := 126
def N_GCD : UInt64 := 127
def N_LCM : UInt64 := 128
def N_FLOOR : UInt64 := 129
def N_CEILING : UInt64 := 130
def N_TRUNCATE : UInt64 := 131
def N_ROUND : UInt64 := 132
def P_CXR : UInt64 := 256

/-- The names of the standard procedures and their codes. -/
def primList : List (String × UInt64) :=
  [("not", P_NOT), ("boolean?", P_ISBOOLEAN), ("eq?", P_EQ), ("eqv?", P_EQV),
    ("pair?", P_ISPAIR), ("cons", P_CONS), ("car", P_CAR), ("cdr", P_CDR),
    ("set-car!", P_SETCAR), ("set-cdr!", P_SETCDR), ("null?", P_ISNULL), ("list?", P_ISLIST),
    ("list", P_LIST), ("length", P_LENGTH), ("append", P_APPEND), ("reverse", P_REVERSE),
    ("list-ref", P_LISTREF), ("memq", P_MEMQ), ("memv", P_MEMV), ("assq", P_ASSQ),
    ("assv", P_ASSV), ("procedure?", P_ISPROCEDURE), ("apply", P_APPLY), ("map", P_MAP),
    ("for-each", P_FOREACH), ("call-with-current-continuation", P_CALLCC),
    ("call/cc", P_CALLCC), ("vector?", P_ISVECTOR), ("list->vector", P_LISTTOVECTOR),
    ("number?", N_ISNUMBER), ("complex?", N_ISCOMPLEX), ("real?", N_ISREAL),
    ("rational?", N_ISRATIONAL), ("integer?", N_ISINTEGER), ("exact?", N_ISEXACT),
    ("inexact?", N_ISINEXACT), ("=", N_EQ), ("<", N_LT), (">", N_GT), ("<=", N_LE),
    (">=", N_GE), ("zero?", N_ISZERO), ("positive?", N_ISPOSITIVE),
    ("negative?", N_ISNEGATIVE), ("odd?", N_ISODD), ("even?", N_ISEVEN), ("max", N_MAX),
    ("min", N_MIN), ("+", N_ADD), ("*", N_MUL), ("-", N_SUB), ("/", N_DIV), ("abs", N_ABS),
    ("quotient", N_QUOTIENT), ("remainder", N_REMAINDER), ("modulo", N_MODULO),
    ("gcd", N_GCD), ("lcm", N_LCM), ("floor", N_FLOOR), ("ceiling", N_CEILING),
    ("truncate", N_TRUNCATE), ("round", N_ROUND)] ++
  ([2, 3, 4].flatMap fun n => (List.range (2 ^ n)).map fun bits =>
    let p := 2 ^ n + bits
    let letters := (List.range n).reverse.map fun i => if (bits >>> i) % 2 == 1 then 'a' else 'd'
    (String.ofList ('c' :: letters ++ ['r']), P_CXR + p.toUInt64))

/-! The fixed texts.  The code of a text gives the kind of its irritant. -/

def T_NONE : UInt64 := 0
def T_KEYWORD : UInt64 := 1000
def T_SYMBOL : UInt64 := 1001
def T_OFFSET : UInt64 := 1002

/-- The fixed texts, with the codes of their irritants, in the order of their entries after the
keywords and the procedures. -/
def textList : List (String × UInt64) :=
  [("incomplete datum", T_OFFSET), ("unexpected )", T_OFFSET), ("misplaced dot", T_OFFSET),
    ("bad # syntax", T_OFFSET), ("unknown character name", T_OFFSET), ("invalid token", T_OFFSET),
    ("invalid byte", T_OFFSET), ("bad string escape", T_OFFSET),
    ("empty combination", T_NONE), ("vector as expression", T_NONE),
    ("improper combination", T_NONE), ("keyword as variable: ", T_KEYWORD),
    ("bad form: ", T_KEYWORD), ("unsupported form: ", T_KEYWORD),
    ("duplicate variable: ", T_SYMBOL), ("duplicate case datum", T_NONE),
    ("definition in expression context", T_NONE), ("misplaced keyword: ", T_KEYWORD),
    ("bad quasiquote template", T_NONE),
    ("unbound variable: ", T_SYMBOL), ("undefined variable", T_NONE),
    ("not a procedure", T_NONE), ("wrong number of arguments", T_NONE),
    ("wrong type of argument", T_NONE), ("immutable object", T_NONE),
    ("division by zero", T_NONE), ("index out of range", T_NONE),
    ("number out of range", T_NONE), ("non-integer result", T_NONE),
    ("number outside the profile", T_NONE),
    ("#<unspecified>", T_NONE), ("#<procedure>", T_NONE), ("#<undefined>", T_NONE),
    ("#\\space", T_NONE), ("#\\newline", T_NONE), (" at ", T_NONE)]

/-- The entry indices of the texts, in the order of `textList`. -/
def M_INCOMPLETE : UInt64 := 110
def M_CLOSE : UInt64 := 111
def M_DOT : UInt64 := 112
def M_HASH : UInt64 := 113
def M_CHARNAME : UInt64 := 114
def M_TOKEN : UInt64 := 115
def M_BYTE : UInt64 := 116
def M_STRING : UInt64 := 117
def M_EMPTY : UInt64 := 118
def M_VECTOR : UInt64 := 119
def M_IMPROPER : UInt64 := 120
def M_KEYWORD : UInt64 := 121
def M_BADFORM : UInt64 := 122
def M_UNSUPPORTED : UInt64 := 123
def M_DUPLICATE : UInt64 := 124
def M_DUPDATUM : UInt64 := 125
def M_DEFINITION : UInt64 := 126
def M_MISPLACED : UInt64 := 127
def M_TEMPLATE : UInt64 := 128
def M_UNBOUND : UInt64 := 129
def M_UNDEFINED : UInt64 := 130
def M_NOTPROC : UInt64 := 131
def M_ARITY : UInt64 := 132
def M_TYPE : UInt64 := 133
def M_IMMUTABLE : UInt64 := 134
def M_DIVZERO : UInt64 := 135
def M_INDEX : UInt64 := 136
def M_RANGE : UInt64 := 137
def M_NOTINT : UInt64 := 138
def M_NUMBER : UInt64 := 139
def M_T_UNSPEC : UInt64 := 140
def M_T_PROC : UInt64 := 141
def M_T_UNDEF : UInt64 := 142
def M_T_SPACE : UInt64 := 143
def M_T_NEWLINE : UInt64 := 144
def M_T_AT : UInt64 := 145

/-- The entry index of the first text. -/
def textBase : Nat := keywordList.length + primList.length

/-- The word of the bytes from position `8 j` of `s`, the lowest byte first. -/
def packWord (s : List UInt8) (j : Nat) : UInt64 :=
  ((s.drop (8 * j)).take 8).foldr (fun b w => (w <<< 8) ||| b.toUInt64) 0

/-- The six words of an entry. -/
def entryWords (code : UInt64) (s : String) : List UInt64 :=
  let b := bytes s
  [code, b.length.toUInt64, packWord b 0, packWord b 1, packWord b 2, packWord b 3]

/-- The entries of the table: the keywords, the procedures, and the texts. -/
def entries : List (UInt64 × String) :=
  ((List.range keywordList.length).zip keywordList).map (fun (i, s) => ((i + 1).toUInt64, s)) ++
    primList.map (fun (s, c) => (c, s)) ++ textList.map fun (s, c) => (c, s)

/-- The words of the table. -/
def tableWords : List UInt64 := entries.flatMap fun (c, s) => entryWords c s

/-- The entry index of a text. -/
def textIndex (s : String) : UInt64 := (textBase + (textList.findIdx? (·.1 == s)).getD 0).toUInt64

end Demos.Scheme.Machine
