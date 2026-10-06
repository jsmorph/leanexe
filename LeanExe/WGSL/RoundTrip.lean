import LeanExe.WGSL.Parse

/-!
The parser reads every printed kernel back as itself: `Module.parse_print` states
`Module.parse m.print = some m` for every kernel whose indices fit in eight hexadecimal digits.
The proof goes through the tokens: the lexer recovers the printed tokens, since none is empty or
contains a space or newline, and the parser reads each printed form back with enough fuel.
-/

namespace LeanExe.WGSL

theorem hexValue_hexDigit : ∀ d, d < 16 → hexValue (hexDigit d) = some d := by decide

theorem digitsValue_digits8 (n : Nat) : digitsValue (digits8 n) = some (n % 2 ^ 32) := by
  simp only [digits8, List.map_cons, List.map_nil, digitsValue]
  simp only [hexValue_hexDigit _ (Nat.mod_lt _ (by decide)), Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq]
  omega



theorem digits8_eq (n : Nat) : digits8 n =
    [hexDigit (n / 16 ^ 7 % 16), hexDigit (n / 16 ^ 6 % 16), hexDigit (n / 16 ^ 5 % 16),
      hexDigit (n / 16 ^ 4 % 16), hexDigit (n / 16 ^ 3 % 16), hexDigit (n / 16 ^ 2 % 16),
      hexDigit (n / 16 ^ 1 % 16), hexDigit (n / 16 ^ 0 % 16)] := rfl

theorem parseLit_litToken (v : UInt32) : parseLit (litToken v) = some v := by
  unfold parseLit litToken
  rw [String.toList_ofList, digits8_eq]
  simp only [List.cons_append, List.nil_append]
  rw [← digits8_eq, digitsValue_digits8]
  simp only [Option.map_some, Option.some.injEq]
  apply UInt32.toNat_inj.mp
  simp

theorem parseLit_letter {c : Char} (h : c ≠ '0') (rest : List Char) :
    parseLit (String.ofList (c :: rest)) = none := by
  unfold parseLit
  rw [String.toList_ofList]
  split
  · rename_i h'
    cases h'
    exact absurd rfl h
  · rfl

theorem parseName_same (c : Char) (n : Nat) (h : n < 2 ^ 32) :
    parseName c (String.ofList (c :: digits8 n)) = some n := by
  unfold parseName
  rw [String.toList_ofList]
  simp [digitsValue_digits8, Nat.mod_eq_of_lt h]

theorem parseName_other {c d : Char} (h : c ≠ d) (rest : List Char) :
    parseName d (String.ofList (c :: rest)) = none := by
  unfold parseName
  rw [String.toList_ofList]
  simp [h]

theorem classify_litToken (v : UInt32) : classify (litToken v) = .lit v := by
  simp [classify, parseLit_litToken]

theorem classify_varToken (n : Nat) (h : n < 2 ^ 32) : classify (varToken n) = .var n := by
  unfold classify varToken
  rw [parseLit_letter (by decide), parseName_same _ _ h]

theorem classify_bufToken (n : Nat) (h : n < 2 ^ 32) : classify (bufToken n) = .buf n := by
  unfold classify bufToken
  rw [parseLit_letter (by decide), parseName_other (by decide), parseName_same _ _ h]


def Expr.size : Expr → Nat
  | .lit _ | .bool _ | .var _ | .gidX | .fst _ | .snd _ | .length _ => 1
  | .vec2 a b | .bin _ a b | .min a b => a.size + b.size + 1
  | .not a | .toF32 a | .toU32 a | .sqrt a | .round a | .abs a => a.size + 1
  | .select f t c => f.size + t.size + c.size + 1
  | .index _ p => p.size + 1

/-- Every variable and buffer index fits in eight hexadecimal digits. -/
def Expr.WF : Expr → Prop
  | .lit _ | .bool _ | .gidX => True
  | .var n | .fst n | .snd n | .length n => n < 2 ^ 32
  | .vec2 a b | .bin _ a b | .min a b => a.WF ∧ b.WF
  | .not a | .toF32 a | .toU32 a | .sqrt a | .round a | .abs a => a.WF
  | .select f t c => f.WF ∧ t.WF ∧ c.WF
  | .index b p => b < 2 ^ 32 ∧ p.WF

theorem classify_paren : classify "(" = .kw "(" := rfl
theorem classify_bang : classify "!" = .kw "!" := rfl
theorem classify_true : classify "true" = .kw "true" := rfl
theorem classify_false : classify "false" = .kw "false" := rfl
theorem classify_gid : classify "gid" = .kw "gid" := rfl
theorem classify_vec2 : classify "vec2" = .kw "vec2" := rfl
theorem classify_bitcast : classify "bitcast" = .kw "bitcast" := rfl
theorem classify_sqrt : classify "sqrt" = .kw "sqrt" := rfl
theorem classify_round : classify "round" = .kw "round" := rfl
theorem classify_abs : classify "abs" = .kw "abs" := rfl
theorem classify_select : classify "select" = .kw "select" := rfl
theorem classify_min : classify "min" = .kw "min" := rfl
theorem classify_arrayLength : classify "arrayLength" = .kw "arrayLength" := rfl
theorem classify_let : classify "let" = .kw "let" := rfl
theorem classify_var : classify "var" = .kw "var" := rfl
theorem classify_if : classify "if" = .kw "if" := rfl
theorem classify_return : classify "return" = .kw "return" := rfl
theorem classify_while : classify "while" = .kw "while" := rfl
theorem classify_brace : classify "}" = .kw "}" := rfl

theorem parseOp_token (op : BinOp) : parseOp op.token = some op := by cases op <;> rfl

theorem token_ne_dot (op : BinOp) : op.token ≠ "." := by cases op <;> decide

theorem Expr.parse_tokens : ∀ (e : Expr), e.WF → ∀ fuel, e.size < fuel → ∀ rest : List String,
    rest.head? ≠ some "." → parseExpr fuel (e.tokens ++ rest) = some (e, rest) := by
  intro e
  induction e with
  | lit v =>
      intro _ fuel hf rest _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp [Expr.tokens, parseExpr, classify_litToken]
  | bool b =>
      intro _ fuel hf rest _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      cases b <;> simp [Expr.tokens, parseExpr, classify_true, classify_false]
  | var n =>
      intro hwf fuel hf rest hrest
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp only [Expr.WF] at hwf
      simp only [Expr.tokens, List.singleton_append, parseExpr, classify_varToken n hwf]
      cases rest with
      | nil => rfl
      | cons t r =>
          have ht : t ≠ "." := fun h => hrest (by simp [h])
          split <;> simp_all
  | gidX =>
      intro _ fuel hf rest _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp [Expr.tokens, parseExpr, classify_gid]
  | fst n =>
      intro hwf fuel hf rest _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp only [Expr.WF] at hwf
      simp [Expr.tokens, parseExpr, classify_varToken n hwf]
  | snd n =>
      intro hwf fuel hf rest _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp only [Expr.WF] at hwf
      simp [Expr.tokens, parseExpr, classify_varToken n hwf]
  | vec2 a b iha ihb =>
      intro hwf fuel hf rest _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp only [Expr.WF, Expr.size] at hwf hf
      simp [Expr.tokens, parseExpr, classify_vec2, expect,
        iha hwf.1 f (by omega) _ (by simp : ("," :: (b.tokens ++ ")" :: rest)).head? ≠ some "."),
        ihb hwf.2 f (by omega) _ (by simp : (")" :: rest).head? ≠ some ".")]
  | bin op a b iha ihb =>
      intro hwf fuel hf rest _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp only [Expr.WF, Expr.size] at hwf hf
      simp [Expr.tokens, parseExpr, classify_paren, expect, parseOp_token,
        iha hwf.1 f (by omega) _ (by simp [token_ne_dot] :
          (op.token :: (b.tokens ++ ")" :: rest)).head? ≠ some "."),
        ihb hwf.2 f (by omega) _ (by simp : (")" :: rest).head? ≠ some ".")]
  | not a iha =>
      intro hwf fuel hf rest hrest
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp only [Expr.WF, Expr.size] at hwf hf
      simp [Expr.tokens, parseExpr, classify_bang, iha hwf f (by omega) rest hrest]
  | toF32 a iha =>
      intro hwf fuel hf rest _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp only [Expr.WF, Expr.size] at hwf hf
      simp [Expr.tokens, parseExpr, classify_bitcast, expect,
        iha hwf f (by omega) _ (by simp : (")" :: rest).head? ≠ some ".")]
  | toU32 a iha =>
      intro hwf fuel hf rest _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp only [Expr.WF, Expr.size] at hwf hf
      simp [Expr.tokens, parseExpr, classify_bitcast, expect,
        iha hwf f (by omega) _ (by simp : (")" :: rest).head? ≠ some ".")]
  | sqrt a iha =>
      intro hwf fuel hf rest _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp only [Expr.WF, Expr.size] at hwf hf
      simp [Expr.tokens, parseExpr, classify_sqrt, expect,
        iha hwf f (by omega) _ (by simp : (")" :: rest).head? ≠ some ".")]
  | round a iha =>
      intro hwf fuel hf rest _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp only [Expr.WF, Expr.size] at hwf hf
      simp [Expr.tokens, parseExpr, classify_round, expect,
        iha hwf f (by omega) _ (by simp : (")" :: rest).head? ≠ some ".")]
  | abs a iha =>
      intro hwf fuel hf rest _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp only [Expr.WF, Expr.size] at hwf hf
      simp [Expr.tokens, parseExpr, classify_abs, expect,
        iha hwf f (by omega) _ (by simp : (")" :: rest).head? ≠ some ".")]
  | select a b c iha ihb ihc =>
      intro hwf fuel hf rest _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp only [Expr.WF, Expr.size] at hwf hf
      simp [Expr.tokens, parseExpr, classify_select, expect,
        iha hwf.1 f (by omega) _ (by simp :
          ("," :: (b.tokens ++ "," :: (c.tokens ++ ")" :: rest))).head? ≠ some "."),
        ihb hwf.2.1 f (by omega) _ (by simp : ("," :: (c.tokens ++ ")" :: rest)).head? ≠ some "."),
        ihc hwf.2.2 f (by omega) _ (by simp : (")" :: rest).head? ≠ some ".")]
  | min a b iha ihb =>
      intro hwf fuel hf rest _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp only [Expr.WF, Expr.size] at hwf hf
      simp [Expr.tokens, parseExpr, classify_min, expect,
        iha hwf.1 f (by omega) _ (by simp : ("," :: (b.tokens ++ ")" :: rest)).head? ≠ some "."),
        ihb hwf.2 f (by omega) _ (by simp : (")" :: rest).head? ≠ some ".")]
  | length n =>
      intro hwf fuel hf rest _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp only [Expr.WF] at hwf
      simp [Expr.tokens, parseExpr, classify_arrayLength, classify_bufToken n hwf]
  | index n p ihp =>
      intro hwf fuel hf rest _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Expr.size] at hf; omega⟩
      simp only [Expr.WF, Expr.size] at hwf hf
      simp [Expr.tokens, parseExpr, classify_bufToken n hwf.1, expect,
        ihp hwf.2 f (by omega) _ (by simp : ("]" :: rest).head? ≠ some ".")]

theorem Ty.parse_tokens (ty : Ty) (rest : List String) :
    parseTy (ty.tokens ++ rest) = some (ty, rest) := by
  cases ty <;> rfl

mutual
  def Stmt.size : Stmt → Nat
    | .let_ _ _ e | .var _ _ e | .assign _ e => e.size + 1
    | .store _ p e => p.size + e.size + 1
    | .ite c ts es => c.size + Stmt.listSize ts + Stmt.listSize es + 1
    | .while_ c body => c.size + Stmt.listSize body + 1
    | .ret => 1

  def Stmt.listSize : List Stmt → Nat
    | [] => 0
    | s :: rest => s.size + Stmt.listSize rest + 1
end

mutual
  def Stmt.WF : Stmt → Prop
    | .let_ n _ e | .var n _ e | .assign n e => n < 2 ^ 32 ∧ e.WF
    | .store b p e => b < 2 ^ 32 ∧ p.WF ∧ e.WF
    | .ite c ts es => c.WF ∧ Stmt.ListWF ts ∧ Stmt.ListWF es
    | .while_ c body => c.WF ∧ Stmt.ListWF body
    | .ret => True

  def Stmt.ListWF : List Stmt → Prop
    | [] => True
    | s :: rest => s.WF ∧ Stmt.ListWF rest
end

theorem varToken_ne_brace (n : Nat) : varToken n ≠ "}" := by
  intro h
  have := congrArg (fun t => t.toList.length) h
  simp [varToken, digits8] at this

theorem bufToken_ne_brace (n : Nat) : bufToken n ≠ "}" := by
  intro h
  have := congrArg (fun t => t.toList.length) h
  simp [bufToken, digits8] at this

theorem Stmt.tokens_head (s : Stmt) : ∃ t r, s.tokens = t :: r ∧ t ≠ "}" := by
  cases s with
  | let_ => exact ⟨_, _, rfl, by decide⟩
  | var => exact ⟨_, _, rfl, by decide⟩
  | assign n e => exact ⟨_, _, rfl, varToken_ne_brace n⟩
  | store b p e => exact ⟨_, _, rfl, bufToken_ne_brace b⟩
  | ite c ts es => exact ⟨_, _, rfl, by decide⟩
  | while_ c body => exact ⟨_, _, rfl, by decide⟩
  | ret => exact ⟨_, _, rfl, by decide⟩

mutual
  theorem Stmt.parse_tokens : ∀ (s : Stmt), s.WF → ∀ fuel, s.size < fuel → ∀ rest : List String,
      parseStmt fuel (s.tokens ++ rest) = some (s, rest)
    | .let_ n ty e, hwf, fuel + 1, hf, rest => by
        simp only [Stmt.WF, Stmt.size] at hwf hf
        simp [Stmt.tokens, parseStmt, classify_let, classify_varToken n hwf.1, expect,
          Ty.parse_tokens, Expr.parse_tokens e hwf.2 fuel (by omega) _
            (by simp : (";" :: rest).head? ≠ some ".")]
    | .var n ty e, hwf, fuel + 1, hf, rest => by
        simp only [Stmt.WF, Stmt.size] at hwf hf
        simp [Stmt.tokens, parseStmt, classify_var, classify_varToken n hwf.1, expect,
          Ty.parse_tokens, Expr.parse_tokens e hwf.2 fuel (by omega) _
            (by simp : (";" :: rest).head? ≠ some ".")]
    | .assign n e, hwf, fuel + 1, hf, rest => by
        simp only [Stmt.WF, Stmt.size] at hwf hf
        simp [Stmt.tokens, parseStmt, classify_varToken n hwf.1, expect,
          Expr.parse_tokens e hwf.2 fuel (by omega) _ (by simp : (";" :: rest).head? ≠ some ".")]
    | .store b p e, hwf, fuel + 1, hf, rest => by
        simp only [Stmt.WF, Stmt.size] at hwf hf
        simp [Stmt.tokens, parseStmt, classify_bufToken b hwf.1, expect,
          Expr.parse_tokens p hwf.2.1 fuel (by omega) _
            (by simp : ("]" :: "=" :: (e.tokens ++ ";" :: rest)).head? ≠ some "."),
          Expr.parse_tokens e hwf.2.2 fuel (by omega) _ (by simp : (";" :: rest).head? ≠ some ".")]
    | .ite c ts es, hwf, fuel + 1, hf, rest => by
        simp only [Stmt.WF, Stmt.size] at hwf hf
        simp [Stmt.tokens, parseStmt, classify_if, expect,
          Expr.parse_tokens c hwf.1 fuel (by omega) _
            (by simp : ("{" :: (Stmt.listTokens ts ++ "}" :: "else" :: "{" ::
              (Stmt.listTokens es ++ "}" :: rest))).head? ≠ some "."),
          Stmt.parse_listTokens ts hwf.2.1 fuel (by omega),
          Stmt.parse_listTokens es hwf.2.2 fuel (by omega)]
    | .while_ c body, hwf, fuel + 1, hf, rest => by
        simp only [Stmt.WF, Stmt.size] at hwf hf
        simp [Stmt.tokens, parseStmt, classify_while, expect,
          Expr.parse_tokens c hwf.1 fuel (by omega) _
            (by simp : ("{" :: (Stmt.listTokens body ++ "}" :: rest)).head? ≠ some "."),
          Stmt.parse_listTokens body hwf.2 fuel (by omega)]
    | .ret, _, fuel + 1, _, rest => by
        simp [Stmt.tokens, parseStmt, classify_return]

  theorem Stmt.parse_listTokens : ∀ (ss : List Stmt), Stmt.ListWF ss → ∀ fuel,
      Stmt.listSize ss < fuel → ∀ rest : List String,
      parseStmts fuel (Stmt.listTokens ss ++ "}" :: rest) = some (ss, "}" :: rest)
    | [], _, fuel + 1, _, rest => by simp [Stmt.listTokens, parseStmts]
    | s :: ss, hwf, fuel + 1, hf, rest => by
        simp only [Stmt.ListWF, Stmt.listSize] at hwf hf
        obtain ⟨t, r, ht, hne⟩ := Stmt.tokens_head s
        have hs := Stmt.parse_tokens s hwf.1 fuel (by omega) (Stmt.listTokens ss ++ "}" :: rest)
        rw [ht] at hs
        simp only [Stmt.listTokens, List.append_assoc, ht, List.cons_append, parseStmts, hne,
          ite_false]
        rw [show t :: (r ++ (Stmt.listTokens ss ++ "}" :: rest)) =
          t :: r ++ (Stmt.listTokens ss ++ "}" :: rest) by simp, hs]
        simp [Stmt.parse_listTokens ss hwf.2 fuel (by omega) rest]
end

theorem inputTokens_eq (n : Nat) :
    inputTokens n = (List.range n).flatMap fun i => bufferTokens i false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [inputTokens, ih, List.range_succ]

theorem isPrefixOf_self_append (l x : List String) : l.isPrefixOf (l ++ x) = true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem bufferTokens_read_not_prefix (i : Nat) (x : List String) :
    (bufferTokens i false).isPrefixOf (bufferTokens i true ++ x) = false := by
  simp [bufferTokens, List.isPrefixOf]

theorem bufferTokens_write_not_prefix (i : Nat) (x : List String) :
    (bufferTokens i true).isPrefixOf (bufferTokens i false ++ x) = false := by
  simp [bufferTokens, List.isPrefixOf]

theorem parseBuffers_tokens (n : Nat) (rest : List String) :
    ∀ d k fuel, k + d = n → d < fuel →
      parseBuffers fuel k (((List.range' k d).flatMap fun i => bufferTokens i false) ++
        (bufferTokens n true ++ rest)) = some (n, rest) := by
  intro d
  induction d with
  | zero =>
      intro k fuel hk hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      subst hk
      simp [parseBuffers, bufferTokens_read_not_prefix, isPrefixOf_self_append]
  | succ d ih =>
      intro k fuel hk hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [List.range'_succ, List.flatMap_cons, List.append_assoc, parseBuffers,
        isPrefixOf_self_append, ite_true, List.drop_left]
      exact ih (k + 1) f (by omega) (by omega)

theorem Expr.size_le (e : Expr) : e.size ≤ e.tokens.length := by
  induction e with
  | bool b => cases b <;> simp [Expr.size, Expr.tokens]
  | _ => simp_all [Expr.size, Expr.tokens] <;> omega

mutual
  theorem Stmt.size_le : ∀ s : Stmt, s.size + 1 ≤ s.tokens.length
    | .let_ _ ty e | .var _ ty e => by
        have := e.size_le
        simp [Stmt.size, Stmt.tokens]
        omega
    | .assign _ e => by
        have := e.size_le
        simp [Stmt.size, Stmt.tokens]
        omega
    | .store _ p e => by
        have := p.size_le
        have := e.size_le
        simp [Stmt.size, Stmt.tokens]
        omega
    | .ite c ts es => by
        have := c.size_le
        have := Stmt.listSize_le ts
        have := Stmt.listSize_le es
        simp [Stmt.size, Stmt.tokens]
        omega
    | .while_ c body => by
        have := c.size_le
        have := Stmt.listSize_le body
        simp [Stmt.size, Stmt.tokens]
        omega
    | .ret => by simp [Stmt.size, Stmt.tokens]

  theorem Stmt.listSize_le : ∀ ss : List Stmt, Stmt.listSize ss ≤ (Stmt.listTokens ss).length
    | [] => by simp [Stmt.listSize, Stmt.listTokens]
    | s :: ss => by
        have := Stmt.size_le s
        have := Stmt.listSize_le ss
        have := (Stmt.tokens_head s)
        obtain ⟨t, r, ht, -⟩ := this
        have hlen : 1 ≤ s.tokens.length := by rw [ht]; simp
        simp [Stmt.listSize, Stmt.listTokens]
        omega
end

/-- Every index fits in eight hexadecimal digits. -/
def Module.WF (m : Module) : Prop :=
  m.inputs < 2 ^ 32 ∧ m.workgroupSize < 2 ^ 32 ∧ Stmt.ListWF m.body

theorem inputTokens_length (n : Nat) :
    ((List.range n).flatMap fun i => bufferTokens i false).length = 23 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      simp [bufferTokens]
      omega

theorem parseModule_tokens (m : Module) (h : m.WF) : parseModule m.tokens = some m := by
  obtain ⟨hInputs, hSize, hBody⟩ := h
  have hLength : m.tokens.length =
      23 * m.inputs + 23 + 23 + (Stmt.listTokens m.body).length + 1 := by
    simp only [Module.tokens, List.length_append, inputTokens_eq, inputTokens_length]
    simp [bufferTokens]
  have hLen := Stmt.listSize_le m.body
  have hWorkgroup : (UInt32.ofNat m.workgroupSize).toNat = m.workgroupSize := by
    simp [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hSize]
  simp only [parseModule]
  generalize hF : m.tokens.length + 1 = fuel
  have hBuffers := parseBuffers_tokens m.inputs
    (["@", "compute", "@", "workgroup_size", "(", litToken (UInt32.ofNat m.workgroupSize), ")",
      "fn", "main", "(", "@", "builtin", "(", "global_invocation_id", ")", "gid", ":", "vec3",
      "<", "u32", ">", ")", "{"] ++ Stmt.listTokens m.body ++ ["}"]) m.inputs 0 fuel (by omega)
    (by omega)
  have hStmts := Stmt.parse_listTokens m.body hBody fuel (by omega) []
  simp only [Module.tokens, inputTokens_eq, List.range_eq_range', List.append_assoc] at hBuffers ⊢
  rw [hBuffers]
  simp [classify_litToken, hStmts, hWorkgroup]

/-- A token the lexer reads back: nonempty, with no space or newline. -/
def good (t : String) : Bool := !t.toList.isEmpty && t.toList.all fun c => !isSeparator c

theorem isSeparator_hexDigit : ∀ d, d < 16 → isSeparator (hexDigit d) = false := by decide

theorem digits8_good (n : Nat) : (digits8 n).all (fun c => !isSeparator c) = true := by
  simp [digits8_eq, isSeparator_hexDigit _ (Nat.mod_lt _ (by decide : 16 > 0))]

theorem good_litToken (v : UInt32) : good (litToken v) = true := by
  have := digits8_good v.toNat
  simp_all [good, litToken, isSeparator]

theorem good_varToken (n : Nat) : good (varToken n) = true := by
  have := digits8_good n
  simp_all [good, varToken, isSeparator]

theorem good_bufToken (n : Nat) : good (bufToken n) = true := by
  have := digits8_good n
  simp_all [good, bufToken, isSeparator]

theorem good_opToken (op : BinOp) : good op.token = true := by cases op <;> decide

theorem Ty.good (ty : Ty) : ty.tokens.all good = true := by cases ty <;> decide

theorem Expr.good (e : Expr) : e.tokens.all good = true := by
  induction e with
  | bool b => cases b <;> decide
  | _ =>
    simp_all (config := { decide := true }) [Expr.tokens, List.all_append, List.all_cons,
      good_litToken, good_varToken, good_bufToken, good_opToken]

mutual
  theorem Stmt.good : ∀ s : Stmt, s.tokens.all good = true
    | .let_ n ty e | .var n ty e => by
        simp (config := { decide := true }) [Stmt.tokens, List.all_append, List.all_cons,
          good_varToken, Ty.good, Expr.good]
    | .assign n e => by
        simp (config := { decide := true }) [Stmt.tokens, List.all_append, List.all_cons,
          good_varToken, Expr.good]
    | .store b p e => by
        simp (config := { decide := true }) [Stmt.tokens, List.all_append, List.all_cons,
          good_bufToken, Expr.good]
    | .ite c ts es => by
        simp (config := { decide := true }) [Stmt.tokens, List.all_append, List.all_cons,
          Expr.good, Stmt.listGood ts, Stmt.listGood es]
    | .while_ c body => by
        simp (config := { decide := true }) [Stmt.tokens, List.all_append, List.all_cons,
          Expr.good, Stmt.listGood body]
    | .ret => by decide

  theorem Stmt.listGood : ∀ ss : List Stmt, (Stmt.listTokens ss).all good = true
    | [] => rfl
    | s :: ss => by
        simp only [Stmt.listTokens, List.all_append, Stmt.good s, Stmt.listGood ss, Bool.and_self]
end

theorem bufferTokens_good (i : Nat) (w : Bool) : (bufferTokens i w).all good = true := by
  cases w <;> simp (config := { decide := true }) [bufferTokens, good_litToken, good_bufToken]

theorem Module.good (m : Module) : m.tokens.all good = true := by
  simp (config := { decide := true }) [Module.tokens, inputTokens_eq, List.all_append,
    List.all_flatMap, bufferTokens_good, good_litToken, Stmt.listGood]

theorem isSeparator_separator (t : String) : isSeparator (separator t) = true := by
  unfold separator
  split <;> rfl

theorem noSeparator {t : String} {ts : List String} (h : (t :: ts).all good = true) :
    ∀ c ∈ t.toList, isSeparator c = false := by
  simp only [List.all_cons, Bool.and_eq_true, good, Bool.not_eq_true', List.all_eq_true] at h
  intro c hc
  simpa using h.1.2 c hc

theorem splitOnP_renderChars : ∀ ts : List String, ts.all good = true →
    (renderChars ts).splitOnP isSeparator = ts.map String.toList ++ [[]]
  | [], _ => by simp [renderChars]
  | [t], h => by
      simp only [renderChars, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [List.splitOnP_append_cons_of_forall_mem (noSeparator h) _ (by rfl)]
      simp
  | t :: u :: rest, h => by
      simp only [renderChars]
      rw [List.splitOnP_append_cons_of_forall_mem (noSeparator h) _ (isSeparator_separator t)]
      have ih := splitOnP_renderChars (u :: rest) (by simp_all)
      rw [ih]
      simp

theorem lex_render (ts : List String) (h : ts.all good = true) :
    lex (String.ofList (renderChars ts)) = ts := by
  unfold lex
  rw [String.toList_ofList, splitOnP_renderChars ts h, List.filter_append]
  have hKeep : (ts.map String.toList).filter (fun l => decide (l ≠ [])) = ts.map String.toList := by
    rw [List.filter_eq_self]
    intro l hl
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
    have := (List.all_eq_true.mp h) t ht
    simp only [good, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at this
    simpa using this.1
  rw [hKeep]
  simp [Function.comp_def, String.ofList_toList]

/-- The parser reads a printed kernel back as the kernel. -/
theorem Module.parse_print (m : Module) (h : m.WF) : Module.parse m.print = some m := by
  unfold Module.parse Module.print
  rw [lex_render _ (Module.good m), parseModule_tokens m h]

/-- `Expr.WF` as a computation. -/
def Expr.wfb : Expr → Bool
  | .lit _ | .bool _ | .gidX => true
  | .var n | .fst n | .snd n | .length n => decide (n < 2 ^ 32)
  | .vec2 a b | .bin _ a b | .min a b => a.wfb && b.wfb
  | .not a | .toF32 a | .toU32 a | .sqrt a | .round a | .abs a => a.wfb
  | .select f t c => f.wfb && t.wfb && c.wfb
  | .index b p => decide (b < 2 ^ 32) && p.wfb

theorem Expr.wf_of_wfb (e : Expr) (h : e.wfb = true) : e.WF := by
  induction e <;> simp_all [Expr.wfb, Expr.WF]

mutual
  def Stmt.wfb : Stmt → Bool
    | .let_ n _ e | .var n _ e | .assign n e => decide (n < 2 ^ 32) && e.wfb
    | .store b p e => decide (b < 2 ^ 32) && p.wfb && e.wfb
    | .ite c ts es => c.wfb && Stmt.listWfb ts && Stmt.listWfb es
    | .while_ c body => c.wfb && Stmt.listWfb body
    | .ret => true

  def Stmt.listWfb : List Stmt → Bool
    | [] => true
    | s :: rest => s.wfb && Stmt.listWfb rest
end

mutual
  theorem Stmt.wf_of_wfb : ∀ s : Stmt, s.wfb = true → s.WF
    | .let_ n _ e, h | .var n _ e, h | .assign n e, h => by
        simp only [Stmt.wfb, Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨h.1, Expr.wf_of_wfb e h.2⟩
    | .store b p e, h => by
        simp only [Stmt.wfb, Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨h.1.1, Expr.wf_of_wfb p h.1.2, Expr.wf_of_wfb e h.2⟩
    | .ite c ts es, h => by
        simp only [Stmt.wfb, Bool.and_eq_true] at h
        exact ⟨Expr.wf_of_wfb c h.1.1, Stmt.listWf_of_wfb ts h.1.2, Stmt.listWf_of_wfb es h.2⟩
    | .while_ c body, h => by
        simp only [Stmt.wfb, Bool.and_eq_true] at h
        exact ⟨Expr.wf_of_wfb c h.1, Stmt.listWf_of_wfb body h.2⟩
    | .ret, _ => trivial

  theorem Stmt.listWf_of_wfb : ∀ ss : List Stmt, Stmt.listWfb ss = true → Stmt.ListWF ss
    | [], _ => trivial
    | s :: rest, h => by
        simp only [Stmt.listWfb, Bool.and_eq_true] at h
        exact ⟨Stmt.wf_of_wfb s h.1, Stmt.listWf_of_wfb rest h.2⟩
end

def Module.wfb (m : Module) : Bool :=
  decide (m.inputs < 2 ^ 32) && decide (m.workgroupSize < 2 ^ 32) && Stmt.listWfb m.body

/-- The parser reads a printed kernel back when the check passes, which `decide` evaluates for a
concrete kernel. -/
theorem Module.parse_print_of_wfb (m : Module) (h : m.wfb = true) : Module.parse m.print = some m := by
  simp only [Module.wfb, Bool.and_eq_true, decide_eq_true_eq] at h
  exact Module.parse_print m ⟨h.1.1, h.1.2, Stmt.listWf_of_wfb _ h.2⟩

end LeanExe.WGSL
