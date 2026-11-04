import LeanExe.PTX.Parse

/-!
The parser reads every printed kernel back as itself: `Module.parse_print` states
`Module.parse m.print = some m` for every kernel whose register, parameter, and predicate numbers
and label count fit in eight hexadecimal digits.  The proof uses the tokens: the lexer recovers the
printed tokens, since none is empty or contains a space or newline, and the parser reads each
printed form back with enough fuel and with the label numbers that the printer used.
-/

namespace LeanExe.PTX

/-! ### Digits and names -/

theorem hexValue_hexDigit : ∀ d, d < 16 → hexValue (hexDigit d) = some d := by decide

theorem hexDigits_succ (n v : Nat) :
    hexDigits (n + 1) v = hexDigit (v / 16 ^ n % 16) :: hexDigits n v := by
  simp [hexDigits, List.range_succ]

@[simp] theorem hexDigits_length (n v : Nat) : (hexDigits n v).length = n := by
  simp [hexDigits]

theorem hexNum_hexDigits : ∀ n v, hexNum (hexDigits n v) = some (v % 16 ^ n)
  | 0, v => by simp [hexDigits, hexNum, Nat.mod_one]
  | n + 1, v => by
      rw [hexDigits_succ]
      simp only [hexNum, hexValue_hexDigit _ (Nat.mod_lt _ (by decide)), hexNum_hexDigits n v,
        hexDigits_length, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rw [Nat.mod_pow_succ, Nat.add_comm, Nat.mul_comm]

theorem hexDigits_inj {n a b : Nat} (h : hexDigits n a = hexDigits n b) :
    a % 16 ^ n = b % 16 ^ n := by
  have := congrArg hexNum h
  rw [hexNum_hexDigits, hexNum_hexDigits] at this
  exact Option.some.inj this

theorem isPrefixOf_append_self (l x : List Char) : l.isPrefixOf (l ++ x) = true := by
  induction l <;> simp_all [List.isPrefixOf]

theorem parseNum_name (pre : List Char) (n v : Nat) :
    parseNum pre n (String.ofList (pre ++ hexDigits n v)) = some (v % 16 ^ n) := by
  simp [parseNum, String.toList_ofList, isPrefixOf_append_self, hexNum_hexDigits]

theorem parseNum_other (pre : List Char) (n : Nat) (t : String)
    (h : pre.isPrefixOf t.toList = false) : parseNum pre n t = none := by
  simp [parseNum, h]

theorem nameToken_eq_iff (pre : List Char) (i : Nat) (s : String) :
    nameToken pre i = s ↔ pre ++ hexDigits 8 i = s.toList := by
  unfold nameToken
  constructor
  · rintro rfl
    simp
  · intro h
    rw [h, String.ofList_toList]

theorem lt16 {a : Nat} (h : a < 2 ^ 32) : a < 16 ^ 8 := by simpa using h

theorem nameToken_inj {pre : List Char} {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    nameToken pre a = nameToken pre b ↔ a = b := by
  constructor
  · intro h
    have h1 : pre ++ hexDigits 8 a = pre ++ hexDigits 8 b := by
      have := congrArg String.toList h
      simpa [nameToken] using this
    have := hexDigits_inj (List.append_cancel_left h1)
    rwa [Nat.mod_eq_of_lt (lt16 ha), Nat.mod_eq_of_lt (lt16 hb)] at this
  · rintro rfl
    rfl

theorem parseNum_nameToken (pre : List Char) (i : Nat) (h : i < 2 ^ 32) :
    parseNum pre 8 (nameToken pre i) = some i := by
  unfold nameToken
  rw [parseNum_name, Nat.mod_eq_of_lt (lt16 h)]

theorem w32Idx_token (i : Nat) (h : i < 2 ^ 32) : w32Idx (w32Token i) = some i :=
  parseNum_nameToken _ i h

theorem w64Idx_token (i : Nat) (h : i < 2 ^ 32) : w64Idx (w64Token i) = some i :=
  parseNum_nameToken _ i h

theorem fIdx_token (i : Nat) (h : i < 2 ^ 32) : fIdx (fToken i) = some i :=
  parseNum_nameToken _ i h

theorem predIdx_token (i : Nat) (h : i < 2 ^ 32) : predIdx (predToken i) = some i :=
  parseNum_nameToken _ i h

theorem paramIdx_token (i : Nat) (h : i < 2 ^ 32) : paramIdx (paramToken i) = some i :=
  parseNum_nameToken _ i h

theorem imm64_token (v : UInt64) : imm64 (imm64Token v) = some v := by
  unfold imm64 imm64Token
  rw [show '0' :: 'x' :: hexDigits 16 v.toNat = ['0', 'x'] ++ hexDigits 16 v.toNat from rfl,
    parseNum_name]
  simp [Nat.mod_eq_of_lt (show v.toNat < 16 ^ 16 from UInt64.toNat_lt v)]

theorem imm32_token (v : UInt32) : imm32 (imm32Token v) = some v := by
  unfold imm32 imm32Token
  rw [show '0' :: 'x' :: hexDigits 8 v.toNat = ['0', 'x'] ++ hexDigits 8 v.toNat from rfl,
    parseNum_name]
  simp [Nat.mod_eq_of_lt (show v.toNat < 16 ^ 8 from UInt32.toNat_lt v)]

theorem w64Idx_imm (v : UInt64) : w64Idx (imm64Token v) = none := by
  unfold w64Idx imm64Token
  exact parseNum_other _ _ _ (by simp [List.isPrefixOf])

theorem w32Idx_imm (v : UInt32) : w32Idx (imm32Token v) = none := by
  unfold w32Idx imm32Token
  exact parseNum_other _ _ _ (by simp [List.isPrefixOf])

theorem fIdx_imm (v : UInt32) : fIdx (imm32Token v) = none := by
  unfold fIdx imm32Token
  exact parseNum_other _ _ _ (by simp [List.isPrefixOf])

theorem w32Idx_f (i : Nat) : w32Idx (fToken i) = none := by
  unfold w32Idx fToken nameToken
  exact parseNum_other _ _ _ (by simp [List.isPrefixOf])

theorem imm32_f (i : Nat) : imm32 (fToken i) = none := by
  unfold imm32 fToken nameToken
  rw [parseNum_other _ _ _ (by simp [List.isPrefixOf])]
  rfl

theorem parseSrc32_f (i : Nat) : parseSrc32 (fToken i) = none := by
  simp [parseSrc32, w32Idx_f, imm32_f]

/-! ### Well-formed syntax -/

def Src64.WF : Src64 → Prop
  | .reg i => i < 2 ^ 32
  | .imm _ => True

def Src32.WF : Src32 → Prop
  | .reg i => i < 2 ^ 32
  | .imm _ => True

def SrcF.WF : SrcF → Prop
  | .reg i => i < 2 ^ 32
  | .imm _ => True

/-- Every register and parameter number fits in eight hexadecimal digits. -/
def Instr.WF : Instr → Prop
  | .special d _ => d < 2 ^ 32
  | .mov32 d a => d < 2 ^ 32 ∧ a.WF
  | .mov64 d a => d < 2 ^ 32 ∧ a.WF
  | .bin64 _ d a b => d < 2 ^ 32 ∧ a < 2 ^ 32 ∧ b.WF
  | .shift _ d a b => d < 2 ^ 32 ∧ a < 2 ^ 32 ∧ b.WF
  | .setp _ p a b => p < 2 ^ 32 ∧ a < 2 ^ 32 ∧ b.WF
  | .selp d t f p => d < 2 ^ 32 ∧ t.WF ∧ f.WF ∧ p < 2 ^ 32
  | .notPred d a | .widen d a | .narrow d a | .cvtaGlobal d a | .ldParam d a =>
      d < 2 ^ 32 ∧ a < 2 ^ 32
  | .madWide d a b c => d < 2 ^ 32 ∧ a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ c < 2 ^ 32
  | .ld d a _ => d < 2 ^ 32 ∧ a < 2 ^ 32
  | .st a _ v => a < 2 ^ 32 ∧ v < 2 ^ 32
  | .binF _ d a b | .setpF _ d a b => d < 2 ^ 32 ∧ a < 2 ^ 32 ∧ b < 2 ^ 32
  | .sqrtF d a | .rniF d a | .testNaN d a | .toF d a | .ofF d a => d < 2 ^ 32 ∧ a < 2 ^ 32
  | .selpF d t f p => d < 2 ^ 32 ∧ t.WF ∧ f.WF ∧ p < 2 ^ 32

theorem parseSrc64_token (s : Src64) (h : s.WF) : parseSrc64 s.token = some s := by
  cases s with
  | reg i => simp [parseSrc64, Src64.token, w64Idx_token i h]
  | imm v => simp [parseSrc64, Src64.token, w64Idx_imm, imm64_token]

theorem parseSrc32_token (s : Src32) (h : s.WF) : parseSrc32 s.token = some s := by
  cases s with
  | reg i => simp [parseSrc32, Src32.token, w32Idx_token i h]
  | imm v => simp [parseSrc32, Src32.token, w32Idx_imm, imm32_token]

theorem parseSrcF_token (s : SrcF) (h : s.WF) : parseSrcF s.token = some s := by
  cases s with
  | reg i => simp [parseSrcF, SrcF.token, fIdx_token i h]
  | imm v => simp [parseSrcF, SrcF.token, fIdx_imm, imm32_token]

theorem parseGuard_token (g : Guard) (h : g.pred < 2 ^ 32) : parseGuard g.token = some g := by
  obtain ⟨neg, p⟩ := g
  cases neg
  · simp [parseGuard, Guard.token, parseNum_nameToken _ p h]
  · have : parseNum ['@', '%', 'p'] 8 (nameToken ['@', '!', '%', 'p'] p) = none :=
      parseNum_other _ _ _ (by simp [nameToken, List.isPrefixOf])
    simp [parseGuard, Guard.token, this, parseNum_nameToken _ p h]

theorem Guard.token_ne (g : Guard) (s : String) (h : s.toList.head? ≠ some '@') : g.token ≠ s := by
  intro e
  apply h
  rw [← e]
  unfold Guard.token nameToken
  split <;> simp

theorem parseSpecial_token (s : Special) : parseSpecial s.token = some s := by cases s <;> rfl
theorem parseBin64_token (op : Bin64) : parseBin64 op.token = some op := by cases op <;> rfl
theorem parseShift_token (op : Shift) : parseShift op.token = some op := by cases op <;> rfl
theorem parseCmp_token (c : Cmp) : parseCmp c.token = some c := by cases c <;> rfl
theorem parseBinF_token (op : BinF) : parseBinF op.token = some op := by cases op <;> rfl
theorem parseCmpF_token (c : CmpF) : parseCmpF c.token = some c := by cases c <;> rfl

/-- The tokens of an instruction: its opcode and the operand tokens that follow it. -/
theorem Instr.tokens_cons (i : Instr) : ∃ op ops, i.tokens = op :: ops := by
  cases i <;> exact ⟨_, _, rfl⟩

/-- The parser reads a printed instruction back. -/
theorem Instr.parse_tokens (i : Instr) (h : i.WF) (rest : List String) :
    ∃ op ops, i.tokens = op :: ops ∧ parseInstr op (ops ++ rest) = some (i, rest) := by
  cases i with
  | special d s =>
      exact ⟨_, _, rfl, by simp [parseInstr, ops2, w32Idx_token d h, parseSpecial_token]⟩
  | mov32 d a =>
      exact ⟨_, _, rfl, by simp [parseInstr, ops2, parseMov32, w32Idx_token d h.1,
        parseSrc32_token a h.2]⟩
  | mov64 d a =>
      exact ⟨_, _, rfl, by simp [parseInstr, ops2, w64Idx_token d h.1,
        parseSrc64_token a h.2]⟩
  | bin64 op d a b =>
      refine ⟨_, _, rfl, ?_⟩
      cases op <;> simp [Bin64.token, parseInstr, ops3, parseOp3, parseBin64,
        w64Idx_token d h.1, w64Idx_token a h.2.1, parseSrc64_token b h.2.2]
  | shift op d a b =>
      refine ⟨_, _, rfl, ?_⟩
      cases op <;> simp [Shift.token, parseInstr, ops3, parseOp3, parseBin64, parseShift,
        w64Idx_token d h.1, w64Idx_token a h.2.1, parseSrc32_token b h.2.2]
  | setp c p a b =>
      refine ⟨_, _, rfl, ?_⟩
      cases c <;> simp [Cmp.token, parseInstr, ops3, parseOp3, parseBin64, parseShift, parseCmp,
        predIdx_token p h.1, w64Idx_token a h.2.1, parseSrc64_token b h.2.2]
  | binF op d a b =>
      refine ⟨_, _, rfl, ?_⟩
      cases op <;> simp [BinF.token, parseInstr, ops3, parseOp3, parseBin64, parseShift, parseCmp,
        parseBinF, fIdx_token d h.1, fIdx_token a h.2.1, fIdx_token b h.2.2]
  | setpF c p a b =>
      refine ⟨_, _, rfl, ?_⟩
      cases c <;> simp [CmpF.token, parseInstr, ops3, parseOp3, parseBin64, parseShift, parseCmp,
        parseBinF, parseCmpF, predIdx_token p h.1, fIdx_token a h.2.1, fIdx_token b h.2.2]
  | selp d t f p =>
      exact ⟨_, _, rfl, by simp [parseInstr, ops4, w64Idx_token d h.1,
        parseSrc64_token t h.2.1, parseSrc64_token f h.2.2.1, predIdx_token p h.2.2.2]⟩
  | notPred d a =>
      exact ⟨_, _, rfl, by simp [parseInstr, ops2, predIdx_token d h.1,
        predIdx_token a h.2]⟩
  | widen d a =>
      exact ⟨_, _, rfl, by simp [parseInstr, ops2, w64Idx_token d h.1,
        w32Idx_token a h.2]⟩
  | narrow d a =>
      exact ⟨_, _, rfl, by simp [parseInstr, ops2, w32Idx_token d h.1,
        w64Idx_token a h.2]⟩
  | madWide d a b c =>
      exact ⟨_, _, rfl, by simp [parseInstr, ops4, w64Idx_token d h.1,
        w32Idx_token a h.2.1, w32Idx_token b h.2.2.1, w64Idx_token c h.2.2.2]⟩
  | ldParam d j =>
      exact ⟨_, _, rfl, by simp [parseInstr, w64Idx_token d h.1,
        paramIdx_token j h.2]⟩
  | cvtaGlobal d a =>
      exact ⟨_, _, rfl, by simp [parseInstr, ops2, w64Idx_token d h.1,
        w64Idx_token a h.2]⟩
  | ld d a imm =>
      exact ⟨_, _, rfl, by simp [addressTokens, parseInstr, w64Idx_token d h.1,
        w64Idx_token a h.2, imm64_token]⟩
  | st a imm v =>
      exact ⟨_, _, rfl, by simp [addressTokens, parseInstr, w64Idx_token a h.1,
        w64Idx_token v h.2, imm64_token]⟩
  | sqrtF d a =>
      exact ⟨_, _, rfl, by simp [parseInstr, ops2, fIdx_token d h.1, fIdx_token a h.2]⟩
  | rniF d a =>
      exact ⟨_, _, rfl, by simp [parseInstr, ops2, fIdx_token d h.1, fIdx_token a h.2]⟩
  | testNaN p a =>
      exact ⟨_, _, rfl, by simp [parseInstr, ops2, predIdx_token p h.1, fIdx_token a h.2]⟩
  | selpF d t f p =>
      exact ⟨_, _, rfl, by simp [parseInstr, ops4, fIdx_token d h.1, parseSrcF_token t h.2.1,
        parseSrcF_token f h.2.2.1, predIdx_token p h.2.2.2]⟩
  | toF d a =>
      exact ⟨_, _, rfl, by simp [parseInstr, ops2, parseMov32, w32Idx_f, fIdx_token d h.1,
        w32Idx_token a h.2]⟩
  | ofF d a =>
      exact ⟨_, _, rfl, by simp [parseInstr, ops2, parseMov32, w32Idx_token d h.1,
        parseSrc32_f, fIdx_token a h.2]⟩

/-! ### Statements -/

mutual
  /-- Every guard and branch predicate, and every instruction, is well formed. -/
  def Stmt.WF : Stmt → Prop
    | .instr none i => i.WF
    | .instr (some g) i => g.pred < 2 ^ 32 ∧ i.WF
    | .ite p ts es => p < 2 ^ 32 ∧ Stmt.ListWF ts ∧ Stmt.ListWF es
    | .while_ c p b => p < 2 ^ 32 ∧ Stmt.ListWF c ∧ Stmt.ListWF b
    | .ret => True

  def Stmt.ListWF : List Stmt → Prop
    | [] => True
    | s :: rest => s.WF ∧ Stmt.ListWF rest
end

mutual
  def Stmt.size : Stmt → Nat
    | .instr _ _ | .ret => 1
    | .ite _ ts es => Stmt.listSize ts + Stmt.listSize es + 1
    | .while_ c _ b => Stmt.listSize c + Stmt.listSize b + 1

  def Stmt.listSize : List Stmt → Nat
    | [] => 0
    | s :: rest => s.size + Stmt.listSize rest + 1
end

mutual
  theorem Stmt.tokens_le : ∀ (s : Stmt) (n : Nat), n ≤ (Stmt.tokens n s).2
    | .instr none _, _ | .instr (some _) _, _ | .ret, _ => by simp [Stmt.tokens]
    | .ite _ ts es, n => by
        have h1 := Stmt.listTokens_le ts (n + 2)
        have h2 := Stmt.listTokens_le es (Stmt.listTokens (n + 2) ts).2
        simp only [Stmt.tokens]
        omega
    | .while_ c _ b, n => by
        have h1 := Stmt.listTokens_le c (n + 2)
        have h2 := Stmt.listTokens_le b (Stmt.listTokens (n + 2) c).2
        simp only [Stmt.tokens]
        omega

  theorem Stmt.listTokens_le : ∀ (ss : List Stmt) (n : Nat), n ≤ (Stmt.listTokens n ss).2
    | [], _ => by simp [Stmt.listTokens]
    | s :: rest, n => by
        have h1 := Stmt.tokens_le s n
        have h2 := Stmt.listTokens_le rest (Stmt.tokens n s).2
        simp only [Stmt.listTokens]
        omega
end

theorem labelToken_ne {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : a ≠ b) :
    labelToken a ≠ labelToken b :=
  fun e => h ((nameToken_inj ha hb).mp e)

theorem stops_bra (n : Nat) (rest : List String) : stops n ("bra" :: rest) = true := by
  simp [stops]

theorem stops_label {n m : Nat} (hn : n < 2 ^ 32) (hm : m < 2 ^ 32) (h : m ≠ n)
    (rest : List String) : stops n (labelToken m :: ":" :: rest) = true := by
  have h1 : labelToken m ≠ "bra" := by simp [labelToken, nameToken_eq_iff]
  have h2 : labelToken m ≠ "ret" := by simp [labelToken, nameToken_eq_iff]
  simp [stops, labelToken_ne hm hn h]

theorem stops_guard {n m : Nat} (hn : n < 2 ^ 32) (hm : m < 2 ^ 32) (h : m ≠ n) (p : Nat)
    (hp : p < 2 ^ 32) (rest : List String) :
    stops n (Guard.token ⟨true, p⟩ :: "bra" :: labelToken m :: rest) = true := by
  have h1 : Guard.token ⟨true, p⟩ ≠ "bra" := Guard.token_ne _ _ (by simp)
  have h2 : Guard.token ⟨true, p⟩ ≠ "ret" := Guard.token_ne _ _ (by simp)
  simp [stops, labelToken_ne hm hn h, parseGuard_token ⟨true, p⟩ hp]

theorem stops_ne_brace (n : Nat) : stops n ["}"] = false := by simp [stops]

theorem isPrefixOf_self_append (l x : List String) : l.isPrefixOf (l ++ x) = true := by
  induction l <;> simp_all [List.isPrefixOf]

theorem expectAll_append (l x : List String) : expectAll l (l ++ x) = some x := by
  simp [expectAll, isPrefixOf_self_append]

@[simp] theorem expectAll_cons (a : String) (l x : List String) :
    expectAll (a :: l) (a :: x) = expectAll l x := by
  simp [expectAll, List.isPrefixOf]

@[simp] theorem expectAll_nil (x : List String) : expectAll [] x = some x := by
  simp [expectAll, List.isPrefixOf]

/-- An instruction statement's first two tokens are an opcode and an operand, neither of which
begins another form. -/
theorem Instr.tokens_head (i : Instr) : ∃ op x ops, i.tokens = op :: x :: ops ∧ op ≠ "ret" ∧
    op ≠ "bra" ∧ x ≠ "bra" ∧ x ≠ ":" ∧ parseGuard op = none ∧ op ≠ ":" ∧ op ≠ ".reg" := by
  cases i with
  | bin64 op => cases op <;> exact ⟨_, _, _, rfl, by
      simp [Bin64.token, w64Token, nameToken_eq_iff, parseGuard, parseNum, List.isPrefixOf]⟩
  | shift op => cases op <;> exact ⟨_, _, _, rfl, by
      simp [Shift.token, w64Token, nameToken_eq_iff, parseGuard, parseNum, List.isPrefixOf]⟩
  | setp c => cases c <;> exact ⟨_, _, _, rfl, by
      simp [Cmp.token, predToken, nameToken_eq_iff, parseGuard, parseNum, List.isPrefixOf]⟩
  | binF op => cases op <;> exact ⟨_, _, _, rfl, by
      simp [BinF.token, fToken, nameToken_eq_iff, parseGuard, parseNum, List.isPrefixOf]⟩
  | setpF c => cases c <;> exact ⟨_, _, _, rfl, by
      simp [CmpF.token, predToken, nameToken_eq_iff, parseGuard, parseNum, List.isPrefixOf]⟩
  | _ => exact ⟨_, _, _, rfl, by
      simp [w32Token, w64Token, fToken, predToken, nameToken_eq_iff, parseGuard, parseNum,
        List.isPrefixOf]⟩

/-- A statement's tokens do not end a statement list. -/
theorem Stmt.not_stops (s : Stmt) (n : Nat) (hwf : s.WF) (hn : (Stmt.tokens n s).2 < 2 ^ 32)
    (rest : List String) (hr : rest ≠ ["}"]) :
    stops n ((Stmt.tokens n s).1 ++ rest) = false := by
  cases s with
  | instr g i =>
      obtain ⟨op, x, ops, hi, h1, h2, h3, h4, -, h6, -⟩ := Instr.tokens_head i
      cases g with
      | none => simp [Stmt.tokens, hi, stops, h1, h2, h3, h4]
      | some g =>
          have hg1 : g.token ≠ "bra" := Guard.token_ne g _ (by simp)
          have hg2 : g.token ≠ "ret" := Guard.token_ne g _ (by simp)
          simp [Stmt.tokens, hi, stops, hg1, hg2, h2, h6]
  | ite p ts es =>
      have hle := Stmt.tokens_le (.ite p ts es) n
      have hg1 : Guard.token ⟨true, p⟩ ≠ "bra" := Guard.token_ne _ _ (by simp)
      have hg2 : Guard.token ⟨true, p⟩ ≠ "ret" := Guard.token_ne _ _ (by simp)
      simp [Stmt.tokens, branchUnless, stops]
  | while_ c p b =>
      have hl1 : labelToken n ≠ "bra" := by simp [labelToken, nameToken_eq_iff]
      have hl2 : labelToken n ≠ "ret" := by simp [labelToken, nameToken_eq_iff]
      simp [Stmt.tokens, stops]
  | ret =>
      rcases rest with _ | ⟨y, _ | ⟨z, r⟩⟩
      · simp [Stmt.tokens, stops]
      · have : y ≠ "}" := fun h => hr (by rw [h])
        simp [Stmt.tokens, stops, this]
      · simp [Stmt.tokens, stops]

mutual
  /-- The parser reads a printed statement back, with the printer's label numbers. -/
  theorem Stmt.parse_tokens : ∀ (s : Stmt) (n : Nat), s.WF → (Stmt.tokens n s).2 < 2 ^ 32 →
      ∀ fuel, s.size < fuel → ∀ rest : List String,
        parseStmt fuel n ((Stmt.tokens n s).1 ++ rest) = some (s, rest, (Stmt.tokens n s).2)
    | .instr none i, n, hwf, _, fuel + 1, _, rest => by
        obtain ⟨op, x, ops, hi, h1, h2, h3, h4, h5, -, -⟩ := Instr.tokens_head i
        obtain ⟨op', ops', hi', hp⟩ := Instr.parse_tokens i hwf rest
        rw [hi] at hi'
        obtain ⟨rfl, rfl⟩ := List.cons.inj hi'
        simp only [Stmt.tokens, hi, List.cons_append] at hp ⊢
        simp [parseStmt, h1, h3, h4, h5, hp]
    | .instr (some g) i, n, hwf, _, fuel + 1, _, rest => by
        obtain ⟨op, x, ops, hi, h1, h2, h3, h4, h5, h6, -⟩ := Instr.tokens_head i
        obtain ⟨op', ops', hi', hp⟩ := Instr.parse_tokens i hwf.2 rest
        rw [hi] at hi'
        obtain ⟨rfl, rfl⟩ := List.cons.inj hi'
        have hg : g.token ≠ "ret" := Guard.token_ne g _ (by simp)
        simp only [Stmt.tokens, hi, List.cons_append] at hp ⊢
        simp [parseStmt, hg, h2, h6, parseGuard_token g hwf.1, hp]
    | .ite p ts es, n, hwf, hn, fuel + 1, hf, rest => by
        obtain ⟨hp, hts, hes⟩ := hwf
        simp only [Stmt.size] at hf
        have h1 := Stmt.listTokens_le ts (n + 2)
        have h2 := Stmt.listTokens_le es (Stmt.listTokens (n + 2) ts).2
        simp only [Stmt.tokens] at hn ⊢
        have ht := Stmt.parse_listTokens ts (n + 2) hts (by omega) fuel (by omega)
          (["bra", labelToken (n + 1), ";", labelToken n, ":"] ++
            (Stmt.listTokens (Stmt.listTokens (n + 2) ts).2 es).1 ++ [labelToken (n + 1), ":"] ++
            rest) (by simp [stops])
        have he := Stmt.parse_listTokens es _ hes (by omega) fuel (by omega)
          ([labelToken (n + 1), ":"] ++ rest)
          (stops_label (by omega) (by omega) (by omega) rest)
        simp only [branchUnless, List.append_assoc, List.cons_append, List.nil_append] at ht he ⊢
        simp [parseStmt, parseGuard_token ⟨true, p⟩ hp, ht, he, Option.bind_eq_bind]
    | .while_ c p b, n, hwf, hn, fuel + 1, hf, rest => by
        obtain ⟨hp, hc, hb⟩ := hwf
        simp only [Stmt.size] at hf
        have h1 := Stmt.listTokens_le c (n + 2)
        have h2 := Stmt.listTokens_le b (Stmt.listTokens (n + 2) c).2
        simp only [Stmt.tokens] at hn ⊢
        have hcp := Stmt.parse_listTokens c (n + 2) hc (by omega) fuel (by omega)
          (branchUnless p (n + 1) ++ (Stmt.listTokens (Stmt.listTokens (n + 2) c).2 b).1 ++
            ["bra", labelToken n, ";", labelToken (n + 1), ":"] ++ rest)
          (by
            simp only [branchUnless, List.cons_append, List.nil_append, List.append_assoc]
            exact stops_guard (by omega) (by omega) (by omega) p hp _)
        have hbp := Stmt.parse_listTokens b _ hb (by omega) fuel (by omega)
          (["bra", labelToken n, ";", labelToken (n + 1), ":"] ++ rest) (by simp [stops])
        simp only [branchUnless, List.append_assoc, List.cons_append, List.nil_append] at hcp hbp ⊢
        simp [parseStmt, parseGuard_token ⟨true, p⟩ hp, hcp, hbp, Option.bind_eq_bind]
    | .ret, n, _, _, fuel + 1, _, rest => by simp [Stmt.tokens, parseStmt]

  /-- The parser reads printed statements back, up to tokens that end a statement list. -/
  theorem Stmt.parse_listTokens : ∀ (ss : List Stmt) (n : Nat), Stmt.ListWF ss →
      (Stmt.listTokens n ss).2 < 2 ^ 32 → ∀ fuel, Stmt.listSize ss < fuel →
      ∀ rest : List String, stops (Stmt.listTokens n ss).2 rest = true →
        parseStmts fuel n ((Stmt.listTokens n ss).1 ++ rest) =
          some (ss, rest, (Stmt.listTokens n ss).2)
    | [], n, _, _, fuel + 1, _, rest, hs => by
        simp only [Stmt.listTokens] at hs ⊢
        simp [parseStmts, hs]
    | s :: ss, n, hwf, hn, fuel + 1, hf, rest, hs => by
        obtain ⟨hs1, hss⟩ := hwf
        simp only [Stmt.listSize] at hf
        simp only [Stmt.listTokens] at hn hs ⊢
        have hle := Stmt.listTokens_le ss (Stmt.tokens n s).2
        have hr : (Stmt.listTokens (Stmt.tokens n s).2 ss).1 ++ rest ≠ ["}"] := by
          cases ss with
          | nil =>
              simp only [Stmt.listTokens, List.nil_append]
              intro h
              rw [h, stops_ne_brace] at hs
              cases hs
          | cons t tt =>
              obtain ⟨op, x, ops, hi, -⟩ : ∃ op x ops, (Stmt.tokens (Stmt.tokens n s).2 t).1 =
                  op :: x :: ops ∧ True := by
                cases t with
                | instr g i =>
                    obtain ⟨op, x, ops, hi, -⟩ := Instr.tokens_head i
                    cases g <;> simp [Stmt.tokens, hi]
                | ite => simp [Stmt.tokens, branchUnless]
                | while_ => simp [Stmt.tokens]
                | ret => simp [Stmt.tokens]
              simp [Stmt.listTokens, hi]
        rw [List.append_assoc, parseStmts]
        simp only [Stmt.not_stops s n hs1 (by omega) _ hr, Bool.false_eq_true, ↓reduceIte]
        rw [Stmt.parse_tokens s n hs1 (by omega) fuel (by omega)]
        simp [Stmt.parse_listTokens ss _ hss hn fuel (by omega) rest hs]
end

/-! ### Kernels -/

theorem parseParams_tokens (i k fuel : Nat) (hf : k < fuel) (hi : i + k < 2 ^ 32)
    (rest : List String) :
    parseParams fuel i (paramTokens i k ++ ")" :: rest) = some (i + k + 1, rest) := by
  induction k generalizing i fuel with
  | zero =>
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp [paramTokens, parseParams]
  | succ k ih =>
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp [paramTokens, parseParams, ih (i + 1) f (by omega) (by omega)]
      omega

theorem parseRegs_tokens (cls : String) (name : Nat → String) (i k fuel : Nat) (hf : k < fuel)
    (rest : List String) (hr : [".reg", cls, name (i + k), ";"].isPrefixOf rest = false) :
    parseRegs cls name fuel i (regDecls cls name i k ++ rest) = some (i + k, rest) := by
  induction k generalizing i fuel with
  | zero =>
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [Nat.add_zero] at hr
      simp only [regDecls, List.nil_append, parseRegs, hr, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero]
  | succ k ih =>
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have := ih (i + 1) f (by omega) (by rw [show i + 1 + k = i + (k + 1) by omega]; exact hr)
      simp [regDecls, parseRegs, this]
      omega

mutual
  theorem Stmt.size_le : ∀ (s : Stmt) (n : Nat), s.size + 1 ≤ (Stmt.tokens n s).1.length
    | .instr g i, n => by
        obtain ⟨op, x, ops, hi, -⟩ := Instr.tokens_head i
        cases g <;> simp [Stmt.size, Stmt.tokens, hi]
    | .ite p ts es, n => by
        have h1 := Stmt.listSize_le ts (n + 2)
        have h2 := Stmt.listSize_le es (Stmt.listTokens (n + 2) ts).2
        simp only [Stmt.size, Stmt.tokens, branchUnless, List.length_append, List.length_cons,
          List.length_nil]
        omega
    | .while_ c p b, n => by
        have h1 := Stmt.listSize_le c (n + 2)
        have h2 := Stmt.listSize_le b (Stmt.listTokens (n + 2) c).2
        simp only [Stmt.size, Stmt.tokens, branchUnless, List.length_append, List.length_cons,
          List.length_nil]
        omega
    | .ret, n => by simp [Stmt.size, Stmt.tokens]

  theorem Stmt.listSize_le : ∀ (ss : List Stmt) (n : Nat),
      Stmt.listSize ss ≤ (Stmt.listTokens n ss).1.length
    | [], _ => by simp [Stmt.listSize, Stmt.listTokens]
    | s :: rest, n => by
        have h1 := Stmt.size_le s n
        have h2 := Stmt.listSize_le rest (Stmt.tokens n s).2
        simp only [Stmt.listSize, Stmt.listTokens, List.length_append]
        omega
end

/-- Every number in a kernel fits in eight hexadecimal digits: parameter and register numbers,
and label numbers, which run from 0 up to the printer's final counter. -/
def Module.WF (m : Module) : Prop :=
  m.inputs < 2 ^ 32 ∧ m.regs32 ≤ 2 ^ 32 ∧ m.regs64 ≤ 2 ^ 32 ∧ m.regsF ≤ 2 ^ 32 ∧
    m.preds ≤ 2 ^ 32 ∧
    Stmt.ListWF m.body ∧ (Stmt.listTokens 0 m.body).2 < 2 ^ 32

theorem regDecls_length (cls : String) (name : Nat → String) (i k : Nat) :
    (regDecls cls name i k).length = 4 * k := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [regDecls, ih]; omega

theorem paramTokens_length (i k : Nat) : (paramTokens i k).length = 4 * k + 3 := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [paramTokens, ih]; omega

theorem Stmt.head_ne_reg (s : Stmt) (n : Nat) :
    (Stmt.tokens n s).1.head? ≠ some ".reg" ∧ (Stmt.tokens n s).1 ≠ [] := by
  cases s with
  | instr g i =>
      obtain ⟨op, x, ops, hi, -, -, -, -, -, -, h⟩ := Instr.tokens_head i
      cases g with
      | none => simp [Stmt.tokens, hi, h]
      | some g => simp [Stmt.tokens, Guard.token_ne g ".reg" (by simp)]
  | ite p => simp [Stmt.tokens, branchUnless, Guard.token_ne ⟨true, p⟩ ".reg" (by simp)]
  | while_ => simp [Stmt.tokens, labelToken, nameToken_eq_iff]
  | ret => simp [Stmt.tokens]

theorem body_not_prefix (cls : String) (name : Nat → String) (i : Nat) (ss : List Stmt)
    (n : Nat) (rest : List String) :
    [".reg", cls, name i, ";"].isPrefixOf ((Stmt.listTokens n ss).1 ++ "ret" :: rest) = false := by
  cases ss with
  | nil => simp [Stmt.listTokens, List.isPrefixOf]
  | cons s ss =>
      obtain ⟨h1, h2⟩ := Stmt.head_ne_reg s n
      simp only [Stmt.listTokens, List.append_assoc]
      generalize (Stmt.tokens n s).1 = l at h1 h2
      cases l with
      | nil => exact absurd rfl h2
      | cons t r =>
          have : t ≠ ".reg" := fun e => h1 (by rw [e]; rfl)
          simp [List.isPrefixOf, Ne.symm this]

theorem reg_prefix_false (cls cls' : String) (name name' : Nat → String) (i i' k : Nat)
    (h : cls ≠ cls') (x : List String) (hx : [".reg", cls', name' i', ";"].isPrefixOf x = false) :
    [".reg", cls', name' i', ";"].isPrefixOf (regDecls cls name i k ++ x) = false := by
  cases k with
  | zero => simpa [regDecls] using hx
  | succ k => simp [regDecls, List.isPrefixOf, Ne.symm h]

theorem parseModule_tokens (m : Module) (h : m.WF) : parseModule m.tokens = some m := by
  obtain ⟨hInputs, h32, h64, hf, hp, hBody, hLabels⟩ := h
  have hLen := Stmt.listSize_le m.body 0
  unfold parseModule
  generalize hF : m.tokens.length + 1 = fuel
  have hTok : m.tokens.length = 10 + (4 * m.inputs + 3) + 2 + 4 * m.regs32 + 4 * m.regs64 +
      4 * m.regsF + 4 * m.preds + (Stmt.listTokens 0 m.body).1.length + 3 := by
    simp only [Module.tokens, List.length_append, paramTokens_length, regDecls_length,
      List.length_cons, List.length_nil]
  have hBodyParse := Stmt.parse_listTokens m.body 0 hBody hLabels fuel (by omega)
    ["ret", ";", "}"] (by simp [stops])
  have hRegsP := parseRegs_tokens ".pred" predToken 0 m.preds fuel (by omega)
    ((Stmt.listTokens 0 m.body).1 ++ ["ret", ";", "}"])
    (body_not_prefix ".pred" predToken (0 + m.preds) m.body 0 [";", "}"])
  have hRegsF := parseRegs_tokens ".f32" fToken 0 m.regsF fuel (by omega)
    (regDecls ".pred" predToken 0 m.preds ++ ((Stmt.listTokens 0 m.body).1 ++ ["ret", ";", "}"]))
    (reg_prefix_false ".pred" ".f32" predToken fToken 0 (0 + m.regsF) m.preds (by decide) _
      (body_not_prefix ".f32" fToken (0 + m.regsF) m.body 0 [";", "}"]))
  have hRegs64 := parseRegs_tokens ".b64" w64Token 0 m.regs64 fuel (by omega)
    (regDecls ".f32" fToken 0 m.regsF ++ (regDecls ".pred" predToken 0 m.preds ++
      ((Stmt.listTokens 0 m.body).1 ++ ["ret", ";", "}"])))
    (reg_prefix_false ".f32" ".b64" fToken w64Token 0 (0 + m.regs64) m.regsF (by decide) _
      (reg_prefix_false ".pred" ".b64" predToken w64Token 0 (0 + m.regs64) m.preds (by decide) _
        (body_not_prefix ".b64" w64Token (0 + m.regs64) m.body 0 [";", "}"])))
  have hRegs32 := parseRegs_tokens ".b32" w32Token 0 m.regs32 fuel (by omega)
    (regDecls ".b64" w64Token 0 m.regs64 ++ (regDecls ".f32" fToken 0 m.regsF ++
      (regDecls ".pred" predToken 0 m.preds ++ ((Stmt.listTokens 0 m.body).1 ++
        ["ret", ";", "}"]))))
    (reg_prefix_false ".b64" ".b32" w64Token w32Token 0 (0 + m.regs32) m.regs64 (by decide) _
      (reg_prefix_false ".f32" ".b32" fToken w32Token 0 (0 + m.regs32) m.regsF (by decide) _
        (reg_prefix_false ".pred" ".b32" predToken w32Token 0 (0 + m.regs32) m.preds
          (by decide) _ (body_not_prefix ".b32" w32Token (0 + m.regs32) m.body 0 [";", "}"]))))
  have hParams := parseParams_tokens 0 m.inputs fuel (by omega) (by omega)
    ("{" :: (regDecls ".b32" w32Token 0 m.regs32 ++ (regDecls ".b64" w64Token 0 m.regs64 ++
      (regDecls ".f32" fToken 0 m.regsF ++ (regDecls ".pred" predToken 0 m.preds ++
        ((Stmt.listTokens 0 m.body).1 ++ ["ret", ";", "}"]))))))
  simp only [Module.tokens, List.append_assoc, List.cons_append, List.nil_append]
  simp [hParams, hRegs32, hRegs64, hRegsF, hRegsP, hBodyParse, Option.bind_eq_bind]

/-! ### Lexing -/

/-- A token the lexer reads back: nonempty, with no space or newline. -/
def good (t : String) : Bool := !t.toList.isEmpty && t.toList.all fun c => !isSeparator c

theorem isSeparator_hexDigit : ∀ d, d < 16 → isSeparator (hexDigit d) = false := by decide

theorem hexDigits_good (n v : Nat) : (hexDigits n v).all (fun c => !isSeparator c) = true := by
  simp [hexDigits, isSeparator_hexDigit _ (Nat.mod_lt _ (by decide))]

theorem good_nameToken (pre : List Char) (h1 : pre ≠ [])
    (h2 : pre.all (fun c => !isSeparator c) = true) (i : Nat) : good (nameToken pre i) = true := by
  simp only [good, nameToken, String.toList_ofList, List.all_append, h2, hexDigits_good]
  simp [h1]

theorem good_imm64 (v : UInt64) : good (imm64Token v) = true := by
  simp only [good, imm64Token, String.toList_ofList, List.all_cons, hexDigits_good,
    List.isEmpty_cons]
  decide

theorem good_imm32 (v : UInt32) : good (imm32Token v) = true := by
  simp only [good, imm32Token, String.toList_ofList, List.all_cons, hexDigits_good,
    List.isEmpty_cons]
  decide

theorem good_w32 (i : Nat) : good (w32Token i) = true := good_nameToken _ (by simp) (by decide) i
theorem good_w64 (i : Nat) : good (w64Token i) = true := good_nameToken _ (by simp) (by decide) i
theorem good_pred (i : Nat) : good (predToken i) = true := good_nameToken _ (by simp) (by decide) i
theorem good_f (i : Nat) : good (fToken i) = true := good_nameToken _ (by simp) (by decide) i
theorem good_param (i : Nat) : good (paramToken i) = true :=
  good_nameToken _ (by simp) (by decide) i
theorem good_label (i : Nat) : good (labelToken i) = true :=
  good_nameToken _ (by simp) (by decide) i

theorem good_guard (g : Guard) : good g.token = true := by
  unfold Guard.token
  split <;> exact good_nameToken _ (by simp) (by decide) _

theorem good_src64 (s : Src64) : good s.token = true := by
  cases s <;> simp [Src64.token, good_w64, good_imm64]

theorem good_src32 (s : Src32) : good s.token = true := by
  cases s <;> simp [Src32.token, good_w32, good_imm32]

theorem good_srcF (s : SrcF) : good s.token = true := by
  cases s <;> simp [SrcF.token, good_f, good_imm32]

theorem Instr.good (i : Instr) : i.tokens.all good = true := by
  cases i with
  | special _ s => cases s <;> simp [Instr.tokens, Special.token, good_w32] <;> decide
  | bin64 op => cases op <;> simp [Instr.tokens, Bin64.token, good_w64, good_src64] <;> decide
  | shift op => cases op <;> simp [Instr.tokens, Shift.token, good_w64, good_src32] <;> decide
  | setp c => cases c <;> simp [Instr.tokens, Cmp.token, good_pred, good_w64, good_src64] <;>
      decide
  | binF op => cases op <;> simp [Instr.tokens, BinF.token, good_f] <;> decide
  | setpF c => cases c <;> simp [Instr.tokens, CmpF.token, good_pred, good_f] <;> decide
  | _ => simp [Instr.tokens, addressTokens, good_w32, good_w64, good_f, good_pred, good_param,
      good_src64, good_src32, good_srcF, good_imm64] <;> decide

mutual
  theorem Stmt.good : ∀ (s : Stmt) (n : Nat), (Stmt.tokens n s).1.all good = true
    | .instr none i, _ => by simpa [Stmt.tokens] using Instr.good i
    | .instr (some g) i, _ => by simp [Stmt.tokens, good_guard, Instr.good i]
    | .ite p ts es, n => by
        simp [Stmt.tokens, branchUnless, good_guard, good_label, Stmt.listGood ts,
          Stmt.listGood es]
        decide
    | .while_ c p b, n => by
        simp [Stmt.tokens, branchUnless, good_guard, good_label, Stmt.listGood c,
          Stmt.listGood b]
        decide
    | .ret, _ => by simp [Stmt.tokens]; decide

  theorem Stmt.listGood : ∀ (ss : List Stmt) (n : Nat), (Stmt.listTokens n ss).1.all good = true
    | [], _ => rfl
    | s :: rest, n => by simp [Stmt.listTokens, Stmt.good s n, Stmt.listGood rest]
end

theorem paramTokens_good (i k : Nat) : (paramTokens i k).all good = true := by
  induction k generalizing i with
  | zero => simp [paramTokens, good_param]; decide
  | succ k ih => simp [paramTokens, good_param, ih]; decide

theorem regDecls_good (cls : String) (name : Nat → String) (hc : good cls = true)
    (hn : ∀ i, good (name i) = true) (i k : Nat) : (regDecls cls name i k).all good = true := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [regDecls, hc, hn, ih]; decide

theorem Module.good (m : Module) : m.tokens.all good = true := by
  simp only [Module.tokens, List.all_append, paramTokens_good, Stmt.listGood,
    regDecls_good ".b32" w32Token (by decide) good_w32, regDecls_good ".b64" w64Token (by decide)
      good_w64, regDecls_good ".f32" fToken (by decide) good_f,
    regDecls_good ".pred" predToken (by decide) good_pred, Bool.and_true]
  decide

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

end LeanExe.PTX
