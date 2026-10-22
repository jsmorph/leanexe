import Library.Numerics.Decimal.Shared.StrconvGrammar

/-!
A decoder for the grammar of `StrconvGrammar`, written as a function on lists of bytes with
unbounded integers, and the theorem `derives_iff_decode` that it returns `some n` exactly for the
derivations `Derives general s n`.  The decoder reads the sign, then tests for `inf`, `infinity`,
`nan`, and the prefix `0x` in the general grammar, then splits the significand at the first byte
that is no digit with `takeWhile` and `dropWhile`, and reads the exponent.  The parser's scanner
computes the same splits with positions in an array.  `derives_unique` follows, since `decode` is a
function, and `derives_general` shows that every RFC 8259 number is a number of the general
grammar with the same value.
-/

namespace Library.Numerics.Decimal.Shared.StrconvDecode
open StrconvGrammar

/-- The sign and the rest: `-`, and `+` in the general grammar, are removed. -/
def decodeSign (general : Bool) (s : List UInt8) : Bool × List UInt8 :=
  match s with
  | b :: r => if b = 0x2D then (true, r) else if general = true ∧ b = 0x2B then (false, r)
      else (false, b :: r)
  | [] => (false, [])

/-- The value of an exponent's optional sign and digits. -/
def decodeExpDigits (t : List UInt8) : Option Int :=
  match t with
  | b :: r =>
    if b = 0x2D then (if r ≠ [] ∧ r.all isDigit then some (-(decValue r : Int)) else none)
    else if b = 0x2B then (if r ≠ [] ∧ r.all isDigit then some (decValue r : Int) else none)
    else if (b :: r).all isDigit then some (decValue (b :: r) : Int) else none
  | [] => none

/-- The value of an exponent with a marker byte from `markers`. -/
def decodeExp (markers : List UInt8) (x : List UInt8) : Option Int :=
  match x with
  | m :: t => if m ∈ markers then decodeExpDigits t else none
  | [] => none

/-- The value of an optional exponent, 0 when absent. -/
def decodeOptExp (markers : List UInt8) (x : List UInt8) : Option Int :=
  if x = [] then some 0 else decodeExp markers x

/-- A significand of the general grammar: its integer digits, its fraction digits, and the rest
of the input. -/
def decodeSig (digit : UInt8 → Bool) (r : List UInt8) :
    Option (List UInt8 × List UInt8 × List UInt8) :=
  match r.dropWhile digit with
  | b :: t =>
    if b = 0x2E then
      (if r.takeWhile digit ++ t.takeWhile digit ≠ [] then
        some (r.takeWhile digit, t.takeWhile digit, t.dropWhile digit) else none)
    else if r.takeWhile digit ≠ [] then some (r.takeWhile digit, [], b :: t) else none
  | [] => if r.takeWhile digit ≠ [] then some (r.takeWhile digit, [], []) else none

/-- Whether a string of digits is an RFC 8259 `int`: `0`, or a first digit from 1 to 9. -/
def jsonIntOk (i : List UInt8) : Bool :=
  match i with
  | c :: ds => (c = 0x30 ∧ ds = []) || decide (0x31 ≤ c)
  | [] => false

/-- An RFC 8259 `int [ frac ]`: its integer digits, its fraction digits, and the rest. -/
def decodeJson (r : List UInt8) : Option (List UInt8 × List UInt8 × List UInt8) :=
  if jsonIntOk (r.takeWhile isDigit) then
    match r.dropWhile isDigit with
    | b :: t =>
      if b = 0x2E then
        (if t.takeWhile isDigit ≠ [] then
          some (r.takeWhile isDigit, t.takeWhile isDigit, t.dropWhile isDigit) else none)
      else some (r.takeWhile isDigit, [], b :: t)
    | [] => some (r.takeWhile isDigit, [], [])
  else none

/-- The number that `s` denotes in the grammar selected by `general`, or `none`. -/
def decode (general : Bool) (s : List UInt8) : Option Num :=
  let neg := (decodeSign general s).1
  let r := (decodeSign general s).2
  if general = true ∧ (r.map lower = ascii "inf" ∨ r.map lower = ascii "infinity") then
    some (.inf neg)
  else if general = true ∧ r.map lower = ascii "nan" then some .nan
  else if general = true ∧ (r.take 2 = ascii "0x" ∨ r.take 2 = ascii "0X") then
    match decodeSig isHexDigit (r.drop 2) with
    | some (i, f, x) =>
      (decodeExp (ascii "pP") x).map fun e => .hex neg (hexValue (i ++ f)) (e - 4 * f.length)
    | none => none
  else
    match (if general = true then decodeSig isDigit r else decodeJson r) with
    | some (i, f, x) =>
      (decodeOptExp (ascii "eE") x).map fun e => .dec neg (decValue (i ++ f)) (e - f.length)
    | none => none

/-! ### Splits -/

/-- `x` is empty or starts with a byte outside the class `p`. -/
def Stops (p : UInt8 → Bool) (x : List UInt8) : Prop := ∀ b t, x = b :: t → p b = false

theorem split_of_stops (p : UInt8 → Bool) (l x : List UInt8) (h : ∀ a ∈ l, p a = true)
    (hx : Stops p x) : (l ++ x).takeWhile p = l ∧ (l ++ x).dropWhile p = x := by
  rw [List.takeWhile_append_of_pos h, List.dropWhile_append_of_pos h]
  cases x with
  | nil => simp
  | cons b t =>
    have hb := hx b t rfl
    have hb' : ¬ p b = true := by simp [hb]
    simp [List.takeWhile_cons_of_neg hb', List.dropWhile_cons_of_neg hb']

theorem takeWhile_all (p : UInt8 → Bool) (l : List UInt8) : ∀ a ∈ l.takeWhile p, p a = true := by
  induction l with
  | nil => simp
  | cons b t ih =>
    intro a ha
    by_cases hb : p b = true
    · rw [List.takeWhile_cons_of_pos hb] at ha
      rcases List.mem_cons.mp ha with h | h
      · rw [h]; exact hb
      · exact ih a h
    · rw [List.takeWhile_cons_of_neg hb] at ha
      simp at ha

theorem dropWhile_stops (p : UInt8 → Bool) (l : List UInt8) : Stops p (l.dropWhile p) := by
  induction l with
  | nil => intro b t h; simp at h
  | cons c t ih =>
    intro b u h
    by_cases hc : p c = true
    · rw [List.dropWhile_cons_of_pos hc] at h
      exact ih b u h
    · rw [List.dropWhile_cons_of_neg hc] at h
      simp only [List.cons.injEq] at h
      rw [← h.1]
      simpa using hc

theorem all_iff (p : UInt8 → Bool) (l : List UInt8) : l.all p = true ↔ ∀ a ∈ l, p a = true := by
  simp [List.all_eq_true]

/-! ### Signs -/

theorem decodeSign_spec (general : Bool) (s : List UInt8) :
    s = (if (decodeSign general s).1 then ascii "-" else
      if (decodeSign general s).2 = s then [] else ascii "+") ++ (decodeSign general s).2 ∧
    Sign general (if (decodeSign general s).1 then ascii "-" else
      if (decodeSign general s).2 = s then [] else ascii "+") (decodeSign general s).1 := by
  cases s with
  | nil => exact ⟨rfl, by simpa [decodeSign] using Sign.none general⟩
  | cons b r =>
    by_cases h1 : b = 0x2D
    · subst h1
      exact ⟨rfl, by simpa [decodeSign] using Sign.minus general⟩
    · by_cases h2 : general = true ∧ b = 0x2B
      · obtain ⟨hg, hb⟩ := h2
        subst hg hb
        have hne : ¬ r = (43 : UInt8) :: r := fun h => by
          have := congrArg List.length h; simp at this
        simp only [decodeSign, h1, ite_false, and_self, ite_true, Bool.false_eq_true, hne]
        exact ⟨rfl, Sign.plus⟩
      · simp only [decodeSign, h1, h2, ite_false, Bool.false_eq_true, ite_true]
        exact ⟨rfl, Sign.none general⟩

/-- The sign is the whole of what `decodeSign` removes when the rest starts with no sign byte. -/
theorem decodeSign_of_sign (general : Bool) (sg r : List UInt8) (neg : Bool)
    (h : Sign general sg neg) (hr : ∀ b t, r = b :: t → b ≠ 0x2D ∧ b ≠ 0x2B) :
    decodeSign general (sg ++ r) = (neg, r) := by
  cases h with
  | none =>
    cases r with
    | nil => rfl
    | cons b t =>
      obtain ⟨h1, h2⟩ := hr b t rfl
      simp [decodeSign, h1, h2]
  | minus => rfl
  | plus => rfl

/-! ### Exponents -/

theorem exponent_iff (markers x : List UInt8) (e : Int) :
    Exponent markers x e ↔ decodeExp markers x = some e := by
  constructor
  · intro h
    cases h with
    | plain m ds hm hne hd =>
      obtain ⟨b, r, rfl⟩ := List.exists_cons_of_ne_nil hne
      have hb := hd b (by simp)
      have h1 : b ≠ 0x2D := fun h => by subst h; simp [isDigit] at hb
      have h2 : b ≠ 0x2B := fun h => by subst h; simp [isDigit] at hb
      simp [decodeExp, hm, decodeExpDigits, h1, h2, (all_iff isDigit _).mpr hd]
    | plus m ds hm hne hd =>
      simp [decodeExp, hm, decodeExpDigits, hne, (all_iff isDigit _).mpr hd, ascii_plus]
    | minus m ds hm hne hd =>
      simp [decodeExp, hm, decodeExpDigits, hne, (all_iff isDigit _).mpr hd, ascii_minus]
  · intro h
    match x, h with
    | m :: t, h =>
      simp only [decodeExp] at h
      by_cases hm : m ∈ markers
      · rw [if_pos hm] at h
        match t, h with
        | b :: r, h =>
          simp only [decodeExpDigits] at h
          by_cases h1 : b = 0x2D
          · subst h1
            simp only [ite_true] at h
            by_cases hc : r ≠ [] ∧ r.all isDigit = true
            · rw [if_pos hc] at h
              cases h
              exact Exponent.minus m r hm hc.1 ((all_iff _ _).mp hc.2)
            · rw [if_neg hc] at h; cases h
          · rw [if_neg h1] at h
            by_cases h2 : b = 0x2B
            · subst h2
              simp only [ite_true] at h
              by_cases hc : r ≠ [] ∧ r.all isDigit = true
              · rw [if_pos hc] at h
                cases h
                exact Exponent.plus m r hm hc.1 ((all_iff _ _).mp hc.2)
              · rw [if_neg hc] at h; cases h
            · rw [if_neg h2] at h
              by_cases hc : (b :: r).all isDigit = true
              · rw [if_pos hc] at h
                cases h
                exact Exponent.plain m (b :: r) hm (by simp) ((all_iff _ _).mp hc)
              · rw [if_neg hc] at h; cases h
        | [], h => simp [decodeExpDigits] at h
      · rw [if_neg hm] at h; cases h
    | [], h => simp [decodeExp] at h

theorem optExponent_iff (markers x : List UInt8) (e : Int) :
    OptExponent markers x e ↔ decodeOptExp markers x = some e := by
  constructor
  · intro h
    cases h with
    | none => rfl
    | some x e h =>
      have hne : x ≠ [] := by cases h <;> simp
      rw [decodeOptExp, if_neg hne]
      exact (exponent_iff markers x e).mp h
  · intro h
    by_cases hx : x = []
    · subst hx
      simp only [decodeOptExp, ite_true, Option.some.injEq] at h
      subst h
      exact OptExponent.none
    · rw [decodeOptExp, if_neg hx] at h
      exact OptExponent.some x e ((exponent_iff markers x e).mpr h)

/-- An exponent starts with one of its markers. -/
theorem exponent_head (markers x : List UInt8) (e : Int) (h : Exponent markers x e) :
    ∃ m t, x = m :: t ∧ m ∈ markers := by
  cases h with
  | plain m ds hm _ _ => exact ⟨m, ds, rfl, hm⟩
  | plus m ds hm _ _ => exact ⟨m, _, rfl, hm⟩
  | minus m ds hm _ _ => exact ⟨m, _, rfl, hm⟩

/-- Every byte of an exponent is a marker, a sign, or a digit. -/
theorem exponent_bytes (markers x : List UInt8) (e : Int) (h : Exponent markers x e) :
    ∀ b ∈ x, b ∈ markers ∨ b = 0x2B ∨ b = 0x2D ∨ isDigit b = true := by
  cases h with
  | plain m ds hm _ hd =>
    intro b hb
    rcases List.mem_cons.mp hb with h | h
    · exact Or.inl (h ▸ hm)
    · exact Or.inr (Or.inr (Or.inr (hd b h)))
  | plus m ds hm _ hd =>
    intro b hb
    simp only [ascii_plus, List.cons_append, List.nil_append, List.mem_cons] at hb
    rcases hb with h | h | h
    · exact Or.inl (h ▸ hm)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (hd b h)))
  | minus m ds hm _ hd =>
    intro b hb
    simp only [ascii_minus, List.cons_append, List.nil_append, List.mem_cons] at hb
    rcases hb with h | h | h
    · exact Or.inl (h ▸ hm)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (hd b h)))

/-! ### Significands -/

theorem decodeSig_of (digit : UInt8 → Bool) (hpt : digit 0x2E = false) (m i f x : List UInt8)
    (h : Significand digit m i f) (hx : Stops digit x)
    (hxp : ∀ t, x ≠ 0x2E :: t) : decodeSig digit (m ++ x) = some (i, f, x) := by
  match h with
  | .int i hne hd =>
    obtain ⟨h1, h2⟩ := split_of_stops digit i x hd hx
    unfold decodeSig
    rw [h2, h1]
    cases x with
    | nil => simp [hne]
    | cons b t =>
      have hb : b ≠ 0x2E := fun hb => hxp t (by rw [hb])
      simp [hb, hne]
  | .point i f hne hd =>
    have hi : ∀ a ∈ i, digit a = true := fun a ha => hd a (List.mem_append_left f ha)
    have hf : ∀ a ∈ f, digit a = true := fun a ha => hd a (List.mem_append_right i ha)
    have hs : Stops digit (ascii "." ++ f ++ x) := by
      intro b t h
      simp only [ascii_point, List.cons_append, List.nil_append, List.cons.injEq] at h
      rw [← h.1]; exact hpt
    obtain ⟨h1, h2⟩ := split_of_stops digit i (ascii "." ++ f ++ x) hi hs
    obtain ⟨h3, h4⟩ := split_of_stops digit f x hf hx
    unfold decodeSig
    rw [show i ++ ascii "." ++ f ++ x = i ++ (ascii "." ++ f ++ x) by simp, h2, h1]
    simp only [ascii_point, List.cons_append, List.nil_append, ite_true]
    rw [h3, h4]
    simp [hne]

theorem decodeSig_spec (digit : UInt8 → Bool) (r i f x : List UInt8)
    (h : decodeSig digit r = some (i, f, x)) :
    ∃ m, r = m ++ x ∧ Significand digit m i f := by
  have hr := (List.takeWhile_append_dropWhile (p := digit) (l := r)).symm
  have hi := takeWhile_all digit r
  unfold decodeSig at h
  rcases hd : r.dropWhile digit with _ | ⟨b, t⟩ <;> rw [hd] at h hr <;> dsimp only at h
  · by_cases hne : r.takeWhile digit ≠ []
    · rw [if_pos hne] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨r.takeWhile digit, hr, Significand.int _ hne hi⟩
    · rw [if_neg hne] at h; cases h
  · by_cases hb : b = 0x2E
    · subst hb
      simp only [ite_true] at h
      by_cases hne : r.takeWhile digit ++ t.takeWhile digit ≠ []
      · rw [if_pos hne] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨r.takeWhile digit ++ ascii "." ++ t.takeWhile digit, ?_, ?_⟩
        · have ht := (List.takeWhile_append_dropWhile (p := digit) (l := t)).symm
          conv_lhs => rw [hr, ht]
          simp [ascii_point]
        · refine Significand.point _ _ hne ?_
          intro a ha
          rcases List.mem_append.mp ha with h' | h'
          · exact hi a h'
          · exact takeWhile_all digit t a h'
      · rw [if_neg hne] at h; cases h
    · rw [if_neg hb] at h
      by_cases hne : r.takeWhile digit ≠ []
      · rw [if_pos hne] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨r.takeWhile digit, hr, Significand.int _ hne hi⟩
      · rw [if_neg hne] at h; cases h

/-! ### RFC 8259 significands -/

theorem jsonInt_digits (i : List UInt8) (h : JsonInt i) : ∀ b ∈ i, isDigit b = true := by
  cases h with
  | zero => intro b hb; simp [ascii_zero] at hb; subst hb; decide
  | nonzero c ds h1 h2 hd =>
    intro b hb
    rcases List.mem_cons.mp hb with h | h
    · subst h
      simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, h2⟩
      rw [UInt8.le_iff_toNat_le] at h1 ⊢
      simp only [UInt8.reduceToNat] at h1 ⊢
      omega
    · exact hd b h

theorem jsonIntOk_of (i : List UInt8) (h : JsonInt i) : jsonIntOk i = true := by
  cases h with
  | zero => rfl
  | nonzero c ds h1 _ _ => simp [jsonIntOk, h1]

theorem jsonInt_of_ok (i : List UInt8) (h : jsonIntOk i = true)
    (hd : ∀ b ∈ i, isDigit b = true) : JsonInt i := by
  match i, h with
  | c :: ds, h =>
    simp only [jsonIntOk, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · subst h1 h2; exact JsonInt.zero
    · have hc := hd c (by simp)
      simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hc
      exact JsonInt.nonzero c ds h hc.2 (fun b hb => hd b (List.mem_cons_of_mem c hb))

theorem decodeJson_of (i fr f x : List UInt8) (hi : JsonInt i) (hf : JsonFrac fr f)
    (hx : Stops isDigit x) (hxp : ∀ t, x ≠ 0x2E :: t) :
    decodeJson (i ++ fr ++ x) = some (i, f, x) := by
  have hid := jsonInt_digits i hi
  match hf with
  | .none =>
    obtain ⟨h1, h2⟩ := split_of_stops isDigit i x hid hx
    unfold decodeJson
    rw [show i ++ [] ++ x = i ++ x by simp, h1, h2, if_pos (jsonIntOk_of i hi)]
    cases x with
    | nil => rfl
    | cons b t =>
      have hb : b ≠ 0x2E := fun hb => hxp t (by rw [hb])
      simp [hb]
  | .some f hne hfd =>
    have hs : Stops isDigit (ascii "." ++ f ++ x) := by
      intro b t h
      simp only [ascii_point, List.cons_append, List.nil_append, List.cons.injEq] at h
      rw [← h.1]; decide
    obtain ⟨h1, h2⟩ := split_of_stops isDigit i (ascii "." ++ f ++ x) hid hs
    obtain ⟨h3, h4⟩ := split_of_stops isDigit f x hfd hx
    unfold decodeJson
    rw [show i ++ (ascii "." ++ f) ++ x = i ++ (ascii "." ++ f ++ x) by simp, h1, h2,
      if_pos (jsonIntOk_of i hi)]
    simp only [ascii_point, List.cons_append, List.nil_append, ite_true]
    rw [h3, h4]
    simp [hne]

theorem decodeJson_spec (r i f x : List UInt8) (h : decodeJson r = some (i, f, x)) :
    ∃ fr, r = i ++ fr ++ x ∧ JsonInt i ∧ JsonFrac fr f := by
  have hr := (List.takeWhile_append_dropWhile (p := isDigit) (l := r)).symm
  have hi := takeWhile_all isDigit r
  unfold decodeJson at h
  by_cases hok : jsonIntOk (r.takeWhile isDigit) = true
  · rw [if_pos hok] at h
    have hj := jsonInt_of_ok _ hok hi
    rcases hd : r.dropWhile isDigit with _ | ⟨b, t⟩ <;> rw [hd] at h hr <;> dsimp only at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨[], by simpa using hr, hj, JsonFrac.none⟩
    · by_cases hb : b = 0x2E
      · subst hb
        simp only [ite_true] at h
        by_cases hne : t.takeWhile isDigit ≠ []
        · rw [if_pos hne] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨ascii "." ++ t.takeWhile isDigit, ?_, hj,
            JsonFrac.some _ hne (takeWhile_all isDigit t)⟩
          have ht := (List.takeWhile_append_dropWhile (p := isDigit) (l := t)).symm
          conv_lhs => rw [hr, ht]
          simp [ascii_point]
        · rw [if_neg hne] at h; cases h
      · rw [if_neg hb] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨[], by simpa using hr, hj, JsonFrac.none⟩
  · rw [if_neg hok] at h; cases h

/-! ### Bytes -/

/-- A byte that can occur in a decimal number: a digit, `.`, `e`, `E`, `+`, or `-`. -/
def decByte (b : UInt8) : Bool :=
  isDigit b || b == 0x2E || b == 0x65 || b == 0x45 || b == 0x2B || b == 0x2D

theorem byte_cases (P : UInt8 → Prop) (h : ∀ n, n < 256 → P (UInt8.ofNat n)) (b : UInt8) :
    P b := by
  have := h b.toNat b.toNat_lt
  simpa using this

theorem decByte_facts (b : UInt8) (h : decByte b = true) :
    lower b ≠ 0x69 ∧ lower b ≠ 0x6E ∧ b ≠ 0x78 ∧ b ≠ 0x58 := by
  revert h
  refine byte_cases (fun b => decByte b = true →
    lower b ≠ 0x69 ∧ lower b ≠ 0x6E ∧ b ≠ 0x78 ∧ b ≠ 0x58) ?_ b
  decide +kernel

theorem lower_i_not_sign (b : UInt8) (h : lower b = 0x69 ∨ lower b = 0x6E) :
    b ≠ 0x2D ∧ b ≠ 0x2B := by
  constructor <;> (intro hb; subst hb; revert h; decide)

theorem digit_not_sign (b : UInt8) (h : isDigit b = true) : b ≠ 0x2D ∧ b ≠ 0x2B := by
  constructor <;> (intro hb; subst hb; revert h; decide)

/-- A string of decimal bytes is none of the special words and has no prefix `0x`. -/
theorem not_special (r : List UInt8) (h : ∀ b ∈ r, decByte b = true) :
    ¬ (r.map lower = ascii "inf" ∨ r.map lower = ascii "infinity") ∧
      ¬ r.map lower = ascii "nan" ∧ ¬ (r.take 2 = ascii "0x" ∨ r.take 2 = ascii "0X") := by
  have hl : ∀ c, c ∈ r.map lower → c ≠ 0x69 ∧ c ≠ 0x6E := by
    intro c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    exact ⟨(decByte_facts b (h b hb)).1, (decByte_facts b (h b hb)).2.1⟩
  have hx : ∀ c, c ∈ r.take 2 → c ≠ 0x78 ∧ c ≠ 0x58 := by
    intro c hc
    have hb := h c (List.mem_of_mem_take hc)
    exact ⟨(decByte_facts c hb).2.2.1, (decByte_facts c hb).2.2.2⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro (h1 | h1)
    · exact (hl 0x69 (by rw [h1]; decide)).1 rfl
    · exact (hl 0x69 (by rw [h1]; decide)).1 rfl
  · intro h1
    exact (hl 0x6E (by rw [h1]; decide)).2 rfl
  · rintro (h1 | h1)
    · exact (hx 0x78 (by rw [h1]; decide)).1 rfl
    · exact (hx 0x58 (by rw [h1]; decide)).2 rfl

theorem optExponent_bytes (x : List UInt8) (e : Int) (h : OptExponent (ascii "eE") x e) :
    ∀ b ∈ x, decByte b = true := by
  cases h with
  | none => simp
  | some x e h =>
    intro b hb
    rcases exponent_bytes _ x e h b hb with h1 | h1 | h1 | h1
    · simp only [ascii_eE, List.mem_cons, List.not_mem_nil, or_false] at h1
      rcases h1 with rfl | rfl <;> decide
    · subst h1; decide
    · subst h1; decide
    · simp [decByte, h1]

/-- After a significand, an optional exponent stops the digits and has no point. -/
theorem optExponent_stops (digit : UInt8 → Bool) (hm : digit 0x65 = false ∧ digit 0x45 = false)
    (x : List UInt8) (e : Int) (h : OptExponent (ascii "eE") x e) :
    Stops digit x ∧ ∀ t, x ≠ 0x2E :: t := by
  cases h with
  | none => exact ⟨fun b t h => by simp at h, fun t h => by simp at h⟩
  | some x e h =>
    obtain ⟨m, t, rfl, hmem⟩ := exponent_head _ x e h
    simp only [ascii_eE, List.mem_cons, List.not_mem_nil, or_false] at hmem
    refine ⟨fun b u h => ?_, fun u h => ?_⟩
    · simp only [List.cons.injEq] at h
      rw [← h.1]
      rcases hmem with rfl | rfl
      · exact hm.1
      · exact hm.2
    · simp only [List.cons.injEq] at h
      rcases hmem with rfl | rfl <;> exact absurd h.1 (by decide)

theorem significand_bytes (m i f : List UInt8) (h : Significand isDigit m i f) :
    ∀ b ∈ m, decByte b = true := by
  match h with
  | .int i _ hd => intro b hb; simp [decByte, hd b hb]
  | .point i f _ hd =>
    intro b hb
    simp only [ascii_point, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with (hb | hb) | hb
    · simp [decByte, hd b (List.mem_append_left f hb)]
    · subst hb; decide
    · simp [decByte, hd b (List.mem_append_right i hb)]

theorem significand_head (digit : UInt8 → Bool) (m i f : List UInt8)
    (h : Significand digit m i f) : ∃ c t, m = c :: t ∧ (digit c = true ∨ c = 0x2E) := by
  match h with
  | .int i hne hd =>
    obtain ⟨c, t, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨c, t, rfl, Or.inl (hd c (by simp))⟩
  | .point i f hne hd =>
    cases i with
    | nil => exact ⟨0x2E, f, by simp [ascii_point], Or.inr rfl⟩
    | cons c t => exact ⟨c, t ++ ascii "." ++ f, by simp, Or.inl (hd c (by simp))⟩

/-! ### The decoder and the grammar -/

theorem decode_of_derives (general : Bool) (s : List UInt8) (n : Num)
    (h : Derives general s n) : decode general s = some n := by
  cases h with
  | json sg i fr f x neg e hs hi hf hx =>
    have hd := jsonInt_digits i hi
    obtain ⟨c, t, hct⟩ : ∃ c t, i ++ fr ++ x = c :: t := by
      cases hi with
      | zero => exact ⟨_, _, rfl⟩
      | nonzero c ds _ _ _ => exact ⟨c, _, rfl⟩
    have hc : isDigit c = true := by
      cases hi with
      | zero => simp [ascii_zero] at hct; rw [← hct.1]; decide
      | nonzero c' ds _ _ _ =>
        simp only [List.cons_append, List.cons.injEq] at hct
        rw [← hct.1]; exact hd c' (by simp)
    have hsign := decodeSign_of_sign false sg (i ++ fr ++ x) neg hs (by
      intro b u hbu; rw [hct] at hbu; simp only [List.cons.injEq] at hbu
      rw [← hbu.1]; exact digit_not_sign c hc)
    obtain ⟨hx1, hx2⟩ := optExponent_stops isDigit (by decide) x e hx
    have hj := decodeJson_of i fr f x hi hf hx1 hx2
    have he := (optExponent_iff _ x e).mp hx
    unfold decode
    rw [show sg ++ i ++ fr ++ x = sg ++ (i ++ fr ++ x) by simp, hsign]
    simp only [Bool.false_eq_true, false_and, ite_false, hj, he, Option.map_some]
  | decimal sg m i f x neg e hs hm hx =>
    obtain ⟨c, t, rfl, hc⟩ := significand_head isDigit m i f hm
    have hsign := decodeSign_of_sign true sg (c :: t ++ x) neg hs (by
      intro b u hbu; simp only [List.cons_append, List.cons.injEq] at hbu
      rw [← hbu.1]
      rcases hc with hc | hc
      · exact digit_not_sign c hc
      · subst hc; decide)
    have hbytes : ∀ b ∈ c :: t ++ x, decByte b = true := by
      intro b hb
      rcases List.mem_append.mp hb with h' | h'
      · exact significand_bytes _ i f hm b h'
      · exact optExponent_bytes x e hx b h'
    obtain ⟨n1, n2, n3⟩ := not_special _ hbytes
    obtain ⟨hx1, hx2⟩ := optExponent_stops isDigit (by decide) x e hx
    have hsig := decodeSig_of isDigit (by decide) _ i f x hm hx1 hx2
    have he := (optExponent_iff _ x e).mp hx
    unfold decode
    rw [show sg ++ c :: t ++ x = sg ++ (c :: t ++ x) by simp, hsign]
    simp only [true_and]
    rw [if_neg n1, if_neg n2, if_neg n3]
    simp only [ite_true, hsig, he, Option.map_some]
  | hex sg z m i f x neg e hs hz hm hx =>
    have hz' : z = [0x30, 0x78] ∨ z = [0x30, 0x58] := by
      simpa [ascii_0x, ascii_0X] using hz
    have hsign := decodeSign_of_sign true sg (z ++ m ++ x) neg hs (by
      intro b u hbu
      rcases hz' with rfl | rfl <;>
        (simp only [List.cons_append, List.cons.injEq] at hbu; rw [← hbu.1]; decide))
    obtain ⟨mk, t, rfl, hmk⟩ := exponent_head _ x e hx
    have hx1 : Stops isHexDigit (mk :: t) := by
      intro b u h
      simp only [List.cons.injEq] at h
      rw [← h.1]
      simp only [ascii_pP, List.mem_cons, List.not_mem_nil, or_false] at hmk
      rcases hmk with rfl | rfl <;> decide
    have hx2 : ∀ u, mk :: t ≠ 0x2E :: u := by
      intro u h
      simp only [List.cons.injEq] at h
      simp only [ascii_pP, List.mem_cons, List.not_mem_nil, or_false] at hmk
      rcases hmk with rfl | rfl <;> exact absurd h.1 (by decide)
    have hsig := decodeSig_of isHexDigit (by decide) m i f _ hm hx1 hx2
    have he := (exponent_iff _ _ e).mp hx
    have hn : ¬ ((z ++ m ++ mk :: t).map lower = ascii "inf" ∨
        (z ++ m ++ mk :: t).map lower = ascii "infinity") ∧
        ¬ (z ++ m ++ mk :: t).map lower = ascii "nan" := by
      rcases hz' with rfl | rfl <;> simp [lower, ascii_inf, ascii_infinity, ascii_nan]
    have ht : (z ++ m ++ mk :: t).take 2 = ascii "0x" ∨
        (z ++ m ++ mk :: t).take 2 = ascii "0X" := by
      rcases hz' with rfl | rfl <;> simp [ascii_0x, ascii_0X]
    have hdrop : (z ++ m ++ mk :: t).drop 2 = m ++ mk :: t := by
      rcases hz' with rfl | rfl <;> simp
    unfold decode
    rw [show sg ++ z ++ m ++ mk :: t = sg ++ (z ++ m ++ mk :: t) by simp, hsign]
    simp only [true_and]
    rw [if_neg hn.1, if_neg hn.2, if_pos ht, hdrop, hsig]
    simp [he]
  | inf sg w neg hs hw =>
    have hne : ∃ c u, w = c :: u ∧ lower c = 0x69 := by
      cases w with
      | nil => simp [ascii_inf, ascii_infinity] at hw
      | cons c u =>
        refine ⟨c, u, rfl, ?_⟩
        simp only [List.map_cons, ascii_inf, ascii_infinity, List.mem_cons, List.cons.injEq,
          List.not_mem_nil, or_false] at hw
        rcases hw with h | h <;> exact h.1
    obtain ⟨c, u, rfl, hc⟩ := hne
    have hsign := decodeSign_of_sign true sg (c :: u) neg hs (by
      intro b v hbv; simp only [List.cons.injEq] at hbv
      rw [← hbv.1]; exact lower_i_not_sign c (Or.inl hc))
    unfold decode
    rw [hsign]
    simp only [true_and]
    rw [if_pos (by simpa using hw)]
  | nan sg w neg hs hw =>
    have hne : ∃ c u, w = c :: u ∧ lower c = 0x6E := by
      cases w with
      | nil => simp [ascii_nan] at hw
      | cons c u =>
        refine ⟨c, u, rfl, ?_⟩
        simp only [List.map_cons, ascii_nan, List.cons.injEq] at hw
        exact hw.1
    obtain ⟨c, u, rfl, hc⟩ := hne
    have hsign := decodeSign_of_sign true sg (c :: u) neg hs (by
      intro b v hbv; simp only [List.cons.injEq] at hbv
      rw [← hbv.1]; exact lower_i_not_sign c (Or.inr hc))
    have hn : ¬ ((c :: u).map lower = ascii "inf" ∨ (c :: u).map lower = ascii "infinity") := by
      rw [hw]; decide
    unfold decode
    rw [hsign]
    simp only [true_and]
    rw [if_neg hn, if_pos hw]

theorem derives_of_decode (general : Bool) (s : List UInt8) (n : Num)
    (h : decode general s = some n) : Derives general s n := by
  obtain ⟨hs, hsg⟩ := decodeSign_spec general s
  unfold decode at h
  rcases hd : decodeSign general s with ⟨neg, r⟩
  rw [hd] at hs hsg h
  dsimp only at hs hsg h
  generalize (if neg = true then ascii "-" else if r = s then [] else ascii "+") = sg at hs hsg
  subst hs
  by_cases h1 : general = true ∧ (r.map lower = ascii "inf" ∨ r.map lower = ascii "infinity")
  · rw [if_pos h1] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hg, hw⟩ := h1
    subst hg
    exact Derives.inf sg r neg hsg (by simpa using hw)
  rw [if_neg h1] at h
  by_cases h2 : general = true ∧ r.map lower = ascii "nan"
  · rw [if_pos h2] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hg, hw⟩ := h2
    subst hg
    exact Derives.nan sg r neg hsg hw
  rw [if_neg h2] at h
  by_cases h3 : general = true ∧ (r.take 2 = ascii "0x" ∨ r.take 2 = ascii "0X")
  · rw [if_pos h3] at h
    obtain ⟨hg, hz⟩ := h3
    subst hg
    rcases hsig : decodeSig isHexDigit (r.drop 2) with _ | ⟨i, f, x⟩
    · rw [hsig] at h; cases h
    rw [hsig] at h
    dsimp only at h
    rcases he : decodeExp (ascii "pP") x with _ | e
    · rw [he] at h; cases h
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨m, hm, hsm⟩ := decodeSig_spec isHexDigit _ i f x hsig
    have hr : r = r.take 2 ++ (m ++ x) := by rw [← hm]; simp
    rw [hr, show sg ++ (r.take 2 ++ (m ++ x)) = sg ++ r.take 2 ++ m ++ x by simp]
    exact Derives.hex sg (r.take 2) m i f x neg e hsg (by simpa using hz) hsm
      ((exponent_iff _ x e).mpr he)
  rw [if_neg h3] at h
  cases general with
  | true =>
    simp only [ite_true] at h
    rcases hsig : decodeSig isDigit r with _ | ⟨i, f, x⟩
    · rw [hsig] at h; cases h
    rw [hsig] at h
    dsimp only at h
    rcases he : decodeOptExp (ascii "eE") x with _ | e
    · rw [he] at h; cases h
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨m, hm, hsm⟩ := decodeSig_spec isDigit _ i f x hsig
    rw [hm, ← List.append_assoc]
    exact Derives.decimal sg m i f x neg e hsg hsm ((optExponent_iff _ x e).mpr he)
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    rcases hj : decodeJson r with _ | ⟨i, f, x⟩
    · rw [hj] at h; cases h
    rw [hj] at h
    dsimp only at h
    rcases he : decodeOptExp (ascii "eE") x with _ | e
    · rw [he] at h; cases h
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨fr, hr, hi, hf⟩ := decodeJson_spec r i f x hj
    rw [hr, show sg ++ (i ++ fr ++ x) = sg ++ i ++ fr ++ x by simp]
    exact Derives.json sg i fr f x neg e hsg hi hf ((optExponent_iff _ x e).mpr he)

/-- The grammar's relation is the graph of the decoder. -/
theorem derives_iff_decode (general : Bool) (s : List UInt8) (n : Num) :
    Derives general s n ↔ decode general s = some n :=
  ⟨decode_of_derives general s n, derives_of_decode general s n⟩

/-- A string denotes at most one number. -/
theorem derives_unique {general : Bool} {s : List UInt8} {n n' : Num}
    (h : Derives general s n) (h' : Derives general s n') : n = n' := by
  have h1 := decode_of_derives general s n h
  have h2 := decode_of_derives general s n' h'
  rw [h1] at h2
  exact Option.some.inj h2

/-- Every RFC 8259 number is a number of the general grammar with the same value. -/
theorem derives_general {s : List UInt8} {n : Num} (h : Derives false s n) :
    Derives true s n := by
  cases h with
  | json sg i fr f x neg e hs hi hf hx =>
    have hs' : Sign true sg neg := by
      cases hs with
      | none => exact Sign.none true
      | minus => exact Sign.minus true
    have hd := jsonInt_digits i hi
    have hne : i ≠ [] := by cases hi <;> simp [ascii_zero]
    match hf with
    | .none =>
      have := Derives.decimal sg i i [] x neg e hs' (Significand.int i hne hd) hx
      simpa using this
    | .some f hfne hfd =>
      have hm : Significand isDigit (i ++ ascii "." ++ f) i f := by
        refine Significand.point i f (by simp [hne]) ?_
        intro b hb
        rcases List.mem_append.mp hb with h' | h'
        · exact hd b h'
        · exact hfd b h'
      have := Derives.decimal sg (i ++ ascii "." ++ f) i f x neg e hs' hm hx
      simpa [List.append_assoc] using this

#print axioms derives_iff_decode
#print axioms derives_unique
#print axioms derives_general

end Library.Numerics.Decimal.Shared.StrconvDecode
