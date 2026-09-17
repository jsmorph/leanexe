namespace LeanExe.WGSL

/-- The seven line-ending code points in the pinned WGSL revision. CRLF is
handled as two blankspaces after CR ends the comment. -/
def lineBreak (c : Char) : Bool :=
  [10, 11, 12, 13, 133, 8232, 8233].contains c.toNat

def blankspace (c : Char) : Bool :=
  lineBreak c || [9, 32, 8206, 8207].contains c.toNat

private def identStart (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'

private def digit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
private def identContinue (c : Char) : Bool := identStart c || digit c

private def skipLine : List Char → List Char
  | [] => []
  | c :: cs => if lineBreak c then c :: cs else skipLine cs

/-- Block comments nest. Their removal creates a token boundary. -/
private def skipBlock : Nat → List Char → Option (List Char)
  | _, [] => none
  | depth, '/' :: '*' :: cs => skipBlock (depth + 1) cs
  | 0, '*' :: '/' :: cs => some cs
  | depth + 1, '*' :: '/' :: cs => skipBlock depth cs
  | depth, _ :: cs => skipBlock depth cs
termination_by _ cs => cs.length

private def scan : Nat → List Char → Except String (List String)
  | 0, _ => .error "WGSL lexer exhausted its input bound"
  | _ + 1, [] => .ok []
  | fuel + 1, '/' :: '/' :: cs => scan fuel (skipLine cs)
  | fuel + 1, '/' :: '*' :: cs =>
      match skipBlock 0 cs with
      | none => .error "unterminated WGSL block comment"
      | some rest => scan fuel rest
  | fuel + 1, '>' :: '=' :: cs => (">=" :: ·) <$> scan fuel cs
  | fuel + 1, '|' :: '|' :: cs => ("||" :: ·) <$> scan fuel cs
  | fuel + 1, c :: cs => do
      if blankspace c then return ← scan fuel cs
      if identStart c then
        let letters := cs.takeWhile identContinue
        let rest := cs.dropWhile identContinue
        return String.ofList (c :: letters) :: (← scan fuel rest)
      if digit c then
        -- Keep the entire numeric candidate together. The narrow grammar
        -- checks suffix, canonical decimal spelling and range separately.
        let numeric := fun ch => identContinue ch || ch == '.'
        let letters := cs.takeWhile numeric
        let rest := cs.dropWhile numeric
        return String.ofList (c :: letters) :: (← scan fuel rest)
      if "@(){}[]:;,<>=+*.".toList.contains c then
        return String.singleton c :: (← scan fuel cs)
      throw s!"unsupported character in WGSL subset: {c.toNat}"

/-- A deliberately narrow lexer for the emitted GEMM syntax, not all WGSL.
No Unicode normalization, comment concatenation or source rewriting occurs. -/
def tokenize (source : String) : Except String (List String) :=
  let chars := source.toList
  if chars.contains (Char.ofNat 0) then .error "WGSL forbids null code points"
  else if chars.contains (Char.ofNat 65279) then .error "WGSL subset rejects BOM"
  else scan (chars.length + 1) chars

end LeanExe.WGSL
