import RaftKV.Protocol.Codec

/-!
# Framing: `List Token` ↔ `String`

The lower half of the wire format. Tokens are rendered space-separated as
`n:<decimal>` or `s:<hex>`, where `<hex>` is the lowercase hex of the string's
UTF-8 bytes. Since neither a decimal numeral nor a hex string can contain a
space, splitting on spaces recovers the token boundaries exactly.

**Trust status.** Unlike `RaftKV.Codec`, this layer is *tested, not proved*.
Proving it would require lemmas about `String.splitOn` that Lean core does not
currently provide. It is therefore part of the trusted base, and deliberately
kept trivial so that reading it is a realistic substitute for proving it.
`RaftKV.Frame.selfCheck` re-decodes every outgoing message before it is sent,
turning any encoding fault into a loud local failure rather than silent
corruption of a peer's state.
-/

namespace RaftKV.Frame

/-- Lowercase hex digit for a value below 16. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Value of a lowercase hex digit. -/
def unhexDigit (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else none

/-- Hex-encode a string's UTF-8 bytes. -/
def toHex (s : String) : String :=
  s.toUTF8.foldl (fun acc b =>
    (acc.push (hexDigit (b.toNat / 16))).push (hexDigit (b.toNat % 16))) ""

/-- Decode a hex string back to a `String`. -/
def ofHex (s : String) : Option String := do
  let cs := s.toList
  if cs.length % 2 != 0 then none else
  let rec go : List Char → Option (List UInt8)
    | [] => some []
    | a :: b :: rest => do
        let hi ← unhexDigit a
        let lo ← unhexDigit b
        let tl ← go rest
        some (UInt8.ofNat (hi * 16 + lo) :: tl)
    | _ => none
  let bytes ← go cs
  String.fromUTF8? ⟨bytes.toArray⟩

/-- Render one token. -/
def renderToken : Token → String
  | .n v => s!"n:{v}"
  | .s v => s!"s:{toHex v}"

/-- Parse one token. -/
def parseToken (s : String) : Option Token :=
  if s.startsWith "n:" then (s.drop 2).toString.toNat?.map Token.n
  else if s.startsWith "s:" then (ofHex (s.drop 2).toString).map Token.s
  else none

/-- Render a token list as a single line (contains no newline). -/
def frame (ts : List Token) : String := " ".intercalate (ts.map renderToken)

/-- Parse a line back into a token list. -/
def unframe (s : String) : Option (List Token) :=
  let parts := (s.splitOn " ").filter (· != "")
  parts.foldr (fun p acc => do
    let t ← parseToken p
    let ts ← acc
    some (t :: ts)) (some [])

/-- Encode a message to a wire line. -/
def encodeMsg (m : Msg) : String := frame (Codec.encode m)

/-- Decode a wire line to a message. -/
def decodeMsg (s : String) : Option Msg := do
  let ts ← unframe s
  let (m, _) ← Codec.decode (α := Msg) ts
  some m

/--
Re-decode an encoded message and confirm it round-trips.

The semantic half of the codec is proved; this guards the framing half at
runtime, so a framing fault fails loudly at the sender instead of corrupting a
peer.
-/
def selfCheck (m : Msg) : Option String :=
  let line := encodeMsg m
  if decodeMsg line == some m then some line else none

end RaftKV.Frame
