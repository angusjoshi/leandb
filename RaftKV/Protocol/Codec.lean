import RaftKV.Protocol.Types

/-!
# Wire codec

Another instance of the project's abstraction pattern. `Codec` states the one
property that matters — decoding an encoding recovers the original message —
and the protocol never depends on how that is achieved.

The encoding is split in two deliberately:

* `Msg ↔ List Token`, which carries all the *semantic* structure and is proved
  round-tripping below (`decodeTokens_encodeTokens`); and
* `List Token ↔ String`, pure framing, which is where a future compact binary
  format would slot in.

`Token` exists so the semantic layer never has to reason about number-to-string
conversion — that concern belongs entirely to framing.
-/

namespace RaftKV

/-- An atom of the wire format: either a natural number or a string. -/
inductive Token where
  | n (v : Nat)
  | s (v : String)
  deriving Repr, DecidableEq, Inhabited

/-- The property any wire format must have. -/
class Codec (α : Type) where
  /-- Serialise. -/
  encode : α → List Token
  /-- Deserialise, consuming a prefix and returning the remainder. -/
  decode : List Token → Option (α × List Token)
  /-- **The law**: decoding an encoding recovers the value and leaves the rest untouched. -/
  decode_encode : ∀ (a : α) (rest : List Token), decode (encode a ++ rest) = some (a, rest)

namespace Codec

/-- Round-trip on a complete token list. -/
theorem decode_encode_nil {α : Type} [Codec α] (a : α) :
    decode (encode a) = some (a, []) := by
  simpa using decode_encode a ([] : List Token)

/-- The encoding is injective: distinct values never share a wire form. -/
theorem encode_injective {α : Type} [Codec α] {a b : α} (h : encode a = encode b) : a = b := by
  have ha := decode_encode_nil a
  have hb := decode_encode_nil b
  rw [h, hb] at ha
  exact (congrArg Prod.fst (Option.some.inj ha)).symm

end Codec

/-! ## Commands and entries -/

namespace Command

/-- Token encoding of a command. -/
def enc : Command → List Token
  | .get k   => [.n 0, .s k]
  | .put k v => [.n 1, .s k, .s v]
  | .del k   => [.n 2, .s k]

/-- Token decoding of a command. -/
def dec : List Token → Option (Command × List Token)
  | .n 0 :: .s k :: rest => some (.get k, rest)
  | .n 1 :: .s k :: .s v :: rest => some (.put k v, rest)
  | .n 2 :: .s k :: rest => some (.del k, rest)
  | _ => none

instance : Codec Command where
  encode := enc
  decode := dec
  decode_encode := by intro c rest; cases c <;> rfl

end Command

namespace Entry

/-- Token encoding of a log entry. -/
def enc (e : Entry) : List Token := .n e.term :: .n e.reqId :: Command.enc e.cmd

/-- Token decoding of a log entry. -/
def dec : List Token → Option (Entry × List Token)
  | .n t :: .n r :: rest => do
      let (c, rest) ← Command.dec rest
      some ({ term := t, cmd := c, reqId := r }, rest)
  | _ => none

instance : Codec Entry where
  encode := enc
  decode := dec
  decode_encode := by
    intro e rest
    obtain ⟨t, c, r⟩ := e
    show dec (.n t :: .n r :: (Command.enc c ++ rest)) = _
    cases c <;> rfl

end Entry

/-- Encode a list of entries, length-prefixed. -/
def encEntries (es : List Entry) : List Token := .n es.length :: es.flatMap Entry.enc

/-- Decode exactly `n` entries. -/
def decEntriesN : Nat → List Token → Option (List Entry × List Token)
  | 0, ts => some ([], ts)
  | n + 1, ts => do
      let (e, ts) ← Entry.dec ts
      let (es, ts) ← decEntriesN n ts
      some (e :: es, ts)

/-- Decode a length-prefixed entry list. -/
def decEntries : List Token → Option (List Entry × List Token)
  | .n n :: ts => decEntriesN n ts
  | _ => none

theorem decEntriesN_enc (es : List Entry) (rest : List Token) :
    decEntriesN es.length (es.flatMap Entry.enc ++ rest) = some (es, rest) := by
  induction es generalizing rest with
  | nil => rfl
  | cons e es ih =>
    have hE : Entry.dec (Entry.enc e ++ (es.flatMap Entry.enc ++ rest))
        = some (e, es.flatMap Entry.enc ++ rest) :=
      Codec.decode_encode (α := Entry) e _
    simp [List.flatMap_cons, List.append_assoc, decEntriesN, hE, ih rest]

theorem decEntries_encEntries (es : List Entry) (rest : List Token) :
    decEntries (encEntries es ++ rest) = some (es, rest) := by
  simpa [encEntries, decEntries] using decEntriesN_enc es rest

/-- Encode a list of key/value bindings, length-prefixed. -/
def encPairs (ps : List (String × String)) : List Token :=
  .n ps.length :: ps.flatMap (fun p => [.s p.1, .s p.2])

/-- Decode exactly `n` bindings. -/
def decPairsN : Nat → List Token → Option (List (String × String) × List Token)
  | 0, ts => some ([], ts)
  | n + 1, .s k :: .s v :: ts => do
      let (ps, ts) ← decPairsN n ts
      some ((k, v) :: ps, ts)
  | _ + 1, _ => none

/-- Decode a length-prefixed binding list. -/
def decPairs : List Token → Option (List (String × String) × List Token)
  | .n n :: ts => decPairsN n ts
  | _ => none

theorem decPairsN_enc (ps : List (String × String)) (rest : List Token) :
    decPairsN ps.length (ps.flatMap (fun p => [.s p.1, .s p.2]) ++ rest) = some (ps, rest) := by
  induction ps generalizing rest with
  | nil => rfl
  | cons p ps ih => simp [List.flatMap_cons, decPairsN, ih rest]

theorem decPairs_encPairs (ps : List (String × String)) (rest : List Token) :
    decPairs (encPairs ps ++ rest) = some (ps, rest) := by
  simpa [encPairs, decPairs] using decPairsN_enc ps rest

/-- Encode a list of request ids, length-prefixed. -/
def encNats (ns : List Nat) : List Token := .n ns.length :: ns.map Token.n

/-- Decode exactly `n` request ids. -/
def decNatsN : Nat → List Token → Option (List Nat × List Token)
  | 0, ts => some ([], ts)
  | n + 1, .n x :: ts => do
      let (ns, ts) ← decNatsN n ts
      some (x :: ns, ts)
  | _ + 1, _ => none

/-- Decode a length-prefixed request-id list. -/
def decNats : List Token → Option (List Nat × List Token)
  | .n n :: ts => decNatsN n ts
  | _ => none

theorem decNatsN_enc (ns : List Nat) (rest : List Token) :
    decNatsN ns.length (ns.map Token.n ++ rest) = some (ns, rest) := by
  induction ns generalizing rest with
  | nil => rfl
  | cons n ns ih => simp [decNatsN, ih rest]

theorem decNats_encNats (ns : List Nat) (rest : List Token) :
    decNats (encNats ns ++ rest) = some (ns, rest) := by
  simpa [encNats, decNats] using decNatsN_enc ns rest

/-- The snapshot payload: the bindings, then the requests already carried out. -/
def encSnap (p : List (String × String) × List Nat) : List Token :=
  encPairs p.1 ++ encNats p.2

def decSnap (ts : List Token) : Option ((List (String × String) × List Nat) × List Token) := do
  let (ps, ts) ← decPairs ts
  let (ns, ts) ← decNats ts
  some ((ps, ns), ts)

theorem decSnap_encSnap (p : List (String × String) × List Nat) (rest : List Token) :
    decSnap (encSnap p ++ rest) = some (p, rest) := by
  obtain ⟨ps, ns⟩ := p
  show decSnap ((encPairs ps ++ encNats ns) ++ rest) = _
  rw [List.append_assoc]
  simp [decSnap, decPairs_encPairs ps _, decNats_encNats ns rest]

/-! ## Messages -/

namespace Msg

/-- Token encoding of a protocol message. -/
def enc : Msg → List Token
  | .requestVote t c li lt => [.n 0, .n t, .n c, .n li, .n lt]
  | .requestVoteResp t g => [.n 1, .n t, .n (if g then 1 else 0)]
  | .appendEntries t l pi pt es lc =>
      [.n 2, .n t, .n l, .n pi, .n pt, .n lc] ++ encEntries es
  | .appendEntriesResp t s mi => [.n 3, .n t, .n (if s then 1 else 0), .n mi]
  | .installSnapshot t l li a ps =>
      [.n 4, .n t, .n l, .n li] ++ Entry.enc a ++ encSnap ps

/-- Token decoding of a protocol message. -/
def dec : List Token → Option (Msg × List Token)
  | .n 0 :: .n t :: .n c :: .n li :: .n lt :: rest => some (.requestVote t c li lt, rest)
  | .n 1 :: .n t :: .n g :: rest => some (.requestVoteResp t (g != 0), rest)
  | .n 2 :: .n t :: .n l :: .n pi :: .n pt :: .n lc :: rest => do
      let (es, rest) ← decEntries rest
      some (.appendEntries t l pi pt es lc, rest)
  | .n 3 :: .n t :: .n s :: .n mi :: rest => some (.appendEntriesResp t (s != 0) mi, rest)
  | .n 4 :: .n t :: .n l :: .n li :: rest => do
      let (a, rest) ← Entry.dec rest
      let (ps, rest) ← decSnap rest
      some (.installSnapshot t l li a ps, rest)
  | _ => none

instance : Codec Msg where
  encode := enc
  decode := dec
  decode_encode := by
    intro m rest
    cases m with
    | requestVote => rfl
    | requestVoteResp t g => cases g <;> rfl
    | appendEntries t l pi pt es lc =>
        show dec (_ :: _ :: _ :: _ :: _ :: _ :: (encEntries es ++ rest)) = _
        simp [dec, decEntries_encEntries es rest]
    | appendEntriesResp t s mi => cases s <;> rfl
    | installSnapshot t l li a ps =>
        have hA : Entry.dec (Entry.enc a ++ (encSnap ps ++ rest))
            = some (a, encSnap ps ++ rest) := Codec.decode_encode (α := Entry) a _
        show dec (enc (.installSnapshot t l li a ps) ++ rest) = _
        simp only [enc, List.cons_append, List.nil_append, List.append_assoc]
        simp [dec, hA, decSnap_encSnap ps rest]

end Msg

end RaftKV
