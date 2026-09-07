import RaftKV.Core.Types
import RaftKV.Protocol.Node
import RaftKV.Storage.LogArray

/-!
# A byte codec, with round-trip proved

The device stores bytes, so the durable state has to become bytes and come back.
This is the same two-part shape as the wire codec in `RaftKV.Protocol.Codec` —
operations plus one law — but over `UInt8` rather than tokens, and it is proved
all the way down to `String`.

Getting to `String` without trusting anything is the point of the detour through
code points: Lean's core provides `String.ofList_toList` and `Char.ofNat_toNat`,
so a string can be encoded as the numbers of its characters and read back
exactly. Encoding via UTF-8 would have been shorter and would have added a
trusted round-trip law, since core proves none for `String.fromUTF8?`.

Numbers use LEB128: seven payload bits per byte, the top bit marking "more to
come". That is self-delimiting, which is what makes the law below composable —
each decoder consumes exactly its own bytes and hands the rest on.
-/

namespace RaftKV

/-- Serialisation to bytes, with the round-trip law that makes it composable. -/
class ByteCodec (α : Type) where
  /-- Serialise. -/
  enc : α → List UInt8
  /-- Deserialise, consuming a prefix and returning the remainder. -/
  dec : List UInt8 → Option (α × List UInt8)
  /-- **The law**: decoding an encoding returns the value and leaves the rest alone. -/
  dec_enc : ∀ (a : α) (rest : List UInt8), dec (enc a ++ rest) = some (a, rest)

namespace ByteCodec

/-- Distinct values never share an encoding. -/
theorem enc_injective {α : Type} [ByteCodec α] {a b : α} (h : enc a = enc b) : a = b := by
  have ha := dec_enc a ([] : List UInt8)
  have hb := dec_enc b ([] : List UInt8)
  rw [h, hb] at ha
  exact (congrArg Prod.fst (Option.some.inj ha)).symm

/-- Round-trip on a complete byte list. -/
theorem dec_enc_nil {α : Type} [ByteCodec α] (a : α) : dec (enc a) = some (a, []) := by
  have := dec_enc a ([] : List UInt8)
  rwa [List.append_nil] at this

/-! ## Numbers -/

/-- LEB128: seven bits at a time, high bit set while more follow. -/
def encNat : Nat → List UInt8
  | n =>
    if h : n < 128 then [UInt8.ofNat n]
    else UInt8.ofNat (n % 128 + 128) :: encNat (n / 128)
  decreasing_by
    exact Nat.div_lt_self (by omega) (by omega)

/-- The matching decoder, bounded by the input length. -/
def decNatAux : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: bs =>
      if b.toNat < 128 then some (b.toNat, bs)
      else match decNatAux fuel bs with
        | none => none
        | some (n, rest) => some (b.toNat - 128 + 128 * n, rest)

def decNat (bs : List UInt8) : Option (Nat × List UInt8) := decNatAux (bs.length + 1) bs


theorem toNat_ofNat_of_lt {n : Nat} (h : n < 256) : (UInt8.ofNat n).toNat = n := by
  simp [Nat.mod_eq_of_lt h]

theorem decNatAux_encNat : ∀ (n : Nat) (rest : List UInt8) (fuel : Nat),
    (encNat n).length ≤ fuel → decNatAux fuel (encNat n ++ rest) = some (n, rest) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
      intro rest fuel hfuel
      by_cases hn : n < 128
      · rw [encNat] at hfuel ⊢
        rw [dif_pos hn] at hfuel ⊢
        simp only [List.length_cons, List.length_nil] at hfuel
        cases fuel with
        | zero => omega
        | succ f =>
            rw [List.cons_append, List.nil_append, decNatAux,
              if_pos (by rw [toNat_ofNat_of_lt (by omega)]; omega),
              toNat_ofNat_of_lt (by omega)]
      · have hd : n / 128 < n := Nat.div_lt_self (by omega) (by omega)
        rw [encNat] at hfuel ⊢
        rw [dif_neg hn] at hfuel ⊢
        simp only [List.length_cons] at hfuel
        cases fuel with
        | zero => omega
        | succ f =>
            have hb : (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 := by
              refine toNat_ofNat_of_lt ?_
              have := Nat.mod_lt n (show 0 < 128 by omega)
              omega
            rw [List.cons_append, decNatAux, if_neg (by rw [hb]; omega),
              ih (n / 128) hd rest f (by omega), hb]
            have := Nat.div_add_mod n 128
            simp only [Option.some.injEq, Prod.mk.injEq]
            exact ⟨by omega, trivial⟩

theorem decNat_encNat (n : Nat) (rest : List UInt8) :
    decNat (encNat n ++ rest) = some (n, rest) := by
  unfold decNat
  refine decNatAux_encNat n rest _ ?_
  simp only [List.length_append]
  omega

instance : ByteCodec Nat where
  enc := encNat
  dec := decNat
  dec_enc := decNat_encNat


/-! ## Composites

Each instance is the same shape: encode the parts in order, decode them in the
same order. The round-trip law composes because every decoder consumes exactly
its own bytes, which is what the `rest` in the law is for.
-/

instance : ByteCodec UInt8 where
  enc b := [b]
  dec
    | [] => none
    | b :: bs => some (b, bs)
  dec_enc := by intro a rest; rfl

instance : ByteCodec Bool where
  enc b := [if b then 1 else 0]
  dec
    | [] => none
    | b :: bs => some (b != 0, bs)
  dec_enc := by intro a rest; cases a <;> rfl

instance {α : Type} [ByteCodec α] : ByteCodec (Option α) where
  enc
    | none => [0]
    | some a => 1 :: enc a
  dec bs :=
    match bs with
    | [] => none
    | t :: rest =>
        if t == 0 then some (none, rest)
        else match (dec rest : Option (α × List UInt8)) with
          | none => none
          | some (a, rest') => some (some a, rest')
  dec_enc := by
    intro a rest
    cases a with
    | none => rfl
    | some x =>
        show (match (1 : UInt8) :: (enc x ++ rest) with
          | [] => none
          | t :: r => _) = _
        simp only [List.cons_append, List.append_eq]
        rw [if_neg (by decide)]
        rw [dec_enc x rest]

/-- Encode a list as its length followed by its elements. -/
def encList {α : Type} [ByteCodec α] (l : List α) : List UInt8 :=
  encNat l.length ++ (l.flatMap enc)

def decListAux {α : Type} [ByteCodec α] : Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
      match (dec bs : Option (α × List UInt8)) with
      | none => none
      | some (a, rest) =>
          match decListAux n rest with
          | none => none
          | some (l, rest') => some (a :: l, rest')

theorem decListAux_enc {α : Type} [ByteCodec α] : ∀ (l : List α) (rest : List UInt8),
    decListAux l.length (l.flatMap enc ++ rest) = some (l, rest) := by
  intro l
  induction l with
  | nil => intro rest; rfl
  | cons a l ih =>
      intro rest
      simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decListAux]
      rw [dec_enc a (l.flatMap enc ++ rest)]
      dsimp only
      rw [ih rest]

instance {α : Type} [ByteCodec α] : ByteCodec (List α) where
  enc := encList
  dec bs :=
    match decNat bs with
    | none => none
    | some (n, rest) => decListAux n rest
  dec_enc := by
    intro l rest
    show (match decNat (encList l ++ rest) with
      | none => none
      | some (n, r) => decListAux n r) = _
    unfold encList
    rw [List.append_assoc, decNat_encNat l.length (l.flatMap enc ++ rest)]
    dsimp only
    exact decListAux_enc l rest

instance : ByteCodec Char where
  enc c := enc c.toNat
  dec bs :=
    match (dec bs : Option (Nat × List UInt8)) with
    | none => none
    | some (n, rest) => some (Char.ofNat n, rest)
  dec_enc := by
    intro c rest
    show (match (dec (enc c.toNat ++ rest) : Option (Nat × List UInt8)) with
      | none => none
      | some (n, r) => some (Char.ofNat n, r)) = _
    rw [dec_enc c.toNat rest]
    dsimp only
    rw [Char.ofNat_toNat]

instance : ByteCodec String where
  enc s := enc s.toList
  dec bs :=
    match (dec bs : Option (List Char × List UInt8)) with
    | none => none
    | some (l, rest) => some (String.ofList l, rest)
  dec_enc := by
    intro s rest
    show (match (dec (enc s.toList ++ rest) : Option (List Char × List UInt8)) with
      | none => none
      | some (l, r) => some (String.ofList l, r)) = _
    rw [dec_enc s.toList rest]
    dsimp only
    rw [String.ofList_toList]


/-! ## The domain types -/

instance : ByteCodec Command where
  enc
    | .get k => 0 :: enc k
    | .put k v => 1 :: (enc k ++ enc v)
    | .del k => 2 :: enc k
  dec bs :=
    match bs with
    | [] => none
    | t :: rest =>
        if t == 0 then
          match (dec rest : Option (String × List UInt8)) with
          | none => none
          | some (k, r) => some (.get k, r)
        else if t == 1 then
          match (dec rest : Option (String × List UInt8)) with
          | none => none
          | some (k, r) =>
              match (dec r : Option (String × List UInt8)) with
              | none => none
              | some (v, r') => some (.put k v, r')
        else if t == 2 then
          match (dec rest : Option (String × List UInt8)) with
          | none => none
          | some (k, r) => some (.del k, r)
        else none
  dec_enc := by
    intro c rest
    cases c with
    | get k =>
        show (match (0 : UInt8) :: (enc k ++ rest) with | [] => none | t :: r => _) = _
        simp only [List.cons_append, List.append_eq]
        rw [if_pos (by decide), dec_enc k rest]
    | put k v =>
        show (match (1 : UInt8) :: ((enc k ++ enc v) ++ rest) with
          | [] => none | t :: r => _) = _
        simp only [List.cons_append, List.append_eq, List.append_assoc]
        rw [if_neg (by decide), if_pos (by decide), dec_enc k (enc v ++ rest)]
        dsimp only
        rw [dec_enc v rest]
    | del k =>
        show (match (2 : UInt8) :: (enc k ++ rest) with | [] => none | t :: r => _) = _
        simp only [List.cons_append, List.append_eq]
        rw [if_neg (by decide), if_neg (by decide), if_pos (by decide), dec_enc k rest]

instance : ByteCodec Entry where
  enc e := enc e.term ++ enc e.cmd ++ enc e.reqId
  dec bs :=
    match (dec bs : Option (Nat × List UInt8)) with
    | none => none
    | some (t, r) =>
        match (dec r : Option (Command × List UInt8)) with
        | none => none
        | some (c, r') =>
            match (dec r' : Option (Nat × List UInt8)) with
            | none => none
            | some (i, r'') => some (⟨t, c, i⟩, r'')
  dec_enc := by
    intro e rest
    show (match (dec ((enc e.term ++ enc e.cmd ++ enc e.reqId) ++ rest) :
        Option (Nat × List UInt8)) with | none => none | some (t, r) => _) = _
    simp only [List.append_assoc]
    rw [dec_enc e.term (enc e.cmd ++ (enc e.reqId ++ rest))]
    dsimp only
    rw [dec_enc e.cmd (enc e.reqId ++ rest)]
    dsimp only
    rw [dec_enc e.reqId rest]



instance {α : Type} [ByteCodec α] : ByteCodec (Array α) where
  enc a := enc a.toList
  dec bs :=
    match (dec bs : Option (List α × List UInt8)) with
    | none => none
    | some (l, r) => some (l.toArray, r)
  dec_enc := by
    intro a rest
    show (match (dec (enc a.toList ++ rest) : Option (List α × List UInt8)) with
      | none => none | some (l, r) => some (l.toArray, r)) = _
    rw [dec_enc a.toList rest]

/-- Length-prefixed bytes. -/
instance : ByteCodec ByteArray where
  enc b := enc b.data
  dec bs :=
    match (dec bs : Option (Array UInt8 × List UInt8)) with
    | none => none
    | some (a, r) => some ((⟨a⟩ : ByteArray), r)
  dec_enc := by
    intro b rest
    show (match (dec (enc b.data ++ rest) : Option (Array UInt8 × List UInt8)) with
      | none => none | some (a, r) => some ((⟨a⟩ : ByteArray), r)) = _
    rw [dec_enc b.data rest]

instance {α β : Type} [ByteCodec α] [ByteCodec β] : ByteCodec (α × β) where
  enc p := enc p.1 ++ enc p.2
  dec bs :=
    match (dec bs : Option (α × List UInt8)) with
    | none => none
    | some (a, r) =>
        match (dec r : Option (β × List UInt8)) with
        | none => none
        | some (b, r') => some ((a, b), r')
  dec_enc := by
    intro p rest
    show (match (dec ((enc p.1 ++ enc p.2) ++ rest) : Option (α × List UInt8)) with
      | none => none | some (a, r) => _) = _
    rw [List.append_assoc, dec_enc p.1 (enc p.2 ++ rest)]
    dsimp only
    rw [dec_enc p.2 rest]

/-! ## The durable state

`Persistent σ` is the trio a crash must not lose. It needs the log to be
serialisable, which is a separate obligation from `LogStore` — a memory-mapped
log would satisfy it by handing over the file it already is.
-/

/--
The array-backed log serialises as its base offset and the entries it still
holds — which is the point of compaction: what was discarded is not written.
-/
instance : ByteCodec ArrayLog where
  enc s := enc s.base ++ enc s.entries.toList
  dec bs :=
    match (dec bs : Option (Nat × List UInt8)) with
    | none => none
    | some (b, r) =>
        match (dec r : Option (List Entry × List UInt8)) with
        | none => none
        | some (l, r') => some (⟨b, l.toArray⟩, r')
  dec_enc := by
    intro s rest
    show (match (dec (enc s.base ++ enc s.entries.toList ++ rest) :
        Option (Nat × List UInt8)) with | none => none | some (b, r) => _) = _
    rw [List.append_assoc, dec_enc s.base (enc s.entries.toList ++ rest)]
    dsimp only
    rw [dec_enc s.entries.toList rest]

instance {σ : Type} [ByteCodec σ] : ByteCodec (Protocol.Persistent σ) where
  enc p := enc p.currentTerm ++ enc p.votedFor ++ enc p.log ++ enc p.snapIndex
    ++ enc p.snapPairs ++ enc p.snapSessions
  dec bs :=
    match (dec bs : Option (Nat × List UInt8)) with
    | none => none
    | some (t, r) =>
        match (dec r : Option (Option Nat × List UInt8)) with
        | none => none
        | some (v, r') =>
            match (dec r' : Option (σ × List UInt8)) with
            | none => none
            | some (lg, r'') =>
                match (dec r'' : Option (Nat × List UInt8)) with
                | none => none
                | some (si, r3) =>
                    match (dec r3 : Option (List (String × String) × List UInt8)) with
                    | none => none
                    | some (sk, r4) =>
                        match (dec r4 : Option (List Nat × List UInt8)) with
                        | none => none
                        | some (ss, r5) => some (⟨t, v, lg, si, sk, ss⟩, r5)
  dec_enc := by
    intro p rest
    show (match (dec ((enc p.currentTerm ++ enc p.votedFor ++ enc p.log ++ enc p.snapIndex
        ++ enc p.snapPairs ++ enc p.snapSessions) ++ rest) : Option (Nat × List UInt8)) with
      | none => none | some (t, r) => _) = _
    simp only [List.append_assoc]
    rw [dec_enc p.currentTerm _]
    dsimp only
    rw [dec_enc p.votedFor _]
    dsimp only
    rw [dec_enc p.log _]
    dsimp only
    rw [dec_enc p.snapIndex _]
    dsimp only
    rw [dec_enc p.snapPairs _]
    dsimp only
    rw [dec_enc p.snapSessions rest]

end ByteCodec

end RaftKV
