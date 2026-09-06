/-!
# CRC-32

Every page carries a checksum over its own bytes, so that a page which was torn
by a crash — or quietly rotted by the drive — is *detected* rather than
believed. Without it a half-written page is indistinguishable from a good one,
and the reader follows a child pointer that is half old and half new.

This is the standard IEEE 802.3 polynomial, reflected, with the usual pre- and
post-inversion, so the values agree with `zlib` and friends.

The checksum is not part of the crash-safety proof. That proof rules out reading
a torn page at all, by never overwriting anything the live root can reach; the
checksum is defence for the cases the proof does not model — a drive that
returns a different byte than it was given, or a torn write to a page the
allocator wrongly believed free.
-/

namespace RaftKV.Crc32

/-- One step of the reflected CRC-32 update, unrolled over the eight bits. -/
private def stepByte (acc : UInt32) : Nat → UInt32
  | 0 => acc
  | n + 1 =>
      let acc := if acc &&& 1 == 1 then (acc >>> 1) ^^^ 0xEDB88320 else acc >>> 1
      stepByte acc n

/-- Fold one byte into the running value. -/
def step (crc : UInt32) (b : UInt8) : UInt32 :=
  stepByte (crc ^^^ b.toUInt32) 8

/-- CRC-32 of a byte range `[from, until)` of `bs`. -/
def overRange (bs : ByteArray) (from_ until_ : Nat) : UInt32 :=
  let rec go (i : Nat) (crc : UInt32) : UInt32 :=
    if h : i < until_ then
      go (i + 1) (step crc (bs.get! i))
    else crc
  termination_by until_ - i
  (go from_ 0xFFFFFFFF) ^^^ 0xFFFFFFFF

/-- CRC-32 of a whole byte array. -/
def over (bs : ByteArray) : UInt32 := overRange bs 0 bs.size

end RaftKV.Crc32
