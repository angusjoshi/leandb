/-!
# Core types

Terms, node identifiers, log indices, client commands and the log entry type.

Log indices are **1-based**, matching the Raft paper: index `0` denotes "before
the start of the log" and never holds an entry.

Terms, node ids, log indices and request ids are all plain `Nat` rather than
`abbrev` aliases. That is deliberate: `omega` does not see through `abbrev`, and
the safety proofs are dense with index arithmetic. Meanings are documented at
each binding site instead.
-/

namespace RaftKV

/-- Commands the replicated state machine understands. -/
inductive Command where
  | get (key : String)
  | put (key : String) (value : String)
  | del (key : String)
  deriving Repr, DecidableEq, Inhabited

/-- The result of applying a `Command`. -/
inductive Reply where
  /-- Result of a `get`: the bound value, or `none` if the key is absent. -/
  | value (v : Option String)
  /-- Acknowledgement of a `put` or `del`. -/
  | ok
  deriving Repr, DecidableEq, Inhabited

/--
An entry in the replicated log: the command to apply, the election term in
which the entry was created, and the originating client request.

The `term` field is what makes the Raft safety argument work — it is the
witness that lets a follower detect a divergent log.
-/
structure Entry where
  /-- The election term during which this entry was created by a leader. -/
  term : Nat
  /-- The state-machine command this entry carries. -/
  cmd : Command
  /-- Identifies the client request that produced this entry. -/
  reqId : Nat
  deriving Repr, DecidableEq, Inhabited

end RaftKV
