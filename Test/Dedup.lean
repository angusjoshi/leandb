import RaftKV.Runtime.Random

/-!
# Exactly once, deterministically

The randomised sweeps put retries in the mix, but the *dangerous* interleaving —
a write committing, someone else's write to the same key committing, and then the
first write's retry committing — is rare enough by chance that it is not evidence
of anything. So it is built here by hand, on a single-node cluster where every
request commits immediately and the order is exactly the order it is issued.

The scenario is the one duplicate suppression exists for:

```
  rid 1:  del k        -- commits
  rid 2:  put k "v"    -- commits
  rid 1:  del k        -- retried, commits a second time
  rid 3:  get k        -- what does it say?
```

With suppression the answer is `"v"`: the retried `del` is recognised as a
request already carried out and does nothing. Without it the answer is "not
found", and the client that issued `put` has silently lost its write.
-/

open RaftKV RaftKV.Sim RaftKV.Protocol

/-- A one-node cluster that has elected itself leader. -/
def leader1 : World := (World.init 1).fire 0 .electionTimeout

/-- Issue a command and return the world. -/
def issue (w : World) (rid : Nat) (c : Command) : World := w.fire 0 (.clientReq rid c)

/-- The scenario above, as a sequence of worlds. -/
def scenario : World :=
  let w := leader1
  let w := issue w 1 (.del "k")
  let w := issue w 2 (.put "k" "v")
  let w := issue w 1 (.del "k")      -- the retry
  issue w 3 (.get "k")

/-! Every reply the run produced, in order. -/
#eval scenario.replies

/-! The reply to the final `get`. Should be `value (some "v")`. -/
#eval (scenario.replies.filter (fun p => p.1 == 3)).map Prod.snd

/--
The same log, run through a specification **without** duplicate suppression —
which is what the store did before, and what the answer would have been.
-/
def naiveFinal : Option String :=
  let m := scenario.applied.foldl (fun acc p =>
    if acc.any (fun q => q.1 == p.1) then acc else acc ++ [p]) []
  let st := m.foldl (fun st p => (Spec.applyCmd st p.2.cmd).1) Spec.Map.empty
  st.find "k"

/-- With suppression, the specification's own answer. -/
def dedupFinal : Option String :=
  let m := scenario.applied.foldl (fun acc p =>
    if acc.any (fun q => q.1 == p.1) then acc else acc ++ [p]) []
  let st := m.foldl (fun st p => (Spec.applyEntry st p.2).1) Spec.KVModel.empty
  st.map.find "k"

/-! The retried `del` really did commit a second time: four entries, three ids. -/
#eval scenario.applied.length

#eval naiveFinal      -- none: the write was lost
#eval dedupFinal      -- some "v": the write survived
