------------------------------ MODULE ControlM5 ------------------------------
EXTENDS Naturals
\* Qualification seed for the writfold.agent/1 transport-control profile that
\* Weft consumes as its ordinary agent transport: JSON-RPC 2.0 objects over
\* stdio, implemented methods initialize/shutdown, sole capability
\* "notifications", 65,536-byte LF-inclusive frames in both directions,
\* entropy-backed session identity and a monotonic invocation generation.
\* Ground truth: the pinned writfold-agent-contract archive
\* (contract.json sha256 b673d10f7c14c73d8f5778cfb9b2e84a98a159f1553d5c008054402ee85e7be2)
\* and its stateful vectors. This seed abstracts: one request id spelling,
\* byte bounds as action classes (not arithmetic), JSON structure, exit codes
\* and process identity. See README.md for the required expansion.
\*
\* Unchanged variables are written as explicit primed equalities rather than
\* UNCHANGED tuples: large tuple equalities degrade the SMT encoding of the
\* proof obligations.
\* Finite exploration bounds are definitions, not declared constants, so the
\* proofs see concrete arithmetic.
\* MUTANT M5 (substitute_null_id): correlated error reply substitutes a null id in UnknownRequest.
\* Single deviation from Control.tla; TLC must violate EchoSound.
MaxGen == 3
MaxReject == 2
VARIABLES phase, gen, admit, closed, authority, echo, ninit, nstop,
          ninitreply, nstopreply, nnotif, nnull, stopgen
vars == <<phase, gen, admit, closed, authority, echo, ninit, nstop,
          ninitreply, nstopreply, nnotif, nnull, stopgen>>
Phases == {"running","initialized","stopped"}
Replies == {"none","null","req"}
Live == closed = FALSE /\ phase # "stopped"

\* ---- Envelope admission failures: no generation, no lifecycle ------------
\* A frame above the LF-inclusive bound is drained with bounded memory and
\* answered by an Invalid Request error carrying a null id; input continues.
Oversize == Live /\ nnull < MaxReject /\ nnull' = nnull + 1 /\ echo' = "null"
  /\ phase' = phase /\ gen' = gen /\ admit' = admit /\ closed' = closed
  /\ authority' = authority /\ ninit' = ninit /\ nstop' = nstop
  /\ ninitreply' = ninitreply /\ nstopreply' = nstopreply
  /\ nnotif' = nnotif /\ stopgen' = stopgen
\* Malformed JSON or an invalid JSON-RPC envelope is not a notification:
\* error reply with null id; again no generation is consumed.
Malformed == Live /\ nnull < MaxReject /\ nnull' = nnull + 1 /\ echo' = "null"
  /\ phase' = phase /\ gen' = gen /\ admit' = admit /\ closed' = closed
  /\ authority' = authority /\ ninit' = ninit /\ nstop' = nstop
  /\ ninitreply' = ninitreply /\ nstopreply' = nstopreply
  /\ nnotif' = nnotif /\ stopgen' = stopgen

\* ---- Admitted envelopes: exactly one generation each ---------------------
Admitted == gen < MaxGen /\ gen' = gen + 1 /\ admit' = admit + 1

\* Method lookup precedes lifecycle failures: an unknown method receives its
\* correlated Method-not-found error in every open session state.
UnknownRequest == Live /\ Admitted /\ echo' = "null"
  /\ phase' = phase /\ closed' = closed /\ authority' = authority
  /\ ninit' = ninit /\ nstop' = nstop /\ ninitreply' = ninitreply
  /\ nstopreply' = nstopreply /\ nnotif' = nnotif /\ nnull' = nnull
  /\ stopgen' = stopgen
\* initialize with protocol version "2" and only advertised capabilities:
\* the complete bounded success reply is encoded and written first; the
\* initialized commit happens only after that. Initialization grants no
\* corpus, grounding or effect authority.
InitOk == Live /\ phase = "running" /\ Admitted
  /\ echo' = "req" /\ ninitreply' = ninitreply + 1
  /\ phase' = "initialized" /\ ninit' = ninit + 1 /\ authority' = FALSE
  /\ closed' = closed /\ nstop' = nstop /\ nstopreply' = nstopreply
  /\ nnotif' = nnotif /\ nnull' = nnull /\ stopgen' = stopgen
\* Unsupported protocol version, or an unadvertised capability such as
\* knowledge/citations/storage/edit: correlated refusal, no commit.
InitBadParams == Live /\ phase = "running" /\ Admitted /\ echo' = "req"
  /\ phase' = phase /\ closed' = closed /\ authority' = authority
  /\ ninit' = ninit /\ nstop' = nstop /\ ninitreply' = ninitreply
  /\ nstopreply' = nstopreply /\ nnotif' = nnotif /\ nnull' = nnull
  /\ stopgen' = stopgen
\* A repeated initialize: parameter schema is validated first, then the
\* already-initialized state refuses; nothing is recommitted.
InitAgain == Live /\ phase = "initialized" /\ Admitted /\ echo' = "req"
  /\ phase' = phase /\ closed' = closed /\ authority' = authority
  /\ ninit' = ninit /\ nstop' = nstop /\ ninitreply' = ninitreply
  /\ nstopreply' = nstopreply /\ nnotif' = nnotif /\ nnull' = nnull
  /\ stopgen' = stopgen
\* shutdown request from an initialized session: the complete bounded success
\* reply is encoded and written, then the shutdown commit closes the session
\* and no further envelope is read; stopgen freezes the generation at closure.
StopOk == Live /\ phase = "initialized" /\ Admitted
  /\ echo' = "req" /\ nstopreply' = nstopreply + 1
  /\ phase' = "stopped" /\ nstop' = nstop + 1 /\ stopgen' = gen'
  /\ closed' = closed /\ authority' = authority /\ ninit' = ninit
  /\ ninitreply' = ninitreply /\ nnotif' = nnotif /\ nnull' = nnull
\* shutdown request before any committed initialization: correlated error.
StopEarly == Live /\ phase = "running" /\ Admitted /\ echo' = "req"
  /\ phase' = phase /\ closed' = closed /\ authority' = authority
  /\ ninit' = ninit /\ nstop' = nstop /\ ninitreply' = ninitreply
  /\ nstopreply' = nstopreply /\ nnotif' = nnotif /\ nnull' = nnull
  /\ stopgen' = stopgen
\* A well-formed shutdown notification executes the lifecycle silently.
StopNotify == Live /\ phase = "initialized" /\ Admitted
  /\ phase' = "stopped" /\ nstop' = nstop + 1 /\ nnotif' = nnotif + 1
  /\ stopgen' = gen' /\ closed' = closed /\ authority' = authority
  /\ echo' = echo /\ ninit' = ninit /\ ninitreply' = ninitreply
  /\ nstopreply' = nstopreply /\ nnull' = nnull
\* Any other well-formed notification (unknown method, wrong state or failed
\* params) emits nothing and changes no lifecycle state.
NotifyOther == Live /\ Admitted
  /\ phase' = phase /\ closed' = closed /\ authority' = authority
  /\ echo' = echo /\ ninit' = ninit /\ nstop' = nstop
  /\ ninitreply' = ninitreply /\ nstopreply' = nstopreply
  /\ nnotif' = nnotif /\ nnull' = nnull /\ stopgen' = stopgen
\* A valid envelope whose complete correlated reply cannot fit the bounded
\* frame: encoding failure. The connection terminates with no partial reply,
\* no truncation and no id substitution; the generation was still consumed
\* and no lifecycle commit happened.
HugeIdReply == Live /\ Admitted /\ closed' = TRUE
  /\ phase' = phase /\ authority' = authority /\ echo' = echo
  /\ ninit' = ninit /\ nstop' = nstop /\ ninitreply' = ninitreply
  /\ nstopreply' = nstopreply /\ nnotif' = nnotif /\ nnull' = nnull
  /\ stopgen' = stopgen
\* EOF after a completely evaluated final frame: ordinary exit, no reply.
Eof == Live /\ closed' = TRUE
  /\ phase' = phase /\ gen' = gen /\ admit' = admit /\ authority' = authority
  /\ echo' = echo /\ ninit' = ninit /\ nstop' = nstop
  /\ ninitreply' = ninitreply /\ nstopreply' = nstopreply
  /\ nnotif' = nnotif /\ nnull' = nnull /\ stopgen' = stopgen

Next == Oversize \/ Malformed \/ UnknownRequest \/ InitOk \/ InitBadParams
        \/ InitAgain \/ StopOk \/ StopEarly \/ StopNotify \/ NotifyOther
        \/ HugeIdReply \/ Eof
Init == /\ phase = "running" /\ gen = 0 /\ admit = 0
        /\ closed = FALSE /\ authority = FALSE /\ echo = "none"
        /\ ninit = 0 /\ nstop = 0 /\ ninitreply = 0 /\ nstopreply = 0
        /\ nnotif = 0 /\ nnull = 0 /\ stopgen = 0
Spec == Init /\ [][Next]_vars

\* The type invariant is split (state versus arithmetic) so each proof
\* obligation stays small: several range memberships in one obligation
\* degrade the SMT encoding.
TypeState == phase \in Phases /\ echo \in Replies
TypeArith == /\ closed \in BOOLEAN /\ authority \in BOOLEAN
            /\ gen \in 0..MaxGen /\ admit \in 0..MaxGen
            /\ ninit \in 0..1 /\ nstop \in 0..1 /\ ninitreply \in 0..1
            /\ nstopreply \in 0..1 /\ nnotif \in 0..1
            /\ nnull \in 0..MaxReject /\ stopgen \in 0..MaxGen
TypeOK == TypeState /\ TypeArith
\* Every consumed generation corresponds to one completely admitted envelope;
\* admission failures (oversize, malformed) consume none.
GenAccounting == gen = admit
InitOnce == ninit <= 1
StopOnce == nstop <= 1
\* shutdown requires a committed initialization ("require initialized").
StopAfterInit == nstop <= ninit
\* The session state machine agrees with the committed lifecycle counts.
PhaseCounts == /\ (phase = "running" => ninit = 0)
               /\ (phase = "initialized" => ninit = 1 /\ nstop = 0)
               /\ (phase = "stopped" => ninit = 1 /\ nstop = 1)
\* No successful lifecycle change precedes a completely encoded, written
\* reply: each committed initialization/shutdown has exactly its own success
\* reply, or - only for shutdown - one silent notification execution.
InitCited == ninit = ninitreply
StopCited == nstop = nstopreply + nnotif
\* The control handshake mints no corpus, grounding or effect authority.
AuthorityIsolated == authority = FALSE
\* Null-id errors exist only as admission-failure replies; every correlated
\* reply required an admitted envelope (a consumed generation).
EchoSound == /\ (echo = "null" => nnull >= 1)
             /\ (echo = "req" => gen >= 1 /\ admit >= 1)
\* After the shutdown commit the session reads no further envelope.
StopFrozen == phase = "stopped" => gen = stopgen
=============================================================================
