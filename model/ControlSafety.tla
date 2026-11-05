---------------------------- MODULE ControlSafety ----------------------------
EXTENDS Control, TLAPS
\* Inductive safety for the writfold.agent/1 control-protocol seed. Every
\* obligation below is executed by tlapm (SMT backend) by scripts/run_model.py;
\* nothing is deferred or omitted at seed scope. Each action is discharged as
\* thirteen small postcondition groups, two of which cite the arithmetic
\* lemmas below: one large mixed obligation degrades the SMT encoding, while
\* each group here is proved outright.
Strong == TypeState /\ TypeArith /\ GenAccounting /\ InitOnce /\ StopOnce
          /\ StopAfterInit /\ PhaseCounts /\ InitCited /\ StopCited
          /\ AuthorityIsolated /\ EchoSound /\ StopFrozen

THEOREM AdmitBound == TypeArith /\ GenAccounting /\ Admitted =>
  gen' \in 0..MaxGen /\ admit' \in 0..MaxGen
BY SMT DEF TypeArith, GenAccounting, Admitted, MaxGen, MaxReject

THEOREM RejectBound == TypeArith /\ nnull < MaxReject /\ nnull' = nnull + 1 =>
  nnull' \in 0..MaxReject
BY SMT DEF TypeArith, MaxGen, MaxReject

THEOREM StartOK == Init => Strong
BY SMT DEF Init, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies

THEOREM Preserve == Strong /\ [Next]_vars => Strong'
<1>1. Strong /\ Oversize => Strong'
  <2>1. Strong /\ Oversize => phase' \in Phases
    BY SMT DEF Oversize, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>2. Strong /\ Oversize => echo' \in Replies
    BY SMT DEF Oversize, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>3. Strong /\ Oversize => closed' \in BOOLEAN /\ authority' \in BOOLEAN
    BY SMT DEF Oversize, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>4. Strong /\ Oversize => gen' \in 0..MaxGen /\ admit' \in 0..MaxGen
    BY AdmitBound, SMT DEF Oversize, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>5. Strong /\ Oversize => ninit' \in 0..1 /\ nstop' \in 0..1 /\ ninitreply' \in 0..1 /\ nstopreply' \in 0..1 /\ nnotif' \in 0..1
    BY SMT DEF Oversize, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>6. Strong /\ Oversize => nnull' \in 0..MaxReject
    BY RejectBound, SMT DEF Oversize, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>7. Strong /\ Oversize => stopgen' \in 0..MaxGen
    BY SMT DEF Oversize, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>8. Strong /\ Oversize => gen' = admit' /\ nstop' <= ninit'
    BY SMT DEF Oversize, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>9. Strong /\ Oversize => ninit' = ninitreply' /\ nstop' = nstopreply' + nnotif'
    BY SMT DEF Oversize, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>10. Strong /\ Oversize => (phase' = "running" => ninit' = 0) /\ (phase' = "initialized" => ninit' = 1 /\ nstop' = 0) /\ (phase' = "stopped" => ninit' = 1 /\ nstop' = 1)
    BY SMT DEF Oversize, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>11. Strong /\ Oversize => authority' = FALSE
    BY SMT DEF Oversize, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>12. Strong /\ Oversize => (echo' = "null" => nnull' >= 1) /\ (echo' = "req" => gen' >= 1 /\ admit' >= 1)
    BY SMT DEF Oversize, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>13. Strong /\ Oversize => (phase' = "stopped" => gen' = stopgen')
    BY SMT DEF Oversize, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
    DEF Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce,
    StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated,
    EchoSound, StopFrozen
<1>2. Strong /\ Malformed => Strong'
  <2>1. Strong /\ Malformed => phase' \in Phases
    BY SMT DEF Malformed, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>2. Strong /\ Malformed => echo' \in Replies
    BY SMT DEF Malformed, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>3. Strong /\ Malformed => closed' \in BOOLEAN /\ authority' \in BOOLEAN
    BY SMT DEF Malformed, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>4. Strong /\ Malformed => gen' \in 0..MaxGen /\ admit' \in 0..MaxGen
    BY AdmitBound, SMT DEF Malformed, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>5. Strong /\ Malformed => ninit' \in 0..1 /\ nstop' \in 0..1 /\ ninitreply' \in 0..1 /\ nstopreply' \in 0..1 /\ nnotif' \in 0..1
    BY SMT DEF Malformed, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>6. Strong /\ Malformed => nnull' \in 0..MaxReject
    BY RejectBound, SMT DEF Malformed, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>7. Strong /\ Malformed => stopgen' \in 0..MaxGen
    BY SMT DEF Malformed, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>8. Strong /\ Malformed => gen' = admit' /\ nstop' <= ninit'
    BY SMT DEF Malformed, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>9. Strong /\ Malformed => ninit' = ninitreply' /\ nstop' = nstopreply' + nnotif'
    BY SMT DEF Malformed, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>10. Strong /\ Malformed => (phase' = "running" => ninit' = 0) /\ (phase' = "initialized" => ninit' = 1 /\ nstop' = 0) /\ (phase' = "stopped" => ninit' = 1 /\ nstop' = 1)
    BY SMT DEF Malformed, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>11. Strong /\ Malformed => authority' = FALSE
    BY SMT DEF Malformed, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>12. Strong /\ Malformed => (echo' = "null" => nnull' >= 1) /\ (echo' = "req" => gen' >= 1 /\ admit' >= 1)
    BY SMT DEF Malformed, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>13. Strong /\ Malformed => (phase' = "stopped" => gen' = stopgen')
    BY SMT DEF Malformed, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
    DEF Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce,
    StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated,
    EchoSound, StopFrozen
<1>3. Strong /\ UnknownRequest => Strong'
  <2>1. Strong /\ UnknownRequest => phase' \in Phases
    BY SMT DEF UnknownRequest, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>2. Strong /\ UnknownRequest => echo' \in Replies
    BY SMT DEF UnknownRequest, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>3. Strong /\ UnknownRequest => closed' \in BOOLEAN /\ authority' \in BOOLEAN
    BY SMT DEF UnknownRequest, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>4. Strong /\ UnknownRequest => gen' \in 0..MaxGen /\ admit' \in 0..MaxGen
    BY AdmitBound, SMT DEF UnknownRequest, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>5. Strong /\ UnknownRequest => ninit' \in 0..1 /\ nstop' \in 0..1 /\ ninitreply' \in 0..1 /\ nstopreply' \in 0..1 /\ nnotif' \in 0..1
    BY SMT DEF UnknownRequest, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>6. Strong /\ UnknownRequest => nnull' \in 0..MaxReject
    BY SMT DEF UnknownRequest, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>7. Strong /\ UnknownRequest => stopgen' \in 0..MaxGen
    BY SMT DEF UnknownRequest, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>8. Strong /\ UnknownRequest => gen' = admit' /\ nstop' <= ninit'
    BY SMT DEF UnknownRequest, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>9. Strong /\ UnknownRequest => ninit' = ninitreply' /\ nstop' = nstopreply' + nnotif'
    BY SMT DEF UnknownRequest, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>10. Strong /\ UnknownRequest => (phase' = "running" => ninit' = 0) /\ (phase' = "initialized" => ninit' = 1 /\ nstop' = 0) /\ (phase' = "stopped" => ninit' = 1 /\ nstop' = 1)
    BY SMT DEF UnknownRequest, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>11. Strong /\ UnknownRequest => authority' = FALSE
    BY SMT DEF UnknownRequest, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>12. Strong /\ UnknownRequest => (echo' = "null" => nnull' >= 1) /\ (echo' = "req" => gen' >= 1 /\ admit' >= 1)
    BY SMT DEF UnknownRequest, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>13. Strong /\ UnknownRequest => (phase' = "stopped" => gen' = stopgen')
    BY SMT DEF UnknownRequest, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
    DEF Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce,
    StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated,
    EchoSound, StopFrozen
<1>4. Strong /\ InitOk => Strong'
  <2>1. Strong /\ InitOk => phase' \in Phases
    BY SMT DEF InitOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>2. Strong /\ InitOk => echo' \in Replies
    BY SMT DEF InitOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>3. Strong /\ InitOk => closed' \in BOOLEAN /\ authority' \in BOOLEAN
    BY SMT DEF InitOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>4. Strong /\ InitOk => gen' \in 0..MaxGen /\ admit' \in 0..MaxGen
    BY AdmitBound, SMT DEF InitOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>5. Strong /\ InitOk => ninit' \in 0..1 /\ nstop' \in 0..1 /\ ninitreply' \in 0..1 /\ nstopreply' \in 0..1 /\ nnotif' \in 0..1
    BY SMT DEF InitOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>6. Strong /\ InitOk => nnull' \in 0..MaxReject
    BY SMT DEF InitOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>7. Strong /\ InitOk => stopgen' \in 0..MaxGen
    BY SMT DEF InitOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>8. Strong /\ InitOk => gen' = admit' /\ nstop' <= ninit'
    BY SMT DEF InitOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>9. Strong /\ InitOk => ninit' = ninitreply' /\ nstop' = nstopreply' + nnotif'
    BY SMT DEF InitOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>10. Strong /\ InitOk => (phase' = "running" => ninit' = 0) /\ (phase' = "initialized" => ninit' = 1 /\ nstop' = 0) /\ (phase' = "stopped" => ninit' = 1 /\ nstop' = 1)
    BY SMT DEF InitOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>11. Strong /\ InitOk => authority' = FALSE
    BY SMT DEF InitOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>12. Strong /\ InitOk => (echo' = "null" => nnull' >= 1) /\ (echo' = "req" => gen' >= 1 /\ admit' >= 1)
    BY SMT DEF InitOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>13. Strong /\ InitOk => (phase' = "stopped" => gen' = stopgen')
    BY SMT DEF InitOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
    DEF Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce,
    StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated,
    EchoSound, StopFrozen
<1>5. Strong /\ InitBadParams => Strong'
  <2>1. Strong /\ InitBadParams => phase' \in Phases
    BY SMT DEF InitBadParams, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>2. Strong /\ InitBadParams => echo' \in Replies
    BY SMT DEF InitBadParams, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>3. Strong /\ InitBadParams => closed' \in BOOLEAN /\ authority' \in BOOLEAN
    BY SMT DEF InitBadParams, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>4. Strong /\ InitBadParams => gen' \in 0..MaxGen /\ admit' \in 0..MaxGen
    BY AdmitBound, SMT DEF InitBadParams, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>5. Strong /\ InitBadParams => ninit' \in 0..1 /\ nstop' \in 0..1 /\ ninitreply' \in 0..1 /\ nstopreply' \in 0..1 /\ nnotif' \in 0..1
    BY SMT DEF InitBadParams, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>6. Strong /\ InitBadParams => nnull' \in 0..MaxReject
    BY SMT DEF InitBadParams, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>7. Strong /\ InitBadParams => stopgen' \in 0..MaxGen
    BY SMT DEF InitBadParams, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>8. Strong /\ InitBadParams => gen' = admit' /\ nstop' <= ninit'
    BY SMT DEF InitBadParams, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>9. Strong /\ InitBadParams => ninit' = ninitreply' /\ nstop' = nstopreply' + nnotif'
    BY SMT DEF InitBadParams, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>10. Strong /\ InitBadParams => (phase' = "running" => ninit' = 0) /\ (phase' = "initialized" => ninit' = 1 /\ nstop' = 0) /\ (phase' = "stopped" => ninit' = 1 /\ nstop' = 1)
    BY SMT DEF InitBadParams, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>11. Strong /\ InitBadParams => authority' = FALSE
    BY SMT DEF InitBadParams, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>12. Strong /\ InitBadParams => (echo' = "null" => nnull' >= 1) /\ (echo' = "req" => gen' >= 1 /\ admit' >= 1)
    BY SMT DEF InitBadParams, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>13. Strong /\ InitBadParams => (phase' = "stopped" => gen' = stopgen')
    BY SMT DEF InitBadParams, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
    DEF Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce,
    StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated,
    EchoSound, StopFrozen
<1>6. Strong /\ InitAgain => Strong'
  <2>1. Strong /\ InitAgain => phase' \in Phases
    BY SMT DEF InitAgain, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>2. Strong /\ InitAgain => echo' \in Replies
    BY SMT DEF InitAgain, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>3. Strong /\ InitAgain => closed' \in BOOLEAN /\ authority' \in BOOLEAN
    BY SMT DEF InitAgain, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>4. Strong /\ InitAgain => gen' \in 0..MaxGen /\ admit' \in 0..MaxGen
    BY AdmitBound, SMT DEF InitAgain, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>5. Strong /\ InitAgain => ninit' \in 0..1 /\ nstop' \in 0..1 /\ ninitreply' \in 0..1 /\ nstopreply' \in 0..1 /\ nnotif' \in 0..1
    BY SMT DEF InitAgain, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>6. Strong /\ InitAgain => nnull' \in 0..MaxReject
    BY SMT DEF InitAgain, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>7. Strong /\ InitAgain => stopgen' \in 0..MaxGen
    BY SMT DEF InitAgain, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>8. Strong /\ InitAgain => gen' = admit' /\ nstop' <= ninit'
    BY SMT DEF InitAgain, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>9. Strong /\ InitAgain => ninit' = ninitreply' /\ nstop' = nstopreply' + nnotif'
    BY SMT DEF InitAgain, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>10. Strong /\ InitAgain => (phase' = "running" => ninit' = 0) /\ (phase' = "initialized" => ninit' = 1 /\ nstop' = 0) /\ (phase' = "stopped" => ninit' = 1 /\ nstop' = 1)
    BY SMT DEF InitAgain, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>11. Strong /\ InitAgain => authority' = FALSE
    BY SMT DEF InitAgain, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>12. Strong /\ InitAgain => (echo' = "null" => nnull' >= 1) /\ (echo' = "req" => gen' >= 1 /\ admit' >= 1)
    BY SMT DEF InitAgain, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>13. Strong /\ InitAgain => (phase' = "stopped" => gen' = stopgen')
    BY SMT DEF InitAgain, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
    DEF Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce,
    StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated,
    EchoSound, StopFrozen
<1>7. Strong /\ StopOk => Strong'
  <2>1. Strong /\ StopOk => phase' \in Phases
    BY SMT DEF StopOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>2. Strong /\ StopOk => echo' \in Replies
    BY SMT DEF StopOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>3. Strong /\ StopOk => closed' \in BOOLEAN /\ authority' \in BOOLEAN
    BY SMT DEF StopOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>4. Strong /\ StopOk => gen' \in 0..MaxGen /\ admit' \in 0..MaxGen
    BY AdmitBound, SMT DEF StopOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>5. Strong /\ StopOk => ninit' \in 0..1 /\ nstop' \in 0..1 /\ ninitreply' \in 0..1 /\ nstopreply' \in 0..1 /\ nnotif' \in 0..1
    BY SMT DEF StopOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>6. Strong /\ StopOk => nnull' \in 0..MaxReject
    BY SMT DEF StopOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>7. Strong /\ StopOk => stopgen' \in 0..MaxGen
    BY SMT DEF StopOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>8. Strong /\ StopOk => gen' = admit' /\ nstop' <= ninit'
    BY SMT DEF StopOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>9. Strong /\ StopOk => ninit' = ninitreply' /\ nstop' = nstopreply' + nnotif'
    BY SMT DEF StopOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>10. Strong /\ StopOk => (phase' = "running" => ninit' = 0) /\ (phase' = "initialized" => ninit' = 1 /\ nstop' = 0) /\ (phase' = "stopped" => ninit' = 1 /\ nstop' = 1)
    BY SMT DEF StopOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>11. Strong /\ StopOk => authority' = FALSE
    BY SMT DEF StopOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>12. Strong /\ StopOk => (echo' = "null" => nnull' >= 1) /\ (echo' = "req" => gen' >= 1 /\ admit' >= 1)
    BY SMT DEF StopOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>13. Strong /\ StopOk => (phase' = "stopped" => gen' = stopgen')
    BY SMT DEF StopOk, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
    DEF Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce,
    StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated,
    EchoSound, StopFrozen
<1>8. Strong /\ StopEarly => Strong'
  <2>1. Strong /\ StopEarly => phase' \in Phases
    BY SMT DEF StopEarly, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>2. Strong /\ StopEarly => echo' \in Replies
    BY SMT DEF StopEarly, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>3. Strong /\ StopEarly => closed' \in BOOLEAN /\ authority' \in BOOLEAN
    BY SMT DEF StopEarly, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>4. Strong /\ StopEarly => gen' \in 0..MaxGen /\ admit' \in 0..MaxGen
    BY AdmitBound, SMT DEF StopEarly, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>5. Strong /\ StopEarly => ninit' \in 0..1 /\ nstop' \in 0..1 /\ ninitreply' \in 0..1 /\ nstopreply' \in 0..1 /\ nnotif' \in 0..1
    BY SMT DEF StopEarly, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>6. Strong /\ StopEarly => nnull' \in 0..MaxReject
    BY SMT DEF StopEarly, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>7. Strong /\ StopEarly => stopgen' \in 0..MaxGen
    BY SMT DEF StopEarly, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>8. Strong /\ StopEarly => gen' = admit' /\ nstop' <= ninit'
    BY SMT DEF StopEarly, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>9. Strong /\ StopEarly => ninit' = ninitreply' /\ nstop' = nstopreply' + nnotif'
    BY SMT DEF StopEarly, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>10. Strong /\ StopEarly => (phase' = "running" => ninit' = 0) /\ (phase' = "initialized" => ninit' = 1 /\ nstop' = 0) /\ (phase' = "stopped" => ninit' = 1 /\ nstop' = 1)
    BY SMT DEF StopEarly, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>11. Strong /\ StopEarly => authority' = FALSE
    BY SMT DEF StopEarly, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>12. Strong /\ StopEarly => (echo' = "null" => nnull' >= 1) /\ (echo' = "req" => gen' >= 1 /\ admit' >= 1)
    BY SMT DEF StopEarly, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>13. Strong /\ StopEarly => (phase' = "stopped" => gen' = stopgen')
    BY SMT DEF StopEarly, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
    DEF Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce,
    StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated,
    EchoSound, StopFrozen
<1>9. Strong /\ StopNotify => Strong'
  <2>1. Strong /\ StopNotify => phase' \in Phases
    BY SMT DEF StopNotify, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>2. Strong /\ StopNotify => echo' \in Replies
    BY SMT DEF StopNotify, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>3. Strong /\ StopNotify => closed' \in BOOLEAN /\ authority' \in BOOLEAN
    BY SMT DEF StopNotify, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>4. Strong /\ StopNotify => gen' \in 0..MaxGen /\ admit' \in 0..MaxGen
    BY AdmitBound, SMT DEF StopNotify, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>5. Strong /\ StopNotify => ninit' \in 0..1 /\ nstop' \in 0..1 /\ ninitreply' \in 0..1 /\ nstopreply' \in 0..1 /\ nnotif' \in 0..1
    BY SMT DEF StopNotify, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>6. Strong /\ StopNotify => nnull' \in 0..MaxReject
    BY SMT DEF StopNotify, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>7. Strong /\ StopNotify => stopgen' \in 0..MaxGen
    BY SMT DEF StopNotify, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>8. Strong /\ StopNotify => gen' = admit' /\ nstop' <= ninit'
    BY SMT DEF StopNotify, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>9. Strong /\ StopNotify => ninit' = ninitreply' /\ nstop' = nstopreply' + nnotif'
    BY SMT DEF StopNotify, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>10. Strong /\ StopNotify => (phase' = "running" => ninit' = 0) /\ (phase' = "initialized" => ninit' = 1 /\ nstop' = 0) /\ (phase' = "stopped" => ninit' = 1 /\ nstop' = 1)
    BY SMT DEF StopNotify, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>11. Strong /\ StopNotify => authority' = FALSE
    BY SMT DEF StopNotify, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>12. Strong /\ StopNotify => (echo' = "null" => nnull' >= 1) /\ (echo' = "req" => gen' >= 1 /\ admit' >= 1)
    BY SMT DEF StopNotify, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>13. Strong /\ StopNotify => (phase' = "stopped" => gen' = stopgen')
    BY SMT DEF StopNotify, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
    DEF Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce,
    StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated,
    EchoSound, StopFrozen
<1>10. Strong /\ NotifyOther => Strong'
  <2>1. Strong /\ NotifyOther => phase' \in Phases
    BY SMT DEF NotifyOther, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>2. Strong /\ NotifyOther => echo' \in Replies
    BY SMT DEF NotifyOther, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>3. Strong /\ NotifyOther => closed' \in BOOLEAN /\ authority' \in BOOLEAN
    BY SMT DEF NotifyOther, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>4. Strong /\ NotifyOther => gen' \in 0..MaxGen /\ admit' \in 0..MaxGen
    BY AdmitBound, SMT DEF NotifyOther, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>5. Strong /\ NotifyOther => ninit' \in 0..1 /\ nstop' \in 0..1 /\ ninitreply' \in 0..1 /\ nstopreply' \in 0..1 /\ nnotif' \in 0..1
    BY SMT DEF NotifyOther, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>6. Strong /\ NotifyOther => nnull' \in 0..MaxReject
    BY SMT DEF NotifyOther, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>7. Strong /\ NotifyOther => stopgen' \in 0..MaxGen
    BY SMT DEF NotifyOther, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>8. Strong /\ NotifyOther => gen' = admit' /\ nstop' <= ninit'
    BY SMT DEF NotifyOther, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>9. Strong /\ NotifyOther => ninit' = ninitreply' /\ nstop' = nstopreply' + nnotif'
    BY SMT DEF NotifyOther, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>10. Strong /\ NotifyOther => (phase' = "running" => ninit' = 0) /\ (phase' = "initialized" => ninit' = 1 /\ nstop' = 0) /\ (phase' = "stopped" => ninit' = 1 /\ nstop' = 1)
    BY SMT DEF NotifyOther, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>11. Strong /\ NotifyOther => authority' = FALSE
    BY SMT DEF NotifyOther, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>12. Strong /\ NotifyOther => (echo' = "null" => nnull' >= 1) /\ (echo' = "req" => gen' >= 1 /\ admit' >= 1)
    BY SMT DEF NotifyOther, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>13. Strong /\ NotifyOther => (phase' = "stopped" => gen' = stopgen')
    BY SMT DEF NotifyOther, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
    DEF Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce,
    StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated,
    EchoSound, StopFrozen
<1>11. Strong /\ HugeIdReply => Strong'
  <2>1. Strong /\ HugeIdReply => phase' \in Phases
    BY SMT DEF HugeIdReply, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>2. Strong /\ HugeIdReply => echo' \in Replies
    BY SMT DEF HugeIdReply, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>3. Strong /\ HugeIdReply => closed' \in BOOLEAN /\ authority' \in BOOLEAN
    BY SMT DEF HugeIdReply, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>4. Strong /\ HugeIdReply => gen' \in 0..MaxGen /\ admit' \in 0..MaxGen
    BY AdmitBound, SMT DEF HugeIdReply, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>5. Strong /\ HugeIdReply => ninit' \in 0..1 /\ nstop' \in 0..1 /\ ninitreply' \in 0..1 /\ nstopreply' \in 0..1 /\ nnotif' \in 0..1
    BY SMT DEF HugeIdReply, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>6. Strong /\ HugeIdReply => nnull' \in 0..MaxReject
    BY SMT DEF HugeIdReply, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>7. Strong /\ HugeIdReply => stopgen' \in 0..MaxGen
    BY SMT DEF HugeIdReply, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>8. Strong /\ HugeIdReply => gen' = admit' /\ nstop' <= ninit'
    BY SMT DEF HugeIdReply, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>9. Strong /\ HugeIdReply => ninit' = ninitreply' /\ nstop' = nstopreply' + nnotif'
    BY SMT DEF HugeIdReply, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>10. Strong /\ HugeIdReply => (phase' = "running" => ninit' = 0) /\ (phase' = "initialized" => ninit' = 1 /\ nstop' = 0) /\ (phase' = "stopped" => ninit' = 1 /\ nstop' = 1)
    BY SMT DEF HugeIdReply, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>11. Strong /\ HugeIdReply => authority' = FALSE
    BY SMT DEF HugeIdReply, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>12. Strong /\ HugeIdReply => (echo' = "null" => nnull' >= 1) /\ (echo' = "req" => gen' >= 1 /\ admit' >= 1)
    BY SMT DEF HugeIdReply, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>13. Strong /\ HugeIdReply => (phase' = "stopped" => gen' = stopgen')
    BY SMT DEF HugeIdReply, Admitted, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
    DEF Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce,
    StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated,
    EchoSound, StopFrozen
<1>12. Strong /\ Eof => Strong'
  <2>1. Strong /\ Eof => phase' \in Phases
    BY SMT DEF Eof, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>2. Strong /\ Eof => echo' \in Replies
    BY SMT DEF Eof, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>3. Strong /\ Eof => closed' \in BOOLEAN /\ authority' \in BOOLEAN
    BY SMT DEF Eof, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>4. Strong /\ Eof => gen' \in 0..MaxGen /\ admit' \in 0..MaxGen
    BY AdmitBound, SMT DEF Eof, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>5. Strong /\ Eof => ninit' \in 0..1 /\ nstop' \in 0..1 /\ ninitreply' \in 0..1 /\ nstopreply' \in 0..1 /\ nnotif' \in 0..1
    BY SMT DEF Eof, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>6. Strong /\ Eof => nnull' \in 0..MaxReject
    BY SMT DEF Eof, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>7. Strong /\ Eof => stopgen' \in 0..MaxGen
    BY SMT DEF Eof, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>8. Strong /\ Eof => gen' = admit' /\ nstop' <= ninit'
    BY SMT DEF Eof, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>9. Strong /\ Eof => ninit' = ninitreply' /\ nstop' = nstopreply' + nnotif'
    BY SMT DEF Eof, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>10. Strong /\ Eof => (phase' = "running" => ninit' = 0) /\ (phase' = "initialized" => ninit' = 1 /\ nstop' = 0) /\ (phase' = "stopped" => ninit' = 1 /\ nstop' = 1)
    BY SMT DEF Eof, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>11. Strong /\ Eof => authority' = FALSE
    BY SMT DEF Eof, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>12. Strong /\ Eof => (echo' = "null" => nnull' >= 1) /\ (echo' = "req" => gen' >= 1 /\ admit' >= 1)
    BY SMT DEF Eof, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2>13. Strong /\ Eof => (phase' = "stopped" => gen' = stopgen')
    BY SMT DEF Eof, Live, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
    DEF Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce,
    StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated,
    EchoSound, StopFrozen
<1>13. Strong /\ UNCHANGED vars => Strong'
  <2>1. Strong /\ UNCHANGED vars => Strong'
    BY SMT DEF vars, Strong, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
  <2> QED BY <2>1 DEF Strong
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11,
  <1>12, <1>13 DEF Next

THEOREM SeedSafety ==
  Spec => [](TypeOK /\ GenAccounting /\ InitOnce /\ StopOnce /\ StopAfterInit
             /\ PhaseCounts /\ InitCited /\ StopCited /\ AuthorityIsolated
             /\ EchoSound /\ StopFrozen)
<1>1. Spec => []Strong BY StartOK, Preserve, PTL DEF Spec
<1> QED BY <1>1, PTL DEF Strong, TypeOK, TypeState, TypeArith, GenAccounting, InitOnce, StopOnce, StopAfterInit, PhaseCounts, InitCited, StopCited, AuthorityIsolated, EchoSound, StopFrozen, MaxGen, MaxReject, Phases, Replies
=============================================================================
