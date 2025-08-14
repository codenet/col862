------------------------------- MODULE TPProofs ------------------------------
EXTENDS TLAPS
CONSTANT RM
VARIABLES rmState, tmState, tmPrepared, msgs

TC == INSTANCE TCommit
TP == INSTANCE TwoPhase
TCSpec == TC!TCSpec
TPSpec == TP!TPSpec

------------------------------------------------------------------------------
TPInv1 == (\E rm \in RM: rmState[rm] = "waiting") => TC!notCommitted
TPInv2 == [type |-> "Abort"] \in msgs => TC!notCommitted
TPInv3 == [type |-> "Commit"] \in msgs => TC!canCommit
TPInv == (TPInv1 /\ TPInv2 /\ TPInv3)

THEOREM Invariants == TP!TPSpec => []TPInv
PROOF
<1>1. TP!TPInit => TPInv

<1>2. TPInv /\ [TP!TPNext]_<<rmState, tmState, tmPrepared, msgs>> => TPInv'

<1>3. QED
    BY <1>1, <1>2, PTL DEF TP!TPSpec

------------------------------------------------------------------------------
THEOREM Implements == TP!TPSpec => TC!TCSpec
PROOF
<1>1. TP!TPInit => TC!TCInit

<1>2. [TP!TPNext]_<<rmState, tmState, tmPrepared, msgs>> => [TC!TCNext]_rmState

<1>3. QED
    BY <1>1, <1>2, PTL DEF TC!TCSpec, TP!TPSpec

------------------------------------------------------------------------------
\* The following obviously does not work
\* THEOREM Implements == TC!TCSpec => TP!TPSpec
\* PROOF
\* <1>1. TC!TCInit => TP!TPInit

\* <1>2. [TC!TCNext]_rmState => [TP!TPNext]_<<rmState, tmState, tmPrepared, msgs>>

\* <1>3. QED
\*     BY <1>1, <1>2, PTL DEF TC!TCSpec, TP!TPSpec

==============================================================================