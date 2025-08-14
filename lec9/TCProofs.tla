------------------------------- MODULE TCProofs ------------------------------
EXTENDS TLAPS
CONSTANT RM
VARIABLES rmState

TC == INSTANCE TCommit
Inv == TC!TCTypeOK /\ TC!TCConsistent

------------------------------------------------------------------------------
THEOREM Safe == TC!TCSpec => []Inv
PROOF
<1>1. TC!TCInit => Inv

<1>2. Inv /\ [TC!TCNext]_rmState => Inv'

<1>3. QED
    BY <1>1, <1>2, PTL DEF TC!TCSpec
==============================================================================