------------------------------ MODULE MCICR ---------------------------------
EXTENDS ICR, FiniteSets, TLC

Symmetries == Permutations(VALS) \cup Permutations(RID) \cup Permutations(WID)
LimitedMsgs == \A s \in SERVERS: Len(srvReqs[s]) <= 2

SSSpec == SS!SSSpec

=============================================================================