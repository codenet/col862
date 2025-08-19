----------------------------- MODULE FairTCommit ---------------------------- 
EXTENDS TCommit
\* FairTCSpec == TCSpec
\* FairTCSpec == TCSpec /\ WF_rmState(\E rm \in RM: Prepare(rm))
FairTCSpec == TCSpec /\ WF_rmState(TCNext)
Committed == \A rm \in RM: rmState[rm] = "committed"
Aborted == \A rm \in RM: rmState[rm] = "aborted"
EventuallyDecided == <>([]Committed \/ []Aborted)

THEOREM FairTCSpec => EventuallyDecided
=============================================================================