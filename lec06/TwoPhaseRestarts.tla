-------------------------- MODULE TwoPhaseRestarts -------------------------- 
CONSTANT RM \* The set of resource managers

VARIABLES
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  tmState,       \* The state of the transaction manager.
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
  msgs           \* messages.

(* An incorrect specification that does not do write-ahead logging. RMs
 * simply reset themselves and TM unilaterally aborts after a restart. *)

\* Go back to working
RMRestart(r) == 
    /\ rmState' = [rmState EXCEPT ![r] = "working"] 
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* Restart and unilaterally abort
TMRestart ==
    /\ tmState' = "aborted"
    /\ tmPrepared' = {}
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<rmState>>

TP == INSTANCE TwoPhase
TPRNext == \/ TP!TPNext 
           \/ TMRestart
           \/ \E rm \in RM: RMRestart(rm)
-----------------------------------------------------------------------------
TPRSpec == TP!TPInit /\ [][TPRNext]_<<rmState, tmState, tmPrepared, msgs>>

TPTypeOK == TP!TPTypeOK
THEOREM TPRSpec => []TPTypeOK

TCConsistent == TP!TCConsistent
THEOREM TPRSpec => []TCConsistent
=============================================================================