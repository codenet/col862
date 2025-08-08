------------------------------ MODULE SS ------------------------------
(* Single server spec *)

EXTENDS Naturals, Sequences

CONSTANT VALS
CONSTANT NIL
CONSTANT INITVAL
ASSUME INITVAL \in VALS
ASSUME NIL \notin VALS

CONSTANTS RID, WID
ASSUME RID \cap WID = {}

VARIABLE reqs,      \* Set of requests
         val,       \* Current value
         accepted,  \* reqs may not be idempotent. Need to track accepted reqs.
         resps      \* Sequence of responses


(*id is kept to have multiple in-flight messages of the same type in the set.*)
RdReq == [id: RID]
WrReq == [id: WID, v: VALS]
                     
RdRes == [id: RID, v: VALS]
WrRes == [id: WID]

Req == RdReq \union WrReq
Res == RdRes \union WrRes

SSTypeOK ==
    /\ reqs \subseteq Req
    /\ val \in VALS
    /\ accepted \in [r: SUBSET RID, w: SUBSET WID]
    /\ resps \in Seq(Res)

SSInit ==
    /\ val = INITVAL
    /\ reqs = {}
    /\ accepted = [r |-> {}, w |-> {}]
    /\ resps = <<>>

IssueRead(rid) ==
    /\ reqs' = reqs \cup {[id |-> rid]}
    /\ UNCHANGED <<val, accepted, resps>>
    
IssueWrite(wid) ==
    \E v \in VALS:
        /\ reqs' = reqs \cup {[id |-> wid, v |-> v]}
        /\ UNCHANGED <<val, accepted, resps>>
        
LostRead(op) ==
    /\ op.id \in RID
    /\ accepted' = [accepted EXCEPT !.r = @ \cup {op.id}]
    /\ UNCHANGED <<reqs, val, resps>>

LostWrite(op) ==
    /\ op.id \in WID
    /\ accepted' = [accepted EXCEPT !.w = @ \cup {op.id}]
    /\ UNCHANGED <<reqs, val, resps>>

ApplyRead(op) ==
    /\ op.id \in RID
    /\ op.id \notin accepted.r
    /\ resps' = Append(resps, [id |-> op.id, v |-> val])
    /\ accepted' = [accepted EXCEPT !.r = @ \cup {op.id}]
    /\ UNCHANGED <<reqs, val>>

ApplyWrite(op) ==
    /\ op.id \in WID
    /\ op.id \notin accepted.w
    /\ val' = op.v
    /\ resps' = Append(resps, [id |-> op.id])
    /\ accepted' = [accepted EXCEPT !.w = @ \cup {op.id}]
    /\ UNCHANGED reqs

SSNext == 
    \/ \E rid \in RID: IssueRead(rid)
    \/ \E wid \in WID: IssueWrite(wid)
    \/ \E op \in reqs: 
        \/ LostRead(op)
        \/ LostWrite(op)
        \/ ApplyRead(op)
        \/ ApplyWrite(op)

SSSpec == SSInit /\ [][SSNext]_<<reqs, val, accepted, resps>>

THEOREM SSSpec => [] SSTypeOK
=============================================================================