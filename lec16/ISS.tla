------------------------------ MODULE ISS -----------------------------
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
         resps,     \* Sequence of responses
         val,       \* Current value
         accepted   \* reqs may not be idempotent. Need to track accepted reqs.


(*id is kept to have multiple in-flight messages of the same type in the set.*)
RdReq == [id: RID]
WrReq == [id: WID, v: VALS]
                     
RdRes == [id: RID, v: VALS]
WrRes == [id: WID]

Req == RdReq \union WrReq
Res == RdRes \union WrRes

SSTypeOK ==
    /\ reqs \subseteq Req
    /\ resps \in Seq(Res)
    /\ val \in VALS
    /\ accepted \in [r: SUBSET RID, w: SUBSET WID]

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

ApplyRead(op) ==
    /\ op.id \in RID
    /\ op.id \notin accepted.r
    /\ accepted' = [accepted EXCEPT !.r = @ \cup {op.id}]
    /\ resps' = Append(resps, [id |-> op.id, v |-> val])
    /\ UNCHANGED <<reqs, val>>

ApplyWrite(op) ==
    /\ op.id \in WID
    /\ op.id \notin accepted.w
    /\ accepted' = [accepted EXCEPT !.w = @ \cup {op.id}]
    /\ resps' = Append(resps, [id |-> op.id])
    /\ val' = op.v
    /\ UNCHANGED reqs

SSNext ==
    \/ \E rid \in RID: IssueRead(rid)
    \/ \E wid \in WID: IssueWrite(wid)
    \/ \E op \in reqs:
        \/ ApplyRead(op)
        \/ ApplyWrite(op)

SSSpec == SSInit /\ [][SSNext]_<<reqs, val, accepted, resps>>

THEOREM SSSpec => [] SSTypeOK
=============================================================================