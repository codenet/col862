------------------------------ MODULE CR ------------------------------------
(* Chain Replication Spec *)

EXTENDS Naturals, Sequences

CONSTANT VALS
CONSTANT NIL
CONSTANT INITVAL
ASSUME INITVAL \in VALS

CONSTANTS RID, WID
ASSUME RID \cap WID = {}

CONSTANT TAIL
SERVERS == 1..TAIL
HEAD == 1

VARIABLE srvVals,       \* Current value at each server
         srvReqs,       \* Sequence of requests at each server
         srvReplied,    \* Reqs may not be idempotent. Track replied
         resps,         \* Sequence of responses
         reqs           \* Set of requests. Just for proving equivalence with 
                        \* SSLinear. Not used otherwise!

RdReq == [id: RID]
WrReq == [id: WID, v: VALS]
RdRes == [id: RID, v: VALS]
WrRes == [id: WID]
Req == RdReq \cup WrReq
Res == RdRes \cup WrRes

CRTypeOK ==
    /\ srvVals \in [SERVERS -> VALS]
    /\ srvReqs \in [SERVERS -> Seq(Req)]
    /\ srvReplied \in [SERVERS -> [r: SUBSET RID, w: SUBSET WID]]
    /\ resps \in Seq(Res)
    /\ reqs \subseteq Req
-----------------------------------------------------------------------------

CRInit ==
    /\ srvVals = [s \in SERVERS |-> INITVAL]
    /\ srvReqs = [s \in SERVERS |-> <<>>]
    /\ srvReplied = [s \in SERVERS |-> [r |-> {}, w |-> {}]]
    /\ resps = <<>>
    /\ reqs = {}

IssueRead(rid) ==
    LET op == [id |-> rid] IN
    /\ reqs' = reqs \cup {op}
    /\ srvReqs' = [srvReqs EXCEPT ![TAIL] = Append(@, op)]
    /\ UNCHANGED <<srvVals, srvReplied, resps>>
    
IssueWrite(wid) ==
    \E v \in VALS:
        LET op == [id |-> wid, v |-> v] IN
        /\ reqs' = reqs \cup {op}
        /\ srvReqs' = [srvReqs EXCEPT ![HEAD] = Append(@, op)]
        /\ UNCHANGED <<srvVals, srvReplied, resps>>

DropRead(op, s) ==
    /\ op.id \in RID 
    /\ op.id \in srvReplied[s].r
    /\ srvReqs' = [srvReqs EXCEPT ![s] = Tail(@)]
    /\ UNCHANGED <<srvVals, resps, srvReplied, reqs>>

DropWrite(op, s) ==
    /\ op.id \in WID 
    /\ op.id \in srvReplied[s].w
    /\ srvReqs' = [srvReqs EXCEPT ![s] = Tail(@)]
    /\ UNCHANGED <<srvVals, resps, srvReplied, reqs>>

ServerReads(op, s) == 
    /\ op.id \in RID
    /\ op.id \notin srvReplied[s].r
    /\ srvReplied' = [srvReplied EXCEPT ![s] = [@ EXCEPT !.r = @ \union {op.id}]]
    /\ resps' = Append(resps, [id |-> op.id, v |-> srvVals[s]])
    /\ UNCHANGED <<srvVals, srvReqs, reqs>>

ServerWrites(op, s) ==
    /\ op.id \in WID
    /\ op.id \notin srvReplied[s].w
    /\ srvReplied' = [srvReplied EXCEPT ![s] = [@ EXCEPT !.w = @ \union {op.id}]]
    /\ srvVals' = [srvVals EXCEPT ![s] = op.v]
    /\ \/ /\ s+1 > TAIL 
          /\ resps' = Append(resps, [id |-> op.id])
          /\ srvReqs' = srvReqs
       \/ /\ s+1 <= TAIL
          /\ srvReqs' = [srvReqs  EXCEPT ![s+1] = Append(@, op)]
          /\ resps' = resps
    /\ UNCHANGED <<reqs>>
    

CRNext == \/ \E rid \in RID: IssueRead(rid)
          \/ \E wid \in WID: IssueWrite(wid)
          \/ \E s \in SERVERS:
            /\ Len(srvReqs[s]) > 0
            /\ LET o == Head(srvReqs[s]) IN
                \/ DropRead(o, s)
                \/ DropWrite(o, s)
                \/ ServerReads(o, s)
                \/ ServerWrites(o, s)

CRSpec == CRInit /\ [][CRNext]_<<srvReplied, srvVals, srvReqs, resps, reqs>>
THEOREM CRSpec => [] CRTypeOK
=============================================================================