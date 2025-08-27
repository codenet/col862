# How to Build a Highly Available System Using Consensus

The .tla files are taken from
[here](https://lamport.azurewebsites.net/tla/paxos-algorithm.html).  Read `Spec`
in `Consensus.tla`, `Voting.tla`, and `Paxos.tla`.  There are accompanying
lecture videos and slides from Leslie on the link.

In a nutshell, there are `2F+1` acceptors who have to collectively choose
*exactly one* value from a set of `Value`s. For example, in building a replicated
key-value store (as a replicated state machine), acceptors want to choose the
next "client request" to service. Regardless of acceptor failures, leader
failures, lost messages, delayed messages, duplicate messages, and clock skews,
everyone *must* agree on a single chosen value. The algorithm can tolerate `F`
acceptor faults. If `F+1` acceptors are eventually alive, the algorithm might
eventually choose a value. The algorithm may never choose a value (in line with
the FLP impossibility theorem).

The heart of the algorithm is the theorem `ShowsSafety` in
[Voting.tla](./Voting.tla). The theorem basically ensures that *leaders can only
propose **safe values***.  A value is safe if it is the one that was chosen
(quorum of acceptors chose this value in a previous ballot); or any other value
if there was no consensus yet (quorum of acceptors never voted and never will
vote on the same value in any previous ballot).  Before trying to understand
this theorem, build intuitions for it from the scenarios given in Section 6.4 of
the paper.

Here, we try to explain this theorem informally in english. The theorem ensures
that the leader of ballot `b` will only propose a value `v` if `ShowsSafeAt(Q,
b, v)` holds for any quorum `Q`. Say `c` is the last ballot where *anyone* in
the quorum `Q` had voted. 

Case 1: If no one in the quorum has ever voted (`c=-1`), we are sure that there
*cannot* be a chosen value (all quorums have at least one common acceptor with
`Q`). Therefore, it is safe to propose any value, including `v`.

Case 2: Someone in the quorum had voted for the value `v` in ballot `c`. Due to
the invariant `OneValuePerBallot` (leader only proposes a single value in a
ballot), other acceptors (potentially outside of `Q`) could also have only voted
for the value `v`. In case there was a quorum in the ballot `c`, the quorum only
could have been for the value `v`. Hence, it is safe to propose `v`.

Could there be a quorum at some ballot number, say `d`, which is greater than
`c` and less than `b`? No! We know that `c` was the *last ballot* for which
*anyone* in the quorum `Q` had voted. Hence, in the ballot `d`, we could not have
established a quorum (all quorums have at least one common acceptor with `Q`).

Could acceptors have voted for `v` in ballot `c`, but a quorum was reached for
another value, say `w`, in ballot `d` < `c`? No! Acceptors voted for value `v`
in ballot `c` **because it was safe** (from this same theorem). If `w` was
already chosen in ballot `d`, value `v` could not have been proposed in ballot
`c`.