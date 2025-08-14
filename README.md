Lectures

1. Introduction to distributed storage systems. Safety and Liveness. Linearizability.<br/>Recommended reading: [How Amazon web services uses formal methods](https://dl.acm.org/doi/pdf/10.1145/2699417)
2. [Leslie's lectures 1-4.](https://lamport.azurewebsites.net/video/videos.html)
3. Read/write/visualize some TLA+ specs. State machines, actions, invariants, enabling condition of an action, explicit model checkers (like TLC) check invariants by just traversing the state machine.
4. Distributed ACID transactions. Isolation: Serializability, optimistic/pessimistic concurrency control, wound-wait deadlock avoidance. Atomicity: Two-phase commits. 
5. [Leslie's lectures 5-6.](https://lamport.azurewebsites.net/video/videos.html)
6. Read TLA+ specs for transaction commit and two-phase commit. Restarts in two-phase commits. Write-ahead logging.
7. [Chain Replication](https://www.usenix.org/legacy/publications/library/proceedings/osdi04/tech/full_papers/renesse/renesse.pdf). Replicated state machines. Write TLA+ specs for a single server key-value store and a chain replicated key-value store. 
8. [Leslie's lectures 8(a,b).](https://lamport.azurewebsites.net/video/videos.html)
9. TLA+ specification is just a temporal formula that accepts certain behaviors. State formulas, invariants, action formulas, box action formulas. Induction for proving invariants. Prove TCSpec from transaction commit has TCTypeOk invariant.
10. Stuttering. Prove that two-phase commit implements transaction commit. Eventually. TLA inference and equivalence rules.
