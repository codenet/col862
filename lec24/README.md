## Material sources
- Main paper: [High Throughput Replication with Integrated Membership Management](https://www.usenix.org/system/files/atc22-fouto.pdf)
- Reference Slides: [PDF link](https://www.usenix.org/system/files/atc22_slides_fouto.pdf)
- Official paper presentation: [YouTube link](https://youtu.be/0E1k73hXmkA)

## ChainPaxos Animation

This repository also contains an animation of the ChainPaxos protocol built using TLA+ and Spectacle.

## Running the Animation

1. Open the ChainCraft animation viewer:

   https://chainraft.web.app

2. Fill the configuration details.

3. Start the animation and use the available actions to explore protocol execution, reconfiguration, and failure scenarios.

## What the Animation Shows

The animation provides an interactive view of:

* Client operations and requests
* Server states
* Message exchanges
* Replicated logs
* Buffers and read queues
* Leader information
* Reconfiguration events (AddNode and RemoveNode)
* State transfer during node addition
* Failure-handling scenarios

## Instructions

A detailed explanation of:

* How to run the animation
* Available actions
* Meaning of each visual component
* Interpretation of protocol states and messages

is provided in [this PDF.](./Instructions.pdf)

Please refer to the PDF for a complete walkthrough of the animation and its features.
