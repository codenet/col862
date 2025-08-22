------------------------------ MODULE MCSS ------------------------------------
EXTENDS SS, FiniteSets, TLC

Symmetries == Permutations(VALS) \cup Permutations(RID) \cup Permutations(WID)
=============================================================================