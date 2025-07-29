------------------------- MODULE Goat -----------------------------
EXTENDS Naturals, FiniteSets
VARIABLES left, boat, right

C == "Cabbage"
G == "Goat"
W == "Wolf"
F == "Farmer"
Boat == {{}, {F}, {F, C}, {F, W}, {F, G}}
Danger == {{G, C}, {G, W}, {G, W, C}}

TypeOK == /\ boat \in Boat
          /\ left \in SUBSET {F, C, G, W}
          /\ right \in SUBSET {F, C, G, W}

Sane == /\ left \cap right = {}
        /\ left \cap boat = {}
        /\ right \cap boat = {}
        /\ left \notin Danger
        /\ right \notin Danger

NotSolved == right # {F, C, G, W}

-------------------------------------------------------------------
Init == /\ left = {C, G, W, F}
        /\ boat = {}
        /\ right = {}

EmptyLeft == /\ boat' = {}
             /\ left' = left \cup boat
             /\ right' = right

EmptyRight == /\ boat' = {}
              /\ right' = right \cup boat
              /\ left' = left

FillLeft(P) == /\ (boat \cup P) \in Boat
               /\ (left \ P) \notin Danger
               /\ boat' = (boat \cup P)
               /\ left' = (left \ P)
               /\ right' = right

FillRight(P) == /\ (boat \cup P) \in Boat
                /\ (right \ P) \notin Danger
                /\ boat' = (boat \cup P)
                /\ right' = (right \ P)
                /\ left' = left

Next == \/ EmptyLeft
        \/ EmptyRight
        \/ \E P \in SUBSET left: FillLeft(P)
        \/ \E P \in SUBSET right: FillRight(P)

Spec == /\ Init
        /\ [][Next]_<<left, right, boat>>
===================================================================