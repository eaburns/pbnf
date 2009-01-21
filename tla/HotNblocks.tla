-------------------- MODULE HotNblocks --------------------
EXTENDS FiniteSets, Naturals
CONSTANTS NNblocks, NProcs, Search, NextBlock, None
VARIABLES state, acquired, isHot, Succs
Vars == <<state, acquired, isHot, Succs>>
States == {Search, NextBlock}
Nblocks == 0 .. NNblocks - 1
Procs == 0 .. NProcs - 1
ASSUME NNblocks >= NProcs /\ NProcs > 0 /\ NNblocks > 1 /\ None \notin Nblocks /\ Cardinality(States) = 2

TypeInv == /\ state \in [Procs -> States]
           /\ acquired \in [Procs -> Nblocks \union {None}]
           /\ isHot \in [Nblocks -> BOOLEAN]
           /\ Succs \in [Nblocks -> SUBSET Nblocks]

Preds(x) == {y \in Nblocks : x \in Succs[y]}                     \* Set of predecessors to Nblock x
IntScope(x) == Succs[x] \union UNION {Preds(y) : y \in Succs[x]} \* The interference scope of x
Busy(A) == A \union UNION {Succs[x] : x \in A}                   \* Set of Nblocks which are busy given the set of acquired nblocks
Overlap(x, A) == Succs[x] \intersect Busy(A)                     \* Set of Busy Nblocks overlapping the 
Hot(A) == {x \in Nblocks : isHot[x] /\ Overlap(x, A) # {}}       \* Set of all hot nblocks given the set of acquired nblocks
HotInterference(A) == UNION {IntScope(x) : x \in Hot(A)}         \* Set of Nblocks in interference scopes of hot nblocks
Free(A) == {x \in Nblocks : Overlap(x, A) = {} /\ x \notin HotInterference(A)} \* Free Nblocks given the set of acquired nblocks
Acquired == {acquired[x] : x \in Procs} \ {None}                 \* Set of Nblocks which are currently acquired

DoNextBlock(x) == /\ UNCHANGED<<Succs>>
                  /\ state[x] = NextBlock
                  /\ acquired[x] = None => Free(Acquired) # {}
                  /\ IF Free(Acquired \ {acquired[x]}) # {} THEN
                       /\ \E y \in Free(Acquired \ {acquired[x]}) : acquired' = [acquired EXCEPT ![x] = y]
                       /\ state' = [state EXCEPT ![x] = Search]
                       /\ isHot' = [y \in Nblocks |-> IF y \in Free(Acquired \ {acquired[x]}) THEN FALSE ELSE isHot[y]]
                     ELSE /\ acquired' = [acquired EXCEPT ![x] = None]
                          /\ UNCHANGED<<state, isHot>>

DoSearch(x) == /\ UNCHANGED<<acquired, Succs>>
               /\ state[x] = Search
               /\ state' = [state EXCEPT ![x] = NextBlock]
               /\ \/ UNCHANGED<<isHot>>
                  \/ \E y \in Succs[acquired[x]] : /\ ~isHot[y]
                                                   /\ IntScope(y) \intersect Hot(Acquired) = {}
                                                   /\ isHot' = [isHot EXCEPT ![y] = TRUE]

Init == /\ state = [x \in Procs |-> NextBlock]
        /\ acquired = [x \in Procs |-> None]
        /\ isHot = [x \in Nblocks |-> FALSE]
(*
        /\ Succs = [x \in Nblocks |-> IF x = 0 THEN {1}
                                      ELSE IF x = 1 THEN {0,2}
                                      ELSE IF x = 2 THEN {0,3}
                                      ELSE IF x = 3 THEN {0,4}
                                      ELSE IF x = 4 THEN {3}
                                      ELSE {}]
*)
        /\ TypeInv
        /\ \A x \in Nblocks : /\ x \notin Succs[x]
                              \* This is just so that TLC won't have to search too many initial states.
                              /\ IF x > 0 /\ x < NNblocks - 1 THEN /\ \E i,j \in Nblocks : i < x /\ x < j /\ Succs[x] = {i, j}
                                 ELSE IF x = 0 THEN \E i \in Nblocks : i > x /\ Succs[x] = {i}
                                      ELSE \E i \in Nblocks : i < x /\ Succs[x] = {i}

Next == \E x \in Procs : (DoNextBlock(x) \/ DoSearch(x))
Fairness == \A x \in Procs : WF_Vars(DoNextBlock(x) \/ DoSearch(x))
Prog == Init /\ [][Next]_Vars /\ Fairness
------------------------------------------------------------
HotNblocks == \A x \in Nblocks : isHot[x] ~> ~isHot[x]

NoCollisions == \A x,y \in Procs : x # y => \/ acquired[x] = None
                                            \/ acquired[y] = None
                                            \/ /\ acquired[x] # acquired[y]
                                               /\ Succs[x] \intersect Succs[y] = {}
============================================================
