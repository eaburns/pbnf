-------------------- MODULE HotNblocks --------------------
EXTENDS FiniteSets, Naturals
CONSTANTS NNblocks, NProcs, Search, NextBlock, None
VARIABLES state, acquired, isHot, scope
Vars == <<state, acquired, isHot, scope>>
States == {Search, NextBlock}
Nblocks == 0 .. NNblocks - 1
Procs == 0 .. NProcs - 1
ASSUME NNblocks >= NProcs /\ NProcs > 0 /\ NNblocks > 1 /\ None \notin Nblocks /\ Cardinality(States) = 2

TypeInv == /\ state \in [Procs -> States]
           /\ acquired \in [Procs -> Nblocks \union {None}]
           /\ isHot \in [Nblocks -> BOOLEAN]
           /\ scope \in [Nblocks -> SUBSET Nblocks]

InterferesWith(x) == { y \in Nblocks : x \in scope[y] }          \* Set of Nblocks which x prevents from becoming free
Busy(A) == A \union UNION { scope[x] : x \in A }                 \* Set of Nblocks which are busy given the set of acquired nblocks
Blocking(x, A) == scope[x] \intersect Busy(A)                    \* Set of Nblocks blocking nblock x from being free, given the acquired set
Cold(A) == { x \in Nblocks : ~isHot[x] \/ Blocking(x, A) = {} }  \* Set of all cold nblocks given the set of acquired nblocks.
\* Free Nblocks given the set of acquired nblocks
Free(A) == { x \in Nblocks : Blocking(x, Busy(A)) = {} /\ InterferesWith(x) \subseteq Cold(A)}
Acquired == { x \in Nblocks : \E y \in Procs : acquired[y] = x } \* Set of Nblocks which are currently acquired
CurFree == Free(Acquired)                                        \* Nblocks which are currently free

DoNextBlock(x) == /\ UNCHANGED<<scope>>
                  /\ state[x] = NextBlock
                  /\ acquired[x] = None => CurFree # {}
                  /\ IF Free(Acquired \ {acquired[x]}) # {} THEN
                       /\ \E y \in Free(Acquired \ {acquired[x]}) : acquired' = [acquired EXCEPT ![x] = y]
                       /\ state' = [state EXCEPT ![x] = Search]
                       /\ isHot' = [y \in Nblocks |-> IF y \in Acquired' \/ Blocking(y, Busy(Acquired))' = {} THEN FALSE
                                                      ELSE isHot[y]]
                     ELSE /\ acquired' = [acquired EXCEPT ![x] = None]
                          /\ UNCHANGED<<state, isHot>>

DoSearch(x) == /\ UNCHANGED<<acquired, scope>>
               /\ state[x] = Search
               /\ state' = [state EXCEPT ![x] = NextBlock]
               /\ \/ UNCHANGED<<isHot>>
                  \/ \E y \in scope[acquired[x]] : /\ ~isHot[y]
                                                   /\ \A z \in Nblocks : x \in InterferesWith(z) => ~isHot[z]
                                                   /\ \A z \in Nblocks : isHot[x] => z \notin InterferesWith(x)
                                                   /\ isHot' = [isHot EXCEPT ![y] = TRUE]

Init == /\ state = [x \in Procs |-> NextBlock]
        /\ acquired = [x \in Procs |-> None]
        /\ isHot = [x \in Nblocks |-> FALSE]
        /\ TypeInv
        /\ \A x \in Nblocks : /\ x \notin scope[x]
                              \* This is just so that TLC won't have to search too many initial states.
                              /\ IF x > 0 /\ x < NNblocks - 1 THEN /\ \E i,j \in Nblocks : i < x /\ x < j /\ scope[x] = {i, j}
                                 ELSE IF x = 0 THEN \E i \in Nblocks : i > x /\ scope[x] = {i}
                                      ELSE \E i \in Nblocks : i < x /\ scope[x] = {i}

Next == \E x \in Procs : (DoNextBlock(x) \/ DoSearch(x))
Fairness == \A x \in Procs : WF_Vars(DoNextBlock(x) \/ DoSearch(x))
Prog == Init /\ [][Next]_Vars /\ Fairness
------------------------------------------------------------
HotNblocks == \A x \in Nblocks : isHot[x] ~> x \in CurFree \/ x \in Acquired

NoCollisions == \A x,y \in Procs : x # y => \/ acquired[x] = None /\ acquired[y] = None
                                            \/ /\ acquired[x] # acquired[y]
                                               /\ acquired[x] \notin InterferesWith(y)
                                               /\ acquired[y] \notin InterferesWith(x)
                                               /\ Blocking(x, Acquired) = {}
                                               /\ Blocking(y, Acquired) = {}
============================================================
