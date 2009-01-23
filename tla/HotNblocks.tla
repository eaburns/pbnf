-------------------- MODULE HotNblocks --------------------
EXTENDS FiniteSets, Naturals
CONSTANTS nnblocks, nprocs, search, nextblock, none
VARIABLES state, acquired, isHot, Succs
Vars == <<state, acquired, isHot, Succs>>
States == {search, nextblock}
Nblocks == 0 .. nnblocks - 1
Procs == 0 .. nprocs - 1
ASSUME nnblocks >= nprocs /\ nprocs > 0 /\ nnblocks > 1 /\ none \notin Nblocks /\ Cardinality(States) = 2

TypeInv == /\ state \in [Procs -> States]
           /\ acquired \in [Procs -> Nblocks \union {none}]
           /\ isHot \in [Nblocks -> BOOLEAN]
           /\ Succs \in [Nblocks -> SUBSET Nblocks]

Preds(x) == {y \in Nblocks : x \in Succs[y]}                     \* Set of predecessors to Nblock x
IntScope(x) == Succs[x] \union UNION {Preds(y) : y \in Succs[x]} \* The interference scope of x
Busy(A) == A \union UNION {Succs[x] : x \in A}                   \* Set of Nblocks which are busy given the set of acquired nblocks
Overlap(x, A) == Succs[x] \intersect Busy(A)                     \* Set of Busy Nblocks overlapping the successors of x
Hot(A) == {x \in Nblocks : isHot[x] /\ Overlap(x, A) # {}}       \* Set of all hot nblocks given the set of acquired nblocks
HotInterference(A) == UNION {IntScope(x) : x \in Hot(A)}         \* Set of Nblocks in interference scopes of hot nblocks
Free(A) == {x \in Nblocks : Overlap(x, A) = {} /\ x \notin HotInterference(A)} \* Free Nblocks given the set of acquired nblocks
Acquired == {acquired[x] : x \in Procs} \ {none}                 \* Set of Nblocks which are currently acquired

Donextblock(x) == /\ UNCHANGED<<Succs>>
                  /\ state[x] = nextblock
                  /\ acquired[x] = none => Free(Acquired) # {}
                  /\ IF Free(Acquired \ {acquired[x]}) # {} THEN
                       /\ \E y \in Free(Acquired \ {acquired[x]}) : acquired' = [acquired EXCEPT ![x] = y]
                       /\ state' = [state EXCEPT ![x] = search]
                       /\ isHot' = [y \in Nblocks |-> IF y \in Free(Acquired \ {acquired[x]}) THEN FALSE ELSE isHot[y]]
                     ELSE /\ acquired' = [acquired EXCEPT ![x] = none]
                          /\ UNCHANGED<<state, isHot>>

Dosearch(x) == /\ UNCHANGED<<acquired, Succs>>
               /\ state[x] = search
               /\ state' = [state EXCEPT ![x] = nextblock]
               /\ \/ UNCHANGED<<isHot>>
                  \/ \E y \in Succs[acquired[x]] : /\ ~isHot[y]
                                                   /\ IntScope(y) \intersect Hot(Acquired) = {}
                                                   /\ isHot' = [isHot EXCEPT ![y] = TRUE]

Init == /\ state = [x \in Procs |-> nextblock]
        /\ acquired = [x \in Procs |-> none]
        /\ isHot = [x \in Nblocks |-> FALSE]
        /\ Succs = [x \in Nblocks |-> IF x = 0 THEN {nnblocks - 1, x + 1}
                                      ELSE IF x = nnblocks - 1 THEN {0, x - 1} ELSE {x - 1, x + 1}]
        /\ TypeInv

Next == \E x \in Procs : (Donextblock(x) \/ Dosearch(x))
Fairness == \A x \in Procs : WF_Vars(Donextblock(x) \/ Dosearch(x))
Prog == Init /\ [][Next]_Vars /\ Fairness
------------------------------------------------------------
HotNblocks == \A x \in Nblocks : isHot[x] ~> ~isHot[x]

NoCollisions == \A x,y \in Procs : x # y => \/ acquired[x] = none
                                            \/ acquired[y] = none
                                            \/ /\ acquired[x] # acquired[y]
                                               /\ Succs[x] \intersect Succs[y] = {}
============================================================
