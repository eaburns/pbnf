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
IntBy(x) == {y \in Nblocks : x \in IntScope(y)}                  \* Set of Nblocks which x interferes.
Busy(A) == A \union UNION {Succs[x] : x \in A}                   \* Set of Nblocks which are busy given the set of acquired nblocks
Overlap(x, A) == Succs[x] \intersect Busy(A)                     \* Set of Busy Nblocks overlapping the successors of x
Hot(A) == {x \in Nblocks : isHot[x] /\ Overlap(x, A) # {}}       \* Set of all hot nblocks given the set of acquired nblocks
HotInterference(A) == UNION {IntScope(x) : x \in Hot(A)}         \* Set of Nblocks in interference scopes of hot nblocks
Free(A) == {x \in Nblocks : Overlap(x, A) = {} /\ x \notin HotInterference(A)} \* Free Nblocks given the set of acquired nblocks
Acquired == {acquired[x] : x \in Procs} \ {none}                 \* Set of Nblocks which are currently acquired
OverlapAmt(x) == Cardinality(Overlap(x, Acquired))               \* The number of nblocks overlapping x.

doNextBlock(x) == /\ UNCHANGED<<Succs>>
                  /\ state[x] = nextblock
                  /\ acquired[x] = none => Free(Acquired) # {}
                  /\ IF Free(Acquired \ {acquired[x]}) # {} THEN
                       /\ \E y \in Free(Acquired \ {acquired[x]}) : acquired' = [acquired EXCEPT ![x] = y]
                       /\ state' = [state EXCEPT ![x] = search]
                       /\ isHot' = [y \in Nblocks |-> IF y \in Free(Acquired \ {acquired[x]}) THEN FALSE ELSE isHot[y]]
                     ELSE /\ acquired' = [acquired EXCEPT ![x] = none]
                          /\ isHot' = [y \in Nblocks |-> IF y \in Free(Acquired') THEN FALSE ELSE isHot[y]]
                          /\ UNCHANGED<<state>>

doSearch(x) == /\ UNCHANGED<<acquired, Succs>>
               /\ state[x] = search
               /\ state' = [state EXCEPT ![x] = nextblock]
               /\ \/ UNCHANGED<<isHot>>
                  \/ \E y \in IntBy(acquired[x]) : /\ ~isHot[y]
                                                   /\ IntScope(y) \intersect Hot(Acquired) = {}
                                                   /\ y \notin HotInterference(Acquired)
                                                   /\ isHot' = [isHot EXCEPT ![y] = TRUE]

Init == /\ state = [x \in Procs |-> nextblock]
        /\ acquired = [x \in Procs |-> none]
        /\ isHot = [x \in Nblocks |-> FALSE]
        \* This is just a basic graph where each nblock is connected to its neighbors forming a loop.
        /\ Succs = [x \in Nblocks |-> IF x = 0 THEN {nnblocks - 1, x + 1}
                                      ELSE IF x = nnblocks - 1 THEN {0, x - 1} ELSE {x - 1, x + 1}]
(*
        \* The interesting feature of this graph is that 2 is in the interference scope of 1,
        \* but 1 is not in the interference scope of 2.
        /\ Cardinality(Nblocks) = 8
        /\ Succs = [x \in Nblocks |-> IF x = 0 THEN { 6 }
                                      ELSE IF x = 1 THEN { 2, 4 }
                                      ELSE IF x = 2 THEN { 3, 5, 0 }
                                      ELSE IF x = 3 THEN { 4, 7 }
                                      ELSE IF x = 4 THEN { 1, 3 }
                                      ELSE IF x = 5 THEN { 2, 6, 7 }
                                      ELSE IF x = 6 THEN { 0 }
                                      ELSE (* x = 7 *) { 5 } ]
*)
        /\ TypeInv

Next == \E x \in Procs : (doNextBlock(x) \/ doSearch(x))
Fairness == \A x \in Procs : WF_Vars(doNextBlock(x) \/ doSearch(x))
Prog == Init /\ [][Next]_Vars /\ Fairness
------------------------------------------------------------
HotNblocks == \A x \in Nblocks : isHot[x] ~> ~isHot[x]

HotNblockSafety == \A x \in Nblocks : isHot[x] => OverlapAmt(x) > 0 /\ x \notin HotInterference(Acquired)

NoCollisions == \A x,y \in Procs : x # y => \/ acquired[x] = none
                                            \/ acquired[y] = none
                                            \/ /\ acquired[x] # acquired[y]
                                               /\ Succs[x] \intersect Succs[y] = {}
============================================================
