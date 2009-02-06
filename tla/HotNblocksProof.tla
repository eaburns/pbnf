-------------------- MODULE HotNblocksProof --------------------
(*
Anything labeled PROOF OMITTED  will need to be done before the proof is complete.
Also, we need to figure out what to label the steps that use:
    ((A /\ B ~> C) /\ [](A => B)) => (A ~> C)
*)
EXTENDS HotNblocks

\* The set of all processors which are blocking x.
Blocking(x) == { p \in Procs : acquired[p] \in Overlap(x, Acquired) }

PROOF Prog => HotNblocks

LET S == Nat \ {0}
    G == ~isHot[x]
    H(c) == x \in Nblocks /\ isHot[x] /\ OverlapAmt(x) = c

<1>1. Prog /\ c \in S => (H(c) ~> (G \/ \E d \in S : d < c /\ H(d)))
      ASSUME Prog /\ c \in S
      PROVE H(c) ~> (G \/ \E d \in S : d < c /\ H(d))
      <2>1. H(c) => \E i \in Procs : acquired[i] \in Overlap(x, Acquired)
            PROOF BY <1>1 \* the assumption that c is not zero and by the definition of OverlapAmt
      <2>2. ASSUME [][Next] /\ WF_Vars(A)
            PROVE (H(c) ~> (G \/ \E d \in S : d < c /\ H(d))
------------------------------------------------------------
            \* This is a WF1 proof
            LET P == H(c) /\ i \in Procs /\ acquired[i] \in Overlap(xpdf, Acquired) /\ state[i] = nextblock
                Q == G \/ (\E d \in S : d < c /\ H(d))
                A == i \in Procs /\ acquired[i] \in Overlap(x, Acquired) /\ doNextBlock(i)
                N == Next
            <3>1. P /\ [N]_Vars => (P' \/ Q')
                  ASSUME j \in Procs
                  PROVE P /\ [doSearch(j) \/ doNextBlock(j)]_Vars => (P' \/ Q')
                  <4>1. P /\ UNCHANGED<<Vars>> => (P' \/ Q')
                        PROOF OBVIOUS \* Studdering step... nothing changes and we have P'.
                  <4>2. P /\ doNextBlock(j) => (P' \/ Q')
                        ASSUME P /\ doNextBlock(j) /\ HotNblockSafety
                        \* Proof Safety1 shows that HotNblockSafety is an invariant and INV2 lets us add it here for free.
                        PROVE P' \/ Q'
                        <5>1. CASE state[j] = search
                              PROOF OBVIOUS \* The LHS is false since doNextBlock(j) is not enabled.
                        <5>2. CASE state[j] = nextblock /\ j # i
                              <6>1. CASE acquried[j] = none /\ Free(Acquired) = {}
                                    PROOF OBVIOUS \* The action is not enabled.
                              <6>2. CASE acquired[j] = none /\ Free(Acquired) # {}
                                    <7>1. Free(Acquired \ {acquired[j]}) = Free(Acquired)
                                          PROOF OBVIOUS \* by assumption none \notin Free(Acquired)
                                    <7>2. Free(Acquried \ {acquired[j]}) # {}
                                          PROOF BY <6>2 and <7>1
                                    <7>3. /\ UNCHANGED<<Succ>>
                                          /\ \E y \in Free(Acquired) : acquired' = [acquired EXCEPT ![j] = y]
                                          /\ state' = [state EXCEPT ![j] = search]
                                          /\ isHot' = [y \in Nblocks |-> IF y \in Free(Acquired) THEN FALSE ELSE isHot[y]]
                                          PROOF BY <4>2, <7>1 and <7>2
                                          \* The 'THEN' portion of the IF in doNextBlock(j) with a simple substitution from <7>1
                                    <7>4. Overlap(x, Acquired) # {}
                                          PROOF BY <4>2 \* OverlapAmt(x) = c /\ c \in Nat \ {0}, trivial
                                    <7>5. x \notin Free(Acquired)
                                          PROOF BY <7>4 \* and definition of Free(Acquired)
                                    <7>6. isHot'[x] = isHot[x]
                                          PROOF BY <7>3 and <7>5
                                    <7>7. acquired'[j] \notin Succs[x]
                                          <8>1. acquired'[j] \in Free(Acquired)
                                                PROOF BY <7>3
                                          <8>2. acquired'[j] \notin HotInterference(Acquired)
                                                PROOF BY <8>1 \* and the definition of Free(Acquired)
                                          <8>3. Succs[x] \subseteq HotInterference(Acquired)
                                                PROOF OBVIOUS \* by the definition of HotInterference and IntScope
                                          <8>4. QED BY <8>3
                                    <7>8. Overlap(x, Acquired')' = Overlap(x, Acquired)
                                          PROOF BY <7>3 and <7>7
                                          \* Only acquired[j] changes in acquired', and acquired'[j] \notin Succs[x] and therefore
                                          \* it is not overlapping.
                                    <7>9. acquired'[i] = acquired[i] /\ state'[i] = state[i]
                                          PROOF BY <5>2 and <7>3 \* i # j and only acquired[j] changes and only state[j] changes
                                    <7>10. QED BY <7>6, <7>8 and <7>9 \* We have P'
                              <6>3. CASE /\ acquired[j] # none
                                         /\ Free(Acquired \ {acquired[j]}) # {}
                                         /\ acquired[j] \in Overlap(x, Acquired)
                                    <7>1. /\ UNCHANGED<<Succ>>
                                          /\ \E y \in Free(Acquired \ {acquired[j]}) : acquired' = [acquired EXCEPT ![j] = y]
                                          /\ state' = [state EXCEPT ![j] = search]
                                          /\ isHot' = [y \in Nblocks |-> IF y \in Free(Acquired \ {acquired[j]})
                                                                         THEN FALSE ELSE isHot[y]]
                                          PROOF BY <4>2 and <6>3
                                          \* The 'THEN' portion of the IF in doNextBlock(j)
                                    <7>2. acquired'[j] \notin Succs[x]
                                          <8>1. acquired'[j] \in Free(Acquired \ {acquried[j]})
                                                PROOF BY <7>3
                                          <8>2. acquired'[j] \notin HotInterference(Acquired \ {acquired[j]})
                                                PROOF BY <8>1 \* and the definition of Free(Acquired \ {acquired[j]})
                                          <8>3. Succs[x] \subseteq HotInterference(Acquired \ {acquired[j]})
                                                PROOF OBVIOUS \* by the definition of HotInterference and IntScope
                                          <8>4. QED BY <8>3
                                    <7>3. Acquired' = Acquired \ {acquired[j]} \union {acquired'[j]}
                                          PROOF BY <7>1 \* acquired' and the definition of Acquired
                                    <7>4. Overlap(x, Acquired')' \subset Overlap(x, Acquired)
                                          PROOF BY <6>3, <7>2 and <7>3
                                          \* Now acquired[j] is not overlapping and acquired'[j] doesn't either
                                    <7>5. OverlapAmt(x)' < OverlapAmt(x)
                                          PROOF BY <7>4
                                    <7>6. Overlap(x, Acquired) # {acquired[j]}
                                          PROOF BY <4>2, <5>2 and <6>3 \* Since i # j and acquired[i] is also in Overlap(x, Acquired)
                                    <7>7. acquired[i] \in Overlap(x, Acquired \ {acquired[j]})
                                          PROOF BY <4>2 and <5>2
                                    <7>8. x \notin Free(Acquired \ {acquired[j]})
                                          PROOF BY <7>7 \* and the definition of Free.
                                    <7>9. isHot'[x] = isHot[x]
                                          PROOF BY <7>1 and <7>8 \* from isHot' only falsifying things in Free(Acquired \ {acquired[j]})
                                    <7>10. QED BY <7>5 and <7>9 \* We have Q'
                              <6>4. CASE /\ acquired[j] # none
                                         /\ Free(Acquired \ {acquired[j]}) # {}
                                         /\ acquired[j] \notin Overlap(x, Acquired)
                                    <7>1. /\ UNCHANGED<<Succs>>
                                          /\ \E y \in Free(Acquired \ {acquired[j]}) : acquired' = [acquired EXCEPT ![j] = y]
                                          /\ state' = [state EXCEPT ![j] = search]
                                          /\ isHot' = [y \in Nblocks |-> IF y \in Free(Acquired \ {acquired[j]})
                                                                         THEN FALSE ELSE isHot[y]]
                                          PROOF BY <4>2 and <6>4
                                          \* The 'THEN' portion of the IF in doNextBlock(j)
                                    <7>2. acquired'[j] \notin Succs[x]
                                          <8>1. acquired'[j] \in Free(Acquired \ {acquried[j]})
                                                PROOF BY <7>3
                                          <8>2. acquired'[j] \notin HotInterference(Acquired \ {acquired[j]})
                                                PROOF BY <8>1 \* and the definition of Free(Acquired \ {acquired[j]})
                                          <8>3. Succs[x] \subseteq HotInterference(Acquired \ {acquired[j]})
                                                PROOF OBVIOUS \* by the definition of HotInterference and IntScope
                                          <8>4. QED BY <8>3
                                          \* acquired[j] \notin Overlap(x, Acquired) so the set of blocks overlapping x are the same.
                                    <7>3. Acquried' = Acquired \ {acquired[j]} \union {acquired'[j]}
                                          PROOF BY <7>1 \* acquired' and the definition of Acquired
                                    <7>4. Overlap(x, Acquired')' = Overlap(x, Acquired)
                                          PROOF BY <7>1, <7>2 and <7>3
                                    <7>5. acquired[i] \in Overlap(x, Acquired')'
                                          PROOF BY <4>2 and <7>4 \* This remains true since the overlap sets are the same.
                                    <7>6. acquired'[i] = acquired[i]
                                          PROOF BY <5>2 and <7>1 \* i # j and only acquired[j] changes.
                                    <7>7. acquired'[i] \in Overlap(x, Acquired')'
                                          PROOF BY <7>5 and <7>7
                                    <7>8. state'[i] = state[i]
                                          PROOF BY <5>2 and <7>1 \* i # j and only state[j] changes.
                                    <7>9. acquired[i] \in Overlap(x, Acquired \ {acquired[j]})
                                          PROOF BY <4>2 and <5>2 \* i # j and acquired[i] \in Overlap(x, Acquired)
                                    <7>10. x \notin Free(Acquired \ {acquired[j]})
                                          PROOF BY <7>9 \* and the definition of Free(Acquired \ {acquired[j]})
                                    <7>11. isHot'[x] = isHot[x]
                                          PROOF BY <7>1 and <7>10 \* the definition of isHot'
                                    <7>12. QED BY <7>4, <7>7, <7>8 and <7>11 \* We have P'
                              <6>5. CASE /\ acquired[j] # none
                                         /\ Free(Acquired \ {acquired[j]}) = {}
                                         /\ acquired[j] \in Overlap(x, Acquired)
                                    <7>1. /\ acquired' = [acquired EXCEPT ![j] = none]
                                          /\ isHot' = [y \in Nblocks |-> IF y \in Free(Acquired') THEN FALSE THEN isHot[y]]
                                          /\ UNCHANGED<<Succs, state>>
                                          PROOF BY <4>2 and <6>5
                                          \* The ELSE clause of the IF expression in doNextBlock(j)
                                    <7>2. acquired'[j] \notin Overlap(x, Acquired')'
                                          PROOF BY <7>1 and TypeInv
                                          \* acquired'[j] = none, assumption none \notin Nblocks
                                          \* and Succs[x] \in [Nblocks -> SUBSET Nblocks]
                                    <7>3. OverlapAmt(x)' < Overlap(x)
                                          PROOF BY <6>5, <7>1 and <7>2 \* Only acquired[j] changes, and it is not in Overlap(x, Acquired')'
                                    <7>4. Acquired' = Acquired \ {acquired[j]}
                                          PROOF BY <7>1
                                    <7>5. acquired[i] \in Overlap(x, Acquired')
                                          PROOF BY <4>2, <5>2 and <7>4 \* acquired[i] is still overlapping x since it is still in Acquired'
                                    <7>6. x \notin Free(Acquired')
                                          PROOF BY <7>5 \* and the definition of Free(Acquired')
                                    <7>7. isHot'[x] = isHot[x]
                                          PROOF BY <7>1 and <7>6 \* isHot'[x] is not set to false.
                                    <7>8. QED BY <7>3 and <7>7
                              <6>6. CASE /\ acquired[j] # none
                                         /\ Free(Acquired \ {acquired[j]}) = {}
                                         /\ acquired[j] \notin Overlap(x, Acquired)
                                    <7>1. /\ acquired' = [acquired EXCEPT ![j] = none]
                                          /\ isHot' = [y \in Nblocks |-> IF y \in Free(Acquired') THEN FALSE THEN isHot[y]]
                                          /\ UNCHANGED<<Succs, state>>
                                          PROOF BY <4>2 and <6>6
                                          \* The ELSE clause of the IF expression in doNextBlock(j)
                                    <7>2. Acquired' = Acquired \ {acquired[j]}
                                          PROOF BY <7>1 \* and the definition of Acquired
                                    <7>3. acquired[i] \in Overlap(x, Acquired')
                                          PROOF BY <4>2, <5>2 and <7>4 \* acquired[i] is still overlapping x since it is still in Acquired'
                                    <7>4. x \notin Free(Acquired')
                                          PROOF BY <7>3 \* and the definition of Free(Acquired')
                                    <7>5. isHot'[x] = isHot[x]
                                          PROOF BY <7>4 \* and the definition of isHot'
                                    <7>6. Acquired' = Acquired \ {acquired[j]}
                                          PROOF BY <7>1 \* and the definition of Acquired'
                                    <7>7. Overlap(x, Acquired')' = Overlap(x, Acquired)
                                          PROOF BY <6>6 and <7>6 \* acquired[j] is not in the overlap set and everything else stays the same
                                    <7>8. OverlapAmt(x)' = OverlapAmt(x)
                                          PROOF BY <7>7
                                    <7>9. state'[i] = state[i]
                                          PROOF BY <5>2 and <7>1 \* i # j and only state[j] changes
                                    <7>10. QED BY <7>5, <7>7, <7>8 and <7>9 \* We have P'
                              <6>7. QED BY <6>1, <6>2, <6>3, <6>4, <6>5 and <6>6
                        <5>3. CASE state[j] = nextblock /\ j = i
                              <6>1. acquired[i] # none
                                    <7>1. acquired[i] \in Overlap(x, Acquired)
                                          PROOF BY <4>2 \* This is in the assumption of P
                                    <7>2. none \notin Overlap(x, Acquired)
                                          PROOF OMITTED \* none \notin Nblocks and Ovelap(x, Acquired) can be shown to be \in SUBSET Nblocks.
                                    <7>3. QED BY <7>1 and <7>2
                              <6>2. Q'
                                    <7>1. Overlap(x, Acquired) = {acquired[i]} /\ Free(Acquired \ {acquired[i]}) # {}
                                          <8>1. /\ \E y \in Free(Acquired \ {acquired[i]}) : acquired' = [acquired EXCEPT ![i] = y]
                                                /\ isHot' = [y \in Nblocks |-> IF y \in Free(Acquired \ {acquired[i]})
                                                                               THEN FALSE ELSE isHot[y]]
                                                PROOF BY <4>2 and <7>1 \* This is the THEN clause of the IF in doNextBlock(i)
                                          <8>2. Overlap(x, Acquired \ {acquired[i]}) = {}
                                                PROOF BY <7>1 \* and the definition of the overlap set of x.
                                          <8>3. x \notin HotInterference(Acquired \ {acquired[i]})
                                                PROOF BY <4>2 \* and HotNblockSafety
                                          <8>4. x \in Free(Acquired \ {acquired[i]})
                                                PROOF BY <8>2 and <8>3 \* and the definition of the Free set.
                                          <8>5. ~isHot'[x]
                                                PROOF BY <7>1 and <8>4
                                          <8>6. QED BY <8>5
                                    <7>2. Overlap(x, Acquired) = {acquired[i]} /\ Free(Acquired \ {acquired[i]}) = {}
                                          <8>1. /\ acquired' = [acquired EXCEPT ![i] = none]
                                                /\ isHot' = [y \in Nblocks |-> IF y \in Free(Acquired')
                                                                               THEN FALSE ELSE isHot[x]]
                                                PROOF BY <4>2 and <7>2 \* The ELSE clause of the IF in doNextBlock(i)
                                          <8>2. Acquired' = Acquired \ {acquired[i]}
                                                PROOF BY <8>1 \* and the definition of the Acquired set.
                                          <8>3. Overlap(x, Acquired') = {}
                                                PROOF BY <7>2 and <8>2 \* The last acquired block overlapping x is released.
                                          <8>4. x \notin HotInterference(Acquired')
                                                PROOF BY <4>2 \* and HotNblockSafety
                                          <8>5. x \in Free(Acquired')
                                                PROOF BY <8>3 and <8>4
                                          <8>6. ~isHot'[x]                                             
                                                PROOF BY <8>1 and <8>5
                                          <8>7. QED BY <8>6
                                    <7>3. CASE Overlap(x, Acquired) # {acquired[i]} /\ Free(Acquired \ {acquired[i]}) # {}
                                          <8>1. /\ \E y \in Free(Acquired \ {acquired[i]}) : acquired' = [acquired EXCEPT ![i] = y]
                                                /\ state' = [state EXCEPT ![i] = search]
                                                /\ isHot' = [y \in Nblocks |-> IF y \in Free(Acquired \ {acquired[i]})
                                                                               THEN FALSE ELSE isHot[y]]
                                                PROOF BY <4>2 and <7>3 \* This is the THEN clause of the IF in doNextBlock(i)
                                          <8>2. Overlap(x, Acquired \ {acquired[i]}) \subset Overlap(x, Acquired)
                                                PROOF OBVIOUS \* an element in the ovelap set of x is now not there
                                          <8>3. Acquired' = Acquired \ {acquired[i]} \union {acquired'[i]}
                                                PROOF BY <8>1 \* i acquires a new block.
                                          <8>4. acquired'[i] \notin HotInterference(Acquired)
                                                PROOF BY <8>1 \* and the definition of the Free set.
                                          <8>5. Overlap(x, Acquired) \subseteq HotInterference(Acquired)
                                                PROOF OBVIOUS \* by the definition of these two sets.
                                          <8>6. acquired'[i] \notin Overlap(x, Acquired')'
                                                PROOF BY <8>1, <8>2, <8>3 and <8>4
                                          <8>7. Overlap(x, Acquired')' \subset Overlap(x, Acquired)
                                                PROOF BY <7>3 and <8>6 \* acquired[i] is no longer in the overlap set of x.
                                          <8>8. OverlapAmt(x)' < OverlapAmt(x)
                                                PROOF BY <8>7
                                          <8>9. Overlap(x, Acquired \ {acquired[i]}) # {}
                                                PROOF BY <7>3 and <8>1 \* only one block was released and it was not the last one.
                                          <8>10. x \notin Free(Acquired \ {acquired[i]})
                                                PROOF BY <8>9 \* and the definition of the Free set.
                                          <8>11. isHot'[x]
                                                PROOF BY <8>10
                                          <8>11. QED BY <8>8 and <8>11
                                    <7>4. CASE Overlap(x, Acquired) # {acquired[i]} /\ Free(Acquired \ {acquired[i]}) = {}
                                          <8>1. /\ acquired' = [acquired EXCEPT ![i] = none]
                                                /\ isHot' = [y \in Nblocks |-> IF y \in Free(Acquired')
                                                                               THEN FALSE ELSE isHot[x]]
                                                /\ UNCHANGED<<state>>
                                                PROOF BY <4>2 and <7>4 \* This is the ELSE clause of the IF in doNextBlock(i)
                                          <8>2. Acquired' = Acquired \ {acquired[i]}
                                                PROOF BY <8>2 \* and the definition of the Acquired set.
                                          <8>3. Overlap(x, Acquired') \subset Overlap(x, Acquired)
                                                PROOF BY <8>2 \* and the definition of the Overlap set of x.
                                          <8>4. OverlapAmt(x)' < OverlapAmt(x)
                                                PROOF BY <8>3
                                          <8>5. Overlap(x, Acquired') # {}
                                                PROOF BY <7>4 and <8>2 \* acquired[i] was not the last element of the Overlap set.
                                          <8>6. x \notin Free(Acquired')
                                                PROOF BY <8>5 \* and the definition of the Free set.
                                          <8>7. isHot'[x]
                                                PROOF BY <8>1 and <8>6
                                          <8>8. QED BY <8>4 and <8>7
                                    <7>5. QED BY <7>1, <7>2, <7>3 and <7>4
                              <6>3. QED BY <6>2
                        <5>4. QED BY <5>1, <5>2 and <5>3
                  <4>3. P /\ doSearch(j) => (P' \/ Q')
                        <5>1. CASE state[j] = search
                              <6>1. j # i
                                    PROOF BY <4>3 \* state[i] = nextblock
                              <6>2. UNCHANGED<<acquired, Succs>>
                                    PROOF BY <4>3 \* this is always in doSearch(j)
                              <6>3. QED BY <6>1 and <6>2 \* only state[j] changes and j # i, so we have P'
                        <5>2. CASE state[j] = nextblock
                              PROOF OBVIOUS \* The LHS is false since doSearch(j) is not enabled.
                        <5>3. QED BY <5>1 and <5>2
                  <4>4. QED BY <4>1, <4>2 and <4>3
            <3>2. P /\ <<N /\ A>>_Vars => Q'
                  <4>1. ASSUME P /\ <<N /\ A /\ HotNblockSafety>>_Vars /\ state[i] = nextblock
                        PROVE Q'
                        <5>1. CASE Free(Acquired \ {acquired[i]}) # {}
                              <6>1. CASE Overlap(x, Acquired) = {acquired[i]}
                                    <7>1. /\ \E y \in Free(Acquired \ {acquired[i]}): acquired' = [acquired EXCEPT ![i] = y]
                                          /\ state' = [state EXCEPT ![i] = search]
                                          /\ isHot' = [y \in Nblocks |-> IF y \in Free(Acquired \ {acquired[i]})
                                                                         THEN FALSE ELSE isHot[y]]
                                          PROOF BY<4>1 and <5>1 \* This is the THEN clause of the IF in doNextBlock(i)
                                    <7>2. x \notin HotInterference(Aqcuired)
                                          PROOF BY <4>1 \* This is just a reiteration of HotNblockSafety assumed in <4>1
                                    <7>3. HotInterference(Acquired \ {acquired[i]}) \subseteq HotInterference(Acquired)
                                          PROOF OBVIOUS \* There are either the same hot blocks or less when we release acquired[i].
                                    <7>4. x \notin HotInterference(Acquired \ {acquired[i]})
                                          PROOF BY <7>3 and <7>4
                                    <7>5. x \in Free(Acquired \ {acquired[i]})
                                          PROOF BY <6>1 and <7>1 \* The last overlapping block is not acquired.
                                    <7>6. ~isHot'[x]
                                          PROOF BY <7>4 and <7>5 \* and the definition of the Free set.
                                    <7>7. QED BY <7>6
                              <6>2. CASE Overlap(x, Acquired) # {acquired[i]}
                                    <7>1. /\ \E y \in Free(Acquired \ {acquired[i]}): acquired' = [acquired EXCEPT ![i] = y]
                                          /\ state' = [state EXCEPT ![i] = search]
                                          /\ isHot' = [y \in Nblocks |-> IF y \in Free(Acquired \ {acquired[i]})
                                                                         THEN FALSE ELSE isHot[y]]
                                          /\ UNCHANGED<<Succs>>
                                          PROOF BY<4>1 and <5>1 \* This is the THEN clause of the IF in doNextBlock(i)
                                    <7>2. Overlap(x, Acquired \ {acquired[i]}) # {}
                                          PROOF BY <4>1 and <6>2 \* There are other things overlapping x besides acquired[i].
                                    <7>3. x \notin Free(Acquired \ {acquired[i]})
                                          PROOF BY <7>2 \* and the definition of the Free set.
                                    <7>4. isHot'[x] = isHot[x]
                                          PROOF BY <7>1 and <7>3 \* x doesn't become free so it remains hot.
                                    <7>5. Acquired' = Acquired \ {acquired[i]} \union {acquired'[i]}
                                          PROOF BY <7>1 \* and the definition of the Acquired set.
                                    <7>6. acquired'[i] \notin HotInterference(Acquired \ {acquired[i]})
                                          PROOF BY <7>1 \* and the definition of the Free set.
                                    <7>7. Overlap(x, Acquired \ {acquired[i]}) \subseteq HotInterference(Aqcuired \ {acquired[i]})
                                          PROOF OBVIOUS \* by the deinition of the Overlap and HotInterference sets.
                                    <7>8. acquired'[i] \notin Overlap(x, Acquired \ {acquired[i]})
                                          PROOF BY <7>6 and <7>7
                                    <7>9. acquired'[i] \notin Overlap(x, Acquired')'
                                          PROOF BY <7>1, <7>5 and <7>8 \* Succs is unchanged, acquired'[i] is not interfering with the overlap set.
                                    <7>10. Overlap(x, Acquired')' \subset Overlap(x, Acquired)
                                          PROOF BY <4>3 and <7>9 \* acquired[i] is no longer in the Overlap set of x.
                                    <7>11. QED BY <7>4 and <7>10 \* We have Q'
                              <6>3. QED BY <6>1 and <6>2
                        <5>2. CASE Free(Acquired \ {acquired[i]}) = {}
                              <6>1. CASE Overlap(x, Acquired) = {acquired[i]}
                                    <7>1. isHot' = [y \in Nblocks : IF y \in Free(Acquired \ {acquired[i]} THEN FALSE ELSE isHot[y]]
                                          PROOF BY <4>1 and <5>2 \* This is the ELSE clause of the IF in doNextBlock(i)
                                    <7>2. x \notin HotInterference(Acquired)
                                          PROOF BY <4>1 \* This is just a reiteration of HotNblockSafety assumed in <4>1.
                                    <7>3. HotInterference(Aqcuired \ {acquired[i]}) \subseteq HotInterference(Acquired)
                                          PROOF OBVIOUS \* There are either the same hot blocks or less when we release acquired[i].
                                    <7>4. x \notin HotInterference(Acquired \ {acquired[i]})
                                          PROOF BY <7>2 and <7>3
                                    <7>5. Overlap(x, Acquired \ {acquired[i]}) = {}
                                          PROOF BY <6>1 \* acquired[i] is the only thing in the overlap set, if we remove it then the set is empty.
                                    <7>6. x \in Free(Acquired \{acquired[i]})
                                          PROOF BY <7>4 and <7>5 \* and the definition of the Free set.
                                    <7>7. ~isHot'[x]
                                          PROOF BY <7>1 and <7>6
                                    <7>8. QED BY <7>7
                              <6>2. CASE Overlap(x, Acquired) # {acquired[i]}
                                    <7>1. /\ acquired' = [acquired EXCEPT ![i] = none
                                          /\ isHot' = [y \in Nblocks : IF y \in Free(Acquired \ {acquired[i]} THEN FALSE ELSE isHot[y]]
                                          /\ UNCHANGED<<state>>
                                          PROOF BY <4>1 and <5>2 \* This is the ELSE clause of the IF in doNextBlock(i)
                                    <7>2. Overlap(x, Acquired \ {acquired[i]}) # {}
                                          PROOF BY <4>1 and <6>2 \* There are other things overlapping x besides acquired[i].
                                    <7>3. x \notin Free(Acquired \ {acquired[i]})
                                          PROOF BY <7>2 \* and the definition of the Free set.
                                    <7>4. isHot'[x] = isHot[x]
                                          PROOF BY <7>1 and <7>3
                                    <7>5. Acquried' = Acquired \ {acquired[i]}
                                          PROOF BY <7>1
                                    <7>6. Overlap(x, Acquired')' \subset Overlap(x, Acquired)
                                          PROOF BY <4>1 and <7>5 \* acquired[i] leaves the Overlap set of x.
                                    <7>7. QED BY <7>4 and <7>6 \* We have Q'
                              <6>3. QED BY <6>1 and <6>2
                        <5>3. QED BY <5>1 and <5>2
                  <4>2. ASSUME P /\ <<N /\ A>>_Vars /\ state[i] = search
                        PROVE Q'
                        PROOF OBVIOUS \* The LHS is false and the implication holds trivially.
                  <4>3. QED BY <4>1 and <4>2 \* these are the two cases for state[i]
            <3>3. P => ENABLED<<A>>_Vars
                  PROOF OBVIOUS \* P contains the guard for A
            <3>4. H(c) /\ i \in Procs /\ acquired[i] \in Overlap(x, Acquired) /\ state[i] = nextblock ~> G \/ (\E d \in S : d < c /\ H(d))
                  PROOF BY <3>1, <3>2 and <3>3 \* WF1

------------------------------------------------------------
            \* This is a WF1 proof
            LET P == H(c) /\ acquired[i] \in Overlap(x, Acquired) /\ state[i] = search
                Q == \/ (G \/ (\E d \in S : d < c /\ H(d)))
                     \/ H(c) /\ i \in Procs /\ acquired[i] \in Overlap(x, Acquired) /\ state[i] = nextblock))
                A == i \in Procs /\ acquired[i] \in Overlap(x, Acquired) : doNextBlock(i)
                N == Next
            <3>5. P /\ [N]_Vars => (P' \/ Q')
                  ASSUME j \in Procs
                  PROVE P /\ [doSearch(j) \/ doNextBlock(j)]_Vars => (P' \/ Q')
                  <4>1. P /\ UNCHANGED<<Vars>> => (P' \/ Q')
                        PROOF OBVIOUS \* Studdering step
(*
----------------------------------------------------------------------------------------------------
*)
                  <4>2. P /\ doNextBlock(j) => (P' \/ Q')
                        ASSUME P /\ doNextBlock(j)
                        PROVE P' \/ Q'
                        PROOF OMITTED
(*
----------------------------------------------------------------------------------------------------
*)
                  <4>3. P /\ doSearch(j) => (P' \/ Q')
                        PROOF OMITTED
                  <4>4. QED BY <4>1, <4>2 and <4>3
            <3>6. P /\ <<N /\ A>>_Vars => Q'
                  PROOF OMITTED
            <3>7. P => ENABLED<<A>>_Vars
                  PROOF OMITTED
            
            <3>8. H(c) /\ i \in Procs /\ acquired[i] \in Overlap(x, Acquired) /\ state[i] = search
                  ~> Q \/ (H(c) /\ i \in Procs /\ acquired[i] \in Overlap(x, Acquired) /\ state[i] = nextblock)
                  PROOF BY <3>5, <3>6 and <3>7 \* WF1
                  
            <3>9. H(c) /\ i \in Procs /\ acquired[i] \in Overlap(x, Acquired) /\ state[i] = search ~> G \/ (\E d \in S : d < c /\ H(d))
                  PROOF BY <3>4 and <3>8 \* ((A ~> B \/ C) /\ (C ~> B)) => (A ~> B)
------------------------------------------------------------
            <3>10. H(c) /\ i \in Procs /\ acquired[i] \in Overlap(x, Acquired) ~> Q
                  PROOF BY <3>4 and <3>9 \* Disjunction of ~>
            <3>11. H(c) => i \in Procs /\ acquired[i] \in Overlap(x, Acquired)
                  PROOF OBVIOUS
            <3>12. QED BY <3>11 and <3>10 \* This is that ((A /\ B => C) /\ A /\ (A => B)) => (A => C) thing again.
------------------------------------------------------------
            
      <2>3. [][Next] /\ WF_Vars(i \in Procs /\ acquired[i] \in Overlap(x, Acquired) /\ doNextBlock(i))
            <3>1. [][Next]
                  PROOF OBVIOUS \* This is part of Prog, which we assume in <1>1
            <3>2. WF_Vars(i \in Procs /\ acquired[i] \in Overlap(x, Acquired) /\ doNextBlock(i))
                  PROOF OMITTED
                  \* There are two pieces here... first, everything in Overlap(x, Acquired) is in Procs
                  \* and second, Overlap(x, Acquired) isn't empty... which it may be... but H(c) implies that it is not
                  \* just look at <2>1
<1>2. Prog => (\E c \in S : H(c)) ~> G
      PROOF BY <1>1 \* and the Lattice rule and we get rid of (i \in Procs), the assumption nprocs > 0 makes this trivial.
            
<1>3. Prog => (x \in Nblocks /\ isHot[x] ~> ~isHot[x])
      PROOF BY <1>2 and Safety1 \* TODO: what is this called?
      \* Since <1>2 is a safety property (which we will demonstrate in <1>3), we can add/remove it somehow at our leasure.
      \* What we really want here is:
      \* ((A /\ B ~> C) /\ [](A => B)) => (A ~> B)

<1>4. QED BY <1>3 \* Universal Generalization
============================================================
