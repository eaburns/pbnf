-------------------- MODULE Safety1Proof --------------------
EXTENDS HotNblocks

(*
The this safety property is used later for the proof of the HotNblocks liveness property.
*)
PROOF Safety1 == Prog => [](HotNblockSafety)

LET I == x \in Nblocks /\ isHot[x] => OverlapAmt(x) > 0 /\ x \notin HotInterference(Acquired)
    N == Next
<1>1. Prog => [](I)
      <2>1. Init => I
            PROOF OBVIOUS \* Nothing is hot in Init, and therefore the implication holds trivially.
      <2>2. I /\ [\E i \in Procs : (doNextBlock(i) \/ doSearch(i))]_Vars => I'
            <3>1. I /\ Vars = Vars' => I'
                  PROOF OBVIOUS \* Studdering step.
            <3>2. I /\ (\E i \in Procs : doNextBlock(i)) => I'
                  ASSUME I /\ (\E i \in Procs : do NextBlock(i))
                  PROVE I'
                  <4>1. CASE isHot[x]
                        <5>1. CASE x \in Free(Acquired \ acquired[i])
                              <6>1. ~isHot'[x]
                                    PROOF OBVIOUS \* By the definition of isHot'
                              <6>2. QED BY <6>1 \* The LHS is false and the implication holds trivially.
                        <5>2. CASE x \notin Free(Acquired \ acquired[i])
                              <6>1. Busy(Acquired \ acquired[i]) \subset Busy(Acquired \ acquired[i])
                                    PROOF OBVIOUS
                                    \* There are less acquired blocks, and therefore there are less busy blocks.
                              <6>2. Overlap(x, Acquired \ acquired[i]) \subseteq Overlap(x, Acquired)
                                    <7>1. CASE acquired[i] \in Succs[x]
                                           PROOF OBVIOUS \* There is less overlap
                                    <7>2. CASE acquired[i] \notin Succs[x]
                                           PROOF OBVIOUS \* The overlap set doesn't change
                                    <7>3. QED BY <7>1 and <7>2
                              <6>3. HotInterference(Aqcuired \ acquired[i]) \subseteq HotInterference(Acquired)
                                    PROOF BY <6>1 and <6>2 \* and the definition of HotInteference(A).
                              <6>4. x \notin HotInterference(Acquired)
                                    PROOF BY <3>2 \* By the assumption of the invariant and the case assumption this is trivial.
                              <6>5. x \notin HotInterference(Acquired \ acquired[i])
                                    PROOF BY <6>4 and <6>3
                              <6>6. Cardinality(Overlap(x, Acquired)) > 0
                                    PROOF BY <5>2 and <6>5 \* ((<5>2 => <6>6 \/ ~<6>5) /\ <5>2 /\ <6>5) => <6>6
                              <6>7. Hot(Acquired')' \subseteq Hot(Acquired)
                                    PROOF OBVIOUS \* Since isHot' is the same as or more false than isHot.
                                    \* Is there a better way to explain this?!
                              <6>8. HotInterference(Acquired')' \subseteq HotInterference(Acquired)
                                    PROOF BY <6>7 \* and the definition of HotInterference(A).
                                    \* There are less hot blocks, so naturally there are less blocks which interfere with hot blocks.
                              <6>9. x \notin HotInterference(Acquired')'
                                    PROOF BY <6>7 and <6>8
                              <6>10. QED BY <6>6 and <6>9 \* The RHS is true and the implication holds trivially.
                        <5>3. QED BY <5>1 and <5>2
                  <4>2. CASE ~isHot[x]
                        <5>1. ~isHot'[x]
                              PROOF OBVIOUS \* isHot' is the same or more false than isHot.
                        <5>2. QED BY <5>1 \* The LHS is false and the implication holds trivially.
                  <4>3. QED BY <4>1 and <4>2
            <3>3. I /\ (\E i \in Procs : doSearch(i)) => I'
                  ASSUME I /\ (\E i \in Procs : doSearch(i))
                  PROVE I'
                  <4>1. CASE isHot[x]
                        <5>1. CASE isHot' = isHot
                              PROOF OBVIOUS
                        <5>2. CASE isHot' # isHot
                              ASSUME /\ y \in Succs[acquired[i]]
                                     /\ ~isHot[y]
                                     /\ IntScope(y) \union Hot(Acquired) = {}
                                     /\ y \notin HotInterference(Acquired)
                                     /\ isHot'[y] = [isHot EXCEPT ![y] = TRUE]
                              PROVE I'
                              <6>1. OverlapAmt(x)' > 0
                                    PROOF BY <3>3 \* UNCHANGED<<acquired, Succs>>
                              <6>2. x \notin HotInterference(Acquired')'
                                 <7>1. Overlap(x, Acquired) # {}
                                       PROOF BY <3>3 and <4>1 \* We assume I and isHot[x], so Overlap(x, Acquired) # {}
                                 <7>2. Acquired' = Acquired
                                       PROOF BY <3>3 \* UNCHANGED<<acquired>>
                                 <7>3. Overlap(x, Acquired') # {}
                                       PROOF BY <7>1 and <7>2
                                 <7>4. Overlap(x, Acquired')' = Overlap(x, Acquired')
                                       PROOF BY <3>3 \* UNCHANGED<<Succ>>
                                 <7>5. Overlap(x, Acquired')' = {}
                                       PROOF BY <7>3 and <7>4
                                 <7>6. isHot'[x]
                                       PROOF BY <4>1 and <5>2 \* definition of isHot'
                                 <7>7. QED BY <7>5 and <7>6 \* and the definition of Hot(Acquired') 
                              <6>3. QED BY <6>1 and <6>2
                        <5>3. QED BY <5>1 and <5>2
                  <4>2. CASE ~isHot[x]
                        <5>1. CASE isHot' = isHot
                              PROOF OBVIOUS
                        <5>2. CASE isHot' # isHot
                              ASSUME /\ y \in Succs[acquired[i]]
                                     /\ ~isHot[y]
                                     /\ IntScope(y) \union Hot(Acquired) = {}
                                     /\ y \notin HotInterference(Acquired)
                                     /\ isHot'[y] = [isHot EXCEPT ![y] = TRUE]
                              PROVE I'
                              <6>1. CASE x = y
                                    <7>1. acquired[i] \in Preds(x)
                                          PROOF BY <5>2 and <6>1 \* y = x and y \in Succs[acquired[i]]
                                    <7>2. acquired'[i] = acquired[i]
                                          PROOF BY <3>3 \* UNCHONGED<<acquired>>
                                    <7>3. acquired'[i] \in Overlap(x, Acquired')'
                                          PROOF BY <7>1, <7>2 \* and the definition of Overlap(x, A)
                                    <7>4. OverlapAmt(x) > 0
                                          PROOF BY <7>3 \* and the definition of OverlapAmt(x)
                                    <7>5. x \notin HotInterference(Acquired)
                                          PROOF BY <5>2 and <6>1
                                    <7>6. QED BY <7>4 and <7>5
                              <6>2. CASE x # y
                                    PROOF BY <4>2 and <6>2 \* Since x is not hot, and won't be set to hot the implication holds trivially.
                              <6>3. QED BY <6>1 and <6>2
                        <5>3 QED BY <5>1 and <5>2
                  <4>3. QED BY <4>1 and <4>2
            <3>4. QED BY <3>1, <3>2 and <3>3
      <2>3. QED BY <2>1, <2>2 \* INV1
<1>2. QED BY <1>1
============================================================
