-------------------- MODULE Safety1Proof --------------------
EXTENDS HotNblocks

(*
The this safety property is used later for the proof of the HotNblocks liveness property.
*)
PROOF Safety1 == Prog => [](HotNblocksOverlap)

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
               <6>1. Cardinality(Overlap(x, Acquired)) > 0
                  <7>1. x \notin HotInterference(Acquired \ acquired[i])
                     <8>1. HotInterference(Aqcuired \ acquired[i]) \subseteq HotInterference(Acquired)
                        <9>1. Busy(Acquired \ acquired[i]) \subset Busy(Acquired \ acquired[i])
                           PROOF OBVIOUS
                        \* There are less acquired blocks, and therefore there are less busy blocks.
                        <9>2. Overlap(x, Acquired \ acquired[i]) \subseteq Overlap(x, Acquired)
                           <10>1. CASE acquired[i] \in Succs[x]
                               PROOF OBVIOUS \* There is less overlap
                           <10>2. CASE acquired[i] \notin Succs[x]
                               PROOF OBVIOUS \* The overlap set doesn't change
                           <10>3. QED BY <10>1 and <10>2
                        <9>3. QED BY <9>1 and <9>2
                        \* If there is the same or less overlap, then the hot interference is the same or smaller.
                     <8>2. x \notin HotInterference(Acquired)
                        PROOF BY <3>2
                      \* By the assumption of the invariant and the case assumption this is trivial.
                     <8>3. QED BY <8>1 and <8>2
                  <7>2. QED BY <5>2 and <7>1 \* ((<5>2 => <6>1 \/ ~<7>1) /\ <5>2 /\ <6>1) => <6>1
               <6>2. x \notin HotInterference(Acquired')'
                  <7>1. Hot(Acquired')' \subseteq Hot(Acquired)
                     PROOF OBVIOUS \* Since isHot' is the same as or more false than isHot.
                     \* Is there a better way to explain this?!
                  <7>2. HotInterference(Acquired')' \subseteq HotInterference(Acquired)
                     PROOF BY <7>1 \* and the definition of HotInterference(A).
                     \* There are less hot blocks, so naturally there are less blocks which interfere with hot blocks.
                  <7>3. QED BY <7>2
               <6>3. QED BY <6>1 and <6>2 \* The RHS is true and the implication holds trivially.
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
<1>2. I => HotNblocksOverlap
   PROOF OBVIOUS \* Weakening and universal generalization.
<1>3. QED BY <1>1 and <1>2

------------------------------------------------------------

PROOF Prog => HotNblocks

LET S == Nat \ {0}
    G == ~isHot[x]
    H(c) == x \in Nblocks /\ isHot[x] /\ OverlapAmt(x) = c

<1>1. Prog => ((\E c \in S: H(c) ~> ~isHot[x])
   <2>1. Prog /\ c \in S => (H(c) ~> (G \/ \E d \in S : d < c /\ H(d)))
      ASSUME Prog /\ c \in S
      PROVE H(c) ~> (G \/ \E d \in S : d < c /\ H(d))
      <3>1. (\E i \in Procs : H(c) /\ i \in Blocking(x) ~> (G \/ \E d \in S : d < c /\ H(d))
         <4>1. H(c) /\ x \in Procs /\ i \in Blocking(x) ~> (G \/ \E d \in S : d < c /\ H(d))
            <5>1. H(c) /\ i \in Procs /\ i \in Blocking(x) /\ state[i] = nextblock ~> (G \/ \E d \in S : d < c /\ H(d)
               \* Use WF1 on doNextBlock(i)
               LET P == H(c) /\ i \in Procs /\ i \in Blocking(x) /\ state[i] = nextblock
                    N == \E j \in Procs : (doNextBlock(j) \/ doSearch(j))
                    A == doNextBlock(i) \/ doSearch(i)
                    Q == G \/ (H(d) /\ d < c)
               <6>1. P /\ [N]_Vars => (P' \/ Q')
                  PROOF OMITTED \* TODO Cases, j = i and j # i
               <6>2. P /\ <<N /\ A>>_Vars => Q'
                  PROOF OMITTED \* TODO
               <6>3. P => ENABLED<<A>>_Vars
                  PROOF OMITTED \* TODO
            <5>2. H(c) /\ i \in Procs /\ i \in Blocking(x) /\ state[i] = search ~> (G \/ \E d in \in S : d < c /\ H(d))
               <6>1. H(c) /\ i \in Procs /\ i \in Blocking(x) /\ state[i] = search
                     ~> (G \/ \E d \in S : d < c /\ H(d)) \/ H(c) /\ i \in Procs /\ i \in Blocking(x) /\ state[i] = nextblock
                  LET P == H(c) /\ i \in Procs /\ i \in Blocking(x) /\ state[i] = search
                      N == \E j \in Procs : (doNextBlock(j) \/ doSearch(j))
                      A == doNextBlock(i) \/ doSearch(i)
                      Q == (G \/ (H(d) /\ d < c)) \/ (H(c) /\ i \in Procs /\ i \in Blocking(x) /\ state[x] = nextblock)
                  <7>1. P /\ [N]_Vars => (P' \/ Q')
                     PROOF OMITTED
                  \* TODO two cases:
                  \* i = j then this leads to the LHS of <5>1 and we have it
                  \* i # j two cases here too:
                  \*      - Either j will release a block in Overlap(x, Acquired) and we have it (\E d \in S : d < c /\ H(d))
                  \*      - or j won't release a block in Overlap(x, Acquired), but that is fine, we have WF1 on i=j so we
                  \*        should be good (ENABLED<<doSearch(j) /\ j=i>> is good).
                  <7>2. P /\ <<N /\ A>>_Vars => Q'
                     PROOF OMITTED \* TODO
                  <7>3. P => ENABLED<<A>>_Vars
                     PROOF OMITTED \* TODO
               <6>2. QED BY <6>1 and <5>1 \* ((P ~> Q \/ R) /\ (R ~> Q)) => (P ~> Q)
            <5>3. QED BY <5>1 and <5>2 \* Disjunction of ~>
         <4>2. QED BY <4>1 \* UG then change \A to \E (which is allowed).
      <3>2. Prog => [](H(c) => \E i \in Procs : acquired[i] \in Overlap(x, Acquired))
         PROOF OMITTED \* TODO
      <3>3. QED BY <3>1 and <3>2 \* TODO: what is this called?
     \* I dunno what this is called... since H(c) implies that something is acquired in the overlap
     \* we can add/remove the overlap part.
   <2>2. QED \* Lattice rule with <2>1
<1>2. Prog => (x \in Nblocks /\ isHot[x] ~> ~isHot[x])
   PROOF BY <1>1 and Safety1 \* TODO: what is this called?
   \* Since <1>2 is a safety property (which we will demonstrate in <1>3), we can add/remove it somehow at our leasure.
   \* What we really want here is:
   \* ((A /\ B ~> C) /\ [](A => B)) => (A ~> B)
<1>3. QED BY <1>2 \* Universal Generalization
============================================================
