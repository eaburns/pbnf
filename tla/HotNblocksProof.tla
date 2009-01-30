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
      <2>1. H(c) => \E i \in Procs : i \in Overlap(x, Acquired)
            PROOF BY <1>1 \* the assumption that c is not zero and by the definition of OverlapAmt
      <2>2. ASSUME [][Next] /\ WF_Vars(A)
            PROVE (H(c) ~> (G \/ \E d \in S : d < c /\ H(d))
------------------------------------------------------------
            \* This is a WF1 proof
            LET P == H(c) /\ i \in Overlap(x, Acquired) /\ state[i] = nextblock
                Q == G \/ (\E d \in S : d < c /\ H(d))
                A == \E i \in Overlap(x, Acquired) : doNextBlock(i)
                N == Next
            <3>1. P /\ [N]_Vars => (P' \/ Q')
                  ASSUME j \in Procs
                  PROVE P /\ [doSearch(j) \/ doNextBlock(j)]_Vars => (P' \/ Q')
                  <4>1. P /\ Vars' = Vars => (P' \/ Q')
                        PROOF OBVIOUS \* Studdering step... nothing changes and we have P'.
                  <4>2. P /\ doNextBlock(j) => (P' \/ Q')
                        <5>1. CASE state[j] = search
                              PROOF OBVIOUS \* The LHS is false since doNextBlock(j) is not enabled.
                        <5>2. CASE state[j] = nextblock
                              PROOF OMITTED
                        <5>3. QED BY <5>1 and <5>2
                  <4>3. P /\ doSearch(j) => (P' \/ Q')
                        <5>1. CASE state[j] = search
                              PROOF OMITTED
                        <5>2. CASE state[j] = nextblock
                              PROOF OBVIOUS \* The LHS is false since doSearch(j) is not enabled.
                        <5>3. QED BY <5>1 and <5>2
                  <4>4. QED BY <4>1, <4>2 and <4>3
            <3>2. P /\ <<N /\ A>>_Vars => Q'
                  PROOF OMITTED
            <3>3. P => ENABLED<<A>>_Vars
                  PROOF OBVIOUS \* P contains the guard for A
            <3>4. H(c) /\ i \in Overlap(x, Acquired) /\ state[i] = nextblock ~> G \/ (\E d \in S : d < c /\ H(d))
                  PROOF BY <3>1, <3>2 and <3>3 \* WF1

------------------------------------------------------------
            \* This is a WF1 proof
            LET P == H(c) /\ i \in Overlap(x, Acquired) /\ state[i] = search
                Q == \/ (G \/ (\E d \in S : d < c /\ H(d)))
                     \/ H(c) /\ i \in Overlap(x, Acquired) /\ state[i] = nextblock))
                A == \E i \in Overlap(x, Acquired) : doNextBlock(i)
                N == Next
            <3>5. P /\ [N]_Vars => (P' \/ Q')
                  PROOF OMITTED
            <3>6. P /\ <<N /\ A>>_Vars => Q'
                  PROOF OMITTED
            <3>7. P => ENABLED<<A>>_Vars
                  PROOF OMITTED
            
            <3>8. H(c) /\ i \in Overlap(x, Acquired) /\ state[i] = search
                  ~> Q \/ (H(c) /\ i \in Overlap(x, Acquired) /\ state[i] = nextblock)
                  PROOF BY <3>5, <3>6 and <3>7 \* WF1
                  
            <3>9. H(c) /\ i \in Overlap(x, Acquired) /\ state[i] = search ~> G \/ (\E d \in S : d < c /\ H(d))
                  PROOF BY <3>4 and <3>8 \* ((A ~> B \/ C) /\ (C ~> B)) => (A ~> B)
------------------------------------------------------------
            <3>10. H(c) /\ i \in Overlap(x, Acquired) ~> Q
                  PROOF BY <3>4 and <3>9 \* Disjunction of ~>
            <3>11. H(c) => i \in Overlap(x, Acquired)
                  PROOF OBVIOUS
            <3>12. QED BY <3>11 and <3>10 \* This is that ((A /\ B => C) /\ A /\ (A => B)) => (A => C) thing again.
------------------------------------------------------------
            
      <2>3. [][Next] /\ WF_Vars(i \in Overlap(x, Acquired) /\ doNextBlock(i))
            <3>1. [][Next]
                  PROOF OBVIOUS \* This is part of Prog, which we assume in <1>1
            <3>2. WF_Vars(i \in Overlap(x, Acquired) /\ doNextBlock(i))
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
