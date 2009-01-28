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
