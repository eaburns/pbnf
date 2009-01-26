-------------------- MODULE HotNblocksProof --------------------
EXTENDS HotNblocks

PROOF Prog => HotNblocks

LET OverlapAmt(x) == Cardinality(Overlap(x, Acquired))
    S == Nat \ {0}
    G == ~isHot[x]
    H(c) == x \in Nblocks /\ isHot[x] /\ OverlapAmt(x) = c
IN

<1>1. Prog => ((\E c \in S: H(c) ~> ~isHot[x])

  <2>1. Prog /\ c \in S => (H(c) ~> (G \/ \E d \in S : d < c /\ H(d)))
       ASSUME Prog /\ c \in S
       PROVE H(c) ~> (G \/ \E d \in S : d < c /\ H(d))

   \* The set of processes which have acquired blocks overlapping x's duplicate detection scope.
   LET Blocking(x) == { p \in Procs : acquired[p] \in Overlap(x, Acquired) } IN
   
   <3>1. (\E i \in Procs : H(c) /\ i \in Blocking(x) ~> (G \/ \E d \in S : d < c /\ H(d))

    <4>1. H(c) /\ x \in Procs /\ i \in Blocking(x) ~> (G \/ \E d \in S : d < c /\ H(d))


     <5>1. H(c) /\ i \in Procs /\ i \in Blocking(x) /\ state[i] = nextblock ~> (G \/ \E d \in S : d < c /\ H(d)

      \* WF1 on doNextBlock(i)
           
     <5>2. H(c) /\ i \in Procs /\ i \in Blocking(x) /\ state[i] = search ~> (G \/ \E d in \in S : d < c /\ H(d))

      <6>1. /\ H(c)
            /\ i \in Procs
            /\ i \in Blocking(x)
            /\ state[i] = search
            ~> \/ \E d \in S : d < c /\ H(d)
               \/ H(c) /\ i \in Procs /\ i \in Blocking(x) /\ state[i] = nextblock

           \* Two cases:
           \* i = j then this leads to the LHS of <5>1 and we have it
           \* i # j Two cases here too:
           \*      - Either j will release a block in Overlap(x, Acquired) and we have it (\E d \in S : d < c /\ H(d))
           \*      - or j won't release a block in Overlap(x, Acquired), but that is fine, we have WF1 on i=j so we
           \*        should be good (ENABLED<<doSearch(j) /\ j=i>> is good).

    <4>2. QED BY <4>1 \* UG then change \A to \E (which is allowed).

   <3>2. H(c) => \E i \in Procs : acquired[i] \in Overlap(x, Acquired)
         PROOF OMITTED \* TODO

   <3>3. QED BY <3>1 and <3>2 \* TODO what is this called?
         \* I dunno what this is called... since H(c) implies that something is acquired in the overlap
         \* we can add/remove the overlap part.

     
  <2>2. QED \* Lattice rule with <2>1

<1>2. x \in Nblocks /\ isHot[x] => \E c \in S : H(c)
      PROOF OMITTED \* since x is hot, there is something overlapping its scope.

<1>3. Prog => (x \in Nblocks /\ isHot[x] ~> ~isHot[x])
      BY <1>1 and <1>2 \* TODO: what is this called?
      \* Since <1>2 is a safety property (which we will demonstrate in <1>3), we can add/remove it somehow at our leasure.

<1>4. Prog => \A x \in Nblocks : isHot[x] ~> ~isHot[x]
      BY <1>3 \* Universal Generalization

<1>5. QED BY <1>4
============================================================
