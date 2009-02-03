-------------------- MODULE BidirectionalProof --------------------
EXTENDS HotNblocks


Bidirectional == \A x,y \in Nblocks : x \in Succs[y] => y \in Succs[x]

PROOF Bidirectional => \A x,y \in Nblocks: x \in IntScope(y) => y \in IntScope(x)

ASSUME Bidirectional
PROVE \A x,y \in Nblocks: x \in IntScope(y) => y \in IntScope(x)
<1>1. x \in Nblocks /\ y \in Nblocks /\ x \in IntScope(y) => y \in IntScope(x)
      ASSUME x \in Nblocks /\ y \in Nblocks /\ x \in IntScope(y)
      PROVE y \in IntScope(x)
      <2>1. CASE y \in Succs[x]
            <3>1. x \in Succs[y]
                  PROOF OBVIOUS \* This follows dirrectly from bidirectional assumption.
            <3>2. QED BY <3>2 \* and the definition of IntScope(x).
      <2>2. CASE z \in Succs[x] /\ y \in Preds(z)
            <3>1. z \in Succs[y]
                  PROOF BY <0>, <2>2 \* and by the definition of Preds.
            <3>2. x \in Preds(z)
                  PROOF BY <0>, <2>2 \* and by the definition of Preds.
            <3>3. QED BY <3>1 and <3>2
      <2>3. QED BY <2>1 and <2>2 \* These are the two sets which construct IntScope(x).

<1>2. QED BY <1>1 \* universal generalization

============================================================
