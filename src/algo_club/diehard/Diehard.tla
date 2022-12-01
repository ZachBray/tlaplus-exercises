---- MODULE Diehard ----

EXTENDS Integers

VARIABLES big_jug, small_jug

vars == <<big_jug, small_jug>>

Init == /\ big_jug = 0
        /\ small_jug = 0

TypeOK == /\ big_jug \in 0..5
          /\ small_jug \in 0..3

FillSmall == /\ small_jug' = 3
             /\ big_jug' = big_jug

EmptySmall == /\ small_jug' = 0
              /\ big_jug' = big_jug
             
FillBig == /\ small_jug' = small_jug
           /\ big_jug' = 5

EmptyBig == /\ small_jug' = small_jug
            /\ big_jug' = 0


PourSmallToBig == IF big_jug + small_jug > 5
                  THEN /\ big_jug' = 5
                       /\ small_jug' = small_jug - (5 - big_jug)
                  ELSE /\ big_jug' = big_jug + small_jug
                       /\ small_jug' = 0

PourBigToSmall == IF big_jug + small_jug > 3
                  THEN /\ small_jug' = 3
                       /\ big_jug' = big_jug - (3 - small_jug)
                  ELSE /\ small_jug' = big_jug + small_jug
                       /\ big_jug' = 0
 

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ PourSmallToBig
        \/ PourBigToSmall

Spec == Init /\ [][Next]_vars


Solution == big_jug # 4

====
