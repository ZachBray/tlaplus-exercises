------- MODULE Diehard -------
EXTENDS Integers

VARIABLES small, big

TypeOK == /\ small \in 0..3 
          /\ big \in 0..5

Init == /\ small = 0
        /\ big = 0


Jugs(S, B) == /\ small' = S
              /\ big' = B

EmptySmall == Jugs(0, big)

EmptyBig == Jugs(small, 0)

FillSmall == Jugs(3, big)

FillBig == Jugs(small, 5)

SmallToBig == \/ /\ small + big <= 5 
                 /\ Jugs(0, small + big)
              \/ /\ small + big > 5
                 /\ Jugs(small - (5 - big), 5)

BigToSmall == \/ /\ small + big <= 3
                 /\ Jugs(small + big, 0)
              \/ /\ small + big > 3
                 /\ Jugs(3, big - (3 - small))

Next == \/ EmptySmall
        \/ EmptyBig
        \/ FillSmall
        \/ FillBig
        \/ SmallToBig
        \/ BigToSmall

Spec == Init /\ [][Next]_<<small, big>>

(* Is it impossible to get 4 litres of water by
 * filling, emptying and transferring water between
 * a 5 litre jug and a 3 litre jug? *)
Solution == big # 4
        
========
