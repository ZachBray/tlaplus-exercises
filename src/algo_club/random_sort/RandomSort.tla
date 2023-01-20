---- MODULE RandomSort ----

EXTENDS Integers

CONSTANTS range, length

VARIABLES elements

vars == <<elements>>

Domain == 1..length


TypeOK == /\ elements \in [ Domain -> range ]

Init == TypeOK

Swap == \E i \in Domain :
            \E j \in Domain :
                /\ i < j
                /\ elements[j] < elements[i]
                /\ elements' = [ elements EXCEPT ![i] = elements[j], ![j] = elements[i] ]

Next == Swap

Spec == Init /\ [][Next]_vars /\ WF_vars(Swap)

Ordered == \A i \in Domain :
           \A j \in Domain :
              \/ i = j
              \/ i < j /\ elements[i] <= elements[j]
              \/ i > j /\ elements[i] >= elements[j]
              

EventuallyOrdered == <>[]Ordered

====
