------- MODULE AlternatingBit -------

EXTENDS Integers, TLC
CONSTANTS Data
VARIABLES AVar, BVar

DataIndex == 1
BitIndex == 2

Bit == { 0, 1 }
ABVar == Data \X Bit

ABReverseBit(b) == 1 - b

ABTypeOK == /\ AVar \in ABVar
            /\ BVar \in ABVar

ABInit == /\ AVar \in ABVar
          /\ BVar = AVar

AChooses == /\ AVar = BVar
            /\ \E d \in Data: /\ AVar' = <<d, ABReverseBit(AVar[BitIndex])>>
                              /\ UNCHANGED <<BVar>>

BCopies == /\ AVar # BVar
           /\ BVar' = AVar
           /\ UNCHANGED <<AVar>>

ABNext == \/ AChooses
          \/ BCopies

ABInv == AVar[BitIndex] = BVar[BitIndex] => AVar = BVar

ABSpec == ABInit /\ [][ABNext]_<<AVar, BVar>> /\ WF_<<AVar, BVar>>(ABNext)

ABEventual == \A v \in ABVar: (AVar = v) ~> (BVar = v)

=======
