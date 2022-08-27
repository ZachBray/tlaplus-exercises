------- MODULE AlternatingBitV1 -------

EXTENDS Integers, Sequences, TLC
CONSTANTS Data
VARIABLES AVar, BVar, AToB, BToA

Vars == <<AVar, BVar, AToB, BToA>>

DataIndex == 1
BitIndex == 2

Bit == { 0, 1 }
Message == Data \X Bit
MsgChannel == Seq(Message)
AckChannel == Seq(Bit)

NegateBit(b) == 1 - b

TypeOK == /\ AToB \in MsgChannel
          /\ BToA \in AckChannel
          /\ AVar \in Message
          /\ BVar \in Message

Init == /\ AVar \in Message
        /\ BVar = AVar
        /\ AToB = <<>>
        /\ BToA = <<>>


ASnd == /\ AToB' = Append(AToB, AVar)
        /\ UNCHANGED <<AVar, BVar, BToA>>

BSnd == /\ BToA' = Append(BToA, BVar[BitIndex])
        /\ UNCHANGED <<AVar, BVar, AToB>>

BRcv == /\ Len(AToB) > 0
        /\ AToB' = Tail(AToB)
        /\ BVar' = Head(AToB)
        /\ UNCHANGED <<AVar, BToA>>

ARcv == /\ Len(BToA) > 0
        /\ BToA' = Tail(BToA)
        /\ \/ /\ Head(BToA) = AVar[BitIndex]
              /\ \E d \in Data: AVar' = <<d, NegateBit(AVar[BitIndex])>>
           \/ /\ Head(BToA) # AVar[BitIndex]
              /\ AVar' = AVar
        /\ UNCHANGED <<BVar, AToB>>

Remove(seq, i) == SubSeq(seq, 1, i - 1) \o SubSeq(seq, i + 1, Len(seq))

DropMessage(nextSeq, currSeq) == /\ Len(currSeq) > 0
                                 /\ \E i \in 1..Len(currSeq): nextSeq = Remove(currSeq, i)

LoseMessage ==
      /\ \/ DropMessage(AToB', AToB) /\ UNCHANGED<<BToA>>
         \/ DropMessage(BToA', BToA) /\ UNCHANGED<<AToB>>
      /\ UNCHANGED<<AVar, BVar>>

Next == \/ ASnd
        \/ BRcv
        \/ BSnd
        \/ ARcv
        \/ LoseMessage

Spec == /\ Init 
        /\ [][Next]_Vars

FairSpec == /\ Spec
            /\ WF_Vars(ASnd)
            /\ SF_Vars(BRcv)
            /\ WF_Vars(BSnd)
            /\ SF_Vars(ARcv)

-------

AB == INSTANCE AlternatingBit

AB_FairSpec == AB!ABFairSpec
AB_Inv == AB!ABInv
AB_Eventual == AB!ABEventual

THEOREM Spec => AB_Inv
THEOREM Spec => AB_FairSpec
THEOREM Spec => AB_Eventual

-------

Checkable == /\ Len(AToB) <= 3
             /\ Len(BToA) <= 3

=======
