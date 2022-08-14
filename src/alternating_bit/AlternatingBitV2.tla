------- MODULE AlternatingBitV2 -------

EXTENDS Integers, Sequences, TLC
CONSTANTS Data, Bad
VARIABLES AVar, BVar, AToB2, BToA2


Vars == <<AVar, BVar, AToB2, BToA2>>

DataIndex == 1
BitIndex == 2

Bit == { 0, 1 }
Message == Data \X Bit
Corruptable(x) == x \union {Bad}
MsgChannel == Seq(Corruptable(Message))
AckChannel == Seq(Corruptable(Bit))

ASSUME /\ Bad \notin Message
       /\ Bad \notin Bit

NegateBit(b) == 1 - b

TypeOK == /\ AToB2 \in MsgChannel
          /\ BToA2 \in AckChannel
          /\ AVar \in Message
          /\ BVar \in Message

Init == /\ AVar \in Message
        /\ BVar = AVar
        /\ AToB2 = <<>>
        /\ BToA2 = <<>>


ASnd == /\ AToB2' = Append(AToB2, AVar)
        /\ UNCHANGED <<AVar, BVar, BToA2>>

BSnd == /\ BToA2' = Append(BToA2, BVar[BitIndex])
        /\ UNCHANGED <<AVar, BVar, AToB2>>

BRcv == /\ Len(AToB2) > 0
        /\ AToB2' = Tail(AToB2)
        /\ \/ /\ Head(AToB2) # Bad
              /\ BVar' = Head(AToB2)
              /\ UNCHANGED <<AVar, BToA2>>
           \/ /\ Head(AToB2) = Bad
              /\ UNCHANGED <<AVar, BVar, BToA2>>

ARcv == /\ Len(BToA2) > 0
        /\ BToA2' = Tail(BToA2)
        /\ \/ /\ Head(BToA2) = AVar[BitIndex]
              /\ \E d \in Data: AVar' = <<d, NegateBit(AVar[BitIndex])>>
           \/ /\ Head(BToA2) # AVar[BitIndex]
              /\ UNCHANGED <<AVar>>
        /\ UNCHANGED <<BVar, AToB2>>

Replace(seq, i, msg) == SubSeq(seq, 1, i - 1) \o <<msg>> \o SubSeq(seq, i + 1, Len(seq))

CorruptMessage(nextSeq, currSeq) == /\ Len(currSeq) > 0
                                    /\ \E i \in 1..Len(currSeq): nextSeq = Replace(currSeq, i, Bad)

LoseMessage ==
      /\ \/ CorruptMessage(AToB2', AToB2) /\ UNCHANGED<<BToA2>>
         \/ CorruptMessage(BToA2', BToA2) /\ UNCHANGED<<AToB2>>
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

AB_Spec == AB!ABSpec
AB_Inv == AB!ABInv
AB_Eventual == AB!ABEventual

THEOREM Spec => AB_Inv
THEOREM Spec => AB_Spec

(* This specification does not implement AB_FairSpec nor AB_Eventual, as the fairness conditions
 * that we specify do not guarantee that ARcv and BRcv will run on non-corrupted messages.
 * Therefore, we include behaviours with loops that do fire ARcv and BRcv but not in useful ways. *)

-------

RECURSIVE FilterNot(_, _)
FilterNot(seq, x) == 
  IF seq = <<>>
  THEN <<>>
  ELSE IF Head(seq) = x 
       THEN FilterNot(Tail(seq), x)
       ELSE <<Head(seq)>> \o FilterNot(Tail(seq), x)

ABv1 == INSTANCE AlternatingBitV1 WITH AToB <- FilterNot(AToB2, Bad),
                                       BToA <- FilterNot(BToA2, Bad)

ABv1_Spec == ABv1!Spec

THEOREM Spec => ABv1_Spec

-------

Checkable == /\ Len(AToB2) <= 3
             /\ Len(BToA2) <= 3

=======
