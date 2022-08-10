------- MODULE TwoPhaseCommit -------

EXTENDS TLC
CONSTANTS participants
VARIABLES pState, mState, mPrepared, msgs

Vars == <<pState, mState, mPrepared, msgs>>

Messages == [ type: {"preparing", "aborted"}, me: participants] \union [ type: {"committed", "aborted"} ]

TwoPTypeOK == /\ \A p \in participants: pState[p] \in { "working", "preparing", "committed", "aborted" }
              /\ mState \in {"init", "done"}
              /\ mPrepared \subseteq participants
              /\ msgs \subseteq Messages

TwoPInit == /\ pState = [ p \in participants |-> "working" ]
            /\ mState = "init"
            /\ mPrepared = {}
            /\ msgs = {}

TwoPPartySnd(p, s) == /\ pState[p] = "working"
                      /\ \A q \in participants: pState[q] # "aborted"
                      /\ pState' = [pState EXCEPT ![p] = s]
                      /\ mState' = mState
                      /\ mPrepared' = mPrepared
                      /\ msgs' = {[type |-> s, me |-> p]} \union msgs

TwoPPartyRec(p, s, inStates) == /\ pState[p] \in inStates
                                /\ [type |-> s] \in msgs
                                /\ pState' = [pState EXCEPT ![p] = s]
                                /\ mState' = mState
                                /\ mPrepared' = mPrepared
                                /\ msgs' = msgs

TwoPManRecPrepare == \E p \in participants: /\ [type |-> "preparing", me |-> p] \in msgs
                                            /\ pState' = pState
                                            /\ mState' = mState
                                            /\ mPrepared' = {p} \union mPrepared
                                            /\ msgs' = msgs
                     
TwoPManCommit == /\ \A p \in participants: [type |-> "preparing", me |-> p] \in msgs
                 /\ mState = "init"
                 /\ pState' = pState
                 /\ mState' = "done"
                 /\ mPrepared' = mPrepared
                 /\ msgs' = {[type |-> "committed"]} \union msgs

TwoPManAbort == /\ \E p \in participants: [type |-> "aborted", me |-> p] \in msgs
                /\ mState = "init"
                /\ pState' = pState
                /\ mState' = "done"
                /\ mPrepared' = mPrepared
                /\ msgs' = {[type |-> "aborted"]} \union msgs

TwoPNext == \/ \E p \in participants: \/ TwoPPartySnd(p, "preparing")
                                      \/ TwoPPartySnd(p, "aborted")
                                      \/ TwoPPartyRec(p, "committed", {"preparing"})
                                      \/ TwoPPartyRec(p, "aborted", {"working", "preparing"})
            \/ TwoPManRecPrepare
            \/ TwoPManCommit
            \/ TwoPManAbort


TwoPSpec == TwoPInit /\ [][TwoPNext]_Vars /\ WF_Vars(TwoPNext)

-------

Tx == INSTANCE TxCommit

TxConsistent == Tx!TxConsistent
TxSpec == Tx!TxSpec
TxEventual == Tx!TxEventual

THEOREM TwoPSpec => TxSpec

-------

Symmetry == Permutations(participants)

=======
