------- MODULE TxCommit -------

CONSTANTS participants
VARIABLES pState

Vars == <<pState>>

TxTypeOK == \A p \in participants: pState[p] \in { "working", "preparing", "committed", "aborted" }

TxInit == pState = [ p \in participants |-> "working" ]

CanPrepare(p) == /\ pState[p] = "working"
                 /\ \A q \in participants: pState[q] # "aborted"

CanCommit(p) == /\ pState[p] = "preparing"
                /\ \A q \in participants: pState[q] \in { "preparing", "committed" }

CanAbort(p) == /\ pState[p] \in { "working", "preparing" }
               /\ \A q \in participants: pState[q] # "committed"

Prepare(p) == pState' = [pState EXCEPT ![p] = "preparing"] 

Commit(p) == pState' = [pState EXCEPT ![p] = "committed"] 

Abort(p) == pState' = [pState EXCEPT ![p] = "aborted"] 


TxNext == \E p \in participants: \/ /\ CanPrepare(p)
                                    /\ Prepare(p)
                                 \/ /\ CanCommit(p)
                                    /\ Commit(p)
                                 \/ /\ CanAbort(p)
                                    /\ Abort(p)

TxConsistent == \neg /\ \E p \in participants: pState[p] = "committed"
                     /\ \E p \in participants: pState[p] = "aborted"


TxSpec == TxInit /\ [][TxNext]_Vars /\ WF_Vars(TxNext)

TxEventual == /\ (\E p \in participants: pState[p] = "committed") ~> 
                           (\A p \in participants: pState[p] = "committed")
              /\ (\E p \in participants: pState[p] = "aborted") ~> 
                           (\A p \in participants: pState[p] = "aborted")

=======
