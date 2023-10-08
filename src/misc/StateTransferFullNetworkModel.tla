---- MODULE StateTransferFullNetworkModel ----

EXTENDS StateTransferAnimated

NetworkIsNotFull == ~(Len(network) = NetworkCapacity)

====
