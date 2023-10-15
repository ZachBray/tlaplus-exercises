---- MODULE MSI ----

EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS Addresses, Values, ProcessCount
VARIABLES memory, memory_bus, caches, metadata, cache_buses

vars == <<memory, memory_bus, caches, metadata, cache_buses>>

ProcessIds == 1..ProcessCount
MemoryId == 0
BusDestinations == {MemoryId} \cup ProcessIds
Zero == 0

ValidValues == Values \cup {Zero}

TypeOK ==
    /\ Addresses \subseteq Nat
    /\ Values \subseteq Nat
    /\ memory \in [Addresses -> ValidValues]
    /\ caches \in [ProcessIds -> [Addresses -> ValidValues]]
    /\ metadata \in [ProcessIds -> [Addresses -> {"Modified", "Shared", "Invalid"}]]

Init ==
    /\ memory = [a \in Addresses |-> Zero]
    /\ memory_bus = [p \in BusDestinations |-> <<>>]
    /\ caches = [p \in ProcessIds |-> [a \in Addresses |-> Zero]]
    /\ metadata = [p \in ProcessIds |-> [a \in Addresses |-> "Invalid"]]
    /\ cache_buses = [p \in ProcessIds |-> <<>>]

MemoryBusEmpty == \A p \in BusDestinations : memory_bus[p] = <<>>

MemoryBusRequest(msg) ==
    memory_bus' = [ d \in BusDestinations |-> <<msg>> ]

MemoryBusReply(msg) ==
    memory_bus' = [ d \in BusDestinations |-> IF d = MemoryId THEN <<>> ELSE <<msg>> ]

MemoryBusRespond(H(_)) ==
    /\ memory_bus[MemoryId] # <<>>
    /\ \A p \in ProcessIds : memory_bus[p] = <<>>
    /\ \/ /\ Head(memory_bus[MemoryId]).sender = MemoryId
          /\ UNCHANGED <<memory, memory_bus, caches, metadata, cache_buses>>
       \/ /\ Head(memory_bus[MemoryId]).sender # MemoryId
          /\ H(Head(memory_bus[MemoryId]))

MemoryBusConsume(endpoint, H(_)) ==
    /\ memory_bus[endpoint] # <<>>
    /\ \/ /\ Head(memory_bus[endpoint]).sender = endpoint
          /\ UNCHANGED <<memory, caches, metadata, cache_buses>>
       \/ /\ Head(memory_bus[endpoint]).sender # endpoint
          /\ H(Head(memory_bus[endpoint]))
    /\ memory_bus' = [ memory_bus EXCEPT ![endpoint] = <<>> ]

PrRd(p) ==
    /\ p \in ProcessIds
    /\ cache_buses[p] = <<>>
    /\ \E a \in Addresses :
        /\ cache_buses' = [ cache_buses EXCEPT ![p] = <<[type |-> "PrRd", addr |-> a]>> ]
        /\ UNCHANGED <<memory, memory_bus, caches, metadata>>

PrWr(p) ==
    /\ p \in ProcessIds
    /\ cache_buses[p] = <<>>
    /\ \E a \in Addresses, v \in Values :
        /\ cache_buses' = [ cache_buses EXCEPT ![p] = <<[ type |-> "PrWr", addr |-> a, val |-> v]>> ]
        /\ UNCHANGED <<memory, memory_bus, caches, metadata>>

PrContinue(p) ==
    /\ p \in ProcessIds
    /\ cache_buses[p] # <<>>
    /\ Head(cache_buses[p]).type = "Ready"
    /\ cache_buses' = [ cache_buses EXCEPT ![p] = <<>> ]
    /\ UNCHANGED <<memory, memory_bus, caches, metadata>>

LOCAL PendingPrRd(p, state, Transition(_)) ==
    /\ p \in ProcessIds
    /\ cache_buses[p] # <<>>
    /\ Head(cache_buses[p]).type = "PrRd"
    /\ LET a == Head(cache_buses[p]).addr
       IN  /\ metadata[p][a] = state
           /\ Transition(a)

RdModified(p) ==
    LET Transition(a) ==
        LET v == caches[p][a]
        IN  /\ MemoryBusEmpty
            /\ cache_buses' = [ cache_buses EXCEPT ![p] = <<[type |-> "Ready", addr |-> a, val |-> v ]>> ]
            /\ UNCHANGED <<memory, memory_bus, caches, metadata>>
    IN PendingPrRd(p, "Modified", Transition)

RdShared(p) ==
    LET Transition(a) ==
        LET v == caches[p][a]
        IN  /\ MemoryBusEmpty
            /\ cache_buses' = [ cache_buses EXCEPT ![p] = <<[type |-> "Ready", addr |-> a, val |-> v ]>> ]
            /\ UNCHANGED <<memory, memory_bus, caches, metadata>>
    IN PendingPrRd(p, "Shared", Transition)

RdInvalidBegin(p) ==
    LET Transition(a) ==
         /\ MemoryBusEmpty
         /\ MemoryBusRequest([type |-> "Rd", sender |-> p, origin |-> p, addr |-> a])
         /\ UNCHANGED <<memory, caches, metadata, cache_buses>>
    IN PendingPrRd(p, "Invalid", Transition)

RdInvalidEnd(p) ==
    LET Transition(a) ==
        LET HandleReply(msg) ==
            /\ msg.type = "RdReply"
            /\ msg.addr = a
            /\ msg.origin = p
            /\ caches' = [ caches EXCEPT ![p][a] = msg.val ]
            /\ metadata' = [ metadata EXCEPT ![p][a] = "Shared" ]
            /\ cache_buses' = [ cache_buses EXCEPT ![p] = <<[type |-> "Ready", addr |-> a, val |-> msg.val ]>> ]
            /\ UNCHANGED <<memory>>
        IN MemoryBusConsume(p, HandleReply)
    IN PendingPrRd(p, "Invalid", Transition)

RdMemory ==
    LET HandleRequest(msg) ==
        /\ msg.type = "Rd"
        /\ MemoryBusReply([type |-> "RdReply", sender |-> MemoryId, origin |-> msg.sender, addr |-> msg.addr, val |-> memory[msg.addr]])
        /\ UNCHANGED <<memory, caches, metadata, cache_buses>>
    IN MemoryBusRespond(HandleRequest)

LOCAL PendingPrWr(p, state, Transition(_,_)) ==
    /\ p \in ProcessIds
    /\ cache_buses[p] # <<>>
    /\ Head(cache_buses[p]).type = "PrWr"
    /\ LET a == Head(cache_buses[p]).addr
           v == Head(cache_buses[p]).val
       IN  /\ metadata[p][a] = state
           /\ Transition(a, v)

WrModifiedBegin(p) ==
    LET Transition(a, v) ==
        /\ MemoryBusEmpty
        /\ caches' = [ caches EXCEPT ![p][a] = v ]
        /\ cache_buses' = [ cache_buses EXCEPT ![p] = <<[type |-> "Ready", addr |-> a, val |-> v ]>> ]
        /\ MemoryBusRequest([type |-> "Wr", sender |-> p, origin |-> p, addr |-> a, val |-> v])
        /\ UNCHANGED <<memory, metadata>>
    IN PendingPrWr(p, "Modified", Transition)

WrModifiedEnd(p) ==
    LET HandleReply(msg) ==
        /\ msg.type = "WrReply"
        /\ msg.origin = p
        /\ metadata[p][msg.addr] = "Modified"
        /\ UNCHANGED <<memory, caches, metadata, cache_buses>>
    IN MemoryBusConsume(p, HandleReply)

WrSharedBegin(p) ==
    LET Transition(a, v) ==
        /\ MemoryBusEmpty
        /\ MemoryBusRequest([type |-> "Wr", sender |-> p, origin |-> p, addr |-> a, val |-> v])
        /\ UNCHANGED <<memory, caches, metadata, cache_buses>>
    IN PendingPrWr(p, "Shared", Transition)

WrSharedEnd(p) ==
    LET Transition(a, v) ==
        LET HandleReply(msg) ==
            /\ msg.type = "WrReply"
            /\ msg.addr = a
            /\ msg.origin = p
            /\ caches' = [ caches EXCEPT ![p][a] = msg.val ]
            /\ metadata' = [ metadata EXCEPT ![p][a] = "Modified" ]
            /\ cache_buses' = [ cache_buses EXCEPT ![p] = <<[type |-> "Ready", addr |-> a, val |-> msg.val ]>> ]
            /\ UNCHANGED <<memory>>
        IN MemoryBusConsume(p, HandleReply)
    IN PendingPrWr(p, "Shared", Transition)

WrInvalidBegin(p) ==
    LET Transition(a, v) ==
        /\ MemoryBusEmpty
        /\ MemoryBusRequest([type |-> "Wr", sender |-> p, origin |-> p, addr |-> a, val |-> v])
        /\ UNCHANGED <<memory, caches, metadata, cache_buses>>
    IN PendingPrWr(p, "Invalid", Transition)

WrInvalidEnd(p) ==
    LET Transition(a, v) ==
        LET HandleReply(msg) ==
            /\ msg.type = "WrReply"
            /\ msg.addr = a
            /\ msg.origin = p
            /\ caches' = [ caches EXCEPT ![p][a] = msg.val ]
            /\ metadata' = [ metadata EXCEPT ![p][a] = "Modified" ]
            /\ cache_buses' = [ cache_buses EXCEPT ![p] = <<[type |-> "Ready", addr |-> a, val |-> msg.val ]>> ]
            /\ UNCHANGED <<memory>>
        IN MemoryBusConsume(p, HandleReply)
    IN PendingPrWr(p, "Invalid", Transition)

WrMemory ==
    LET HandleRequest(msg) ==
        /\ msg.type = "Wr"
        /\ memory' = [ memory EXCEPT ![msg.addr] = msg.val ]
        /\ MemoryBusReply([type |-> "WrReply", sender |-> MemoryId, origin |-> msg.sender, addr |-> msg.addr, val |-> msg.val])
        /\ UNCHANGED <<caches, metadata, cache_buses>>
    IN MemoryBusRespond(HandleRequest)

Evict(p) ==
    /\ p \in ProcessIds
    /\ \E a \in Addresses :
        /\ metadata[p][a] # "Invalid"
        /\ metadata' = [ metadata EXCEPT ![p][a] = "Invalid" ]
        /\ caches' = [ caches EXCEPT ![p][a] = Zero ]
        /\ UNCHANGED <<memory, memory_bus, cache_buses>>

Snoop(p) ==
    LET Inspect(msg) ==
        /\ msg.origin # p
        /\ \/ /\ metadata[p][msg.addr] = "Modified"
              /\ msg.type = "Rd"
              /\ metadata' = [ metadata EXCEPT ![p][msg.addr] = "Shared" ]
              /\ UNCHANGED <<memory, caches, cache_buses>>
           \/ /\ metadata[p][msg.addr] = "Shared"
              /\ msg.type = "Rd"
              /\ UNCHANGED <<memory, caches, metadata, cache_buses>>
           \/ /\ metadata[p][msg.addr] \in { "Shared", "Modified" }
              /\ msg.type = "Wr"
              /\ metadata' = [ metadata EXCEPT ![p][msg.addr] = "Invalid" ]
              /\ UNCHANGED <<memory, caches, cache_buses>>
           \/ /\ metadata[p][msg.addr] = "Invalid"
              /\ msg.type \in {"Rd", "Wr"}
              /\ UNCHANGED <<memory, caches, metadata, cache_buses>>
           \/ /\ msg.type \in {"RdReply", "WrReply"}
              /\ UNCHANGED <<memory, caches, metadata, cache_buses>>
    IN MemoryBusConsume(p, Inspect)

Next ==
    \/ RdMemory
    \/ WrMemory
    \/ \E p \in ProcessIds :
            \/ PrRd(p)
            \/ PrWr(p)
            \/ PrContinue(p)
            \/ RdModified(p)
            \/ RdShared(p)
            \/ RdInvalidBegin(p)
            \/ RdInvalidEnd(p)
            \/ WrModifiedBegin(p)
            \/ WrModifiedEnd(p)
            \/ WrSharedBegin(p)
            \/ WrSharedEnd(p)
            \/ WrInvalidBegin(p)
            \/ WrInvalidEnd(p)
            \/ Evict(p)
            \/ Snoop(p)

Fairness == \* Actions that drain the memory bus
    /\ WF_vars(RdMemory)
    /\ WF_vars(WrMemory)
    /\ \A p \in ProcessIds :
         /\ WF_vars(RdInvalidEnd(p))
         /\ WF_vars(WrModifiedEnd(p))
         /\ WF_vars(WrSharedEnd(p))
         /\ WF_vars(WrInvalidEnd(p))
         /\ WF_vars(Snoop(p))

Spec == Init /\ [][Next]_vars /\ Fairness

MaximumOfOneModifiedLinePerAddress ==
    \A a \in Addresses :
        \A p \in ProcessIds :
            \/ metadata[p][a] # "Modified"
            \/ \A q \in ProcessIds :
                   \/ q = p
                   \/ metadata[q][a] = "Invalid"

CachesAreCoherent ==
    \A p1, p2 \in ProcessIds :
        \A a \in Addresses:
            \/ metadata[p1][a] = "Invalid"
            \/ metadata[p2][a] = "Invalid"
            \/ caches[p1][a] = caches[p2][a]

BusDrains == []<>(memory_bus = [p \in BusDestinations |-> <<>>])

CachesAreCoherentWhenBusDrains ==
    ~ MemoryBusEmpty \/ CachesAreCoherent

MaximumOfOneModifiedLinePerAddressWhenBusDrains ==
    ~ MemoryBusEmpty \/ MaximumOfOneModifiedLinePerAddress

====
