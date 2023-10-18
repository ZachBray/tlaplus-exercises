---- MODULE MSI ----

EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS Addresses, Values, ProcessCount
VARIABLES memory, memory_bus, bus_owner, caches, metadata, cache_buses

vars == <<memory, memory_bus, bus_owner, caches, metadata, cache_buses>>

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
    /\ memory_bus = <<>>
    /\ bus_owner = MemoryId
    /\ caches = [p \in ProcessIds |-> [a \in Addresses |-> Zero]]
    /\ metadata = [p \in ProcessIds |-> [a \in Addresses |-> "Invalid"]]
    /\ cache_buses = [p \in ProcessIds |-> [type |-> "Ready"]]

BusEmpty ==
    memory_bus = <<>>

BusSend(msg) ==
    /\ msg.sender = bus_owner
    /\ memory_bus' = <<msg>>

BusRead(endpoint, H(_)) ==
    /\ bus_owner = endpoint
    /\ memory_bus # <<>>
    /\ H(Head(memory_bus))

BusConsume ==
    memory_bus' = <<>>

PrRd(p) ==
    /\ p \in ProcessIds
    /\ cache_buses[p] = <<>> \/ cache_buses[p].type = "Ready"
    /\ \E a \in Addresses :
        /\ cache_buses' = [ cache_buses EXCEPT ![p] = [type |-> "PrRd", addr |-> a] ]
        /\ UNCHANGED <<memory, memory_bus, bus_owner, caches, metadata>>

PrWr(p) ==
    /\ p \in ProcessIds
    /\ cache_buses[p] = <<>> \/ cache_buses[p].type = "Ready"
    /\ \E a \in Addresses, v \in Values :
        /\ cache_buses' = [ cache_buses EXCEPT ![p] = [type |-> "PrWr", addr |-> a, val |-> v] ]
        /\ UNCHANGED <<memory, memory_bus, bus_owner, caches, metadata>>

LOCAL PendingPrRd(p, state, Transition(_)) ==
    /\ p \in ProcessIds
    /\ cache_buses[p].type = "PrRd"
    /\ LET a == cache_buses[p].addr
       IN  /\ metadata[p][a] = state
           /\ Transition(a)

RdModified(p) ==
    LET Transition(a) ==
        LET v == caches[p][a]
        IN  /\ BusEmpty
            /\ cache_buses' = [ cache_buses EXCEPT ![p] = [type |-> "Ready", addr |-> a, val |-> v ] ]
            /\ UNCHANGED <<memory, memory_bus, bus_owner, caches, metadata>>
    IN /\ PendingPrRd(p, "Modified", Transition)

RdShared(p) ==
    LET Transition(a) ==
        LET v == caches[p][a]
        IN  /\ BusEmpty
            /\ cache_buses' = [ cache_buses EXCEPT ![p] = [type |-> "Ready", addr |-> a, val |-> v ] ]
            /\ UNCHANGED <<memory, memory_bus, bus_owner, caches, metadata>>
    IN /\ PendingPrRd(p, "Shared", Transition)

RdInvalidBegin(p) ==
    LET Transition(a) ==
         /\ BusEmpty
         /\ BusSend([type |-> "Rd", sender |-> p, origin |-> p, addr |-> a])
         /\ UNCHANGED <<memory, bus_owner, caches, metadata, cache_buses>>
    IN /\ PendingPrRd(p, "Invalid", Transition)

RdInvalidEnd(p) ==
    LET Transition(a) ==
        LET HandleReply(msg) ==
            /\ msg.type = "Rd"
            /\ msg.addr = a
            /\ msg.origin = p
            /\ msg.sender = MemoryId
            /\ caches' = [ caches EXCEPT ![p][a] = msg.val ]
            /\ metadata' = [ metadata EXCEPT ![p][a] = "Shared" ]
            /\ cache_buses' = [ cache_buses EXCEPT ![p] = [type |-> "Ready", addr |-> a, val |-> msg.val ] ]
            /\ BusConsume
            /\ UNCHANGED <<memory, bus_owner>>
        IN BusRead(p, HandleReply)
    IN /\ PendingPrRd(p, "Invalid", Transition)

RdMemory ==
    LET HandleRequest(msg) ==
        /\ msg.type = "Rd"
        /\ msg.sender # MemoryId
        /\ BusSend([type |-> "Rd", sender |-> MemoryId, origin |-> msg.sender, addr |-> msg.addr, val |-> memory[msg.addr]])
        /\ UNCHANGED <<memory, bus_owner, caches, metadata, cache_buses>>
    IN /\ BusRead(MemoryId, HandleRequest)

LOCAL PendingPrWr(p, state, Transition(_,_)) ==
    /\ p \in ProcessIds
    /\ cache_buses[p].type = "PrWr"
    /\ LET a == cache_buses[p].addr
           v == cache_buses[p].val
       IN  /\ metadata[p][a] = state
           /\ Transition(a, v)

WrModifiedBegin(p) ==
    LET Transition(a, v) ==
        /\ BusEmpty
        /\ BusSend([type |-> "Wr", sender |-> p, origin |-> p, addr |-> a, val |-> v])
        /\ UNCHANGED <<memory, bus_owner, caches, metadata, cache_buses>>
    IN /\ PendingPrWr(p, "Modified", Transition)

WrModifiedEnd(p) ==
    LET HandleReply(msg) ==
        /\ msg.type = "Wr"
        /\ msg.origin = p
        /\ msg.sender = MemoryId
        /\ metadata' = [ metadata EXCEPT ![p][msg.addr] = "Modified" ]
        /\ caches' = [ caches EXCEPT ![p][msg.addr] = msg.val ]
        /\ cache_buses' = [ cache_buses EXCEPT ![p] = [type |-> "Ready", addr |-> msg.addr, val |-> msg.val ] ]
        /\ BusConsume
        /\ UNCHANGED <<memory, bus_owner>>
    IN /\ BusRead(p, HandleReply)

WrSharedBegin(p) ==
    LET Transition(a, v) ==
        /\ BusEmpty
        /\ BusSend([type |-> "Wr", sender |-> p, origin |-> p, addr |-> a, val |-> v])
        /\ UNCHANGED <<memory, bus_owner, caches, metadata, cache_buses>>
    IN /\ PendingPrWr(p, "Shared", Transition)

WrSharedEnd(p) ==
    LET Transition(a, v) ==
        LET HandleReply(msg) ==
            /\ msg.type = "Wr"
            /\ msg.addr = a
            /\ msg.origin = p
            /\ msg.sender = MemoryId
            /\ caches' = [ caches EXCEPT ![p][a] = msg.val ]
            /\ metadata' = [ metadata EXCEPT ![p][a] = "Modified" ]
            /\ cache_buses' = [ cache_buses EXCEPT ![p] = [type |-> "Ready", addr |-> a, val |-> msg.val ] ]
            /\ BusConsume
            /\ UNCHANGED <<memory, bus_owner>>
        IN BusRead(p, HandleReply)
    IN /\ PendingPrWr(p, "Shared", Transition)

WrInvalidBegin(p) ==
    LET Transition(a, v) ==
        /\ BusEmpty
        /\ BusSend([type |-> "Wr", sender |-> p, origin |-> p, addr |-> a, val |-> v])
        /\ UNCHANGED <<memory, bus_owner, caches, metadata, cache_buses>>
    IN /\ PendingPrWr(p, "Invalid", Transition)

WrInvalidEnd(p) ==
    LET Transition(a, v) ==
        LET HandleReply(msg) ==
            /\ msg.type = "Wr"
            /\ msg.addr = a
            /\ msg.origin = p
            /\ msg.sender = MemoryId
            /\ caches' = [ caches EXCEPT ![p][a] = msg.val ]
            /\ metadata' = [ metadata EXCEPT ![p][a] = "Modified" ]
            /\ cache_buses' = [ cache_buses EXCEPT ![p] = [type |-> "Ready", addr |-> a, val |-> msg.val ] ]
            /\ BusConsume
            /\ UNCHANGED <<memory, bus_owner>>
        IN BusRead(p, HandleReply)
    IN /\ PendingPrWr(p, "Invalid", Transition)

WrMemory ==
    LET HandleRequest(msg) ==
        /\ msg.type = "Wr"
        /\ msg.sender # MemoryId
        /\ memory' = [ memory EXCEPT ![msg.addr] = msg.val ]
        /\ BusSend([type |-> "Wr", sender |-> MemoryId, origin |-> msg.sender, addr |-> msg.addr, val |-> msg.val])
        /\ UNCHANGED <<caches, bus_owner, metadata, cache_buses>>
    IN /\ BusRead(MemoryId, HandleRequest)

Evict(p) ==
    /\ p \in ProcessIds
    /\ \E a \in Addresses :
        /\ metadata[p][a] # "Invalid"
        /\ metadata' = [ metadata EXCEPT ![p][a] = "Invalid" ]
        /\ caches' = [ caches EXCEPT ![p][a] = Zero ]
        /\ UNCHANGED <<memory, bus_owner, memory_bus, cache_buses>>

Snoop(p) ==
    LET Inspect(msg) ==
        /\ msg.origin # p
        /\ \/ /\ metadata[p][msg.addr] = "Modified"
              /\ msg.type = "Rd"
              /\ metadata' = [ metadata EXCEPT ![p][msg.addr] = "Shared" ]
              /\ UNCHANGED <<memory, caches, cache_buses>>
           \/ /\ metadata[p][msg.addr] \in { "Shared", "Modified" }
              /\ msg.type = "Wr"
              /\ metadata' = [ metadata EXCEPT ![p][msg.addr] = "Invalid" ]
              /\ UNCHANGED <<memory, caches, cache_buses>>
    IN /\ BusRead(p, Inspect)
       /\ UNCHANGED<<memory_bus, bus_owner>>

Work ==
    \/ RdMemory
    \/ WrMemory
    \/ \E p \in ProcessIds :
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
            \/ Snoop(p)

PassToken ==
    /\ ~ ENABLED Work
    /\ LET nextId == bus_owner + 1 IN
       LET nextOwner == IF nextId > ProcessCount THEN MemoryId ELSE nextId IN
       bus_owner' = nextOwner
    /\ UNCHANGED <<memory, memory_bus, caches, metadata, cache_buses>>

Perturbation ==
    \/ \E p \in ProcessIds :
        \/ PrRd(p)
        \/ PrWr(p)
        \/ Evict(p)

Next ==
    \/ Work
    \/ Perturbation
    \/ PassToken

Fairness ==
    /\ WF_vars(Work)
    /\ SF_vars(PassToken)

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

BusDrains == []<>(memory_bus = <<>>)

CachesAreCoherentWhenBusDrains ==
    ~ BusEmpty \/ CachesAreCoherent

MaximumOfOneModifiedLinePerAddressWhenBusDrains ==
    ~ BusEmpty \/ MaximumOfOneModifiedLinePerAddress

PrActionsEventuallySucceed ==
    \A p \in ProcessIds :
        /\ cache_buses[p].type \in { "Rd", "Wr" } ~> cache_buses[p].type = "Ready"

====
