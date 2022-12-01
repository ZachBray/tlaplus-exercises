---- MODULE Wolf ----

EXTENDS FiniteSets

(* Farmer location is represented by the boat_position *)
VARIABLES north, south, boat_position

vars == <<north, south, boat_position>>

TypeOK == /\ north \subseteq { "wolf", "goat", "cabbage" }
          /\ south \subseteq { "wolf", "goat", "cabbage" }
          /\ boat_position \in { "north", "south" }

Init == /\ north = {}
        /\ south = { "wolf", "goat", "cabbage" }
        /\ boat_position = "south"


NoEating(place) ==
  /\ { "wolf", "goat" } \notin SUBSET place
  /\ { "goat", "cabbage" } \notin SUBSET place

(* Travel with a passenger *)
ToNorth == /\ boat_position = "south"
           /\ \E passenger \in south : 
                       /\ north' = north \cup { passenger }
                       /\ south' = south \ { passenger }
                       /\ NoEating(south')
                       /\ boat_position' = "north"

(* Travel alone *)
ToNorthEmpty == /\ boat_position = "south"
                /\ NoEating(south)
                /\ north' = north
                /\ south' = south
                /\ boat_position' = "north"

(* Travel with a passenger *)
ToSouth == /\ boat_position = "north"
           /\ \E passenger \in north : 
                       /\ south' = south \cup { passenger }
                       /\ north' = north \ { passenger }
                       /\ NoEating(north')
                       /\ boat_position' = "south"

(* Travel alone *)
ToSouthEmpty == /\ boat_position = "north"
                /\ NoEating(north)
                /\ south' = south
                /\ north' = north
                /\ boat_position' = "south"

Next == \/ ToNorth
        \/ ToNorthEmpty
        \/ ToSouth
        \/ ToSouthEmpty

Spec == Init /\ [][Next]_vars

Solution == north # { "wolf", "goat", "cabbage" }

====
