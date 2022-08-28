---- MODULE StateTransferAnimated ----

EXTENDS StateTransfer, SVG, Json, TLC, SequencesExt

NodeLabelPos == [y |-> 80, x |-> {} ]
NodeBoxPos == [y |-> 100, w |-> 100, h |-> 100, x |-> {}]
NodeStatePos == [y |-> 190, x |-> {} ]
NetworkPos == [x |-> 150, y |-> 100, w |-> 350, h |-> 100 ]
MutatorPos == [x |-> 0 ]
ObserverPos == [x |-> 550 ]

MapSeq(seq, f(_, _)) == [ i \in 1 .. Len(seq) |-> f(i, seq[i]) ]

NetworkSlotBox(n) ==
  LET 
    width == NetworkPos.w \div NetworkCapacity
    padding == 2
  IN
    [ x |-> NetworkPos.x + NetworkPos.w - n * width + padding,
      y |-> NetworkPos.y + padding,
      w |-> width - 2 * padding,
      h |-> NetworkPos.h - 2 * padding ]

TopHalf(box) == [box EXCEPT !.h = box.h \div 2]
BottomHalf(box) == [box EXCEPT !.y = box.y + box.h \div 2,
                               !.h = box.h \div 2]

StateBoxStyle == [
  stroke |-> "black",
  stroke_thickness |-> "2px",
  fill |-> "white"
]

NetworkBoxStyle == [
  stroke |-> "black",
  stroke_thickness |-> "2px",
  fill |-> "darkgrey"
]

SnapshotBoxStyle == [
  stroke |-> "darkblue",
  stroke_thickness |-> "2px",
  fill |-> "lightblue"
]

DeltaBoxStyle == [
  stroke |-> "darkblue",
  stroke_thickness |-> "2px",
  fill |-> "white"
]

CenteredTextStyle == [
  text_anchor |-> "middle",
  dominant_baseline |-> "middle"
]

Label(name, position) ==
  <<Text(position.x, position.y, name, CenteredTextStyle)>>

LabelIn(name, box) ==
  Label(name, [ x |-> box.x + box.w \div 2, y |-> box.y + box.h \div 2])

Box(location, style) ==
  <<Rect(location.x, location.y, location.w, location.h, style)>>

NodeState(name, position, state) == 
  LET box == [ NodeBoxPos EXCEPT !.x = position.x ] IN
  Label(name, [ NodeLabelPos EXCEPT !.x = position.x + NodeBoxPos.w \div 2 ]) \o
  Box(box, StateBoxStyle) \o
  LabelIn(ToString(state), box)


NetworkSlot(i, msg) == 
  LET
    box == NetworkSlotBox(i)
    value == IF msg.type = "delta" THEN
               LET old == CHOOSE old \in PickableValues: msg.event[old] # Invalid IN
               ToString(old) \o " -> " \o ToString(msg.event[old])
             ELSE ToString(msg.value)
    style == IF msg.type = "delta" THEN DeltaBoxStyle ELSE SnapshotBoxStyle
  IN
    Box(box, style) \o
    LabelIn(msg.type, TopHalf(box)) \o
    LabelIn(value, BottomHalf(box))

Network ==
  Label("network", [ x |-> NetworkPos.x + NetworkPos.w \div 2, y |-> NodeLabelPos.y ]) \o
  Box(NetworkPos, NetworkBoxStyle) \o
  FlattenSeq(MapSeq(network, NetworkSlot))

Elements == 
  NodeState("mutator", MutatorPos, mutator) \o
  NodeState("observer", ObserverPos, observer) \o
  Network

View == SVGElemToString(Group(Elements, <<>>))

====
