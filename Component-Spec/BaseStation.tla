------------------------- MODULE BaseStation -------------------------
EXTENDS Node, Sequences, Natural
BsID == 10  \* Identifier for base station

BNode == [
  BsNode            |-> Node(BsID),
  BsReceivedDData   |-> BOOLEAN,
  BsBroadCastDInfo  |-> BOOLEAN,
  BsIssueOrders     |-> BOOLEAN
]
VARIABLE BaseStation

NodeIDs == 1..15
Nodes == [n \in NodeIDs |-> Node(n)]

BsAlwaysConInvariant ==
  \A g \in DOMAIN Nodes :
    (Nodes[g].NodeType = Gateway /\ Nodes[g].NCon = "Connected") =>
      BaseStation.BsNode.NCon = "Connected"

=============================================================================
