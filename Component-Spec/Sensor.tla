------------------------- MODULE Sensor -------------------------
EXTENDS Node, Sequences, Natural
VARIABLE Sensors
SensorType == << "seismic", "Radon", "WaterLevel", "Gas" >>

NodeIDs == 1..4
Nodes == [n \in NodeIDs |-> Node(n)]
Sensor(sid, stype) == LET snode == Node(sid) IN
    [
      snode |-> snode,
      Stype |-> stype,
      SMode |-> snode.NMode
    ]

SensorTypeInvariant ==
  \A s \in Sensors : s.snode.NodeType = Sensor

SensorConnectedInvariat ==
  \A s \in Sensors :
    s.snode.NCon = "Connected" =>
      \E n \in DOMAIN Nodes :
        Nodes[n].NodeType = Gateway /\ Nodes[n].NCon = "Connected"

=============================================================================
