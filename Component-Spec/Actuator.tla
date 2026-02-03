------------------------- MODULE Actuator -------------------------
EXTENDS Node, Sequences, Natural
VARIABLE Actuator
ActuatorID == 3
ActuatorNode == [
  AcNode |-> Node(ActuatorID),
  AcReceivedDData |-> BOOLEAN]
NodeIDs == 1..6
Nodes == [n \in NodeIDs |-> Node(n)]

ActuatorModeInvariant ==
  /\ \E n \in DOMAIN Nodes :
        Nodes[n].NodeType = 
		Gateway /\ Nodes[n].NCon = "Connected"

  /\ IF Actuator.AcReceivedDData = FALSE THEN
        Actuator.AcNode.NMode = "Inactive"
     ELSE
        Actuator.AcNode.NMode = "Active"
=============================================================================
