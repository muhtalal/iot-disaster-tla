------------------------- MODULE Gateway -------------------------
EXTENDS Node, Sequences, Natural
VARIABLE Gateway
GwID == 2  
GatewayNode == [
  GwNode |-> Node(GwID),
  GwReceivedEqData |-> BOOLEAN,
  GwRelayedEqData  |-> BOOLEAN
		]
ActiveModeInvariant ==
  Gw.GwNode.NMode = "Active"
NodeIDs == 1..6
Nodes == [n \in NodeIDs |-> Node(n)]
AlwaysConnectedInvariant ==
                          /\ \E n \in DOMAIN Nodes :
                                Nodes[n].NodeType = Sensor 
                        		/\ Nodes[n].NCon = "Connected"
                          /\ \E n \in DOMAIN Nodes :
                                Nodes[n].NodeType = Actuator 
                        		/\ Nodes[n].NCon = "Connected"
                          /\ \E n \in DOMAIN Nodes :
                                Nodes[n].NodeType = BaseStation 
                        		/\ Nodes[n].NCon = "Connected"
=============================================================================
