---- MODULE Node ----
EXTENDS Naturals, Reals

CONSTANTS Sensor, Actuator, Gateway, BaseStation

Types == {Sensor, Actuator, Gateway, BaseStation}

Mode == {"Active", "Inactive"}

Connectivity == {"Connected", "NotConnected"}

(*
  DataRecord(type) returns a record whose fields depend on the node type.
*)
DataRecord(type) ==
  IF type = Sensor THEN
    [ SnSensedDisaster   |-> BOOLEAN,
      SnTransmittedDInfo |-> BOOLEAN ]
  ELSE IF type = Gateway THEN
    [ GwReceivedDInfo          |-> BOOLEAN,
      GwRelayedDinfoToBS       |-> BOOLEAN,
      GwRelayedDinfoToActuator |-> BOOLEAN ]
  ELSE IF type = BaseStation THEN
    [ BsReceivedDData  |-> BOOLEAN,
      BsBroadcastDInfo |-> BOOLEAN ]
  ELSE
    (* Actuator (or any other case) *)
    [ ActuatorReceivedDInfo |-> BOOLEAN ]

(*
  Node(n, nodeType) returns a node record for node id n and type nodeType.
  nodeType should be one of the constants: Sensor, Actuator, Gateway, BaseStation.
*)
Node(n, nodeType) ==
  [ NodeID    |-> n,
    NodeType  |-> nodeType,
    NMode     |-> CHOOSE mode \in Mode : TRUE,
    NConnectivity |-> CHOOSE con \in Connectivity : TRUE,
    DData     |-> DataRecord(nodeType)
  ]

====  
