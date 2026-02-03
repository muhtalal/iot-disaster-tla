------------------------------- MODULE DisasterWarningAndResponse ------------------------------
EXTENDS Integers, Sequences, TLC, Naturals

(* --algorithm DisasterWarningandResponse 

variables
  SensorMode = "Inactive",
  SensorConnectivity = "NotConnected",
  SnSensedDisaster = FALSE, 
  SnTransmittedDInfo = FALSE, 
  GwReceivedDInfo = FALSE, 
  GwRelayedDinfoToBS = FALSE, 
  GwRelayedDinfoToActuator = FALSE,
  BsReceivedDData = FALSE, 
  BsBroadcastDInfo = FALSE, 
  DisasterDetected = FALSE,
  \* Actuator variables
  ActuatorMode = "Inactive",
  ActuatorConnectivity = "Connected",
  ActuatorReceivedDInfo = FALSE

process Sensor = "sensor"
begin
  sensor_loop:
  while TRUE do
    \* Non-deterministically set sensor mode
    either
      SensorMode := "Active"
    or
      SensorMode := "Inactive"
    end either;
    \* Non-deterministically set sensor connectivity
    either
      SensorConnectivity := "Connected"
    or
      SensorConnectivity := "NotConnected"
    end either;
    \* Set SnSensedDisaster based on mode
    if SensorMode = "Active" then
      either SnSensedDisaster  := TRUE or SnSensedDisaster := FALSE end either
    else
      SnSensedDisaster := FALSE
    end if;
    \* Transmit data if connected
    if SensorConnectivity = "Connected" then
      SnTransmittedDInfo := SnSensedDisaster 
    else
      SnTransmittedDInfo := FALSE
    end if
  end while
end process

process Gateway = "gateway"
begin
  gateway_loop:
  while TRUE do
    GwReceivedDInfo := SnTransmittedDInfo; 
    \* Relay to both BaseStation and Actuator in parallel
    GwRelayedDinfoToBS := GwReceivedDInfo;
    GwRelayedDinfoToActuator := GwReceivedDInfo
  end while
end process

process BaseStation = "basestation"
begin
  bs_loop:
  while TRUE do
    BsReceivedDData := GwRelayedDinfoToBS;
    BsBroadcastDInfo := BsReceivedDData;
    DisasterDetected := BsBroadcastDInfo 
  end while
end process

\* New Actuator process
process Actuator = "actuator"
begin
  actuator_loop:
  while TRUE do
    \* Actuator is always connected to gateway
    ActuatorConnectivity := "Connected";
    \* Receive disaster info from gateway
    ActuatorReceivedDInfo := GwRelayedDinfoToActuator;
    \* Set actuator mode based on received info
    if ActuatorReceivedDInfo = TRUE then
      ActuatorMode := "Active"
    else
      ActuatorMode := "Inactive"
    end if
  end while
end process

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "cba1f27e" /\ chksum(tla) = "713c8db")
VARIABLES SensorMode, SensorConnectivity, SnSensedDisaster, 
          SnTransmittedDInfo, GwReceivedDInfo, GwRelayedDinfoToBS, 
          GwRelayedDinfoToActuator, BsReceivedDData, BsBroadcastDInfo, 
          DisasterDetected, ActuatorMode, ActuatorConnectivity, 
          ActuatorReceivedDInfo
vars == << SensorMode, SensorConnectivity, SnSensedDisaster, 
           SnTransmittedDInfo, GwReceivedDInfo, GwRelayedDinfoToBS, 
           GwRelayedDinfoToActuator, BsReceivedDData, BsBroadcastDInfo, 
           DisasterDetected, ActuatorMode, ActuatorConnectivity, 
           ActuatorReceivedDInfo >>
ProcSet == {"sensor"} \cup {"gateway"} \cup {"basestation"} \cup {"actuator"}
Init == (* Global variables *)
        /\ SensorMode = "Inactive"
        /\ SensorConnectivity = "NotConnected"
        /\ SnSensedDisaster = FALSE
        /\ SnTransmittedDInfo = FALSE
        /\ GwReceivedDInfo = FALSE
        /\ GwRelayedDinfoToBS = FALSE
        /\ GwRelayedDinfoToActuator = FALSE
        /\ BsReceivedDData = FALSE
        /\ BsBroadcastDInfo = FALSE
        /\ DisasterDetected = FALSE
        /\ ActuatorMode = "Inactive"
        /\ ActuatorConnectivity = "Connected"
        /\ ActuatorReceivedDInfo = FALSE
Sensor == /\ \/ /\ SensorMode' = "Active"
             \/ /\ SensorMode' = "Inactive"
          /\ \/ /\ SensorConnectivity' = "Connected"
             \/ /\ SensorConnectivity' = "NotConnected"
          /\ IF SensorMode' = "Active"
                THEN /\ \/ /\ SnSensedDisaster' = TRUE
                        \/ /\ SnSensedDisaster' = FALSE
                ELSE /\ SnSensedDisaster' = FALSE
          /\ IF SensorConnectivity' = "Connected"
                THEN /\ SnTransmittedDInfo' = SnSensedDisaster'
                ELSE /\ SnTransmittedDInfo' = FALSE
          /\ UNCHANGED << GwReceivedDInfo, GwRelayedDinfoToBS, 
                          GwRelayedDinfoToActuator, BsReceivedDData, 
                          BsBroadcastDInfo, DisasterDetected, ActuatorMode, 
                          ActuatorConnectivity, ActuatorReceivedDInfo >>
Gateway == /\ GwReceivedDInfo' = SnTransmittedDInfo
           /\ GwRelayedDinfoToBS' = GwReceivedDInfo'
           /\ GwRelayedDinfoToActuator' = GwReceivedDInfo'
           /\ UNCHANGED << SensorMode, SensorConnectivity, SnSensedDisaster, 
                           SnTransmittedDInfo, BsReceivedDData, 
                           BsBroadcastDInfo, DisasterDetected, ActuatorMode, 
                           ActuatorConnectivity, ActuatorReceivedDInfo >>
BaseStation == /\ BsReceivedDData' = GwRelayedDinfoToBS
               /\ BsBroadcastDInfo' = BsReceivedDData'
               /\ DisasterDetected' = BsBroadcastDInfo'
               /\ UNCHANGED << SensorMode, SensorConnectivity, 
                               SnSensedDisaster, SnTransmittedDInfo, 
                               GwReceivedDInfo, GwRelayedDinfoToBS, 
                               GwRelayedDinfoToActuator, ActuatorMode, 
                               ActuatorConnectivity, ActuatorReceivedDInfo >>
Actuator == /\ ActuatorConnectivity' = "Connected"
            /\ ActuatorReceivedDInfo' = GwRelayedDinfoToActuator
            /\ IF ActuatorReceivedDInfo' = TRUE
                  THEN /\ ActuatorMode' = "Active"
                  ELSE /\ ActuatorMode' = "Inactive"
            /\ UNCHANGED << SensorMode, SensorConnectivity, SnSensedDisaster, 
                            SnTransmittedDInfo, GwReceivedDInfo, 
                            GwRelayedDinfoToBS, GwRelayedDinfoToActuator, 
                            BsReceivedDData, BsBroadcastDInfo, 
                            DisasterDetected >>

Next == Sensor \/ Gateway \/ BaseStation \/ Actuator
Spec == Init /\ [][Next]_vars
=============================================
