---- MODULE MC ----
EXTENDS DisasterDetection, TLC

\* CONSTANT definitions @modelParameterConstants:0InputIndicators
const_177011095618911000 == 
{"tremor", "shaking", "crack", "water", "flood"}
----

\* CONSTANT definitions @modelParameterConstants:1IndicatorsByDisaster
const_177011095618912000 == 
<<
{"tremor", "shaking", "seismic", "crack", "aftershock"},
{"water", "flood", "rain", "current", "inundation"},     
{"smoke", "flame", "heat", "fire", "ash"}
>>
----

\* CONSTANT definitions @modelParameterConstants:3DisasterNames
const_177011095618913000 == 
<< "Earthquake", "Flood", "Wildfire" >>
----

=============================================================================
\* Modification History
\* Created Tue Feb 03 14:29:16 PKT 2026 by muhta
