------------------------- MODULE DisasterDetection --------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS InputIndicators, DisasterNames,
          IndicatorsByDisaster
(* PlusCal algorithm for disaster identification *)

(* --algorithm DisasterDetection
variables DisasterMatches = [d \in 1..Len(DisasterNames) |-> 0],
          ProbableDisaster = "", HighestMatchCount = 0, i = 1,
          disasterIndicators, newMatchCount;
begin
 CountMatches:
  while i <= Len(DisasterNames) do
    (* Local variable assignments *)
    disasterIndicators := IndicatorsByDisaster[i];
    newMatchCount := Cardinality(disasterIndicators 
                     \intersect InputIndicators);
    DisasterMatches[i] := newMatchCount;
    i := i + 1;
  end while;
        
    (* Reset the counter for the next loop *)
    i := 1;

    DetermineDisaster:
        while i <= Len(DisasterNames) do
            if DisasterMatches[i] 
                > HighestMatchCount then
                ProbableDisaster := DisasterNames[i];
                HighestMatchCount := DisasterMatches[i];
            end if;
            i := i + 1;
        end while;
print(<<"Most Probable disaster based on indicators is: ",
       ProbableDisaster, " with ", HighestMatchCount,
       " matching indicators.">>);
end algorithm *)

\* BEGIN TRANSLATION (chksum(pcal) = "d50f0a22" /\ chksum(tla) = "45f40e27")
CONSTANT defaultInitValue
VARIABLES DisasterMatches, ProbableDisaster, HighestMatchCount, i, 
          disasterIndicators, newMatchCount, pc

vars == << DisasterMatches, ProbableDisaster, HighestMatchCount, i, 
           disasterIndicators, newMatchCount, pc >>

Init == (* Global variables *)
        /\ DisasterMatches =                [d \in
                             1..Len(DisasterNames) |-> 0]
        /\ ProbableDisaster = ""
        /\ HighestMatchCount = 0
        /\ i = 1
        /\ disasterIndicators = defaultInitValue
        /\ newMatchCount = defaultInitValue
        /\ pc = "CountMatches"

CountMatches == /\ pc = "CountMatches"
                /\ IF i <= Len(DisasterNames)
                      THEN /\ disasterIndicators' = IndicatorsByDisaster[i]
                           /\ newMatchCount' = Cardinality(disasterIndicators'
                                               \intersect InputIndicators)
                           /\ DisasterMatches' = [DisasterMatches EXCEPT ![i] = newMatchCount']
                           /\ i' = i + 1
                           /\ pc' = "CountMatches"
                      ELSE /\ i' = 1
                           /\ pc' = "DetermineDisaster"
                           /\ UNCHANGED << DisasterMatches, disasterIndicators, 
                                           newMatchCount >>
                /\ UNCHANGED << ProbableDisaster, HighestMatchCount >>

DetermineDisaster == /\ pc = "DetermineDisaster"
                     /\ IF i <= Len(DisasterNames)
                           THEN /\ IF DisasterMatches[i]
                                       > HighestMatchCount
                                      THEN /\ ProbableDisaster' = DisasterNames[i]
                                           /\ HighestMatchCount' = DisasterMatches[i]
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << ProbableDisaster, 
                                                           HighestMatchCount >>
                                /\ i' = i + 1
                                /\ pc' = "DetermineDisaster"
                           ELSE /\ PrintT((<<"Most Probable disaster based on indicators is: ",
                                              ProbableDisaster,
                                            " with ", HighestMatchCount, " matching indicators.">>))
                                /\ pc' = "Done"
                                /\ UNCHANGED << ProbableDisaster, 
                                                HighestMatchCount, i >>
                     /\ UNCHANGED << DisasterMatches, disasterIndicators, 
                                     newMatchCount >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == CountMatches \/ DetermineDisaster
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

================
