---- MODULE Foreach ----
EXTENDS TLC, Integers, FiniteSets
CONSTANT RM
(*--algorithm Foreach {
    variable s = RM;
    {
        L1: while (s#{}) {
            with (i \in s) {
                print i;
                s := s \ {i};
            }    
        };
    }
}
end algorithm;*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b09234aaebcd3c960fc52c502682e524
VARIABLES s, pc

vars == << s, pc >>

Init == (* Global variables *)
        /\ s = RM
        /\ pc = "L1"

L1 == /\ pc = "L1"
      /\ IF s#{}
            THEN /\ \E i \in s:
                      /\ PrintT(i)
                      /\ s' = s \ {i}
                 /\ pc' = "L1"
            ELSE /\ pc' = "Done"
                 /\ s' = s

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == L1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-beaed52b575b0f3bc9f83fe60978c091


====
