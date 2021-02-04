---- MODULE seq_bank_account ----
EXTENDS TLC, Integers
CONSTANT BAL

(* --algorithm transfer
variables alice = BAL, bob = BAL, money \in 1..20;
begin
    A: alice := alice - money;
    B: bob := bob + money;
    C: assert alice >= 0;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-db8618f57c384c166366ca480067999b
VARIABLES alice, bob, money, pc

vars == << alice, bob, money, pc >>

Init == (* Global variables *)
        /\ alice = BAL
        /\ bob = BAL
        /\ money \in 1..20
        /\ pc = "A"

A == /\ pc = "A"
     /\ alice' = alice - money
     /\ pc' = "B"
     /\ UNCHANGED << bob, money >>

B == /\ pc = "B"
     /\ bob' = bob + money
     /\ pc' = "C"
     /\ UNCHANGED << alice, money >>

C == /\ pc = "C"
     /\ Assert(alice >= 0, "Failure of assertion at line 10, column 8.")
     /\ pc' = "Done"
     /\ UNCHANGED << alice, bob, money >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A \/ B \/ C
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a2c36c40b04264302019bd4ab607967b

====
