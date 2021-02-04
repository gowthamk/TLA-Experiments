----------------------------- MODULE 2PC ------------------------------
EXTENDS Integers, FiniteSets, TLC
CONSTANT RM      \* The set of participating resource managers RM=1..3 
(****************************************************************************)
(*--algorithm TransactionCommit {
    variable rmState = [rm \in RM |-> "working"];
    define {
        canCommit ==    \A rm \in RM: rmState[rm] \in {"can_commit"}
        canAbort ==     \E rm \in RM : rmState[rm] \in {"aborted"}  
    }
    procedure setRMStates(m) 
    variable s = RM; {
        TS: while (s#{}) {
            with (p \in s) {
                rmState[p] := m;
                s := s \ {p};}}
    }
    fair process (RManager \in RM) {
        R1: await rmState[self] = "prepared";
        either {rmState[self] := "can_commit";} 
            or {rmState[self] := "aborted";};
    }
    fair process (TManager=0) {
        T1: call setRMStates("prepared");
        T2: either {await canCommit; call setRMStates("committed");} 
            or {await canAbort;call setRMStates("aborted");} 
    }
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "96844d41" /\ chksum(tla) = "c5edc252")
CONSTANT defaultInitValue
VARIABLES rmState, pc, stack

(* define statement *)
canCommit ==    \A rm \in RM: rmState[rm] \in {"can_commit"}
canAbort ==     \E rm \in RM : rmState[rm] \in {"aborted"}

VARIABLES m, s

vars == << rmState, pc, stack, m, s >>

ProcSet == (RM) \cup {0}

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]
        (* Procedure setRMStates *)
        /\ m = [ self \in ProcSet |-> defaultInitValue]
        /\ s = [ self \in ProcSet |-> RM]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "R1"
                                        [] self = 0 -> "T1"]

TS(self) == /\ pc[self] = "TS"
            /\ IF s[self]#{}
                  THEN /\ \E p \in s[self]:
                            /\ rmState' = [rmState EXCEPT ![p] = m[self]]
                            /\ s' = [s EXCEPT ![self] = s[self] \ {p}]
                       /\ pc' = [pc EXCEPT ![self] = "TS"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                       /\ UNCHANGED << rmState, s >>
            /\ UNCHANGED << stack, m >>

setRMStates(self) == TS(self)

R1(self) == /\ pc[self] = "R1"
            /\ rmState[self] = "prepared"
            /\ \/ /\ rmState' = [rmState EXCEPT ![self] = "can_commit"]
               \/ /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << stack, m, s >>

RManager(self) == R1(self)

T1 == /\ pc[0] = "T1"
      /\ /\ m' = [m EXCEPT ![0] = "prepared"]
         /\ stack' = [stack EXCEPT ![0] = << [ procedure |->  "setRMStates",
                                               pc        |->  "T2",
                                               s         |->  s[0],
                                               m         |->  m[0] ] >>
                                           \o stack[0]]
      /\ s' = [s EXCEPT ![0] = RM]
      /\ pc' = [pc EXCEPT ![0] = "TS"]
      /\ UNCHANGED rmState

T2 == /\ pc[0] = "T2"
      /\ \/ /\ canCommit
            /\ /\ m' = [m EXCEPT ![0] = "committed"]
               /\ stack' = [stack EXCEPT ![0] = << [ procedure |->  "setRMStates",
                                                     pc        |->  "Done",
                                                     s         |->  s[0],
                                                     m         |->  m[0] ] >>
                                                 \o stack[0]]
            /\ s' = [s EXCEPT ![0] = RM]
            /\ pc' = [pc EXCEPT ![0] = "TS"]
         \/ /\ canAbort
            /\ /\ m' = [m EXCEPT ![0] = "aborted"]
               /\ stack' = [stack EXCEPT ![0] = << [ procedure |->  "setRMStates",
                                                     pc        |->  "Done",
                                                     s         |->  s[0],
                                                     m         |->  m[0] ] >>
                                                 \o stack[0]]
            /\ s' = [s EXCEPT ![0] = RM]
            /\ pc' = [pc EXCEPT ![0] = "TS"]
      /\ UNCHANGED rmState

TManager == T1 \/ T2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == TManager
           \/ (\E self \in ProcSet: setRMStates(self))
           \/ (\E self \in RM: RManager(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in RM : WF_vars(RManager(self))
        /\ WF_vars(TManager) /\ WF_vars(setRMStates(0))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
