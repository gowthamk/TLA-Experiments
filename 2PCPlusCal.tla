----------------------------- MODULE 2PCPlusCal ------------------------------
CONSTANT RM \* The set of resource managers
(****************************************************************************)
(*--algorithm TwoPhase {

    variables rmState = [rm \in RM |-> "working"], 
              tmState = "init",
              tmPrepared = {},
              msgs = {};

    fair process (RManager \in RM) {
        T1: await rmState[self] = "working";
            either {
                rmState[self] := "prepared";
                msgs := msgs \cup {[type |-> "Prepared", rm |-> self]};
            } or {
                rmState[self] := "aborted";
            } or {
                await [type |-> "Commit"] \in msgs;
                rmState[self] := "committed";
            } or {
                await [type |-> "Abort"] \in msgs;
                rmState[self] := "aborted";
            }
    }

    fair process (TManager = 999) {
        T2: await tmState = "init";
        either {
            await [type |-> "Prepared", rm |-> rm] \in msgs;
            tmPrepared := tmPrepared \cup {rm};
        } or {
            await tmPrepared = RM;
            tmState := "committed";
            msgs := msgs \cup {[type |-> "Commit"]};
        } or {
            tmState := "aborted";
            msgs := msgs \cup {[type |-> "Abort"]};
        }
    }
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "89ae9bf" /\ chksum(tla) = "42513246")
VARIABLES rmState, tmState, tmPrepared, msgs, pc

vars == << rmState, tmState, tmPrepared, msgs, pc >>

ProcSet == (RM) \cup {999}

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        /\ tmPrepared = {}
        /\ msgs = {}
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "T1"
                                        [] self = 999 -> "T2"]

T1(self) == /\ pc[self] = "T1"
            /\ rmState[self] = "working"
            /\ \/ /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                  /\ msgs' = (msgs \cup {[type |-> "Prepared", rm |-> self]})
               \/ /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                  /\ msgs' = msgs
               \/ /\ [type |-> "Commit"] \in msgs
                  /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                  /\ msgs' = msgs
               \/ /\ [type |-> "Abort"] \in msgs
                  /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                  /\ msgs' = msgs
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << tmState, tmPrepared >>

RManager(self) == T1(self)

T2 == /\ pc[999] = "T2"
      /\ tmState = "init"
      /\ \/ /\ [type |-> "Prepared", rm |-> rm] \in msgs
            /\ tmPrepared' = (tmPrepared \cup {rm})
            /\ UNCHANGED <<tmState, msgs>>
         \/ /\ tmPrepared = RM
            /\ tmState' = "committed"
            /\ msgs' = (msgs \cup {[type |-> "Commit"]})
            /\ UNCHANGED tmPrepared
         \/ /\ tmState' = "aborted"
            /\ msgs' = (msgs \cup {[type |-> "Abort"]})
            /\ UNCHANGED tmPrepared
      /\ pc' = [pc EXCEPT ![999] = "Done"]
      /\ UNCHANGED rmState

TManager == T2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == TManager
           \/ (\E self \in RM: RManager(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in RM : WF_vars(RManager(self))
        /\ WF_vars(TManager)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================
