---------------------------- MODULE IdempotentWrite ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Keys, Values

VARIABLES
    store,
    processed

vars == <<store, processed>>

\* Type invariant
TypeOK ==
    /\ store \in [Keys -> Values]
    /\ processed \subseteq STRING

\* Initial state
Init ==
    /\ store = [k \in Keys |-> "initial"]
    /\ processed = {}

\* Write action
Write(key, value, req_id) ==
    /\ req_id \notin processed
    /\ store' = [store EXCEPT ![key] = value]
    /\ processed' = processed \union {req_id}

\* Duplicate write (idempotency test)
DuplicateWrite(key, value, req_id) ==
    /\ req_id \in processed
    /\ UNCHANGED <<store, processed>>

\* Idempotency invariant
Idempotent ==
    \A req_id \in processed :
        \A key \in Keys :
            \A value \in Values :
                DuplicateWrite(key, value, req_id) => UNCHANGED store

\* Next state relation
Next ==
    \/ Write("k1", "v1", "req1")
    \/ Write("k2", "v2", "req2")
    \/ DuplicateWrite("k1", "v1", "req1")

\* Specification
Spec == Init /\ [][Next]_vars

\* Theorem
THEOREM Spec => [](TypeOK /\ Idempotent)
=============================================================================
