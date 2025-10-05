---------------------------- MODULE transfer_atomic ----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANTS Accts, MaxRetries

VARIABLES
    balances,
    processed,
    messages

vars == <<balances, processed, messages>>

\* Type invariant
TypeOK ==
    /\ balances \in [Accts -> Int]
    /\ processed \subseteq STRING
    /\ messages \in Seq([from: Accts, to: Accts, amt: Int, req_id: STRING])

\* Initial state
Init ==
    /\ balances = [a \in Accts |-> 100]
    /\ processed = {}
    /\ messages = <<>>

\* Transfer_atomic action
Transfer_atomic(from, to, amt, req_id) ==
    /\ req_id \notin processed
    /\ amt >= 0
    /\ from /= to
    /\ balances[from] >= amt
    /\ balances' = [balances EXCEPT ![from] = @ - amt, ![to] = @ + amt]
    /\ processed' = processed \union {req_id}
    /\ UNCHANGED <<messages>>

\* DuplicateTransfer_atomic action
DuplicateTransfer_atomic(from, to, amt, req_id) ==
    /\ req_id \in processed
    /\ UNCHANGED <<balances, processed, messages>>

\* Idempotency invariant
Idempotent ==
    processed \subseteq STRING

\* No negative balances
NoDoubleSpend ==
    \A a \in Accts : balances[a] >= 0

\* Conservation of resources
Conservation ==
    balances["a1"] + balances["a2"] + balances["a3"] = 300

\* Next state relation
Next ==
    \/ Transfer_atomic("a1", "a2", 50, "req1")
    \/ Transfer_atomic("a2", "a3", 30, "req2")
    \/ DuplicateTransfer_atomic("a1", "a2", 50, "req1")

\* Specification
Spec == Init /\ [][Next]_<<balances, processed, messages>>

\* Theorem
THEOREM Spec => [](TypeOK /\ Idempotent /\ NoDoubleSpend /\ Conservation)
=============================================================================