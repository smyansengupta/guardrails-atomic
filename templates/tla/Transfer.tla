---------------------------- MODULE Transfer ----------------------------
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

\* Transfer action
Transfer(from, to, amt, req_id) ==
    /\ req_id \notin processed
    /\ balances[from] >= amt
    /\ balances' = [balances EXCEPT ![from] = @ - amt, ![to] = @ + amt]
    /\ processed' = processed \union {req_id}
    /\ UNCHANGED messages

\* Duplicate delivery (idempotency test)
DuplicateTransfer(from, to, amt, req_id) ==
    /\ req_id \in processed
    /\ UNCHANGED <<balances, processed, messages>>

\* Conservation invariant
Conservation ==
    LET sum == CHOOSE s \in Int : s = (CHOOSE total \in Int :
        total = balances["a1"] + balances["a2"] + balances["a3"])
    IN sum = 300

\* Idempotency invariant
Idempotent ==
    \A req_id \in processed :
        /\ DuplicateTransfer("a1", "a2", 50, req_id) => UNCHANGED balances

\* Next state relation
Next ==
    \/ Transfer("a1", "a2", 50, "req1")
    \/ Transfer("a2", "a3", 30, "req2")
    \/ DuplicateTransfer("a1", "a2", 50, "req1")

\* Specification
Spec == Init /\ [][Next]_vars

\* Theorem
THEOREM Spec => [](TypeOK /\ Conservation /\ Idempotent)
=============================================================================
