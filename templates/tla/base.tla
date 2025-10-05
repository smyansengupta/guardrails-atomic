---------------------------- MODULE {{MODULE_NAME}} ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS {{CONSTANTS}}

VARIABLES {{VARIABLES}}

vars == <<{{VARS_TUPLE}}>>

\* Type invariant
TypeOK == {{TYPE_INVARIANT}}

\* Initial state
Init == {{INIT_CONDITION}}

\* Actions
{{ACTIONS}}

\* Next state relation
Next == {{NEXT_RELATION}}

\* Invariants
{{INVARIANTS}}

\* Specification
Spec == Init /\ [][Next]_vars

\* Theorem
THEOREM Spec => [](TypeOK {{INVARIANT_CONJUNCTION}})
=============================================================================
