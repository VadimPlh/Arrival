-------------------------------- MODULE MCTruncateLog -------------------------------
EXTENDS TruncateLog, TLC
-----------------------------------------------------------------------------
CONSTANTS a1, a2, a3, a4  \* Records id
CONSTANTS r1, r2, r3      \* Replicas

MCRecordsId == {a1, a2, a3, a4}
MCReplicas == {r1, r2, r3}

=============================================================================
