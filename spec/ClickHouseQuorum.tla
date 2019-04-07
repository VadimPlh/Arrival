------------------------------------------MODULE ClickHouseQuorum-------------------------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANTS 
    Replicas,
    LenLog,
    QuorunCount
    
NONE == "NONE"
NULL == 0

ASSUME 
    /\ NONE \notin Replicas

VARIABLES
    \* Log in zookeeper.
    log,

    \* State replica. Active or not and e.t.c
    replicaState,

    \* Unique id generator for new records in log
    nextRecordId,
    
    \* Quoru, in ZK
    quorum
    
vars == <<log, replicaState, nextRecordId, quorum>>

IsActive(replica) == replicaState[replica].is_active


Init ==
    /\ log = <<>>
    /\ replicaState = [replica \in Replicas |-> [is_active |-> TRUE,
                                                 log_pointer |-> NULL,
                                                 local_log |-> <<>>]]
    /\ nextRecordId = 1
    /\ quorum = [val |-> NULL,
                 replicas |-> {}]
                 
AppendQuorum(replica) == quorum' = [val |-> quorum.val,
                                    replicas |-> quorum.replicas \union {replica}]
                                   
FetchLog(replica) == replicaState' = [replicaState EXCEPT ![replica] = [
                                      is_active |-> TRUE,
                                      log_pointer |-> @.log_pointer + 1,
                                      local_log |-> Append(@.local_log, log[@.log_pointer + 1])]]
    
ExecuteLog == \E replica \in Replicas :
    /\ IsActive(replica)
    /\ IF replicaState[replica].log_pointer = Len(log) THEN AppendQuorum(replica)
       ELSE FetchLog(replica)
    /\ UNCHANGED <<log, replicaState, quorum>>
 
QuorumInsert == \E replica \in Replicas :
    /\ IsActive(replica)
    /\ quorum.value = NULL
    /\ quorum' = [replicas |-> {replica},
                 value |-> nextRecordId]
    /\ nextRecordId' = nextRecordId + 1
    /\ UNCHANGED <<log, replicaState>>
    
AppendQuorumReplicas == \E replica \in Replicas :
    /\ replicaState[replica].active = TRUE
    /\ replica \notin quorum.replicas
    /\ quorum' = [replicas |-> quorum.replicas \union {replica},
                 value |-> quorum.value]
    
    /\ UNCHANGED <<log, replicaState, nextRecordId>>
    
Next ==
    \/ ExecuteLog
    \/ QuorumInsert
    \/ AppendQuorumReplicas

Spec == Init /\ [][Next]_vars
======================================================================