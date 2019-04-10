------------------------------------------MODULE ClickHouseQuorum-------------------------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANTS 
    Replicas,
    QuorumCount
    
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

GetReplicasWithPart(part) == {replica \in Replicas: part \in replicaState[replica].local_parts}

Init ==
    /\ log = <<>>
    /\ replicaState = [replica \in Replicas |-> [log_pointer |-> NULL,
                                                 local_parts |-> {}]]
    /\ nextRecordId = 1
    /\ quorum = [value |-> NULL,
                 replicas |-> {}]
                 
FetchLog(replica) == /\ replicaState' = [replicaState EXCEPT ![replica] = [
                                         log_pointer |-> @.log_pointer + 1,
                                         local_parts |-> @.local_parts \union {log[@.log_pointer + 1]}]]
                 
AppendQuorum(replica) == IF Cardinality(quorum.replicas) >= (QuorumCount - 1) THEN quorum' = [value |-> NULL,
                                                                                              replicas |-> {}]
                         ELSE quorum' = [value |-> quorum.value,
                                         replicas |-> quorum.replicas \union {replica}]
    
ExecuteLog == 
    /\ Len(log) > 0
    /\ \E replica \in Replicas :
        /\ replicaState[replica].log_pointer < (Len(log) - 1)
        /\ FetchLog(replica)
    /\ UNCHANGED <<log, nextRecordId, quorum>>
    
UpdateQuorum == 
    /\ quorum.value # NULL
    /\ \E replica \in Replicas :
        /\ replica \notin quorum.replicas
        /\ replicaState[replica].log_pointer = (Len(log) - 1)
        /\ AppendQuorum(replica)
        /\ FetchLog(replica)
    /\ UNCHANGED <<log, nextRecordId>>
 
QuorumInsert == 
    /\ quorum.value = NULL
    /\ quorum' = [replicas |-> {},
                  value |-> nextRecordId]
    /\ log' = Append(log, nextRecordId)
    /\ nextRecordId' = nextRecordId + 1
    /\ UNCHANGED <<replicaState>>
    
Next ==
    \/ ExecuteLog
    \/ UpdateQuorum
    \/ QuorumInsert

Spec == Init /\ [][Next]_vars
             /\ WF_vars(Next)
             
QuorumSelect == [](Len(log) = 0 \/ \A i \in 1..Len(log): Cardinality(GetReplicasWithPart(log[i])) >= QuorumCount \/ quorum.value = log[i])
======================================================================