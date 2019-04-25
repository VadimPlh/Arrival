------------------------------------------MODULE ClickHouseQuorum-------------------------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANTS 
    Replicas,
    QuorumCount,
    LogLength,
    HistoryLength
    
NONE == "NONE"
NULL == 0

ASSUME 
    /\ NONE \notin Replicas

VARIABLES
    \* Log in zookeeper.
    log,

    \* State replica. Active or not and e.t.c
    replicaState,

    \* Unique id generator for new records in log.
    nextRecordId,
    
    \* Quorum, in ZK.
    quorum,
    
    lastAddedValue,
    
    \* Variabe for check properties.
    history
    
vars == <<log, replicaState, nextRecordId, quorum, lastAddedValue, history>>

IsActive(replica) == replicaState[replica].is_active

GetReplicasWithPart(part) == {replica \in Replicas: part \in replicaState[replica].local_parts}

GetSelectFromHistory(h) == {record \in h: record.type = "Read"}

Max(S) == IF S # {} THEN CHOOSE x \in S:
                      /\ \A y \in S \ {x}:
                          y <= x
          ELSE 0

Init ==
    /\ log = <<>>
    /\ replicaState = [replica \in Replicas |-> [log_pointer |-> NULL,
                                                 local_parts |-> {}]]
    /\ nextRecordId = 1
    /\ quorum = [value |-> NULL,
                 replicas |-> {}]
    /\ lastAddedValue = NULL
    /\ history = <<>>
                 
FetchLog(replica) == /\ replicaState' = [replicaState EXCEPT ![replica] = [
                                         log_pointer |-> @.log_pointer + 1,
                                         local_parts |-> @.local_parts \union {log[@.log_pointer + 1]}]]
                 
AppendQuorum(replica) == IF Cardinality(quorum.replicas) >= (QuorumCount - 1) THEN /\ quorum' = [value |-> NULL,
                                                                                                 replicas |-> {}]
                                                                                   /\ history' = Append(history, [type |-> "Write",
                                                                                                                  data |-> quorum.value])
                                                                                   /\ lastAddedValue' = quorum.value
                         ELSE /\ quorum' = [value |-> quorum.value,
                                            replicas |-> quorum.replicas \union {replica}]
                              /\ history' = history
                              /\ lastAddedValue' = lastAddedValue
                              
GetMaxAddedPart == IF quorum.value # NULL THEN log[Len(log) - 1]
                   ELSE log[Len(log)]
    
ExecuteLog == 
    /\ Len(log) > 0
    /\ \E replica \in Replicas :
        /\ replicaState[replica].log_pointer < (Len(log) - 1)
        /\ FetchLog(replica)
    /\ UNCHANGED <<log, nextRecordId, quorum, lastAddedValue, history>>
    
UpdateQuorum == 
    /\ quorum.value # NULL
    /\ \E replica \in Replicas :
        /\ replica \notin quorum.replicas
        /\ replicaState[replica].log_pointer = (Len(log) - 1)
        /\ AppendQuorum(replica)
        /\ FetchLog(replica)
    /\ UNCHANGED <<log, nextRecordId>>
 
QuorumInsert == 
    /\ Len(log) < LogLength
    /\ Len(history) < HistoryLength
    /\ quorum.value = NULL
    /\ quorum' = [replicas |-> {},
                  value |-> nextRecordId]
    /\ log' = Append(log, nextRecordId)
    /\ nextRecordId' = nextRecordId + 1
    /\ UNCHANGED <<replicaState, lastAddedValue, history>>
    
QuorumReadv1 ==
    /\ Len(log) > 0
    /\ Len(history) < HistoryLength
    /\ \E replica \in Replicas :
        /\ Cardinality(replicaState[replica].local_parts \ {quorum.value}) > 0
        /\ LET max_value == Max(replicaState[replica].local_parts \ {quorum.value})
           IN history' = Append(history, [type |-> "Read",
                                          data |-> max_value])
    /\ UNCHANGED <<log, replicaState, nextRecordId, quorum, lastAddedValue>>
    

QuorumReadv2 == 
    /\ Len(log) > 0
    /\ Len(history) < HistoryLength
    /\ \E replica \in Replicas :
        /\ lastAddedValue \in replicaState[replica].local_parts
        /\ LET max_value == Max(replicaState[replica].local_parts \ {quorum.value})
           IN history' = Append(history, [type |-> "Read",
                                          data |-> max_value])
    /\ UNCHANGED <<log, replicaState, nextRecordId, quorum, lastAddedValue>>
    
Next ==
    \/ ExecuteLog
    \/ UpdateQuorum
    \/ QuorumInsert
    \/ QuorumReadv2

Spec == Init /\ [][Next]_vars
             /\ SF_vars(QuorumInsert)
             /\ SF_vars(QuorumReadv2)
             
QuorumSelect == [](Len(log) = 0 \/ \A i \in 1..Len(log): Cardinality(GetReplicasWithPart(log[i])) >= QuorumCount \/ quorum.value = log[i])

Linearizability == \A i, j \in DOMAIN history : /\ i < j
                                                => history[j].data >= history[i].data
                                                
Monotonic(h) == \A i, j \in DOMAIN h : i <= j => h[i].data <= h[j].data

ReadAfterWrite == \A i, j \in DOMAIN history : /\ i < j
                                               /\ history[i].type = "Write"
                                               /\ history[j].type = "Read"
                                               => history[j].data >= history[i].data
                                               
Strong == /\ Linearizability
          /\ Monotonic(history)
          /\ ReadAfterWrite
======================================================================