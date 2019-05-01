------------------------------------------MODULE ClickHouseQuorum-------------------------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANTS 
    Replicas,
    QuorumCount,
    LogLength,
    HistoryLength,
    NONE

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

(*
 * TLA+ utilities 
 *)
 
Range(f) == {f[x] : x \in DOMAIN f}

Max(S) == IF S # {} THEN CHOOSE x \in S:
                      /\ \A y \in S \ {x}:
                          y <= x
          ELSE 0

(*
 * Util for work with is_active status
 *)
 
IsActive(replica) == replicaState[replica].is_active
GetActiveReplicas == {replica \in Replicas: IsActive(replica)}
          
(*
 * TypeInv for model, because TLA+ is not statically typed
 *)
 
QuorumState == [value: Nat,
                replicas: SUBSET Replicas]
                
HistoryEventInsert == [type: "Write", event_id: Nat, data: Nat]
HistoryEventSelect == [type: "Read", event_id: Nat, data: Nat]
HistoryEvents == HistoryEventInsert \union HistoryEventSelect
 
TypeOK == /\ nextRecordId \in Nat
          /\ quorum \in QuorumState
          /\ lastAddedValue \in Nat
(*
 * Constructor for history events
 *)
 
GetHistoryId == Len(history) + 1

InsertEvents(value) == [type |-> "Write", event_id |-> GetHistoryId, data |-> value]
SelectEvents(value) == [type |-> "Read", event_id |-> GetHistoryId, data |-> value]

(*
 * Get smth for check Invarioants
 *)

GetReplicasWithPart(part) == {replica \in Replicas: part \in replicaState[replica].local_parts}

GetSelectFromHistory(h) == {record \in Range(h): record.type = "Read"}

GetMaxAddedPart == IF quorum.value # NONE THEN log[Len(log) - 1]
                   ELSE log[Len(log)]
                   
(*
 * Get record from log and update local_parts
 *) 

FetchLog(replica) == replicaState' = [replicaState EXCEPT ![replica] = [is_active |-> @.is_active,
                                                                        log_pointer |-> @.log_pointer + 1,
                                                                        local_parts |-> @.local_parts \union {log[@.log_pointer + 1]}]]

NULLQuorum == [value |-> NONE, replicas |-> {}]

Init ==
    /\ log = <<>>
    /\ replicaState = [replica \in Replicas |-> [is_active |-> TRUE,
                                                 log_pointer |-> NONE,
                                                 local_parts |-> {}]]
    /\ nextRecordId = 1
    /\ quorum = NULLQuorum
    /\ lastAddedValue = NONE
    /\ history = <<>>


BecomeInactive(replica) ==
    /\ replicaState' = [replicaState EXCEPT ![replica] = [is_active |-> FALSE,
                                                          log_pointer |-> @.log_pointer,
                                                          local_parts |-> @.local_parts]]
    /\ UNCHANGED <<log, nextRecordId, quorum, lastAddedValue, history>>
    
BecomeActive(replica) ==
    /\ replicaState' = [replicaState EXCEPT ![replica] = [is_active |-> TRUE,
                                                          log_pointer |-> @.log_pointer,
                                                          local_parts |-> @.local_parts]]
    /\ UNCHANGED <<log, nextRecordId, quorum, lastAddedValue, history>>

ExecuteLog(replica) == 
    /\ Len(log) > 0
    /\ \/ replicaState[replica].log_pointer < (Len(log) - 1)
       \/ /\ replicaState[replica].log_pointer = (Len(log) - 1)
          /\ quorum.value = NONE
    /\ FetchLog(replica)
    /\ UNCHANGED <<log, nextRecordId, quorum, lastAddedValue, history>>
    
UpdateQuorumReplicas(replica) == 
    /\ quorum' = [value |-> quorum.value,
                  replicas |-> quorum.replicas \union {replica}]
    
UpdateQuorum(replica) == 
    /\ quorum.value # NONE
    /\ replica \notin quorum.replicas
    /\ quorum.replicas \intersect GetActiveReplicas # {}
    /\ replicaState[replica].log_pointer = (Len(log) - 1)
    /\ UpdateQuorumReplicas(replica)
    /\ FetchLog(replica)
    /\ UNCHANGED <<log, nextRecordId, history, lastAddedValue>>
    
FailedQuorum(replica) ==
    /\ quorum.value # NONE
    /\ replica \notin quorum.replicas
    /\ quorum.replicas \intersect GetActiveReplicas = {}
    /\ quorum' = NULLQuorum
    /\ UNCHANGED <<log, replicaState, nextRecordId, lastAddedValue, history>>
    
EndQuorum(replica) ==
    /\ quorum.value # NONE
    /\ replica \in quorum.replicas
    /\ Cardinality(quorum.replicas) >= QuorumCount
    /\ quorum' = NULLQuorum
    /\ history' = Append(history, InsertEvents(quorum.value))
    /\ lastAddedValue' = quorum.value
    /\ UNCHANGED <<log, replicaState, nextRecordId>>
 
QuorumInsert == 
    /\ Len(log) < LogLength
    /\ quorum.value = NONE
    /\ quorum' = [replicas |-> {},
                  value |-> nextRecordId]
    /\ log' = Append(log, nextRecordId)
    /\ nextRecordId' = nextRecordId + 1
    /\ UNCHANGED <<replicaState, lastAddedValue, history>>
    
QuorumReadv1 ==
    /\ Len(log) > 0
    /\ Cardinality(GetSelectFromHistory(history)) < HistoryLength
    /\ \E replica \in Replicas :
        /\ Cardinality(replicaState[replica].local_parts \ {quorum.value}) > 0
        /\ LET max_value == Max(replicaState[replica].local_parts \ {quorum.value})
           IN history' = Append(history, SelectEvents(max_value))
    /\ UNCHANGED <<log, replicaState, nextRecordId, quorum, lastAddedValue>>
    

QuorumReadv2 == 
    /\ Len(log) > 0
    /\ Cardinality(GetSelectFromHistory(history)) < HistoryLength
    /\ \E replica \in Replicas :
        /\ lastAddedValue \in replicaState[replica].local_parts
        /\ LET max_value == Max(replicaState[replica].local_parts \ {quorum.value})
           IN history' = Append(history, SelectEvents(max_value))
    /\ UNCHANGED <<log, replicaState, nextRecordId, quorum, lastAddedValue>>
    
LegitimateTermination ==
    /\ Len(log) = LogLength
    /\ Cardinality(GetSelectFromHistory(history)) = HistoryLength
    /\ UNCHANGED vars
    
Next ==
    \/ \E replica \in Replicas:
        \/ /\ IsActive(replica)
           /\ \/ ExecuteLog(replica)
              \/ UpdateQuorum(replica)
              \/ EndQuorum(replica)
              \/ BecomeInactive(replica)
              \/ FailedQuorum(replica)
        \/ /\ ~IsActive(replica)
           /\ BecomeActive(replica)
    \/ QuorumInsert
    \/ QuorumReadv2
    \/ LegitimateTermination

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