------------------------------------------MODULE ClickHouseQuorum-------------------------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets, Util

CONSTANTS 
    QuorumCount,
    HistoryLength

VARIABLES    
    \* Quorum, in ZK.
    quorum,
    
    failedParts,
    
    lastAddeddata,
    
    \* Variabe for check properties.
    history
    
vars == <<log, replicaState, nextRecordData, quorum, failedParts, lastAddeddata, history>>

          
(*
 * TypeInv for model, because TLA+ is not statically typed
 *)
 
QuorumState == [data: Nat,
                replicas: SUBSET Replicas,
                id: Nat \union NONE]
                
HistoryEventInsert == [type: "Write", event_id: Nat, data: Nat]
HistoryEventSelect == [type: "Read", event_id: Nat, data: Nat]
HistoryEvents == HistoryEventInsert \union HistoryEventSelect
 
TypeOK == /\ nextRecordData \in Nat
          /\ quorum \in QuorumState
          /\ lastAddeddata \in Nat
 
GetCommitedId == {record_id \in GetIds(log): record_id \notin GetIds(failedParts) /\ record_id # quorum.id}

(*
 * Get id for new record
 *)
 
GetNewRecordId == IF \E new_id \in RecordsId: 
    /\ new_id \notin GetCommitedId
    /\ new_id \notin GetIds(failedParts) THEN CHOOSE new_id \in RecordsId: 
    /\ new_id \notin GetCommitedId
    /\ new_id \notin GetIds(failedParts)
    ELSE NONE

(*
 * Constructor for history events
 *)
 
GetHistoryId == Len(history) + 1

InsertEvents(data) == [type |-> "Write", event_id |-> GetHistoryId, data |-> data]
SelectEvents(data) == [type |-> "Read", event_id |-> GetHistoryId, data |-> data]

(*
 * Get smth for check Invarioants
 *)

GetSelectFromHistory(h) == {record \in Range(h): record.type = "Read"}

(*
 * Utilities for work with Quorum
 *)

IsCurrentQuorum(id) == id = quorum.id
IsReplicaInQuorum(replica) == replica \in quorum.replicas
UpdateQuorumReplicas(replica) == quorum' = [data |-> quorum.data,
                                            replicas |-> quorum.replicas \union {replica},
                                            id |-> quorum.id]
                                            
QuorumIsAlive == /\ quorum.replicas # {}
                 /\ GetActiveReplicas \intersect quorum.replicas = {}
                 
UpdateFailedParts(id, value) == failedParts' = Append(failedParts, [id |-> id, data |-> value])

IncData == nextRecordData' = nextRecordData + 1         

NullQuorum == [data |-> NONE, replicas |-> {}, id |-> NONE]

Init ==
    /\ InitLog
    /\ InitReplicaState
    /\ InitNextRecordData
    /\ quorum = NullQuorum
    /\ lastAddeddata = NONE
    /\ failedParts = <<>>
    /\ history = <<>>

    
BecomeActive(replica) ==
    /\ RepicaStartActive(replica)
    /\ UNCHANGED <<log, nextRecordData, quorum, failedParts, lastAddeddata, history>>
    
BecomeInactive(replica) ==
    /\ RepicaStartInactive(replica)
    /\ UNCHANGED <<log, nextRecordData, quorum, failedParts,lastAddeddata, history>>

ExecuteLog(replica) == 
    /\ replicaState[replica].log_pointer <= Len(log)
    /\ ~IsCurrentQuorum(log[replicaState[replica].log_pointer].id)
    /\ quorum.id \notin GetIds(failedParts)
    /\ FetchLog(replica)
    /\ UNCHANGED <<log, nextRecordData, quorum, failedParts, lastAddeddata, history>>
    
UpdateQuorum(replica) == 
    /\ replicaState[replica].log_pointer = Len(log)
    /\ IsCurrentQuorum(log[replicaState[replica].log_pointer].id)
    /\ ~IsReplicaInQuorum(replica)
    /\ ~QuorumIsAlive
    /\ UpdateQuorumReplicas(replica)
    /\ FetchLog(replica)
    /\ UNCHANGED <<log, nextRecordData, history, failedParts, lastAddeddata>>
    
FailedQuorum(replica) ==
    /\ replicaState[replica].log_pointer = Len(log)
    /\ IsCurrentQuorum(log[replicaState[replica].log_pointer].id)
    /\ ~IsReplicaInQuorum(replica)
    /\ QuorumIsAlive
    /\ UpdateFailedParts(quorum.id, quorum.data)
    /\ quorum' = NullQuorum
    /\ UNCHANGED <<log, replicaState, nextRecordData, lastAddeddata, history>>
    
EndQuorum(replica) ==
    /\ quorum.id # NONE
    /\ IsReplicaInQuorum(replica)
    /\ Cardinality(quorum.replicas) >= QuorumCount
    /\ quorum' = NullQuorum
    /\ history' = Append(history, InsertEvents(quorum.data))
    /\ lastAddeddata' = quorum.data
    /\ UNCHANGED <<log, replicaState, nextRecordData, failedParts>>
 
QuorumInsert == 
    /\ quorum.id = NONE
    /\ LET new_record_id == GetNewRecordId
       IN  /\ new_record_id # NONE
           /\ quorum' = [replicas |-> {},
                         data |-> nextRecordData,
                         id |-> new_record_id]
           /\ log' = Append(log, [data |-> nextRecordData,
                               id |-> new_record_id])
    /\ IncData
    /\ UNCHANGED <<replicaState, lastAddeddata, history, failedParts>>
    
QuorumReadv1 ==
    /\ Len(log) > 0
    /\ Cardinality(GetSelectFromHistory(history)) < HistoryLength
    /\ \E replica \in Replicas :
        /\ Cardinality(replicaState[replica].local_parts \ {quorum.data}) > 0
        /\ LET max_data == Max(replicaState[replica].local_parts \ {quorum.data})
           IN history' = Append(history, SelectEvents(max_data))
    /\ UNCHANGED <<log, replicaState, nextRecordData, quorum, lastAddeddata, failedParts>>
    

QuorumReadv2 == 
    /\ Len(log) > 0
    /\ Cardinality(GetSelectFromHistory(history)) < HistoryLength
    /\ \E replica \in Replicas :
        /\ lastAddeddata \in replicaState[replica].local_parts
        /\ LET max_data == Max(replicaState[replica].local_parts \ ({quorum.data} \union GetData(failedParts)))
           IN history' = Append(history, SelectEvents(max_data))
    /\ UNCHANGED <<log, replicaState, nextRecordData, quorum, lastAddeddata, failedParts>>
    
LegitimateTermination ==
    /\ GetIds(failedParts) \union GetCommitedId = RecordsId
    /\ Cardinality(GetSelectFromHistory(history)) = HistoryLength
    /\ UNCHANGED vars
    
Next ==
    \/ \E replica \in Replicas:
        \/ IsActive(replica)
            /\ \/ ExecuteLog(replica)
               \/ UpdateQuorum(replica)
               \/ EndQuorum(replica)
               \/ BecomeInactive(replica)
               \/ FailedQuorum(replica)
        \/ ~IsActive(replica)
            /\ BecomeActive(replica)
    \/ QuorumInsert
    \/ QuorumReadv2
    \/ LegitimateTermination

Spec == Init /\ [][Next]_vars
             /\ SF_vars(QuorumInsert)
             /\ SF_vars(QuorumReadv2)



          
QuorumSelect == [](Len(log) = 0 \/ \A i \in 1..Len(log): Cardinality(GetReplicasWithPart(log[i].data)) >= QuorumCount \/ quorum.id = log[i].id \/ log[i].id \in GetIds(failedParts))

(*
 * Get Trace with not empty failedParts
 *)
NotFailedParts == [](failedParts = <<>>)

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