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
 
QuorumStates == [data: SmthWithNONE(Nat),
                replicas: SUBSET Replicas,
                id: SmthWithNONE(RecordsId)]
QuorumTypeOK == quorum \in QuorumStates

FailedParts == [id: RecordsId, data: Nat]
FailedPartsTypeOK == Range(failedParts)  \subseteq FailedParts

LastAddedDataTypeOK == lastAddeddata \in SmthWithNONE(Nat)

HistoryTypes == {"StartInsert", "EndInsert", "FailedInsert", "Read"}
HistoryEvents == [type: HistoryTypes, timestamp: Nat, record_id: RecordsId]
HistoryTypeOK == history \subseteq HistoryEvents
 
TypeOK == /\ LogTypeOK
          /\ ReplicaStateTypeOK
          /\ RecordDataTypeOK
          /\ QuorumTypeOK
          /\ FailedPartsTypeOK
          /\ LastAddedDataTypeOK
          /\ HistoryTypeOK
 
GetCommitedId == {record_id \in GetIds(log): record_id \notin GetIds(failedParts) /\ record_id # quorum.id}

(*
 * Get id for new record
 *)
 
GetNewRecordId == CHOOSE new_id \in SmthWithNONE(RecordsId): 
                    /\ new_id \notin GetCommitedId
                    /\ new_id \notin GetIds(failedParts)

(*
 * Constructor for history events
 *)
 
GetNumber(h) == Cardinality(h) + 1

StartInsertEvent(id) == history' = history \cup {[type |-> "StartInsert",
                                                  timestamp |-> GetNumber(history),
                                                  record_id |-> id]}
                                                  
EndInsertEvent(id) == history' = history \cup {[type |-> "EndInsert",
                                                timestamp |-> GetNumber(history),
                                                record_id |-> id]}
                                                
FailedInsertEvent(id) == history' = history \cup {[type |-> "FailedInsert",
                                                   timestamp |-> GetNumber(history),
                                                   record_id |-> id]}
                                                   
ReadEvent(id) == history' = history \cup {[type |-> "Read",
                                           timestamp |-> GetNumber(history),
                                           record_id |-> id]}

(*
 * Get smth for check Invarioants
 *)

GetSelectFromHistory(h) == {record \in h: record.type = "Read"}
GetStartInsertFromHistory(h) == {record \in h: record.type = "StartInsert"}
GetFailedInsertFromHistory(h) == {record \in h: record.type = "FailedInsert"}
GetEndInsertFromHistory(h) == {record \in h: record.type = "EndInsert"}

(*
 * Utilities for work with Quorum
 *)

IsCurrentQuorum(id) == id = quorum.id
IsReplicaInQuorum(replica) == replica \in quorum.replicas
UpdateQuorumReplicas(replica) == quorum' = [data |-> quorum.data,
                                            replicas |-> quorum.replicas \cup {replica},
                                            id |-> quorum.id]
                                            
QuorumIsUnalive == /\ quorum.replicas # {}
                   /\ GetActiveReplicas \cap quorum.replicas = {}
                 
UpdateFailedParts(id, value) == failedParts' = Append(failedParts, [id |-> id, data |-> value])         

NullQuorum == [data |-> NONE, replicas |-> {}, id |-> NONE]

Init ==
    /\ InitLog
    /\ InitReplicaState
    /\ InitNextRecordData
    /\ quorum = NullQuorum
    /\ lastAddeddata = NONE
    /\ failedParts = <<>>
    /\ history = {}

    
BecomeActive(replica) ==
    /\ RepicaStartActive(replica)
    /\ UNCHANGED <<log, nextRecordData, quorum, failedParts, lastAddeddata, history>>
    
BecomeInactive(replica) ==
    /\ RepicaStartInactive(replica)
    /\ UNCHANGED <<log, nextRecordData, quorum, failedParts,lastAddeddata, history>>

ExecuteLog(replica) == 
    /\ CanExecuteLog(replica)
    /\ LET record_id == log[replicaState[replica].log_pointer].id
       IN \/ /\ ~IsCurrentQuorum(record_id)
             /\ record_id \notin GetIds(failedParts)
          \/ /\ IsCurrentQuorum(record_id)
             /\ replica \in quorum.replicas
             /\ replicaState[replica].log_pointer = Len(log)
    /\ FetchLog(replica)
    /\ UNCHANGED <<log, nextRecordData, quorum, failedParts, lastAddeddata, history>>
    
UpdateQuorum(replica) == 
    /\ CanExecuteLog(replica)
    /\ LET record_id == log[replicaState[replica].log_pointer].id
       IN IsCurrentQuorum(record_id)
    /\ ~IsReplicaInQuorum(replica)
    /\ ~QuorumIsUnalive
    /\ UpdateQuorumReplicas(replica)
    /\ FetchLog(replica)
    /\ UNCHANGED <<log, nextRecordData, history, failedParts, lastAddeddata>>
    
FailedQuorum(replica) ==
    /\ CanExecuteLog(replica)
    /\ LET record_id == log[replicaState[replica].log_pointer].id
       IN IsCurrentQuorum(record_id)
    /\ ~IsReplicaInQuorum(replica)
    /\ QuorumIsUnalive
    /\ UpdateFailedParts(quorum.id, quorum.data)
    /\ FailedInsertEvent(quorum.id)
    /\ quorum' = NullQuorum
    /\ UNCHANGED <<log, replicaState, nextRecordData, lastAddeddata>>
    
EndQuorum(replica) ==
    /\ quorum.id # NONE
    /\ IsReplicaInQuorum(replica)
    /\ Cardinality(quorum.replicas) >= QuorumCount
    /\ EndInsertEvent(quorum.id)
    /\ lastAddeddata' = quorum.data
    /\ quorum' = NullQuorum
    /\ UNCHANGED <<log, replicaState, nextRecordData, failedParts>>
 
QuorumInsert == 
    /\ quorum.id = NONE
    /\ LET new_record_id == GetNewRecordId
       IN  /\ new_record_id # NONE
           /\ \E replica \in Replicas:
              /\ IsActive(replica)
              /\ quorum' = [replicas |-> {replica},
                            data |-> nextRecordData,
                            id |-> new_record_id]
              /\ replicaState' = [replicaState EXCEPT ![replica] = [is_active |-> @.is_active,
                                                        is_lost |-> FALSE,
                                                        log_pointer |-> @.log_pointer,
                                                        local_parts |-> @.local_parts \union {nextRecordData}]]
           /\ UpdateLog([data |-> nextRecordData, id |-> new_record_id])
           /\ StartInsertEvent(new_record_id)
    /\ IncData
    /\ UNCHANGED <<lastAddeddata, failedParts>>
    
QuorumReadWithoutLin ==
    /\ Len(log) > 0
    /\ Cardinality(GetSelectFromHistory(history)) < HistoryLength
    /\ \E replica \in Replicas :
        /\ IsActive(replica)
        /\ LET max_data == Max(replicaState[replica].local_parts \ ({quorum.data} \cup GetData(failedParts)))
           IN /\ max_data # NONE
              /\ ReadEvent(GetIdForData(max_data, log))
    /\ UNCHANGED <<log, replicaState, nextRecordData, quorum, lastAddeddata, failedParts>>
    
QuorumReadLin == 
    /\ Len(log) > 0
    /\ Cardinality(GetSelectFromHistory(history)) < HistoryLength
    /\ \E replica \in Replicas :
        /\ IsActive(replica)
        /\ Cardinality(GetCommitedId) = Cardinality(replicaState[replica].local_parts \ ({quorum.data} \cup GetData(failedParts)))
        /\ LET max_data == Max(replicaState[replica].local_parts \ ({quorum.data} \cup GetData(failedParts)))
           IN /\ max_data # NONE
              /\ ReadEvent(GetIdForData(max_data, log))
    /\ UNCHANGED <<log, replicaState, nextRecordData, quorum, lastAddeddata, failedParts>>
    
LegitimateTermination ==
    /\ GetIds(failedParts) \cup GetCommitedId = RecordsId
    /\ Cardinality(GetSelectFromHistory(history)) = HistoryLength
    /\ UNCHANGED vars
    
ReplicaAction == 
    \E replica \in Replicas:
     \/ IsActive(replica)
         /\ \/ ExecuteLog(replica)
            \/ UpdateQuorum(replica)
            \/ EndQuorum(replica)
            \/ BecomeInactive(replica)
            \/ FailedQuorum(replica)
     \/ ~IsActive(replica)
         /\ BecomeActive(replica)

ClientAction ==
    \/ QuorumInsert
    \/ QuorumReadLin
    
Next ==
    \/ ClientAction
    \/ ReplicaAction
    \/ LegitimateTermination

Spec == Init /\ [][Next]_vars
             /\ SF_vars(QuorumInsert)
             (*/\ SF_vars(QuorumReadWithoutLin)*)


          
QuorumSelect == [](Len(log) = 0 \/ \A i \in 1..Len(log):
    Cardinality(GetReplicasWithPart(log[i].data)) >= QuorumCount \/ quorum.id = log[i].id \/ log[i].id \in GetIds(failedParts))

(*
 * Get Trace with not empty failedParts
 *)
NotFailedParts == [](failedParts = <<>>)

ReadAfterWrite == \A i \in GetSelectFromHistory(history):
    /\ \E j \in GetStartInsertFromHistory(history):
        /\ \E k \in GetEndInsertFromHistory(history):
            /\ i.record_id = j.record_id
            /\ i.record_id = k.record_id
            /\ i.timestamp > j.timestamp
            /\ i.timestamp > k.timestamp
            
EndOrFailedAfterStartWrite == \A i \in GetStartInsertFromHistory(history):
    \/ \E j \in GetEndInsertFromHistory(history):
        /\ i.record_id = j.record_id
        /\ i.timestamp < j.timestamp
    \/ \E k \in GetFailedInsertFromHistory(history):
        /\ i.record_id = k.record_id
        /\ i.timestamp < k.timestamp
        
MonotonicRead == \A i, j \in GetSelectFromHistory(history):
    /\ i.record_id # j.record_id
    /\ i.timestamp < j.timestamp
    => \E k, l \in GetEndInsertFromHistory(history):
       /\ k.record_id = i.record_id
       /\ l.record_id = j.record_id
       /\ k.timestamp < l.timestamp
        
ValidEvents == [](ReadAfterWrite) /\ <>(EndOrFailedAfterStartWrite) /\ [](MonotonicRead)

======================================================================