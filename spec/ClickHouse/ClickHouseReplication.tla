-------------------------- MODULE ClickHouseReplication --------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets, Util

VARIABLES
    \* Leader node in ZooKeeper
    leader

vars == <<log, replicaState, nextRecordData, leader>>

LeaderTypeOK == leader \in Replicas

TypeOK == /\ LogTypeOK
          /\ ReplicaStateTypeOK
          /\ RecordDataTypeOK
          /\ LeaderTypeOK

InitLeader == leader = NONE

Init ==
    /\ InitLog
    /\ InitReplicaState
    /\ InitNextRecordData
    /\ InitLeader
    
    
GetNewRecordId == CHOOSE new_id \in SmthWithNONE(RecordsId): new_id \notin GetIds(log)
    
(*
 * Constructor for log records
 *)
 
InsertEvent(data, id) == [type |-> "Insert",
                          data |-> nextRecordData,
                          id |-> id]

MergeEvent(old_records, id) == [type |-> "Merge",
                                old_records |-> old_records,
                                id |-> id]

(*
 * Leader election in ZK
 *)
 
IsLeader(expected_leader) == leader = expected_leader

ExpiredLeader(old_leader) ==
    /\ leader # NONE
    /\ replicaState' = [replicaState EXCEPT ![old_leader] = [
                        is_active |-> TRUE,
                        is_lost |-> FALSE,
                        log_pointer |-> @.log_pointer,
                        local_parts |-> @.local_log]]
    /\ leader' = NONE
    /\ UNCHANGED <<log, nextRecordData>>

BecomeLeader(new_leader) ==
     /\ leader = NONE
     /\ leader' = new_leader
     /\ UNCHANGED <<log, replicaState, nextRecordData>>

LeaderCreateMerge(leader) ==
    /\ Len(log) < LogSize
    /\ replica = leader
    /\ log' = Append(log, nextRecordId)
    /\ nextRecordId' = nextRecordId + 1
    /\ UNCHANGED <<replicaState, leader>>

ExecuteLog(replica) ==
    /\ CanExecuteLog(replica)
    /\ FetchLog(replica)
    /\ UNCHANGED <<log, leader>>
    
QuorumInsert == 
    /\ LET new_record_id == GetNewRecordId
       IN  /\ new_record_id # NONE
           /\ \E replica \in Replicas:
              /\ replicaState' = [replicaState EXCEPT ![replica] = [is_active |-> @.is_active,
                                                        is_lost |-> FALSE,
                                                        log_pointer |-> @.log_pointer,
                                                        local_parts |-> @.local_parts \union {nextRecordData}]]
           /\ UpdateLog(InsertEvent(nextRecordData, new_record_id))
    /\ IncData
    /\ UNCHANGED <<leader>>

ReplicaAction ==
    \E replica \in Replicas:
        \/ ExecuteLog(replica)
        \/ BecomeLeader(replica)
        
LeaderAction ==
    \E replica \in Replicas:
        /\ IsLeader(replica)
        /\ \/ ExpiredLeader(replica)
           \/ LeaderCreateMerge(replica)

ClientAction ==
    /\ QuorumInsert

==========================================================================
