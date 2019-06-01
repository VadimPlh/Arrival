-------------------------- MODULE Replication --------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets, Util

VARIABLES
    \* Leader node in ZooKeeper
    leader

vars == <<log, replicaState, nextRecordData, leader>>

RecordType == {"Insert", "Merge"}

LocalLogRecords == [data: Nat, id: RecordsId, type: RecordType]
                   \cup [data: Nat, id: RecordsId, type: RecordType, old_records: Nat ]
LocalLogTypeOK == Range(log) \subseteq LocalLogRecords

LeaderTypeOK == leader \in SmthWithNONE(Replicas)

TypeOK == /\ LocalLogTypeOK
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
                                data |-> nextRecordData,
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
                        local_parts |-> @.local_parts]]
    /\ leader' = NONE
    /\ UNCHANGED <<log, nextRecordData>>

BecomeLeader(new_leader) ==
     /\ leader = NONE
     /\ leader' = new_leader
     /\ UNCHANGED <<log, replicaState, nextRecordData>>

LeaderCreateMerge(curr_leader) ==
    /\ curr_leader = leader
    /\ LET new_record_id == GetNewRecordId
       IN  /\ new_record_id # NONE
           /\ \E record1, record2 \in replicaState[curr_leader].local_parts:
              /\ record1 # record2
              /\ replicaState' = [replicaState EXCEPT ![curr_leader] = [is_active |-> @.is_active,
                                                        is_lost |-> FALSE,
                                                        log_pointer |-> @.log_pointer,
                                                        local_parts |-> (@.local_parts \cup {nextRecordData}) \ {record1, record2}]]
              /\ UpdateLog(MergeEvent({record1, record2}, new_record_id))
    /\ IncData
    /\ UNCHANGED <<leader>>

ExecuteInsert(replica) ==
    /\ CanExecuteLog(replica)
    /\ log[replicaState[replica].log_pointer].type = "Insert"
    /\ FetchLog(replica)
    /\ UNCHANGED <<log, nextRecordData, leader>>

ExecuteMerge(replica) ==
    /\ CanExecuteLog(replica)
    /\ log[replicaState[replica].log_pointer].type = "Merge"
    /\ replicaState' = [replicaState EXCEPT ![replica] = [is_active |-> @.is_active,
                                                              is_lost |-> FALSE,
                                                              log_pointer |-> @.log_pointer + 1,
                                                              local_parts |-> (@.local_parts \cup {log[@.log_pointer].data}) \ log[@.log_pointer].old_records]]
    /\ UNCHANGED <<log, nextRecordData, leader>>

Insert ==
    /\ LET new_record_id == GetNewRecordId
       IN  /\ new_record_id # NONE
           /\ \E replica \in Replicas:
              /\ replicaState' = [replicaState EXCEPT ![replica] = [is_active |-> @.is_active,
                                                        is_lost |-> FALSE,
                                                        log_pointer |-> @.log_pointer,
                                                        local_parts |-> @.local_parts \cup {nextRecordData}]]
           /\ UpdateLog(InsertEvent(nextRecordData, new_record_id))
    /\ IncData
    /\ UNCHANGED <<leader>>

LegitimateTermination ==
    /\ GetIds(log) = RecordsId
    /\ UNCHANGED vars

ReplicaAction ==
    \E replica \in Replicas:
        \/ ExecuteInsert(replica)
        \/ ExecuteMerge(replica)
        \/ BecomeLeader(replica)

LeaderAction ==
    \E replica \in Replicas:
        /\ IsLeader(replica)
        /\ \/ ExpiredLeader(replica)
           \/ LeaderCreateMerge(replica)

ClientAction ==
    /\ Insert

Next ==
    \/ ClientAction
    \/ LeaderAction
    \/ ReplicaAction
    \/ LegitimateTermination

Spec == Init /\ [][Next]_vars
             /\ SF_vars(LeaderAction)


EquivalentReplicas == <>(\A r1, r2 \in Replicas: replicaState[r1].local_parts = replicaState[r2].local_parts)
==========================================================================
