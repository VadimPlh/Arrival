------------------------------------------MODULE TruncateLog-------------------------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets, Util

VARIABLES
    \* Deleted prefix in log
    deletedPrefix

vars == <<log, replicaState, nextRecordData, deletedPrefix>>

(*
 * TypeOK
 *)

DeletedPrefixTypeOK == deletedPrefix \in Nat
 
TypeOK == /\ LogTypeOK
          /\ ReplicaStateTypeOK
          /\ RecordDataTypeOK
          /\ DeletedPrefixTypeOK

GetLogPointers == {replicaState[x].log_pointer: x \in GetActiveReplicas}

GetNewRecordId == CHOOSE new_id \in SmthWithNONE(RecordsId): new_id \notin GetIds(log)

Init ==
    /\ InitLog
    /\ InitReplicaState
    /\ InitNextRecordData
    /\ deletedPrefix = 0

ReplicaBecomeInactive ==
    /\ \E replica \in Replicas :
      /\ IsActive(replica)
      /\ ~IsLost(replica)
      /\ RepicaStartInactive(replica)
    /\ UNCHANGED <<log, nextRecordData, deletedPrefix>>

ReplicaBecomeActive ==
    /\ \E replica \in Replicas :
      /\ ~IsActive(replica)
      /\ ~IsLost(replica)
      /\ RepicaStartActive(replica)
    /\ UNCHANGED <<log, nextRecordData, deletedPrefix>>

ExecuteLog ==
    /\ \E replica \in Replicas :
        /\ replicaState[replica].log_pointer <= Len(log)
        /\ IsActive(replica)
        /\ ~IsLost(replica)
        /\ FetchLog(replica)
    /\ UNCHANGED <<log, nextRecordData, deletedPrefix>>

Insert ==
    /\ \E replica \in Replicas :
        /\ IsActive(replica)
        /\ ~IsLost(replica)
    /\ LET new_record_id == GetNewRecordId
       IN  /\ new_record_id # NONE  
           /\ UpdateLog([data |-> nextRecordData, id |-> new_record_id])
    /\ IncData
    /\ UNCHANGED <<replicaState, deletedPrefix>>


ClearOldLog ==
    /\ Len(log) > 0
    /\ deletedPrefix' = Max({Min(GetLogPointers), deletedPrefix})
    /\ replicaState' = [replica \in Replicas |-> [is_active |-> replicaState[replica].is_active,
                                                  is_lost |-> (replicaState[replica].log_pointer < deletedPrefix'),
                                                  log_pointer |-> replicaState[replica].log_pointer,
                                                  local_parts |-> replicaState[replica].local_parts]]
    /\ UNCHANGED <<log, nextRecordData>>


CloneReplica ==
    /\ \E recovering_replica, active_replica \in Replicas :
        /\ ~IsActive(recovering_replica)
        /\ IsLost(recovering_replica)
        /\ IsActive(active_replica)
        /\ ~IsLost(active_replica)
        /\ replicaState' = [replicaState EXCEPT ![recovering_replica] = [
                            is_active |-> TRUE,
                            is_lost |-> FALSE,
                            log_pointer |-> replicaState[active_replica].log_pointer,
                            local_parts |-> replicaState[active_replica].local_parts]]
    /\ UNCHANGED <<log, nextRecordData, deletedPrefix>>
    
LegitimateTermination ==
    /\ GetIds(log) = RecordsId
    /\ UNCHANGED vars

Next ==    
    \/ ReplicaBecomeInactive
    \/ ReplicaBecomeActive
    \/ ClearOldLog
    \/ CloneReplica
    \/ Insert
    \/ ExecuteLog
    \/ LegitimateTermination

Spec == Init /\ [][Next]_vars
             /\ SF_vars(Insert)
             /\ SF_vars(ReplicaBecomeActive)
             /\ SF_vars(ExecuteLog)
             /\ SF_vars(ClearOldLog)

IsLogCleared == <>(deletedPrefix > 0)

=======================================================================================================
