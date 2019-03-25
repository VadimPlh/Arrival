------------------------------------------MODULE TruncateLog-------------------------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANTS 
    Replicas,
    LenLog
    
None == "NONE"
Nil == 0

ASSUME 
    /\ None \notin Replicas

VARIABLES
    \* Log in zookeeper.
    log,

    \* State replica. Active or not and e.t.c
    replicaState,

    \* Unique id generator for new records in log
    nextRecordId
    
vars == <<log, replicaState, nextRecordId>>

IsActive(replica) == replicaState[replica].is_active

IsLost(replica) == replicaState[replica].is_lost

DeleteRecords(mil_log_pointer) == 
    /\ log' = <<>>
    /\ \A id \in 1..Len(log) : IF id < mil_log_pointer THEN log' = Append(log', [value |-> id, deleted |-> TRUE])
                                                                                ELSE log' = Append(log', [value |-> id, deleted |-> FALSE])

Init ==
    /\ log = <<>>
    /\ replicaState = [replica \in Replicas |-> [is_active |-> TRUE,
                                                 is_lost |-> FALSE,
                                                 log_pointer |-> Nil,
                                                 local_log |-> <<>>]]
    /\ nextRecordId = 1

ReplicaBecomeInactive == \E replica \in Replicas :
    /\ IsActive(replica) = TRUE
    /\ IsLost(replica) = FALSE
    /\ replicaState' = [replicaState EXCEPT ![replica] = [
                        is_active |-> FALSE,
                        is_lost |-> FALSE,
                        log_pointer |-> @.log_pointer,
                        local_log |-> @.local_log]]
    /\ UNCHANGED <<log, nextRecordId>>
    
ReplicaBecomeActive == \E replica \in Replicas :
    /\ IsActive(replica) = FALSE
    /\ IsLost(replica) = FALSE
    /\ replicaState' = [replicaState EXCEPT ![replica] = [
                        is_active |-> TRUE,
                        is_lost |-> FALSE,
                        log_pointer |-> @.log_pointer,
                        local_log |-> @.local_log]]
    /\ UNCHANGED <<log, nextRecordId>>
    
ReplicaIncLogPointer == \E replica \in Replicas :
    /\ Len(log) > 0
    /\ Len(replicaState[replica].local_log) < Len(log)
    /\ IsActive(replica) = TRUE
    /\ IsLost(replica) = FALSE
    /\ replicaState' = [replicaState EXCEPT ![replica] = [
                        is_active |-> TRUE,
                        is_lost |-> FALSE,
                        log_pointer |-> @.log_pointer + 1,
                        local_log |-> Append(@.local_log, log[@.log_pointer + 1].value)]]
    /\ UNCHANGED <<log, nextRecordId>>
    
ReplicaStartRecover == \E lost_replica \in Replicas :
    /\ IsActive(lost_replica) = FALSE
    /\ IsLost(lost_replica) = TRUE
    /\ replicaState' = [replicaState EXCEPT ![lost_replica] = [
                        is_active |-> TRUE,
                        is_lost |-> TRUE,
                        log_pointer |-> @.log_pointer,
                        local_log |-> @.local_log]]
                   
CloneReplica == \E recovering_replica, active_replica \in Replicas : 
    /\ IsActive(recovering_replica) = TRUE
    /\ IsLost(recovering_replica) = TRUE
    /\ IsActive(active_replica) = TRUE
    /\ IsLost(active_replica) = FALSE
    /\ replicaState' = [replicaState EXCEPT ![recovering_replica] = [
                        is_active |-> TRUE,
                        is_lost |-> FALSE,
                        log_pointer |-> replicaState[active_replica].log_pointer,
                        local_log |-> replicaState[active_replica].local_log]]
                        
Insert == \E replica \in Replicas :
    /\ Len(log) < LenLog
    /\ IsActive(replica) = TRUE
    /\ IsLost(replica) = FALSE
    /\ log' = Append(log, [value |-> nextRecordId, deleted |-> FALSE])
    /\ nextRecordId' = nextRecordId + 1
    /\ UNCHANGED <<replicaState>>

ClearOldLog == 
    /\ Len(log) > 2
    /\ \E replica \in Replicas : 
        /\ IsActive(replica) = TRUE
        /\ IsLost(replica) = FALSE
    /\ DeleteRecords(2)
    /\ UNCHANGED <<replicaState, nextRecordId>>
                        
Next ==
    \/ ReplicaIncLogPointer
    \/ Insert
    \/ ReplicaBecomeInactive
    \/ ReplicaBecomeActive
    \/ ClearOldLog
    
Spec == Init /\ [Next]_vars

Simple == \A replica \in Replicas :
    \/
      /\ IsActive(replica)
      /\ replicaState[replica].log_pointer > 0
      /\ log[replicaState[replica].log_pointer].deleted = FALSE
    \/ IsActive(replica) = FALSE
    \/ replicaState[replica].log_pointer = 0
=======================================================================================================