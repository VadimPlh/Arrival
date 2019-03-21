------------------------------------------MODULE TruncateLog-------------------------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANTS 
    Replicas
    
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

Init ==
    /\ log = <<>>
    /\ replicaState = [replica \in Replicas |-> [is_active |-> TRUE,
                                                 is_lost |-> FALSE,
                                                 log_pointer |-> Nil,
                                                 local_log |-> {}]]
    /\ nextRecordId = 1

ReplicaBecomeInactive == \E replica \in Replicas :
    /\ replicaState[replica].is_active = TRUE
    /\ replicaState[replica].is_lost = FALSE
    /\ replicaState' = [replicaState EXCEPT ![replica] = [
                        is_active |-> FALSE,
                        is_lost |-> FALSE,
                        log_pointer |-> @.log_pointer,
                        local_log |-> @.local_log]]
    /\ UNCHANGED <<log, nextRecordId>>
    
ReplicaIncLogPointer == \E replica \in Replicas :
    /\ replicaState[replica].is_active = TRUE
    /\ replicaState[replica].is_lost = FALSE
    /\ replicaState' = [replicaState EXCEPT ![replica] = [
                        is_active |-> TRUE,
                        is_lost |-> FALSE,
                        log_pointer |-> @.log_pointer + 1,
                        local_log |-> @.local_log \union log[@.log_pointer + 1]]]
    /\ UNCHANGED <<log, nextRecordId>>

Insert == \E replica \in Replicas :
    /\ replicaState[replica].is_active = TRUE
    /\ replicaState[replica].is_lost = FALSE
    /\ log' = Append(log, nextRecordId)
    /\ nextRecordId' = nextRecordId + 1
    /\ UNCHANGED <<replicaState>>
    
ReplicaStartRecover == \E lost_replica \in Replicas :
    /\ replicaState[lost_replica].is_active = FALSE
    /\ replicaState[lost_replica].is_lost = TRUE
    /\ replicaState' = [replicaState EXCEPT ![lost_replica] = [
                        is_active |-> TRUE,
                        is_lost |-> TRUE,
                        log_pointer |-> @.log_pointer,
                        local_log |-> @.local_log]]
                   
CloneReplica == \E recovering_replica, active_replica \in Replicas : 
    /\ replicaState[recovering_replica].is_active = TRUE
    /\ replicaState[recovering_replica].is_lost = TRUE
    /\ replicaState[active_replica].is_active = TRUE
    /\ replicaState[active_replica].is_lost = FALSE
    /\ replicaState' = [replicaState EXCEPT ![recovering_replica] = [
                        is_active |-> TRUE,
                        is_lost |-> FALSE,
                        log_pointer |-> replicaState[active_replica].log_pointer,
                        local_log |-> replicaState[active_replica].local_log]]
                        

    
    
=======================================================================================================