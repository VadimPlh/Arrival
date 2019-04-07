------------------------------------------MODULE TruncateLog-------------------------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANTS 
    Replicas,
    LenLog
    
NONE == "NONE"
NULL == 0

ASSUME 
    /\ NONE \notin Replicas

VARIABLES
    \* Log in zookeeper.
    logHead,

    \* State replica. Active or not and e.t.c
    replicaState,
    
    \* Deleted prefix in log
    deletedPrefix
    
vars == <<logHead, replicaState, deletedPrefix>>

IsActive(replica) == replicaState[replica].is_active

IsLost(replica) == replicaState[replica].is_lost

Min(S) == CHOOSE x \in S: 
            /\ \A y \in S \ {x}: 
                y >= x
                
GetActiveReplicas == {replica \in Replicas: IsActive(replica)}

GetLogPointers == {replicaState[x].log_pointer: x \in GetActiveReplicas}


Init ==
    /\ logHead = NULL
    /\ replicaState = [replica \in Replicas |-> [is_active |-> TRUE,
                                                 is_lost |-> FALSE,
                                                 log_pointer |-> NULL]]
    /\ deletedPrefix = NULL

ReplicaBecomeInactive == \E replica \in Replicas :
    /\ IsActive(replica) = TRUE
    /\ IsLost(replica) = FALSE
    /\ replicaState' = [replicaState EXCEPT ![replica] = [
                        is_active |-> FALSE,
                        is_lost |-> FALSE,
                        log_pointer |-> @.log_pointer]]
    /\ UNCHANGED <<logHead, deletedPrefix>>
    
ReplicaBecomeActive == \E replica \in Replicas :
    /\ IsActive(replica) = FALSE
    /\ IsLost(replica) = FALSE
    /\ replicaState' = [replicaState EXCEPT ![replica] = [
                        is_active |-> TRUE,
                        is_lost |-> FALSE,
                        log_pointer |-> @.log_pointer]]
    /\ UNCHANGED <<logHead, deletedPrefix>>
    
ExecuteLog == \E replica \in Replicas :
    /\ replicaState[replica].log_pointer < logHead
    /\ IsActive(replica) = TRUE
    /\ IsLost(replica) = FALSE
    /\ replicaState' = [replicaState EXCEPT ![replica] = [
                        is_active |-> TRUE,
                        is_lost |-> FALSE,
                        log_pointer |-> @.log_pointer + 1]]
    /\ UNCHANGED <<logHead, deletedPrefix>>
                        
Insert == \E replica \in Replicas :
    /\ IsActive(replica) = TRUE
    /\ IsLost(replica) = FALSE
    /\ logHead' = logHead + 1
    /\ UNCHANGED <<replicaState, deletedPrefix>>
                    

MarkReplicas(pref) == replicaState' = [replica \in Replicas |-> [
                                     is_active |-> replicaState[replica].is_active,
                                     is_lost |-> replicaState[replica].log_pointer < pref,
                                     log_pointer |-> replicaState[replica].log_pointer]]
                                                         

ClearOldLog == 
    /\ GetActiveReplicas # {}
    /\ deletedPrefix' = Min(GetLogPointers)
    /\ MarkReplicas(Min(GetLogPointers))
    /\ UNCHANGED <<logHead>>

                   
CloneReplica == \E recovering_replica, active_replica \in Replicas : 
    /\ IsActive(recovering_replica) = FALSE
    /\ IsLost(recovering_replica) = TRUE
    /\ IsActive(active_replica) = TRUE
    /\ IsLost(active_replica) = FALSE
    /\ replicaState' = [replicaState EXCEPT ![recovering_replica] = [
                        is_active |-> TRUE,
                        is_lost |-> FALSE,
                        log_pointer |-> replicaState[active_replica].log_pointer]]
    /\ UNCHANGED <<logHead, deletedPrefix>>
                        
Next ==
    \/ ReplicaBecomeInactive
    \/ ReplicaBecomeActive
    \/ ClearOldLog
    \/ CloneReplica
    \/ Insert
    \/ ExecuteLog
    
Spec == Init /\ [][Next]_vars
             /\ WF_vars(ClearOldLog)
             /\ SF_vars(CloneReplica)
             
Simple == [](\A replica \in GetActiveReplicas: replicaState[replica].log_pointer >= deletedPrefix)
=======================================================================================================

ReplicaStartRecover == \E lost_replica \in Replicas :
    /\ IsActive(lost_replica) = FALSE
    /\ IsLost(lost_replica) = TRUE
    /\ replicaState' = [replicaState EXCEPT ![lost_replica] = [
                        is_active |-> TRUE,
                        is_lost |-> TRUE,
                        log_pointer |-> @.log_pointer,
                        local_log |-> @.local_log]]
    /\ UNCHANGED <<logHead, deletedPrefix>>