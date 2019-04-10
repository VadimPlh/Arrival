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

Min(S) == IF S # {} THEN CHOOSE x \in S: 
                      /\ \A y \in S \ {x}: y >= x
          ELSE 0
                
Max(S) == CHOOSE x \in S: 
            /\ \A y \in S \ {x}: 
                y <= x
                
GetActiveReplicas == {replica \in Replicas: IsActive(replica)}

GetLogPointers == {replicaState[x].log_pointer: x \in GetActiveReplicas}


Init ==
    /\ logHead = NULL
    /\ replicaState = [replica \in Replicas |-> [is_active |-> TRUE,
                                                 is_lost |-> FALSE,
                                                 log_pointer |-> NULL]]
    /\ deletedPrefix = NULL

ReplicaBecomeInactive == 
    /\ \E replica \in Replicas :
      /\ IsActive(replica)
      /\ ~IsLost(replica)
      /\ replicaState' = [replicaState EXCEPT ![replica] = [
                          is_active |-> FALSE,
                          is_lost |-> FALSE,
                          log_pointer |-> @.log_pointer]]
    /\ UNCHANGED <<logHead, deletedPrefix>>
    
ReplicaBecomeActive == 
    /\ \E replica \in Replicas :
      /\ ~IsActive(replica)
      /\ ~IsLost(replica)
      /\ replicaState' = [replicaState EXCEPT ![replica] = [
                          is_active |-> TRUE,
                          is_lost |-> FALSE,
                          log_pointer |-> @.log_pointer]]
    /\ UNCHANGED <<logHead, deletedPrefix>>
    
ExecuteLog == 
    /\ \E replica \in Replicas :
        /\ replicaState[replica].log_pointer < logHead
        /\ IsActive(replica)
        /\ ~IsLost(replica)
        /\ replicaState' = [replicaState EXCEPT ![replica] = [
                            is_active |-> TRUE,
                            is_lost |-> FALSE,
                            log_pointer |-> @.log_pointer + 1]]
    /\ UNCHANGED <<logHead, deletedPrefix>>
                        
Insert == 
    /\ \E replica \in Replicas :
        /\ IsActive(replica)
        /\ ~IsLost(replica)
    /\ logHead' = logHead + 1
    /\ UNCHANGED <<replicaState, deletedPrefix>>
                    

MarkReplicas(pref) == replicaState' = [replica \in Replicas |-> [
                                       is_active |-> replicaState[replica].is_active,
                                       is_lost |-> replicaState[replica].log_pointer < pref,
                                       log_pointer |-> replicaState[replica].log_pointer]]
                                                         

ClearOldLog == 
    /\ deletedPrefix' = Max({Min(GetLogPointers), deletedPrefix})
    /\ MarkReplicas(deletedPrefix')
    /\ UNCHANGED <<logHead>>

                   
CloneReplica == 
    /\ \E recovering_replica, active_replica \in Replicas : 
        /\ ~IsActive(recovering_replica)
        /\ IsLost(recovering_replica) = TRUE
        /\ IsActive(active_replica)
        /\ ~IsLost(active_replica)
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
             /\ WF_vars(Next)
             /\ WF_vars(ClearOldLog)
             
Simple == <>(deletedPrefix > 0)
HasNotLostReplica == [](\A replica \in Replicas : ~IsLost(replica))
=======================================================================================================