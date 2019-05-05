------------------------------------------MODULE Util-------------------------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANTS 
    Replicas,
    RecordsId,
    NONE

VARIABLES
    \* Log in zookeeper.
    log,

    \* State replica. Active or not and e.t.c
    replicaState,

    \* Unique id generator for new records in log.
    nextRecordData

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
 * Get smth for check Invarioants
 *)

GetReplicasWithPart(part) == {replica \in Replicas: part \in replicaState[replica].local_parts}

(*
 * Get data or id's from <<>>
 *)
GetIds(f) == {f[x].id: x \in DOMAIN f}
GetData(f) == {f[x].data: x \in DOMAIN f}
                    
(*
 * Get record from log and update local_parts
 *) 
FetchLog(replica) == replicaState' = [replicaState EXCEPT ![replica] = [is_active |-> @.is_active,
                                                                        is_lost |-> FALSE,
                                                                        log_pointer |-> @.log_pointer + 1,
                                                                        local_parts |-> @.local_parts \union {log[@.log_pointer].data}]]
                                                                        
RepicaStartActive(replica) == replicaState' = [replicaState EXCEPT ![replica] = [is_active |-> TRUE,
                                                                                 is_lost |-> @.is_lost,
                                                                                 log_pointer |-> @.log_pointer,
                                                                                 local_parts |-> @.local_parts]]
                                                                        
RepicaStartInactive(replica) == replicaState' = [replicaState EXCEPT ![replica] = [is_active |-> FALSE,
                                                                                   is_lost |-> @.is_lost,
                                                                                   log_pointer |-> @.log_pointer,
                                                                                   local_parts |-> @.local_parts]]
                                                                              
(*
 * Init action
 *)

InitLog == log = <<>> 
 
InitReplicaState == replicaState = [replica \in Replicas |-> [is_active |-> TRUE,
                                                              is_lost |-> FALSE,
                                                              log_pointer |-> 1,
                                                              local_parts |-> {}]]
                                                              
InitNextRecordData == nextRecordData = 0
======================================================================