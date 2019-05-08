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
GetIds(f) == {x.id: x \in Range(f)} 
GetData(f) == {x.data: x \in Range(f)}
GetRecordLogForData(data, f) == CHOOSE x \in Range(f): x.data = data
GetIdForData(data, f) == GetRecordLogForData(data,f).id
                    
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
 * Add new record to log
 *)
UpdateLog(record) == log' = Append(log, record)
                                                                                   
(*
 * TypeOK
 *)
LogRecords == [data: Nat, id: RecordsId]
LogTypeOK == Range(log) \subseteq LogRecords

ReplicaStates == [is_active: BOOLEAN,
                  is_lost: BOOLEAN,
                  log_pointer: Nat,
                  local_parts: SUBSET Nat]

ReplicaStateTypeOK == replicaState \in [Replicas -> ReplicaStates]

RecordDataTypeOK == nextRecordData \in Nat
                                                                              
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