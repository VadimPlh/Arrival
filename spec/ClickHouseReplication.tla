-------------------------- MODULE ClickHouseReplication --------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANTS 
    Replicas, 
    LogSize

None == "NONE"
Nil == 0

ASSUME 
    /\ None \notin Replicas
    /\ LogSize \in Nat

VARIABLES
    \* Log in zookeeper.
    log,

    \* State replica. Active or not and e.t.c
    replicaState,

    \* Unique id generator for new records in log
    nextRecordId,

    \* Leader node in ZooKeeper
    leader

vars == <<log, replicaState, nextRecordId, leader>>

Init ==
    /\ log = <<>>
    /\ replicaState = [replica \in Replicas |-> [active |-> TRUE,
                                                 leader |-> FALSE,
                                                 log_pointer |-> Nil,
                                                 local_log |-> {}]]
    /\ nextRecordId = 1
    /\ leader = None

DoLogRecord(replica, record) == IF record.type = "INSERT"
                                THEN replicaState[replica].local_log = replicaState[replica].local_log \union record.value
                                ELSE /\ replicaState[replica].local_log = replicaState[replica].local_log \ record.merge_parts
                                     /\ replicaState[replica].local_log \union record.value

------

ExpiredLeader == 
    /\ leader # None
    /\ replicaState' = [replicaState EXCEPT ![leader] = [
                        active |-> FALSE,
                        leader |-> @.leader,
                        log_pointer |-> @.log_pointer,
                        local_log |-> @.local_log]]
    /\ leader' = None
    /\ UNCHANGED <<log, nextRecordId>>

ElectLeader == \E newLeader \in Replicas :
    /\ leader = None
    /\ replicaState[newLeader].active = TRUE
    /\ leader' = newLeader
    /\ UNCHANGED <<log, replicaState, nextRecordId>>
    
BecomeLeader == \E replica \in Replicas :
    /\ leader # None
    /\ replicaState[replica].active = TRUE
    /\ replicaState' = [replicaState EXCEPT ![leader] = [
                        active |-> TRUE,
                        leader |-> TRUE,
                        log_pointer |-> @.log_pointer,
                        local_log |-> @.local_log]]
    /\ UNCHANGED <<log, nextRecordId, leader>>
    
------
    
LeaderCreateMerge == \E replica \in Replicas :
    /\ Len(log) < LogSize
    /\ replica = leader
    /\ log' = Append(log, nextRecordId)
    /\ nextRecordId' = nextRecordId + 1
    /\ UNCHANGED <<replicaState, leader>>

-------
    
ReplicaRecover == \E replica1, replica2 \in Replicas :
    /\ replicaState[replica1].active = FALSE
    /\ replicaState[replica2].active = TRUE
    /\ LET new_state == replicaState[replica2]
       IN replicaState' = [replicaState EXCEPT ![replica1] = [
                           active |-> TRUE,
                           leader |-> FALSE,
                           log_pointer |-> new_state.log_pointer,
                           local_log |-> new_state.local_log]]
    /\ UNCHANGED <<log, nextRecordId, leader>>
    
------
    
ReplicaIncLogPointer == \E replica \in Replicas :
    /\ replicaState[replica].active = TRUE
    /\ replicaState[replica].log_pointer < Len(log)
    /\ DoLogRecord(replica, log[replicaState[replica].log_pointer + 1])
    /\ replicaState' = [replicaState EXCEPT ![replica] = [
                        active |-> TRUE,
                        leader |-> @.leader,
                        log_pointer |-> @.log_pointer + 1,
                        local_log |-> @.local_log \union log[@.log_pointer + 1]]]
    /\ UNCHANGED <<log, nextRecordId, leader>>
    
 ------



==========================================================================