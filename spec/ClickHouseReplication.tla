-------------------------- MODULE ClickHouseReplication --------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANTS 
    Replicas, 
    LogSize,
    QuorumCount

None == "NONE"
Nil == 0

ASSUME 
    /\ None \notin Replicas
    /\ LogSize \in Nat
    /\ QuorumCount \in Nat

VARIABLES
    \* Log in zookeeper.
    log,

    \* State replica. Active or not and e.t.c
    replicaState,

    \* Unique id generator for new records in log
    nextRecordId,

    \* Leader node in ZooKeeper
    leader,
    
    \* Quorun in zookeeper
    quorum

vars == <<log, replicaState, nextRecordId, leader, quorum>>

Init ==
    /\ log = <<>>
    /\ replicaState = [replica \in Replicas |-> [active |-> TRUE,
                                                 log_pointer |-> Nil,
                                                 local_log |-> <<>>]]
    /\ nextRecordId = 1
    /\ leader = None
    /\ quorum = [replicas |-> {},
                 value |-> Nil]

\*BecomeLeader == \E replica \in Replicas :
\*    /\ leader = None
\*    /\ replicaState[replica].active = TRUE
\*    /\ leader' = replica
\*    /\ UNCHANGED <<log, replicaState, nextRecordId>>

------

ExpiredLeader == 
    /\ leader # None
    /\ replicaState' = [replicaState EXCEPT ![leader] = [
                        active |-> FALSE,
                        log_pointer |-> @.log_pointer,
                        local_log |-> @.local_log]]
    /\ leader' = None
    /\ UNCHANGED <<log, nextRecordId, quorum>>

ElectLeader == \E newLeader \in Replicas :
    /\ leader = None
    /\ replicaState[newLeader].active = TRUE
    /\ leader' = newLeader
    /\ UNCHANGED <<log, replicaState, nextRecordId, quorum>>
    
LeaderDoMerge == \E replica \in Replicas :
    /\ Len(log) < LogSize
    /\ replica = leader
    /\ log' = Append(log, nextRecordId)
    /\ nextRecordId' = nextRecordId + 1
    /\ UNCHANGED <<replicaState, leader, quorum>>
    
-------
    
ReplicaRecover == \E replica1, replica2 \in Replicas :
    /\ replicaState[replica1].active = FALSE
    /\ replicaState[replica2].active = TRUE
    /\ LET new_state == replicaState[replica2]
       IN replicaState' = [replicaState EXCEPT ![replica1] = [
                           active |-> TRUE,
                           log_pointer |-> new_state.log_pointer,
                           local_log |-> new_state.local_log]]
    /\ UNCHANGED <<log, nextRecordId, leader, quorum>>
    
------- 
    
ReplicaIncLogPointer == \E replica \in Replicas :
    /\ replicaState[replica].active = TRUE
    /\ replicaState[replica].log_pointer < Len(log)
    /\ replicaState' = [replicaState EXCEPT ![replica] = [
                        active |-> TRUE,
                        log_pointer |-> @.log_pointer + 1,
                        local_log |-> Append(@.local_log, log[@.log_pointer + 1])]]
    /\ UNCHANGED <<log, nextRecordId, leader, quorum>>
    
 ------
 
StartQuorum == \E replica \in Replicas :
    /\ Len(log) < 5
    /\ replicaState[replica].active = TRUE
    /\ quorum.value = Nil
    /\ quorum' = [replicas |-> {replica},
                 value |-> nextRecordId]
    /\ nextRecordId' = nextRecordId + 1
    /\ UNCHANGED <<log, replicaState, leader>>
    
AppendQuorumReplicas == \E replica \in Replicas :
    /\ replicaState[replica].active = TRUE
    /\ replica \notin quorum.replicas
    /\ quorum' = [replicas |-> quorum.replicas \union {replica},
                 value |-> quorum.value]
    
    /\ UNCHANGED <<log, replicaState, nextRecordId, leader>>
    
QuorumInsert == 
    /\ quorum.value # Nil
    /\ Cardinality(quorum.replicas) >= QuorumCount
    /\ log' = Append(log, quorum.value)
    /\ quorum' = [replicas |-> {},
                 value |-> Nil]
    /\ UNCHANGED <<replicaState, nextRecordId, leader>>
 
 ------

Next ==
    \/ StartQuorum
    \/ AppendQuorumReplicas
    \/ QuorumInsert
    \/ ReplicaIncLogPointer
  
 Spec == Init /\ [][Next]_vars
              /\ WF_vars(StartQuorum)
              /\ WF_vars(AppendQuorumReplicas)
              /\ WF_vars(QuorumInsert)
              
Simple == []<>(Len(log) > 0)



==========================================================================