-- ---- MODULE SemiSync ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANT Client, Replica, nil

VARIABLE
    zk_leader, zk_epoch, zk_leader_epoch, zk_status,
    old_leaders, zk_catchup_index,
    db, db_leader, db_replicated, db_epoch, db_status,
    next_req, client_leader, client_success,
    pending, pending_db, client_leader_epoch,
    healer_status, healer_epoch, healer_replicas

vars == <<
    zk_leader, zk_epoch, zk_leader_epoch, zk_status,
    old_leaders, zk_catchup_index,
    db, db_leader, db_replicated, db_epoch, db_status,
    next_req, client_leader, client_success,
    pending, pending_db, client_leader_epoch,
    healer_status, healer_epoch, healer_replicas
>>

zk_vars == <<zk_leader, zk_epoch, zk_leader_epoch, zk_status,
    old_leaders, zk_catchup_index>>
db_vars == <<db, db_leader, db_replicated, db_epoch, db_status>>
client_vars == <<
    next_req, client_leader, client_success,
    pending, pending_db, client_leader_epoch>>
healer_vars == <<healer_status, healer_epoch, healer_replicas>>

max_next_req == 4

max_change_leader == 4

ReqSet == 60..(60 + max_next_req)

Epoch == 0..20

NullReqSet == ReqSet \union {nil}

NullReplica == Replica \union {nil}

LogOffset == 0..20

Range(f) == {f[x]: x \in DOMAIN f}

replication_factor == 2

Quorum == {x \in SUBSET Replica: Cardinality(x) = replication_factor}


TypeOK ==
    /\ zk_leader \in Replica
    /\ zk_epoch \in 1..30
    /\ zk_leader_epoch \in 1..max_change_leader
    /\ zk_status \in {"Normal", "ChangingLeader", "WaitReplicaLog"}
    /\ old_leaders \subseteq Replica
    /\ zk_catchup_index \in (LogOffset \union {nil})

    /\ db \in [Replica -> Seq(ReqSet)]
    /\ db_leader \in [Replica -> Replica]
    /\ db_replicated \in [Replica -> [Replica -> LogOffset]]
    /\ db_epoch \in [Replica -> Epoch]
    /\ db_status \in [Replica -> {"Writable", "Replica", "Frozen"}]

    /\ next_req \in ReqSet
    /\ client_leader \in [Client -> Replica]
    /\ client_success \in [Client -> Seq(ReqSet)]
    /\ pending \in [Client -> NullReqSet]
    /\ pending_db \in [Client -> NullReplica]
    /\ client_leader_epoch \in [Client -> Epoch]

    /\ healer_status \in {"Init", "UpdatingLeader", "WaitReplica"}
    /\ healer_epoch \in Epoch
    /\ healer_replicas \in [Replica -> LogOffset \union {nil}]


Init ==
    /\ zk_leader \in Replica
    /\ zk_epoch = 1
    /\ zk_leader_epoch = 1
    /\ zk_status = "Normal"
    /\ old_leaders = {}
    /\ zk_catchup_index = nil

    /\ db = [r \in Replica |-> <<>>]
    /\ db_leader = [r \in Replica |-> zk_leader]
    /\ db_replicated = [r \in Replica |-> [r1 \in Replica |-> 0]]
    /\ db_epoch = [r \in Replica |-> zk_epoch]
    /\ db_status = [r \in Replica |-> IF zk_leader = r THEN "Writable" ELSE "Replica"]

    /\ next_req = 60
    /\ client_leader = [c \in Client |-> zk_leader]
    /\ client_success = [c \in Client |-> <<>>]
    /\ pending = [c \in Client |-> nil]
    /\ pending_db = [c \in Client |-> nil]
    /\ client_leader_epoch = [c \in Client |-> zk_leader_epoch]

    /\ healer_status = "Init"
    /\ healer_epoch = 1
    /\ healer_replicas = [r \in Replica |-> nil]


StartRequest(c) ==
    /\ pending[c] = nil
    /\ next_req < 60 + max_next_req
    /\ db_status[client_leader[c]] = "Writable"
    /\ next_req' = next_req + 1
    /\ pending' = [pending EXCEPT ![c] = next_req']
    /\ pending_db' = [pending_db EXCEPT ![c] = client_leader[c]]
    /\ LET leader == client_leader[c] IN
        /\ db' = [db EXCEPT ![leader] = Append(@, next_req')]
        /\ db_replicated' = [
            db_replicated EXCEPT ![leader][leader] = Len(db'[leader])]
    /\ UNCHANGED <<client_leader, client_success, client_leader_epoch>>
    /\ UNCHANGED <<db_leader, db_epoch, db_status>>
    /\ UNCHANGED zk_vars
    /\ UNCHANGED healer_vars


Replicate(r) ==
    /\ r /= db_leader[r]
    /\ db_status[r] = "Replica"
    /\ LET leader_data == db[db_leader[r]]
            new_len == Len(db[r]) + 1
            leader == db_leader[r]
        IN
            /\ Len(db[r]) < Len(leader_data)
            /\ db' = [db EXCEPT ![r] = Append(@, leader_data[new_len])]
            /\ db_replicated' = [db_replicated EXCEPT ![leader][r] = new_len]
    /\ UNCHANGED <<db_leader, db_epoch, db_status>>
    /\ UNCHANGED client_vars
    /\ UNCHANGED zk_vars
    /\ UNCHANGED healer_vars


new_repl == [r \in Replica |-> 0]

initReplicated(r) == 
    /\ db_replicated' = [
        db_replicated EXCEPT ![r] = [
            new_repl EXCEPT ![r] = Len(db[r])
        ]]


dbStatusFromZK(r) ==
    IF zk_status \in {"Normal", "WaitReplicaLog"} /\ ~(r \in old_leaders)
        THEN IF zk_leader = r
            THEN "Writable"
            ELSE "Replica"
        ELSE "Frozen"


DBUpdateLeader(r) ==
    /\ db_epoch[r] < zk_epoch
    /\ db_epoch' = [db_epoch EXCEPT ![r] = zk_epoch]
    /\ db_leader' = [db_leader EXCEPT ![r] = zk_leader]
    /\ db_status' = [db_status EXCEPT ![r] = dbStatusFromZK(r)]
    /\ IF db_leader[r] /= zk_leader
        THEN initReplicated(r)
        ELSE UNCHANGED db_replicated
    /\ UNCHANGED <<db>>
    /\ UNCHANGED zk_vars
    /\ UNCHANGED client_vars
    /\ UNCHANGED healer_vars


minOfSet(S) == CHOOSE x \in S: \A x1 \in S: x <= x1

replicatedSet(r, Q) == {db_replicated[r][r1]: r1 \in Q}

minReplicate(r, Q) == minOfSet(replicatedSet(r, Q))


DBResponse(c) ==
    /\ pending[c] /= nil
    /\ LET leader == pending_db[c] IN
        /\ \E index \in DOMAIN db[leader], Q \in Quorum:
            /\ pending[c] = db[leader][index]
            /\ index <= minReplicate(leader, Q)
    /\ pending' = [pending EXCEPT ![c] = nil]
    /\ pending_db' = [pending_db EXCEPT ![c] = nil]
    /\ client_success' = [client_success EXCEPT ![c] = Append(@, pending[c])]
    /\ UNCHANGED db_vars
    /\ UNCHANGED next_req
    /\ UNCHANGED <<client_leader, client_leader_epoch>>
    /\ UNCHANGED zk_vars
    /\ UNCHANGED healer_vars


ClientUpdateLeader(c) ==
    /\ client_leader_epoch[c] < zk_leader_epoch
    /\ client_leader_epoch' = [client_leader_epoch EXCEPT ![c] = zk_leader_epoch]
    /\ client_leader' = [client_leader EXCEPT ![c] = zk_leader]
    /\ pending' = [pending EXCEPT ![c] = nil]
    /\ pending_db' = [pending_db EXCEPT ![c] = nil]
    /\ UNCHANGED zk_vars
    /\ UNCHANGED healer_vars
    /\ UNCHANGED db_vars
    /\ UNCHANGED <<next_req, client_success>>



ReadyToChangeZKLeader ==
    /\ zk_leader_epoch < max_change_leader
    /\ Cardinality(Replica \ old_leaders) > replication_factor
    /\ zk_status = "Normal"

    /\ zk_status' = "ChangingLeader"
    /\ zk_epoch' = zk_epoch + 1
    /\ old_leaders' = old_leaders \union {zk_leader}

    /\ UNCHANGED <<zk_leader, zk_leader_epoch, zk_catchup_index>>
    /\ UNCHANGED client_vars
    /\ UNCHANGED db_vars
    /\ UNCHANGED healer_vars



zkStatusToHealerStatus ==
    IF zk_status = "ChangingLeader"
        THEN "UpdatingLeader"
        ELSE IF zk_status = "WaitReplicaLog"
            THEN "WaitReplica"
            ELSE "Init"


HealerUpdateState ==
    /\ healer_epoch < zk_epoch
    /\ healer_epoch' = zk_epoch
    /\ healer_replicas' = [r \in Replica |-> nil]
    /\ healer_status' = zkStatusToHealerStatus
    /\ UNCHANGED zk_vars
    /\ UNCHANGED client_vars
    /\ UNCHANGED db_vars


HealerGetDBLog(r) ==
    /\ healer_status = "UpdatingLeader"
    /\ healer_replicas[r] = nil
    /\ ~(r \in old_leaders)
    /\ db_epoch[r] = healer_epoch
    /\ healer_replicas' = [healer_replicas EXCEPT ![r] = Len(db[r])]
    /\ UNCHANGED <<healer_status, healer_epoch>>
    /\ UNCHANGED db_vars
    /\ UNCHANGED client_vars
    /\ UNCHANGED zk_vars


collectedDB == {r \in Replica: healer_replicas[r] /= nil}

HealerUpdateLeader ==
    /\ healer_status = "UpdatingLeader"
    /\ healer_epoch = zk_epoch
    /\ Cardinality(collectedDB) >= replication_factor
    /\ \E r \in collectedDB:
        /\ \A r1 \in collectedDB: healer_replicas[r] >= healer_replicas[r1]
        /\ zk_leader' = r
        /\ zk_catchup_index' = healer_replicas[r]
    /\ zk_status' = "WaitReplicaLog"
    /\ zk_epoch' = zk_epoch + 1
    /\ zk_leader_epoch' = zk_leader_epoch + 1
    /\ UNCHANGED old_leaders
    /\ UNCHANGED healer_vars
    /\ UNCHANGED db_vars
    /\ UNCHANGED client_vars


HealerUpdateToNormal ==
    /\ healer_status = "WaitReplica"
    /\ zk_status = "WaitReplicaLog"
    /\ \E Q \in Quorum:
        /\ ~(old_leaders \subseteq Q)
        /\ \A r \in Q: Len(db[r]) >= zk_catchup_index
    /\ zk_status' = "Normal"
    /\ zk_epoch' = zk_epoch + 1
    /\ UNCHANGED <<old_leaders, zk_leader_epoch, zk_leader, zk_catchup_index>>
    /\ UNCHANGED healer_vars
    /\ UNCHANGED db_vars
    /\ UNCHANGED client_vars


RecoverOldLeader(r) ==
    /\ r \in old_leaders
    /\ zk_status = "Normal"
    /\ db' = [db EXCEPT ![r] = <<>>]
    /\ db_status' = [db_status EXCEPT ![r] = "Replica"]
    /\ db_epoch' = [db_epoch EXCEPT ![r] = zk_epoch]
    /\ db_leader' = [db_leader EXCEPT ![r] = zk_leader]
    /\ db_replicated' = [db_replicated EXCEPT ![r] = new_repl]
    /\ old_leaders' = old_leaders \ {r}
    /\ UNCHANGED <<zk_epoch, zk_leader, zk_leader_epoch, zk_status, zk_catchup_index>>
    /\ UNCHANGED client_vars
    /\ UNCHANGED healer_vars



TerminateCond ==
    /\ next_req = 60 + max_next_req
    /\ zk_status = "Normal"
    /\ zk_leader_epoch = max_change_leader
    /\ zk_epoch >= 10
    /\ \A c \in Client: pending[c] = nil /\ pending_db[c] = nil
    /\ \A c \in Client: client_leader_epoch[c] = zk_leader_epoch
    /\ \A r \in Replica: db_epoch[r] = zk_epoch

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E c \in Client:
        \/ StartRequest(c)
        \/ DBResponse(c)
        \/ ClientUpdateLeader(c)
    \/ \E r \in Replica:
        \/ Replicate(r)
        \/ DBUpdateLeader(r)
        \/ RecoverOldLeader(r)
    
    \/ ReadyToChangeZKLeader
    \/ HealerUpdateState
    \/ \E r \in Replica: HealerGetDBLog(r)
    \/ HealerUpdateLeader
    \/ HealerUpdateToNormal

    \/ Terminated


Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)


Consistent ==
    /\ \A c \in Client:
        /\ Len(client_success[c]) <= Len(db[zk_leader])
        /\ \A x \in Range(client_success[c]): x \in Range(db[zk_leader])


Perms == Permutations(Replica)


Inv ==
    /\ zk_epoch < 11
    /\ zk_leader_epoch <= max_change_leader
    \* /\ (zk_leader_epoch >= 2) => (\A c \in Client: Len(client_success[c]) < 4)

Finish == <> TerminateCond

====