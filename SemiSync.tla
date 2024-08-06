-- ---- MODULE SemiSync ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANT Client, Replica, nil

VARIABLE
    zk_leader, zk_epoch, zk_pending, old_leaders,
    db, db_leader, db_replicated, db_epoch, db_readonly, catchup_index,
    next_req, client_leader, client_success, pending, pending_db, client_epoch,
    healer_run, healer_epoch, healer_replicas

vars == <<
    zk_leader, zk_epoch, zk_pending, old_leaders,
    db, db_leader, db_replicated, db_epoch, db_readonly, catchup_index,
    next_req, client_leader, client_success, pending, pending_db, client_epoch,
    healer_run, healer_epoch, healer_replicas
>>

zk_vars == <<zk_leader, zk_epoch, zk_pending, old_leaders>>
db_vars == <<db, db_leader, db_replicated, db_epoch, db_readonly, catchup_index>>
client_vars == <<
    next_req, client_leader, client_success, pending, pending_db, client_epoch>>
healer_vars == <<healer_run, healer_epoch, healer_replicas>>

max_next_req == 4

max_change_leader == 5

ReqSet == 60..(60 + max_next_req)

Epoch == 0..10

NullReqSet == ReqSet \union {nil}

NullReplica == Replica \union {nil}

LogOffset == 0..20

Range(f) == {f[x]: x \in DOMAIN f}

replication_factor == 2

Quorum == {x \in SUBSET Replica: Cardinality(x) = replication_factor}


TypeOK ==
    /\ zk_leader \in Replica
    /\ zk_epoch \in 1..max_change_leader
    /\ zk_pending \in BOOLEAN
    /\ old_leaders \subseteq Replica

    /\ db \in [Replica -> Seq(ReqSet)]
    /\ db_leader \in [Replica -> Replica]
    /\ db_replicated \in [Replica -> [Replica -> LogOffset]]
    /\ db_epoch \in [Replica -> Epoch]
    /\ db_readonly \in [Replica -> BOOLEAN]
    /\ catchup_index \in [Replica -> (LogOffset \union {nil})]

    /\ next_req \in ReqSet
    /\ client_leader \in [Client -> Replica]
    /\ client_success \in [Client -> Seq(ReqSet)]
    /\ pending \in [Client -> NullReqSet]
    /\ pending_db \in [Client -> NullReplica]
    /\ client_epoch \in [Client -> Epoch]

    /\ healer_run \in BOOLEAN 
    /\ healer_epoch \in Epoch
    /\ healer_replicas \in [Replica -> LogOffset \union {nil}]


Init ==
    /\ zk_leader \in Replica
    /\ zk_epoch = 1
    /\ zk_pending = FALSE
    /\ old_leaders = {}

    /\ db = [r \in Replica |-> <<>>]
    /\ db_leader = [r \in Replica |-> zk_leader]
    /\ db_replicated = [r \in Replica |-> [r1 \in Replica |-> 0]]
    /\ db_epoch = [r \in Replica |-> zk_epoch]
    /\ db_readonly = [r \in Replica |-> zk_leader /= r]
    /\ catchup_index = [r \in Replica |-> nil]

    /\ next_req = 60
    /\ client_leader = [c \in Client |-> zk_leader]
    /\ client_success = [c \in Client |-> <<>>]
    /\ pending = [c \in Client |-> nil]
    /\ pending_db = [c \in Client |-> nil]
    /\ client_epoch = [c \in Client |-> zk_epoch]

    /\ healer_run = FALSE
    /\ healer_epoch = 1
    /\ healer_replicas = [r \in Replica |-> nil]


StartRequest(c) ==
    /\ pending[c] = nil
    /\ next_req < 60 + max_next_req
    \* /\ client_epoch[c] = db_epoch[client_leader[c]] \* TODO Remove
    /\ ~db_readonly[client_leader[c]]
    /\ next_req' = next_req + 1
    /\ pending' = [pending EXCEPT ![c] = next_req']
    /\ pending_db' = [pending_db EXCEPT ![c] = client_leader[c]]
    /\ LET leader == client_leader[c] IN
        /\ db' = [db EXCEPT ![leader] = Append(@, next_req')]
        /\ db_replicated' = [
            db_replicated EXCEPT ![leader][leader] = Len(db'[leader])]
    /\ UNCHANGED <<client_leader, client_success, client_epoch>>
    /\ UNCHANGED <<db_leader, db_epoch, db_readonly, catchup_index>>
    /\ UNCHANGED zk_vars
    /\ UNCHANGED healer_vars


Replicate(r) ==
    /\ r /= db_leader[r]
    /\ db_epoch[r] = db_epoch[db_leader[r]]
    /\ LET leader_data == db[db_leader[r]]
            new_len == Len(db[r]) + 1
            leader == db_leader[r]
        IN
            /\ Len(db[r]) < Len(leader_data)
            /\ db' = [db EXCEPT ![r] = Append(@, leader_data[new_len])]
            /\ db_replicated' = [db_replicated EXCEPT ![leader][r] = new_len]
    /\ UNCHANGED <<db_leader, db_epoch, db_readonly, catchup_index>>
    /\ UNCHANGED client_vars
    /\ UNCHANGED zk_vars
    /\ UNCHANGED healer_vars


new_repl == [r \in Replica |-> 0]

initReplicated(r) == 
    /\ db_replicated' = [
        db_replicated EXCEPT ![r] = [
            new_repl EXCEPT ![r] = Len(db[r])
        ]]


DBUpdateLeader(r) ==
    /\ db_epoch[r] < zk_epoch
    /\ db_epoch' = [db_epoch EXCEPT ![r] = zk_epoch]
    /\ db_leader' = [db_leader EXCEPT ![r] = zk_leader]
    /\ db_readonly' = [db_readonly EXCEPT ![r] = zk_pending]
    /\ initReplicated(r)
    /\ UNCHANGED <<db, catchup_index>>
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
    /\ UNCHANGED <<client_leader, client_epoch>>
    /\ UNCHANGED zk_vars
    /\ UNCHANGED healer_vars


ClientUpdateLeader(c) ==
    /\ client_epoch[c] < zk_epoch
    /\ client_epoch' = [client_epoch EXCEPT ![c] = zk_epoch]
    /\ client_leader' = [client_leader EXCEPT ![c] = zk_leader]
    /\ pending' = [pending EXCEPT ![c] = nil]
    /\ pending_db' = [pending_db EXCEPT ![c] = nil]
    /\ UNCHANGED zk_vars
    /\ UNCHANGED healer_vars
    /\ UNCHANGED db_vars
    /\ UNCHANGED <<next_req, client_success>>



ReadyToChangeZKLeader ==
    /\ zk_epoch < max_change_leader - 1
    /\ Cardinality(Replica \ old_leaders) > replication_factor
    /\ ~zk_pending
    /\ zk_pending' = TRUE
    /\ zk_epoch' = zk_epoch + 1
    /\ old_leaders' = old_leaders \union {zk_leader}
    /\ UNCHANGED zk_leader
    /\ UNCHANGED client_vars
    /\ UNCHANGED db_vars
    /\ UNCHANGED healer_vars


HealerUpdateState ==
    /\ healer_epoch < zk_epoch
    /\ healer_epoch' = zk_epoch
    /\ healer_replicas' = [r \in Replica |-> nil]
    /\ healer_run' = zk_pending
    /\ UNCHANGED zk_vars
    /\ UNCHANGED client_vars
    /\ UNCHANGED db_vars


HealerGetDBLog(r) ==
    /\ healer_run
    /\ healer_replicas[r] = nil
    /\ ~(r \in old_leaders)
    /\ db_epoch[r] = healer_epoch
    /\ healer_replicas' = [healer_replicas EXCEPT ![r] = Len(db[r])]
    /\ UNCHANGED <<healer_run, healer_epoch>>
    /\ UNCHANGED db_vars
    /\ UNCHANGED client_vars
    /\ UNCHANGED zk_vars


collectedDB == {r \in Replica: healer_replicas[r] /= nil}


HealerUpdateLeader ==
    /\ healer_run
    /\ healer_epoch = zk_epoch
    /\ Cardinality(collectedDB) >= replication_factor
    /\ \E r \in collectedDB:
        /\ \A r1 \in collectedDB: healer_replicas[r] >= healer_replicas[r1]
        /\ zk_leader' = r
    /\ zk_pending' = FALSE
    /\ zk_epoch' = zk_epoch + 1
    /\ UNCHANGED old_leaders
    /\ UNCHANGED healer_vars
    /\ UNCHANGED db_vars
    /\ UNCHANGED client_vars


PrepareRecoverOldLeader(r) ==
    /\ r \in old_leaders
    /\ zk_pending = FALSE
    /\ catchup_index' = [catchup_index EXCEPT ![r] = Len(db[zk_leader])]
    /\ db' = [db EXCEPT ![r] = <<>>]
    /\ db_readonly' = [db_readonly EXCEPT ![r] = TRUE]
    /\ db_epoch' = [db_epoch EXCEPT ![r] = zk_epoch]
    /\ db_leader' = [db_leader EXCEPT ![r] = zk_leader]
    /\ db_replicated' = [db_replicated EXCEPT ![r] = new_repl]
    /\ UNCHANGED zk_epoch
    /\ UNCHANGED zk_leader
    /\ UNCHANGED zk_pending
    /\ UNCHANGED client_vars
    /\ UNCHANGED healer_vars
    /\ UNCHANGED old_leaders


DoRecoverOldLeader(r) ==
    /\ r \in old_leaders
    /\ catchup_index[r] /= nil
    /\ Len(db[r]) >= catchup_index[r]
    /\ old_leaders' = old_leaders \ {r}
    /\ db_readonly' = [db_readonly EXCEPT ![r] = zk_leader /= r]
    /\ UNCHANGED <<zk_epoch, zk_leader, zk_pending>>
    /\ UNCHANGED client_vars
    /\ UNCHANGED <<db, db_leader, db_replicated, db_epoch, catchup_index>>
    /\ UNCHANGED healer_vars


Terminated ==
    /\ next_req = 60 + max_next_req
    /\ UNCHANGED vars


Next ==
    \/ \E c \in Client:
        \/ StartRequest(c)
        \/ DBResponse(c)
        \/ ClientUpdateLeader(c)
    \/ \E r \in Replica:
        \/ Replicate(r)
        \/ DBUpdateLeader(r)
        \/ PrepareRecoverOldLeader(r)
        \/ DoRecoverOldLeader(r)
    
    \/ ReadyToChangeZKLeader
    \/ HealerUpdateState
    \/ \E r \in Replica: HealerGetDBLog(r)
    \/ HealerUpdateLeader

    \/ Terminated


Consistent ==
    /\ \A c \in Client:
        /\ Len(client_success[c]) <= Len(db[zk_leader])
        /\ \A x \in Range(client_success[c]): x \in Range(db[zk_leader])


Perms == Permutations(Replica)

====