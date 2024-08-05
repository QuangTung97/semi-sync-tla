-- ---- MODULE SemiSync ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANT Client, Replica, nil

VARIABLE
    zk_leader, zk_epoch, zk_pending,
    db, db_leader, db_replicated,
    next_req, client_leader, client_success, pending, pending_db,
    healer_run, healer_epoch, healer_replicas

vars == <<
    zk_leader, zk_epoch, zk_pending,
    db, db_leader, db_replicated,
    next_req, client_leader, client_success, pending, pending_db,
    healer_run, healer_epoch, healer_replicas
>>

zk_vars == <<zk_leader, zk_epoch, zk_pending>>
db_vars == <<db, db_leader, db_replicated>>
client_vars == <<next_req, client_leader, client_success, pending, pending_db>>
healer_vars == <<healer_run, healer_epoch, healer_replicas>>

max_next_req == 4

max_change_leader == 5

ReqSet == 60..(60 + max_next_req)

Epoch == 0..10

NullReqSet == ReqSet \union {nil}

NullReplica == Replica \union {nil}

LogOffset == 0..20

Range(f) == {f[x]: x \in DOMAIN f}


TypeOK ==
    /\ zk_leader \in Replica
    /\ zk_epoch \in 1..max_change_leader
    /\ zk_pending \in BOOLEAN

    /\ db \in [Replica -> Seq(ReqSet)]
    /\ db_leader \in [Replica -> Replica]
    /\ db_replicated \in [Replica -> [Replica -> LogOffset]]

    /\ next_req \in ReqSet
    /\ client_leader \in [Client -> Replica]
    /\ client_success \in [Client -> Seq(ReqSet)]
    /\ pending \in [Client -> NullReqSet]
    /\ pending_db \in [Client -> NullReplica]

    /\ healer_run \in BOOLEAN 
    /\ healer_epoch \in Epoch
    /\ healer_replicas \in [Replica -> LogOffset \union {nil}]


Init ==
    /\ zk_leader \in Replica
    /\ zk_epoch = 1
    /\ zk_pending = FALSE

    /\ db = [r \in Replica |-> <<>>]
    /\ db_leader = [r \in Replica |-> zk_leader]
    /\ db_replicated = [r \in Replica |-> [r1 \in Replica |-> 0]]

    /\ next_req = 60
    /\ client_leader = [c \in Client |-> zk_leader]
    /\ client_success = [c \in Client |-> <<>>]
    /\ pending = [c \in Client |-> nil]
    /\ pending_db = [c \in Client |-> nil]

    /\ healer_run = FALSE
    /\ healer_epoch = 1
    /\ healer_replicas = [r \in Replica |-> nil]


StartRequest(c) ==
    /\ pending[c] = nil
    /\ next_req < 60 + max_next_req
    /\ next_req' = next_req + 1
    /\ pending' = [pending EXCEPT ![c] = next_req']
    /\ pending_db' = [pending_db EXCEPT ![c] = client_leader[c]]
    /\ LET leader == client_leader[c] IN
        /\ db' = [db EXCEPT ![leader] = Append(@, next_req')]
        /\ db_replicated' = [
            db_replicated EXCEPT ![leader][leader] = Len(db'[leader])]
    /\ UNCHANGED <<client_leader, client_success>>
    /\ UNCHANGED db_leader
    /\ UNCHANGED zk_vars
    /\ UNCHANGED healer_vars


Replicate(r) ==
    /\ r /= db_leader[r]
    /\ LET leader_data == db[db_leader[r]]
            new_len == Len(db[r]) + 1
            leader == db_leader[r]
        IN
            /\ Len(db[r]) < Len(leader_data)
            /\ db' = [db EXCEPT ![r] = Append(@, leader_data[new_len])]
            /\ db_replicated' = [db_replicated EXCEPT ![leader][r] = new_len]
    /\ UNCHANGED db_leader
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
    /\ db_leader[r] /= zk_leader
    /\ db_leader' = [db_leader EXCEPT ![r] = zk_leader]
    /\ initReplicated(r)
    /\ UNCHANGED <<db>>
    /\ UNCHANGED zk_vars
    /\ UNCHANGED client_vars
    /\ UNCHANGED healer_vars


minOfSet(S) == CHOOSE x \in S: \A x1 \in S: x <= x1

minReplicate(r) ==
    minOfSet({db_replicated[r][r1]: r1 \in DOMAIN db_replicated[r]})


DBResponse(c) ==
    /\ pending[c] /= nil
    /\ LET leader == pending_db[c] IN
        /\ \E index \in DOMAIN db[leader]:
            /\ pending[c] = db[leader][index]
            /\ index <= minReplicate(leader)
    /\ pending' = [pending EXCEPT ![c] = nil]
    /\ pending_db' = [pending_db EXCEPT ![c] = nil]
    /\ client_success' = [client_success EXCEPT ![c] = Append(@, pending[c])]
    /\ UNCHANGED <<db, db_leader, db_replicated>>
    /\ UNCHANGED next_req
    /\ UNCHANGED <<client_leader>>
    /\ UNCHANGED zk_vars
    /\ UNCHANGED healer_vars


ClientUpdateLeader(c) ==
    /\ client_leader[c] /= zk_leader
    /\ client_leader' = [client_leader EXCEPT ![c] = zk_leader]
    /\ pending' = [pending EXCEPT ![c] = nil]
    /\ pending_db' = [pending_db EXCEPT ![c] = nil]
    /\ UNCHANGED zk_vars
    /\ UNCHANGED healer_vars
    /\ UNCHANGED db_vars
    /\ UNCHANGED <<next_req, client_success>>



ReadyToChangeZKLeader ==
    /\ zk_epoch < max_change_leader - 1
    /\ ~zk_pending
    /\ zk_pending' = TRUE
    /\ zk_epoch' = zk_epoch + 1
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
    /\ healer_replicas' = [healer_replicas EXCEPT ![r] = Len(db[r])]
    /\ UNCHANGED <<healer_run, healer_epoch>>
    /\ UNCHANGED db_vars
    /\ UNCHANGED client_vars
    /\ UNCHANGED zk_vars


collectedDB == {r \in Replica: healer_replicas[r] /= nil}


HealerUpdateLeader ==
    /\ healer_run
    /\ healer_epoch = zk_epoch
    /\ Cardinality(collectedDB) >= 1 \* TODO
    /\ \E r \in collectedDB: zk_leader' = r \* TODO Choose Max
    /\ zk_pending' = FALSE
    /\ zk_epoch' = zk_epoch + 1
    /\ UNCHANGED healer_vars
    /\ UNCHANGED db_vars
    /\ UNCHANGED client_vars


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
    \/ ReadyToChangeZKLeader
    \/ HealerUpdateState
    \/ \E r \in Replica: HealerGetDBLog(r)
    \/ HealerUpdateLeader

    \/ Terminated

Consistent ==
    /\ \A c \in Client:
        /\ Len(client_success[c]) <= Len(db[zk_leader])
        /\ \A x \in Range(client_success[c]): x \in Range(db[zk_leader])



====