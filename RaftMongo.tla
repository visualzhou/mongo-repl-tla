--------------------------------- MODULE RaftMongo ---------------------------------
\* This is the formal specification for the Raft consensus algorithm in MongoDB

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* Server states.
\* Candidate is not used, but this is fine.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

----
\* Global variables

\* Servers in a given config version
\* e.g. << {S1, S2}, {S1, S2, S3} >>
VARIABLE configs

CONSTANTS InitConfig, NewConfig

\* The server's term number in a given config version
VARIABLE globalCurrentTerm

\* The commit point.
VARIABLE commitPoint

----
\* The following variables are all per server (functions with domain Server).

\* The config version on servers.
VARIABLE nodeConfigVersion
configVars == <<configs, nodeConfigVersion>>

\* The server's state (Follower, Candidate, or Leader).
VARIABLE state

electionVars == <<globalCurrentTerm, state>>
serverVars == <<electionVars, configVars>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
logVars == <<log, commitPoint>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<serverVars, logVars>>

----
\* Helpers

\* The servers that are in the same config as i.
ServerViewOn(i) == configs[nodeConfigVersion[i]]

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum(me) == {sub \in SUBSET(ServerViewOn(me)) : Cardinality(sub) * 2 > Cardinality(ServerViewOn(me))}

\* The term of the last entry in a log, or 0 if the log is empty.
GetTerm(xlog, index) == IF index = 0 THEN 0 ELSE xlog[index].term
LogTerm(i, index) == GetTerm(log[i], index)
LastTerm(xlog) == GetTerm(xlog, Len(xlog))

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

HasConfig(i) == nodeConfigVersion[i] /= 0
----
\* Define initial values for all variables

InitServerVars == /\ globalCurrentTerm = << 0 >>
                  /\ state             = [i \in Server |-> Follower]
                  /\ commitPoint       = [term |-> 0, index |-> 0]
                  /\ configs           = << InitConfig >>
                  /\ nodeConfigVersion = [i \in Server |-> IF i \in InitConfig THEN 1 ELSE 0 ]
InitLogVars == /\ log          = [i \in Server |-> << >>]
Init == /\ InitServerVars
        /\ InitLogVars

----
\* Message handlers
\* i = recipient, j = sender, m = message

AppendOplog(i, j) ==
    \* /\ state[i] = Follower  \* Disable primary catchup and draining
    /\ HasConfig(i)
    /\ nodeConfigVersion[i] = nodeConfigVersion[j]
    /\ j \in ServerViewOn(i)  \* j is in the config of i.
    /\ Len(log[i]) < Len(log[j])
    /\ LastTerm(log[i]) = LogTerm(j, Len(log[i]))
    /\ log' = [log EXCEPT ![i] = Append(log[i], log[j][Len(log[i]) + 1])]
    /\ UNCHANGED <<serverVars, commitPoint>>

CanRollbackOplog(i, j) ==
    /\ HasConfig(i)
    /\ nodeConfigVersion[i] = nodeConfigVersion[j]
    /\ j \in ServerViewOn(i)  \* j is in the config of i.
    /\ Len(log[i]) > 0
    /\ \* The log with later term is more up-to-date
       LastTerm(log[i]) < LastTerm(log[j])
    /\
       \/ Len(log[i]) > Len(log[j])
       \* There seems no short-cut of OR clauses, so I have to specify the negative case
       \/ /\ Len(log[i]) <= Len(log[j])
          /\ LastTerm(log[i]) /= LogTerm(j, Len(log[i]))

RollbackOplog(i, j) ==
    /\ CanRollbackOplog(i, j)
    \* Rollback 1 oplog entry
    /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |-> log[i][index2]]
         IN log' = [log EXCEPT ![i] = new]
    /\ UNCHANGED <<serverVars, commitPoint>>

\* The set of nodes that has log[me][logIndex] in their oplog
Agree(me, logIndex) ==
    { node \in ServerViewOn(me) :
        /\ Len(log[node]) >= logIndex
        /\ LogTerm(me, logIndex) = LogTerm(node, logIndex) }

IsCommitted(me, logIndex) ==
    /\ HasConfig(me)
    /\ Agree(me, logIndex) \in Quorum(me)
    \* If we comment out the following line, a replicated log entry from old primary will voilate the safety.
    \* [ P (2), S (), S ()]
    \* [ S (2), S (), P (3)]
    \* [ S (2), S (2), P (3)] !!! the log from term 2 shouldn't be considered as committed.
    /\ LogTerm(me, logIndex) = globalCurrentTerm[nodeConfigVersion[me]]

\* Commit point is visible to clients via write concerns.
\* Commit point only cares about the config on the primary.
AdvanceCommitPoint ==
    \E node \in Server :
        /\ HasConfig(node)
        /\ state[node] = Leader
        /\ IsCommitted(node, Len(log[node]))
        /\ commitPoint' = [term |-> LastTerm(log[node]), index |-> Len(log[node])]
        /\ UNCHANGED <<electionVars, configVars, log>>

Reconfig(i, newConfig) ==
    /\ HasConfig(i)
    /\ state[i] = Leader
    /\ nodeConfigVersion[i] = 1
    /\ i \in NewConfig
    /\ configs' = Append(configs, newConfig)
    /\ nodeConfigVersion' = [nodeConfigVersion EXCEPT ![i] = nodeConfigVersion[i] + 1]
    /\ globalCurrentTerm' = Append(globalCurrentTerm, globalCurrentTerm[nodeConfigVersion[i]])
    /\ PrintT("Reconfig", i)
    /\ UNCHANGED <<state, logVars>>

PropagateNewConfig(i, j) ==
    LET newCV == nodeConfigVersion[j]
        oldCV == nodeConfigVersion[i]
    IN
    /\ nodeConfigVersion[i] < nodeConfigVersion[j] \* i has the old config, j has the new one.
    /\ i \in ServerViewOn(j)  \* Only learn the config if it includes me.
    /\ nodeConfigVersion' = [nodeConfigVersion EXCEPT ![i] = nodeConfigVersion[j]]
    /\ state' = [state EXCEPT ![i] = IF globalCurrentTerm[oldCV] < globalCurrentTerm[newCV] THEN Follower ELSE state[i],
                              ![j] = IF globalCurrentTerm[oldCV] > globalCurrentTerm[newCV] THEN Follower ELSE state[j]]
    /\ globalCurrentTerm' = [ globalCurrentTerm EXCEPT ![newCV] = Max({globalCurrentTerm[oldCV], globalCurrentTerm[newCV]}) ]
    /\ UNCHANGED <<configs, logVars>>

\* ACTION
\* i = the new primary node.
BecomePrimaryByMagic(i) ==
    LET notBehind(me, j) ==
            \/ LastTerm(log[me]) > LastTerm(log[j])
            \/ /\ LastTerm(log[me]) = LastTerm(log[j])
               /\ Len(log[me]) >= Len(log[j])
        ayeVoters(me) ==
            { index \in ServerViewOn(me) : /\ nodeConfigVersion[index] = nodeConfigVersion[me]
                                           /\ notBehind(me, index) }
    IN /\ HasConfig(i)
       /\ ayeVoters(i) \in Quorum(i)
       /\ state' = [index \in Server |-> IF index \notin ServerViewOn(i)
                                         THEN state[index]
                                         ELSE IF index = i THEN Leader ELSE Follower]
       /\ globalCurrentTerm' = [ globalCurrentTerm EXCEPT ![nodeConfigVersion[i]] = globalCurrentTerm[nodeConfigVersion[i]] + 1 ]
       /\ UNCHANGED <<configVars, logVars>>

\* ACTION
\* Leader i receives a client request to add v to the log.
ClientWrite(i) ==
    /\ HasConfig(i)
    /\ state[i] = Leader
    /\ LET entry == [term  |-> globalCurrentTerm[nodeConfigVersion[i]]]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<serverVars, commitPoint>>

----
AppendOplogAction ==
    \E i,j \in Server : AppendOplog(i, j)

RollbackOplogAction ==
    \E i,j \in Server : RollbackOplog(i, j)

BecomePrimaryByMagicAction ==
    \E i \in Server : BecomePrimaryByMagic(i)

ClientWriteAction ==
    \E i \in Server : ClientWrite(i)

ReconfigAction ==
    \E i \in Server : Reconfig(i, NewConfig)

PropagateNewConfigAction ==
    \E i, j \in Server : PropagateNewConfig(i, j)

----
\* Defines how the variables may transition.
Next ==
    \* --- Replication protocol
    \/ AppendOplogAction
    \/ RollbackOplogAction
    \/ BecomePrimaryByMagicAction
    \/ ClientWriteAction
    \/ AdvanceCommitPoint
    \/ ReconfigAction
    \/ PropagateNewConfigAction

Liveness ==
    /\ SF_vars(AppendOplogAction)
    /\ SF_vars(RollbackOplogAction)
    \* A new primary should eventually write one entry.
    /\ WF_vars(\E i \in Server : LastTerm(log[i]) # globalCurrentTerm[nodeConfigVersion[i]] /\ ClientWrite(i))
    \* /\ WF_vars(ClientWriteAction)

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars /\ Liveness

\* RollbackCommitted and NeverRollbackCommitted are not actions.
\* They are used for verification.
RollbackCommitted(i) ==
    /\ Len(log[i]) = commitPoint.index
    /\ LastTerm(log[i]) = commitPoint.term
    /\ \E j \in Server: CanRollbackOplog(i, j)

NeverRollbackCommitted ==
    \A i \in Server: ~RollbackCommitted(i)

===============================================================================
