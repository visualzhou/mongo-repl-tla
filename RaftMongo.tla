--------------------------------- MODULE RaftMongo ---------------------------------
\* This is the formal specification for the Raft consensus algorithm in MongoDB

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
\* Candidate is not used, but this is fine.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

----
\* Global variables

\* The server's term number.
VARIABLE globalCurrentTerm

----
\* The following variables are all per server (functions with domain Server).

\* The server's state (Follower, Candidate, or Leader).
VARIABLE state

\* The commit point learned by each server.
VARIABLE commitPoint

electionVars == <<globalCurrentTerm, state>>
serverVars == <<electionVars, commitPoint>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
logVars == <<log>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<serverVars, logVars>>

----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
GetTerm(xlog, index) == IF index = 0 THEN 0 ELSE xlog[index].term
LogTerm(i, index) == GetTerm(log[i], index)
LastTerm(xlog) == GetTerm(xlog, Len(xlog))

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----
\* Define initial values for all variables

InitServerVars == /\ globalCurrentTerm = 0
                  /\ state             = [i \in Server |-> Follower]
                  /\ commitPoint       = [i \in Server |-> [term |-> 0, index |-> 0]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
Init == /\ InitServerVars
        /\ InitLogVars

----
\* Message handlers
\* i = recipient, j = sender, m = message

AppendOplog(i, j) ==
    /\ Len(log[i]) < Len(log[j])
    /\ LastTerm(log[i]) = LogTerm(j, Len(log[i]))
    /\ log' = [log EXCEPT ![i] = Append(log[i], log[j][Len(log[i]) + 1])]
    /\ UNCHANGED <<serverVars>>

CanRollbackOplog(i, j) ==
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
    /\ UNCHANGED <<serverVars>>

\* The set of nodes that has log[me][logIndex] in their oplog
Agree(me, logIndex) ==
    { node \in Server :
        /\ Len(log[node]) >= logIndex
        /\ LogTerm(me, logIndex) = LogTerm(node, logIndex) }

IsCommitted(me, logIndex) ==
    /\ Agree(me, logIndex) \in Quorum
    \* If we comment out the following line, a replicated log entry from old primary will voilate the safety.
    \* [ P (2), S (), S ()]
    \* [ S (2), S (), P (3)]
    \* [ S (2), S (2), P (3)] !!! the log from term 2 shouldn't be considered as committed.
    /\ LogTerm(me, logIndex) = globalCurrentTerm

\* RollbackCommitted and NeverRollbackCommitted are not actions.
\* They are used for verification.
RollbackCommitted(i) ==
    \E j \in Server:
        /\ CanRollbackOplog(i, j)
        /\ IsCommitted(i, Len(log[i]))

NeverRollbackCommitted ==
    \A i \in Server: ~RollbackCommitted(i)

\* ACTION
\* i = the new primary node.
BecomePrimaryByMagic(i) ==
    LET notBehind(me, j) ==
            \/ LastTerm(log[me]) > LastTerm(log[j])
            \/ /\ LastTerm(log[me]) = LastTerm(log[j])
               /\ Len(log[me]) >= Len(log[j])
        ayeVoters(me) ==
            { index \in Server : notBehind(me, index) }
    IN /\ ayeVoters(i) \in Quorum
       /\ state' = [index \in Server |-> IF index = i THEN Leader ELSE Follower]
       /\ globalCurrentTerm' = globalCurrentTerm + 1
       /\ UNCHANGED <<commitPoint, logVars>>

\* ACTION
\* Leader i receives a client request to add v to the log.
ClientWrite(i, v) ==
    /\ state[i] = Leader
    /\ LET entry == [term  |-> globalCurrentTerm,
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<serverVars>>

\* ACTION
AdvanceCommitPoint ==
    \E leader \in Server :
        /\ state[leader] = Leader
        /\ IsCommitted(leader, Len(log[leader]))
        /\ commitPoint' = [commitPoint EXCEPT ![leader] = [term |-> LastTerm(log[leader]), index |-> Len(log[leader])]]
        /\ UNCHANGED <<electionVars, logVars>>

\* ACTION
\* Node i learns the commit point from j via heartbeat.
LearnCommitPoint(i, j) ==
    /\ \/ commitPoint[i].term < commitPoint[j].term
       \/ /\ commitPoint[i].term = commitPoint[j].term
          /\ commitPoint[i].index < commitPoint[j].index
    /\ commitPoint' = [commitPoint EXCEPT ![i] = commitPoint[j]]
    /\ UNCHANGED <<electionVars, logVars>>

RollbackBeforeCommitPoint(i) ==
    /\ \E j \in Server:
        /\ CanRollbackOplog(i, j)
    /\ \/ LastTerm(log[i]) < commitPoint[i].term
       \/ /\ LastTerm(log[i]) = commitPoint[i].term
          /\ Len(log[i]) <= commitPoint[i].index

NeverRollbackBeforeCommitPoint == \A i \in Server: ~RollbackBeforeCommitPoint(i)

----
\* Defines how the variables may transition.
Next == /\
           \/ \E i,j \in Server : AppendOplog(i, j)
           \/ \E i,j \in Server : RollbackOplog(i, j)
           \/ \E i \in Server : BecomePrimaryByMagic(i)
           \/ \E i \in Server, v \in Value : ClientWrite(i, v)
           \/ AdvanceCommitPoint
           \/ \E i, j \in Server : LearnCommitPoint(i, j)

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

===============================================================================
