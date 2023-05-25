---- MODULE stack ----

EXTENDS Sequences, Integers, TLC
CONSTANT WORKERS_TOTAL

(*--algorithm stack

variables
    Stack = <<>>,
    seq_lock = 0,

define
    \* invariant
    NoRaceCondition == seq_lock <= 1
    \* temporal property
    FinishedEmpty == Len(Stack) = 0
end define;

macro AQUIRE(lock) begin
    lock := lock + 1;
end macro

macro RELEASE(lock) begin
    lock := lock - 1;
end macro

macro WAIT(lock) begin
    await lock = 0;
end macro

process worker \in 1..WORKERS_TOTAL
variables
    topBeforePush = "",
    topBeforePop = "",

begin
pushForEmpty:
    WAIT(seq_lock);
    AQUIRE(seq_lock);
    if Stack /= <<>> then
        topBeforePush := Head(Stack);
    else
        \* special case for empty Stack
        Stack := Append(Stack, Len(Stack));
        goto unlockAfterInitialPush;
    end if;

pushContinue:
    RELEASE(seq_lock);

pushForNotEmpty:
    WAIT(seq_lock);
    
    if Stack = <<>> then
        goto pushForEmpty;
    else
        \* CAS
        if topBeforePush = Head(Stack) then
            AQUIRE(seq_lock);
            Stack := Append(Stack, Len(Stack));
        else
            goto pushForNotEmpty;
        end if;
    end if;

unlockAfterInitialPush:
    RELEASE(seq_lock);

popForEmptyStart:
    WAIT(seq_lock);
    AQUIRE(seq_lock);
    if Stack /= <<>> then
        topBeforePop := Head(Stack);
    else
        goto popForEmptyEnd;
    end if;

popContinue:
    RELEASE(seq_lock);  

popForNotEmpty:
    \* something like CAS
    WAIT(seq_lock);
    if Stack = <<>> then
        goto popForEmptyStart;
    else
        if topBeforePop = Head(Stack) then
            seq_lock := seq_lock + 1;
            Stack := SubSeq(Stack, 1, Len(Stack)-1);
        else
            goto popForNotEmpty;
        end if;
    end if;

popForEmptyEnd:
    RELEASE(seq_lock);

end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "b0d9749e" /\ chksum(tla) = "5f27e26f")
VARIABLES Stack, seq_lock, pc

(* define statement *)
NoRaceCondition == seq_lock <= 1

FinishedEmpty == Len(Stack) = 0

VARIABLES topBeforePush, topBeforePop

vars == << Stack, seq_lock, pc, topBeforePush, topBeforePop >>

ProcSet == (1..WORKERS_TOTAL)

Init == (* Global variables *)
        /\ Stack = <<>>
        /\ seq_lock = 0
        (* Process worker *)
        /\ topBeforePush = [self \in 1..WORKERS_TOTAL |-> ""]
        /\ topBeforePop = [self \in 1..WORKERS_TOTAL |-> ""]
        /\ pc = [self \in ProcSet |-> "pushForEmpty"]

pushForEmpty(self) == /\ pc[self] = "pushForEmpty"
                      /\ seq_lock = 0
                      /\ seq_lock' = seq_lock + 1
                      /\ IF Stack /= <<>>
                            THEN /\ topBeforePush' = [topBeforePush EXCEPT ![self] = Head(Stack)]
                                 /\ pc' = [pc EXCEPT ![self] = "pushContinue"]
                                 /\ Stack' = Stack
                            ELSE /\ Stack' = Append(Stack, Len(Stack))
                                 /\ pc' = [pc EXCEPT ![self] = "unlockAfterInitialPush"]
                                 /\ UNCHANGED topBeforePush
                      /\ UNCHANGED topBeforePop

pushContinue(self) == /\ pc[self] = "pushContinue"
                      /\ seq_lock' = seq_lock - 1
                      /\ pc' = [pc EXCEPT ![self] = "pushForNotEmpty"]
                      /\ UNCHANGED << Stack, topBeforePush, topBeforePop >>

pushForNotEmpty(self) == /\ pc[self] = "pushForNotEmpty"
                         /\ seq_lock = 0
                         /\ IF Stack = <<>>
                               THEN /\ pc' = [pc EXCEPT ![self] = "pushForEmpty"]
                                    /\ UNCHANGED << Stack, seq_lock >>
                               ELSE /\ IF topBeforePush[self] = Head(Stack)
                                          THEN /\ seq_lock' = seq_lock + 1
                                               /\ Stack' = Append(Stack, Len(Stack))
                                               /\ pc' = [pc EXCEPT ![self] = "unlockAfterInitialPush"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "pushForNotEmpty"]
                                               /\ UNCHANGED << Stack, seq_lock >>
                         /\ UNCHANGED << topBeforePush, topBeforePop >>

unlockAfterInitialPush(self) == /\ pc[self] = "unlockAfterInitialPush"
                                /\ seq_lock' = seq_lock - 1
                                /\ pc' = [pc EXCEPT ![self] = "popForEmptyStart"]
                                /\ UNCHANGED << Stack, topBeforePush, 
                                                topBeforePop >>

popForEmptyStart(self) == /\ pc[self] = "popForEmptyStart"
                          /\ seq_lock = 0
                          /\ seq_lock' = seq_lock + 1
                          /\ IF Stack /= <<>>
                                THEN /\ topBeforePop' = [topBeforePop EXCEPT ![self] = Head(Stack)]
                                     /\ pc' = [pc EXCEPT ![self] = "popContinue"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "popForEmptyEnd"]
                                     /\ UNCHANGED topBeforePop
                          /\ UNCHANGED << Stack, topBeforePush >>

popContinue(self) == /\ pc[self] = "popContinue"
                     /\ seq_lock' = seq_lock - 1
                     /\ pc' = [pc EXCEPT ![self] = "popForNotEmpty"]
                     /\ UNCHANGED << Stack, topBeforePush, topBeforePop >>

popForNotEmpty(self) == /\ pc[self] = "popForNotEmpty"
                        /\ seq_lock = 0
                        /\ IF Stack = <<>>
                              THEN /\ pc' = [pc EXCEPT ![self] = "popForEmptyStart"]
                                   /\ UNCHANGED << Stack, seq_lock >>
                              ELSE /\ IF topBeforePop[self] = Head(Stack)
                                         THEN /\ seq_lock' = seq_lock + 1
                                              /\ Stack' = SubSeq(Stack, 1, Len(Stack)-1)
                                              /\ pc' = [pc EXCEPT ![self] = "popForEmptyEnd"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "popForNotEmpty"]
                                              /\ UNCHANGED << Stack, seq_lock >>
                        /\ UNCHANGED << topBeforePush, topBeforePop >>

popForEmptyEnd(self) == /\ pc[self] = "popForEmptyEnd"
                        /\ seq_lock' = seq_lock - 1
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << Stack, topBeforePush, topBeforePop >>

worker(self) == pushForEmpty(self) \/ pushContinue(self)
                   \/ pushForNotEmpty(self) \/ unlockAfterInitialPush(self)
                   \/ popForEmptyStart(self) \/ popContinue(self)
                   \/ popForNotEmpty(self) \/ popForEmptyEnd(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..WORKERS_TOTAL: worker(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 



=====
