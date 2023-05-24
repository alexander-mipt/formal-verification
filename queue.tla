------------------------------- MODULE queue -------------------------------

EXTENDS TLC, Integers, Sequences
CONSTANTS Consumers, Producers, TasksTotal
(*--algorithm message_queue
\* The first element of queue is 0 to indicate end of queue.
\* Later queue will be appended with incremented maxID, therefore other 0 in queue.
variables queue = <<0>>,
         TasksPopped = 0,
         maxID = 0,
         RemainedTasks = TasksTotal,
         ConsumeFlags = [w \in Consumers |-> FALSE];


define
NoMissedTasks == TasksPopped + Len(queue) + RemainedTasks - 1 = TasksTotal
QueueLenValid == Len(queue) <= TasksTotal + 1 /\ Len(queue) >= 1
end define;

macro CompareAndStoreDesired(successFlag, ptr, expected, desired) begin
    if (ptr = expected) then
        ptr := desired;
        successFlag := TRUE;
    else
        successFlag := FALSE;
    end if;
end macro


macro LastQueueElem(Val) begin
    Val := queue[Len(queue)];
end macro


procedure Push() begin
PushLoopBegin:
    while TRUE do
        GetTailPtr: LastQueueElem(PushPtr);
        GetTailInPush1: LastQueueElem(PushVal1);
        
        \* PlusCal do not implement pointers, val1 emulates its behaviour
        \* check that Ptr = *PushPtr && Ptr has the same result - for secure ABA check
        PushTail:
        if PushPtr = PushVal1 then
            if PushPtr = maxID then
                GetTailInPush2: LastQueueElem(PushVal2);
                SuccPush: CompareAndStoreDesired(PushSucc, maxID, PushVal2, PushPtr + 1);
                \* This 'if' atomic with CompareAndStoreDesired above as encapsulate behaviour of atomically update queue.
                \* Same as with SuccDeq
                if PushSucc then
                    if RemainedTasks /= 0 then
                        return;
                    else
                        queue := Append(queue, maxID);
                        RemainedTasks := RemainedTasks - 1;
                        return;
                    end if;
                end if;
            else
                \* Try to swing tail.
                GetTailInPush3: LastQueueElem(PushVal3);
                SwingTailInPush: CompareAndStoreDesired(PushSucc, PushPtr, PushVal3, PushPtr + 1);
            end if;
        end if;
    end while;
end procedure;

procedure Pop() begin
PopLoopBegin:
    while TRUE do
        GetHeaderPtr: PopPtr := Head(queue);
        GetHeaderinPop1: HeaderVal1 := Head(queue);
        GetTailInPop1: LastQueueElem(TailVal1);
        PopHeader:
            if PopPtr = HeaderVal1 then
                if PopPtr = PushPtr then
                    if PopPtr = 0 then \* queue is empty
                        QueueIsEmpty: ConsumeFlags[self] := FALSE;
                        return;
                    else
                        \* Try to swing tail.
                        GetTailInPop2: LastQueueElem(TailVal2);
                        SwingTailInPop: CompareAndStoreDesired(PopSucc, TailVal1, TailVal2, PushPtr + 1);
                    end if;
                else
                    GetHeaderInPop2: HeaderVal2 := Head(queue);
                    SuccDeq: CompareAndStoreDesired(PopSucc, PopPtr, HeaderVal2, PopPtr + 1);
                    if PopSucc then
                        queue := Tail(queue);
                        TasksPopped := TasksPopped + 1;
                        ConsumeFlags[self] := TRUE;
                        return;
                    end if;
                end if;
            end if;
    end while;
end procedure;
    

process writer \in Producers
variables PushPtr = 0, PushVal1 = 0, PushVal2 = 0, PushVal3 = 0, PushSucc = TRUE;
begin Write:
    while RemainedTasks /= 0 do
        call Push();
    end while;
end process;

process reader \in Consumers
variables PopPtr = 0, HeaderVal1 = 0, HeaderVal2 = 0, TailVal1 = 0, TailVal2 = 0, PopSucc = TRUE;
begin Read:
    while TRUE do
        \* This await not for lock queue but work-around infinite states of reading empty queue.
        await Len(queue) > 1;
        Deq: call Pop();
    end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "934045fe" /\ chksum(tla) = "c6099d55")
VARIABLES queue, TasksPopped, maxID, RemainedTasks, ConsumeFlags, pc, stack

(* define statement *)
NoMissedTasks == TasksPopped + Len(queue) + RemainedTasks - 1 = TasksTotal
QueueLenValid == Len(queue) <= TasksTotal + 1 /\ Len(queue) >= 1

VARIABLES PushPtr, PushVal1, PushVal2, PushVal3, PushSucc, PopPtr, HeaderVal1, 
          HeaderVal2, TailVal1, TailVal2, PopSucc

vars == << queue, TasksPopped, maxID, RemainedTasks, ConsumeFlags, pc, stack, 
           PushPtr, PushVal1, PushVal2, PushVal3, PushSucc, PopPtr, 
           HeaderVal1, HeaderVal2, TailVal1, TailVal2, PopSucc >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ queue = <<0>>
        /\ TasksPopped = 0
        /\ maxID = 0
        /\ RemainedTasks = TasksTotal
        /\ ConsumeFlags = [w \in Consumers |-> FALSE]
        (* Process writer *)
        /\ PushPtr = [self \in Producers |-> 0]
        /\ PushVal1 = [self \in Producers |-> 0]
        /\ PushVal2 = [self \in Producers |-> 0]
        /\ PushVal3 = [self \in Producers |-> 0]
        /\ PushSucc = [self \in Producers |-> TRUE]
        (* Process reader *)
        /\ PopPtr = [self \in Consumers |-> 0]
        /\ HeaderVal1 = [self \in Consumers |-> 0]
        /\ HeaderVal2 = [self \in Consumers |-> 0]
        /\ TailVal1 = [self \in Consumers |-> 0]
        /\ TailVal2 = [self \in Consumers |-> 0]
        /\ PopSucc = [self \in Consumers |-> TRUE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "Write"
                                        [] self \in Consumers -> "Read"]

PushLoopBegin(self) == /\ pc[self] = "PushLoopBegin"
                       /\ pc' = [pc EXCEPT ![self] = "GetTailPtr"]
                       /\ UNCHANGED << queue, TasksPopped, maxID, 
                                       RemainedTasks, ConsumeFlags, stack, 
                                       PushPtr, PushVal1, PushVal2, PushVal3, 
                                       PushSucc, PopPtr, HeaderVal1, 
                                       HeaderVal2, TailVal1, TailVal2, PopSucc >>

GetTailPtr(self) == /\ pc[self] = "GetTailPtr"
                    /\ PushPtr' = [PushPtr EXCEPT ![self] = queue[Len(queue)]]
                    /\ pc' = [pc EXCEPT ![self] = "GetTailInPush1"]
                    /\ UNCHANGED << queue, TasksPopped, maxID, RemainedTasks, 
                                    ConsumeFlags, stack, PushVal1, PushVal2, 
                                    PushVal3, PushSucc, PopPtr, HeaderVal1, 
                                    HeaderVal2, TailVal1, TailVal2, PopSucc >>

GetTailInPush1(self) == /\ pc[self] = "GetTailInPush1"
                        /\ PushVal1' = [PushVal1 EXCEPT ![self] = queue[Len(queue)]]
                        /\ pc' = [pc EXCEPT ![self] = "PushTail"]
                        /\ UNCHANGED << queue, TasksPopped, maxID, 
                                        RemainedTasks, ConsumeFlags, stack, 
                                        PushPtr, PushVal2, PushVal3, PushSucc, 
                                        PopPtr, HeaderVal1, HeaderVal2, 
                                        TailVal1, TailVal2, PopSucc >>

PushTail(self) == /\ pc[self] = "PushTail"
                  /\ IF PushPtr[self] = PushVal1[self]
                        THEN /\ IF PushPtr[self] = maxID
                                   THEN /\ pc' = [pc EXCEPT ![self] = "GetTailInPush2"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "GetTailInPush3"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "PushLoopBegin"]
                  /\ UNCHANGED << queue, TasksPopped, maxID, RemainedTasks, 
                                  ConsumeFlags, stack, PushPtr, PushVal1, 
                                  PushVal2, PushVal3, PushSucc, PopPtr, 
                                  HeaderVal1, HeaderVal2, TailVal1, TailVal2, 
                                  PopSucc >>

GetTailInPush2(self) == /\ pc[self] = "GetTailInPush2"
                        /\ PushVal2' = [PushVal2 EXCEPT ![self] = queue[Len(queue)]]
                        /\ pc' = [pc EXCEPT ![self] = "SuccPush"]
                        /\ UNCHANGED << queue, TasksPopped, maxID, 
                                        RemainedTasks, ConsumeFlags, stack, 
                                        PushPtr, PushVal1, PushVal3, PushSucc, 
                                        PopPtr, HeaderVal1, HeaderVal2, 
                                        TailVal1, TailVal2, PopSucc >>

SuccPush(self) == /\ pc[self] = "SuccPush"
                  /\ IF (maxID = PushVal2[self])
                        THEN /\ maxID' = PushPtr[self] + 1
                             /\ PushSucc' = [PushSucc EXCEPT ![self] = TRUE]
                        ELSE /\ PushSucc' = [PushSucc EXCEPT ![self] = FALSE]
                             /\ maxID' = maxID
                  /\ IF PushSucc'[self]
                        THEN /\ IF RemainedTasks /= 0
                                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                        /\ UNCHANGED << queue, RemainedTasks >>
                                   ELSE /\ queue' = Append(queue, maxID')
                                        /\ RemainedTasks' = RemainedTasks - 1
                                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "PushLoopBegin"]
                             /\ UNCHANGED << queue, RemainedTasks, stack >>
                  /\ UNCHANGED << TasksPopped, ConsumeFlags, PushPtr, PushVal1, 
                                  PushVal2, PushVal3, PopPtr, HeaderVal1, 
                                  HeaderVal2, TailVal1, TailVal2, PopSucc >>

GetTailInPush3(self) == /\ pc[self] = "GetTailInPush3"
                        /\ PushVal3' = [PushVal3 EXCEPT ![self] = queue[Len(queue)]]
                        /\ pc' = [pc EXCEPT ![self] = "SwingTailInPush"]
                        /\ UNCHANGED << queue, TasksPopped, maxID, 
                                        RemainedTasks, ConsumeFlags, stack, 
                                        PushPtr, PushVal1, PushVal2, PushSucc, 
                                        PopPtr, HeaderVal1, HeaderVal2, 
                                        TailVal1, TailVal2, PopSucc >>

SwingTailInPush(self) == /\ pc[self] = "SwingTailInPush"
                         /\ IF (PushPtr[self] = PushVal3[self])
                               THEN /\ PushPtr' = [PushPtr EXCEPT ![self] = PushPtr[self] + 1]
                                    /\ PushSucc' = [PushSucc EXCEPT ![self] = TRUE]
                               ELSE /\ PushSucc' = [PushSucc EXCEPT ![self] = FALSE]
                                    /\ UNCHANGED PushPtr
                         /\ pc' = [pc EXCEPT ![self] = "PushLoopBegin"]
                         /\ UNCHANGED << queue, TasksPopped, maxID, 
                                         RemainedTasks, ConsumeFlags, stack, 
                                         PushVal1, PushVal2, PushVal3, PopPtr, 
                                         HeaderVal1, HeaderVal2, TailVal1, 
                                         TailVal2, PopSucc >>

Push(self) == PushLoopBegin(self) \/ GetTailPtr(self)
                 \/ GetTailInPush1(self) \/ PushTail(self)
                 \/ GetTailInPush2(self) \/ SuccPush(self)
                 \/ GetTailInPush3(self) \/ SwingTailInPush(self)

PopLoopBegin(self) == /\ pc[self] = "PopLoopBegin"
                      /\ pc' = [pc EXCEPT ![self] = "GetHeaderPtr"]
                      /\ UNCHANGED << queue, TasksPopped, maxID, RemainedTasks, 
                                      ConsumeFlags, stack, PushPtr, PushVal1, 
                                      PushVal2, PushVal3, PushSucc, PopPtr, 
                                      HeaderVal1, HeaderVal2, TailVal1, 
                                      TailVal2, PopSucc >>

GetHeaderPtr(self) == /\ pc[self] = "GetHeaderPtr"
                      /\ PopPtr' = [PopPtr EXCEPT ![self] = Head(queue)]
                      /\ pc' = [pc EXCEPT ![self] = "GetHeaderinPop1"]
                      /\ UNCHANGED << queue, TasksPopped, maxID, RemainedTasks, 
                                      ConsumeFlags, stack, PushPtr, PushVal1, 
                                      PushVal2, PushVal3, PushSucc, HeaderVal1, 
                                      HeaderVal2, TailVal1, TailVal2, PopSucc >>

GetHeaderinPop1(self) == /\ pc[self] = "GetHeaderinPop1"
                         /\ HeaderVal1' = [HeaderVal1 EXCEPT ![self] = Head(queue)]
                         /\ pc' = [pc EXCEPT ![self] = "GetTailInPop1"]
                         /\ UNCHANGED << queue, TasksPopped, maxID, 
                                         RemainedTasks, ConsumeFlags, stack, 
                                         PushPtr, PushVal1, PushVal2, PushVal3, 
                                         PushSucc, PopPtr, HeaderVal2, 
                                         TailVal1, TailVal2, PopSucc >>

GetTailInPop1(self) == /\ pc[self] = "GetTailInPop1"
                       /\ TailVal1' = [TailVal1 EXCEPT ![self] = queue[Len(queue)]]
                       /\ pc' = [pc EXCEPT ![self] = "PopHeader"]
                       /\ UNCHANGED << queue, TasksPopped, maxID, 
                                       RemainedTasks, ConsumeFlags, stack, 
                                       PushPtr, PushVal1, PushVal2, PushVal3, 
                                       PushSucc, PopPtr, HeaderVal1, 
                                       HeaderVal2, TailVal2, PopSucc >>

PopHeader(self) == /\ pc[self] = "PopHeader"
                   /\ IF PopPtr[self] = HeaderVal1[self]
                         THEN /\ IF PopPtr[self] = PushPtr[self]
                                    THEN /\ IF PopPtr[self] = 0
                                               THEN /\ pc' = [pc EXCEPT ![self] = "QueueIsEmpty"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "GetTailInPop2"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "GetHeaderInPop2"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "PopLoopBegin"]
                   /\ UNCHANGED << queue, TasksPopped, maxID, RemainedTasks, 
                                   ConsumeFlags, stack, PushPtr, PushVal1, 
                                   PushVal2, PushVal3, PushSucc, PopPtr, 
                                   HeaderVal1, HeaderVal2, TailVal1, TailVal2, 
                                   PopSucc >>

GetHeaderInPop2(self) == /\ pc[self] = "GetHeaderInPop2"
                         /\ HeaderVal2' = [HeaderVal2 EXCEPT ![self] = Head(queue)]
                         /\ pc' = [pc EXCEPT ![self] = "SuccDeq"]
                         /\ UNCHANGED << queue, TasksPopped, maxID, 
                                         RemainedTasks, ConsumeFlags, stack, 
                                         PushPtr, PushVal1, PushVal2, PushVal3, 
                                         PushSucc, PopPtr, HeaderVal1, 
                                         TailVal1, TailVal2, PopSucc >>

SuccDeq(self) == /\ pc[self] = "SuccDeq"
                 /\ IF (PopPtr[self] = HeaderVal2[self])
                       THEN /\ PopPtr' = [PopPtr EXCEPT ![self] = PopPtr[self] + 1]
                            /\ PopSucc' = [PopSucc EXCEPT ![self] = TRUE]
                       ELSE /\ PopSucc' = [PopSucc EXCEPT ![self] = FALSE]
                            /\ UNCHANGED PopPtr
                 /\ IF PopSucc'[self]
                       THEN /\ queue' = Tail(queue)
                            /\ TasksPopped' = TasksPopped + 1
                            /\ ConsumeFlags' = [ConsumeFlags EXCEPT ![self] = TRUE]
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "PopLoopBegin"]
                            /\ UNCHANGED << queue, TasksPopped, ConsumeFlags, 
                                            stack >>
                 /\ UNCHANGED << maxID, RemainedTasks, PushPtr, PushVal1, 
                                 PushVal2, PushVal3, PushSucc, HeaderVal1, 
                                 HeaderVal2, TailVal1, TailVal2 >>

QueueIsEmpty(self) == /\ pc[self] = "QueueIsEmpty"
                      /\ ConsumeFlags' = [ConsumeFlags EXCEPT ![self] = FALSE]
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << queue, TasksPopped, maxID, RemainedTasks, 
                                      PushPtr, PushVal1, PushVal2, PushVal3, 
                                      PushSucc, PopPtr, HeaderVal1, HeaderVal2, 
                                      TailVal1, TailVal2, PopSucc >>

GetTailInPop2(self) == /\ pc[self] = "GetTailInPop2"
                       /\ TailVal2' = [TailVal2 EXCEPT ![self] = queue[Len(queue)]]
                       /\ pc' = [pc EXCEPT ![self] = "SwingTailInPop"]
                       /\ UNCHANGED << queue, TasksPopped, maxID, 
                                       RemainedTasks, ConsumeFlags, stack, 
                                       PushPtr, PushVal1, PushVal2, PushVal3, 
                                       PushSucc, PopPtr, HeaderVal1, 
                                       HeaderVal2, TailVal1, PopSucc >>

SwingTailInPop(self) == /\ pc[self] = "SwingTailInPop"
                        /\ IF (TailVal1[self] = TailVal2[self])
                              THEN /\ TailVal1' = [TailVal1 EXCEPT ![self] = PushPtr[self] + 1]
                                   /\ PopSucc' = [PopSucc EXCEPT ![self] = TRUE]
                              ELSE /\ PopSucc' = [PopSucc EXCEPT ![self] = FALSE]
                                   /\ UNCHANGED TailVal1
                        /\ pc' = [pc EXCEPT ![self] = "PopLoopBegin"]
                        /\ UNCHANGED << queue, TasksPopped, maxID, 
                                        RemainedTasks, ConsumeFlags, stack, 
                                        PushPtr, PushVal1, PushVal2, PushVal3, 
                                        PushSucc, PopPtr, HeaderVal1, 
                                        HeaderVal2, TailVal2 >>

Pop(self) == PopLoopBegin(self) \/ GetHeaderPtr(self)
                \/ GetHeaderinPop1(self) \/ GetTailInPop1(self)
                \/ PopHeader(self) \/ GetHeaderInPop2(self)
                \/ SuccDeq(self) \/ QueueIsEmpty(self)
                \/ GetTailInPop2(self) \/ SwingTailInPop(self)

Write(self) == /\ pc[self] = "Write"
               /\ IF RemainedTasks /= 0
                     THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Push",
                                                                   pc        |->  "Write" ] >>
                                                               \o stack[self]]
                          /\ pc' = [pc EXCEPT ![self] = "PushLoopBegin"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ stack' = stack
               /\ UNCHANGED << queue, TasksPopped, maxID, RemainedTasks, 
                               ConsumeFlags, PushPtr, PushVal1, PushVal2, 
                               PushVal3, PushSucc, PopPtr, HeaderVal1, 
                               HeaderVal2, TailVal1, TailVal2, PopSucc >>

writer(self) == Write(self)

Read(self) == /\ pc[self] = "Read"
              /\ Len(queue) > 1
              /\ pc' = [pc EXCEPT ![self] = "Deq"]
              /\ UNCHANGED << queue, TasksPopped, maxID, RemainedTasks, 
                              ConsumeFlags, stack, PushPtr, PushVal1, PushVal2, 
                              PushVal3, PushSucc, PopPtr, HeaderVal1, 
                              HeaderVal2, TailVal1, TailVal2, PopSucc >>

Deq(self) == /\ pc[self] = "Deq"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Pop",
                                                      pc        |->  "Read" ] >>
                                                  \o stack[self]]
             /\ pc' = [pc EXCEPT ![self] = "PopLoopBegin"]
             /\ UNCHANGED << queue, TasksPopped, maxID, RemainedTasks, 
                             ConsumeFlags, PushPtr, PushVal1, PushVal2, 
                             PushVal3, PushSucc, PopPtr, HeaderVal1, 
                             HeaderVal2, TailVal1, TailVal2, PopSucc >>

reader(self) == Read(self) \/ Deq(self)

Next == (\E self \in ProcSet: Push(self) \/ Pop(self))
           \/ (\E self \in Producers: writer(self))
           \/ (\E self \in Consumers: reader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
===========================================
