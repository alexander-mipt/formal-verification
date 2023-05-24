------------------------ MODULE fifo --------------------------
EXTENDS Naturals, Sequences, TLC
CONSTANT MaxBufSize

(*
--algorithm FIFO_queue {
  variables
    valueSet = 0..3,
    inputChain \in [value : valueSet,
                ready : 0..1,
                acquire : 0..1],
                
    outputChain \in [value : valueSet,
                 ready : 0..1,
                 acquire : 0..1];
                 
    q = <<>>;  \* internal queue of the Buffer - a sequence of vals 

  macro CheckInvariants(chan) {
    assert (chan.value \in valueSet); 
    assert (chan.ready \in 0..1); 
    assert (chan.acquire \in 0..1);
    assert (q \in Seq(valueSet));
  }

  \* Sender
  process (MessageSend = "msend")
    variable oldReady;
  {    
    ss0:  while (TRUE) {
    ss1:    await inputChain.ready = inputChain.acquire;
    ss2:    oldReady := inputChain.ready;
            inputChain.ready := 1 - inputChain.ready;
            \* We do not assign chan.value here -> we let TLC pick all
            \* possible vals between in valueSet
             
            print <<inputChain, "MessageSend">>;
            CheckInvariants(inputChain);
            assert (inputChain.ready # oldReady);
            assert (inputChain.ready # inputChain.acquire);
          }    
    
  }; \* end process MessageSend

  \* FIFO Start
  process (BufRecv = "bufrecv")
        variable oldAquire;
  {
    br0:  while (TRUE) {
    br1:    await inputChain.ready # inputChain.acquire /\ Len(q) < MaxBufSize;
    br2:    oldAquire := inputChain.acquire;
            inputChain.acquire := 1 - inputChain.acquire;
            q := Append(q, inputChain.value);

            print <<inputChain, "BufRecv", q>>;
            CheckInvariants(inputChain);
            assert (inputChain.acquire # oldAquire);
            assert (inputChain.ready = inputChain.acquire);
          }       
  }; \* end process BufRecv

  \* FIFO End
  process (BufSend = "bufsend")
    variable oldReady;
  {    
    bs0:  while (TRUE) {
    bs1:    await outputChain.ready = outputChain.acquire;
    bs2:    oldReady := outputChain.ready;
            outputChain.ready := 1 - outputChain.ready;
            \* We do not assign chan.value here -> we let TLC pick all
            \* possible vals between in valueSet
             
            print <<outputChain, "BufSend">>;
            CheckInvariants(outputChain);
            assert (outputChain.ready # oldReady);
            assert (outputChain.ready # outputChain.acquire);
          }    
    
  }; \* end process BufSend


  \* Reciever
  process (RRecv = "rrecv")
        variable oldAquire, rval;
  {
    rr0:  while (TRUE) {
    rr1:    await outputChain.ready # outputChain.acquire /\ Len(q) > 0;
    rr2:    oldAquire := outputChain.acquire;
            outputChain.acquire := 1 - outputChain.acquire;
            rval := Head(q);
            q := Tail(q);

            print <<outputChain, "RRecv", rval>>;
            CheckInvariants(outputChain);
            assert (outputChain.acquire # oldAquire);
            assert (outputChain.ready = outputChain.acquire);
          }       
  }; \* end process RRecv

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "f8e9c2d2" /\ chksum(tla) = "d6293838")
\* Process variable oldReady of process MessageSend at line 28 col 14 changed to oldReady_
\* Process variable oldAquire of process BufRecv at line 47 col 18 changed to oldAquire_
CONSTANT defaultInitValue
VARIABLES valueSet, inputChain, outputChain, q, pc, oldReady_, oldAquire_, 
          oldReady, oldAquire, rval

vars == << valueSet, inputChain, outputChain, q, pc, oldReady_, oldAquire_, 
           oldReady, oldAquire, rval >>

ProcSet == {"msend"} \cup {"bufrecv"} \cup {"bufsend"} \cup {"rrecv"}

Init == (* Global variables *)
        /\ valueSet = 0..3
        /\ inputChain \in    [value : valueSet,
                          ready : 0..1,
                          acquire : 0..1]
        /\ outputChain \in    [value : valueSet,
                           ready : 0..1,
                           acquire : 0..1]
        /\ q = <<>>
        (* Process MessageSend *)
        /\ oldReady_ = defaultInitValue
        (* Process BufRecv *)
        /\ oldAquire_ = defaultInitValue
        (* Process BufSend *)
        /\ oldReady = defaultInitValue
        (* Process RRecv *)
        /\ oldAquire = defaultInitValue
        /\ rval = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "msend" -> "ss0"
                                        [] self = "bufrecv" -> "br0"
                                        [] self = "bufsend" -> "bs0"
                                        [] self = "rrecv" -> "rr0"]

ss0 == /\ pc["msend"] = "ss0"
       /\ pc' = [pc EXCEPT !["msend"] = "ss1"]
       /\ UNCHANGED << valueSet, inputChain, outputChain, q, oldReady_, 
                       oldAquire_, oldReady, oldAquire, rval >>

ss1 == /\ pc["msend"] = "ss1"
       /\ inputChain.ready = inputChain.acquire
       /\ pc' = [pc EXCEPT !["msend"] = "ss2"]
       /\ UNCHANGED << valueSet, inputChain, outputChain, q, oldReady_, 
                       oldAquire_, oldReady, oldAquire, rval >>

ss2 == /\ pc["msend"] = "ss2"
       /\ oldReady_' = inputChain.ready
       /\ inputChain' = [inputChain EXCEPT !.ready = 1 - inputChain.ready]
       /\ PrintT(<<inputChain', "MessageSend">>)
       /\ Assert((inputChain'.value \in valueSet), 
                 "Failure of assertion at line 20, column 5 of macro called at line 38, column 13.")
       /\ Assert((inputChain'.ready \in 0..1), 
                 "Failure of assertion at line 21, column 5 of macro called at line 38, column 13.")
       /\ Assert((inputChain'.acquire \in 0..1), 
                 "Failure of assertion at line 22, column 5 of macro called at line 38, column 13.")
       /\ Assert((q \in Seq(valueSet)), 
                 "Failure of assertion at line 23, column 5 of macro called at line 38, column 13.")
       /\ Assert((inputChain'.ready # oldReady_'), 
                 "Failure of assertion at line 39, column 13.")
       /\ Assert((inputChain'.ready # inputChain'.acquire), 
                 "Failure of assertion at line 40, column 13.")
       /\ pc' = [pc EXCEPT !["msend"] = "ss0"]
       /\ UNCHANGED << valueSet, outputChain, q, oldAquire_, oldReady, 
                       oldAquire, rval >>

MessageSend == ss0 \/ ss1 \/ ss2

br0 == /\ pc["bufrecv"] = "br0"
       /\ pc' = [pc EXCEPT !["bufrecv"] = "br1"]
       /\ UNCHANGED << valueSet, inputChain, outputChain, q, oldReady_, 
                       oldAquire_, oldReady, oldAquire, rval >>

br1 == /\ pc["bufrecv"] = "br1"
       /\ inputChain.ready # inputChain.acquire /\ Len(q) < MaxBufSize
       /\ pc' = [pc EXCEPT !["bufrecv"] = "br2"]
       /\ UNCHANGED << valueSet, inputChain, outputChain, q, oldReady_, 
                       oldAquire_, oldReady, oldAquire, rval >>

br2 == /\ pc["bufrecv"] = "br2"
       /\ oldAquire_' = inputChain.acquire
       /\ inputChain' = [inputChain EXCEPT !.acquire = 1 - inputChain.acquire]
       /\ q' = Append(q, inputChain'.value)
       /\ PrintT(<<inputChain', "BufRecv", q'>>)
       /\ Assert((inputChain'.value \in valueSet), 
                 "Failure of assertion at line 20, column 5 of macro called at line 56, column 13.")
       /\ Assert((inputChain'.ready \in 0..1), 
                 "Failure of assertion at line 21, column 5 of macro called at line 56, column 13.")
       /\ Assert((inputChain'.acquire \in 0..1), 
                 "Failure of assertion at line 22, column 5 of macro called at line 56, column 13.")
       /\ Assert((q' \in Seq(valueSet)), 
                 "Failure of assertion at line 23, column 5 of macro called at line 56, column 13.")
       /\ Assert((inputChain'.acquire # oldAquire_'), 
                 "Failure of assertion at line 57, column 13.")
       /\ Assert((inputChain'.ready = inputChain'.acquire), 
                 "Failure of assertion at line 58, column 13.")
       /\ pc' = [pc EXCEPT !["bufrecv"] = "br0"]
       /\ UNCHANGED << valueSet, outputChain, oldReady_, oldReady, oldAquire, 
                       rval >>

BufRecv == br0 \/ br1 \/ br2

bs0 == /\ pc["bufsend"] = "bs0"
       /\ pc' = [pc EXCEPT !["bufsend"] = "bs1"]
       /\ UNCHANGED << valueSet, inputChain, outputChain, q, oldReady_, 
                       oldAquire_, oldReady, oldAquire, rval >>

bs1 == /\ pc["bufsend"] = "bs1"
       /\ outputChain.ready = outputChain.acquire
       /\ pc' = [pc EXCEPT !["bufsend"] = "bs2"]
       /\ UNCHANGED << valueSet, inputChain, outputChain, q, oldReady_, 
                       oldAquire_, oldReady, oldAquire, rval >>

bs2 == /\ pc["bufsend"] = "bs2"
       /\ oldReady' = outputChain.ready
       /\ outputChain' = [outputChain EXCEPT !.ready = 1 - outputChain.ready]
       /\ PrintT(<<outputChain', "BufSend">>)
       /\ Assert((outputChain'.value \in valueSet), 
                 "Failure of assertion at line 20, column 5 of macro called at line 74, column 13.")
       /\ Assert((outputChain'.ready \in 0..1), 
                 "Failure of assertion at line 21, column 5 of macro called at line 74, column 13.")
       /\ Assert((outputChain'.acquire \in 0..1), 
                 "Failure of assertion at line 22, column 5 of macro called at line 74, column 13.")
       /\ Assert((q \in Seq(valueSet)), 
                 "Failure of assertion at line 23, column 5 of macro called at line 74, column 13.")
       /\ Assert((outputChain'.ready # oldReady'), 
                 "Failure of assertion at line 75, column 13.")
       /\ Assert((outputChain'.ready # outputChain'.acquire), 
                 "Failure of assertion at line 76, column 13.")
       /\ pc' = [pc EXCEPT !["bufsend"] = "bs0"]
       /\ UNCHANGED << valueSet, inputChain, q, oldReady_, oldAquire_, 
                       oldAquire, rval >>

BufSend == bs0 \/ bs1 \/ bs2

rr0 == /\ pc["rrecv"] = "rr0"
       /\ pc' = [pc EXCEPT !["rrecv"] = "rr1"]
       /\ UNCHANGED << valueSet, inputChain, outputChain, q, oldReady_, 
                       oldAquire_, oldReady, oldAquire, rval >>

rr1 == /\ pc["rrecv"] = "rr1"
       /\ outputChain.ready # outputChain.acquire /\ Len(q) > 0
       /\ pc' = [pc EXCEPT !["rrecv"] = "rr2"]
       /\ UNCHANGED << valueSet, inputChain, outputChain, q, oldReady_, 
                       oldAquire_, oldReady, oldAquire, rval >>

rr2 == /\ pc["rrecv"] = "rr2"
       /\ oldAquire' = outputChain.acquire
       /\ outputChain' = [outputChain EXCEPT !.acquire = 1 - outputChain.acquire]
       /\ rval' = Head(q)
       /\ q' = Tail(q)
       /\ PrintT(<<outputChain', "RRecv", rval'>>)
       /\ Assert((outputChain'.value \in valueSet), 
                 "Failure of assertion at line 20, column 5 of macro called at line 94, column 13.")
       /\ Assert((outputChain'.ready \in 0..1), 
                 "Failure of assertion at line 21, column 5 of macro called at line 94, column 13.")
       /\ Assert((outputChain'.acquire \in 0..1), 
                 "Failure of assertion at line 22, column 5 of macro called at line 94, column 13.")
       /\ Assert((q' \in Seq(valueSet)), 
                 "Failure of assertion at line 23, column 5 of macro called at line 94, column 13.")
       /\ Assert((outputChain'.acquire # oldAquire'), 
                 "Failure of assertion at line 95, column 13.")
       /\ Assert((outputChain'.ready = outputChain'.acquire), 
                 "Failure of assertion at line 96, column 13.")
       /\ pc' = [pc EXCEPT !["rrecv"] = "rr0"]
       /\ UNCHANGED << valueSet, inputChain, oldReady_, oldAquire_, oldReady >>

RRecv == rr0 \/ rr1 \/ rr2

Next == MessageSend \/ BufRecv \/ BufSend \/ RRecv

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
===================
